-- Prove2me | solution 1 for AaronsonAmbainis.Short.det_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-17T15:31:31.912204+00:00
-- url     : https://prove2.me/submissions/b17224ef-b672-45ae-a18f-3570224206bb

import Mathlib
import Definitions.Def_AaronsonAmbainis_Short
open AaronsonAmbainis
open Finset

namespace AASolDet

set_option linter.unusedSectionVars false

open MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ### Weights of monomials -/

/-- The weight of a monomial. -/
noncomputable def wt (w : ι → ℝ) (m : ι →₀ ℕ) : ℝ := ∑ i, w i * (m i : ℝ)

lemma wt_add (w : ι → ℝ) (a b : ι →₀ ℕ) : wt w (a + b) = wt w a + wt w b := by
  simp [wt, mul_add, Finset.sum_add_distrib]

lemma wt_zero (w : ι → ℝ) : wt w 0 = 0 := by simp [wt]

lemma wt_single (w : ι → ℝ) (i : ι) : wt w (Finsupp.single i 1) = w i := by
  simp [wt, Finsupp.single_apply]

/-- Every monomial of `p` has weight at least `c`. -/
def WtGE (w : ι → ℝ) (c : ℝ) (p : MvPolynomial ι ℤ) : Prop :=
  ∀ m ∈ p.support, c ≤ wt w m

variable {w : ι → ℝ} {a b : ℝ} {p q : MvPolynomial ι ℤ}

lemma WtGE.mono (h : WtGE w a p) (hc : b ≤ a) : WtGE w b p :=
  fun m hm => hc.trans (h m hm)

lemma WtGE.zero (w : ι → ℝ) (c : ℝ) : WtGE w c 0 := by
  intro m hm
  simp at hm

lemma WtGE.one (w : ι → ℝ) : WtGE w 0 (1 : MvPolynomial ι ℤ) := by
  intro m hm
  rw [MvPolynomial.support_one] at hm
  rw [Finset.mem_singleton.1 hm, wt_zero]

lemma WtGE.X (w : ι → ℝ) (i : ι) : WtGE w (w i) (X i : MvPolynomial ι ℤ) := by
  intro m hm
  rw [MvPolynomial.support_X] at hm
  rw [Finset.mem_singleton.1 hm, wt_single]

lemma WtGE.mul (hp : WtGE w a p) (hq : WtGE w b q) : WtGE w (a + b) (p * q) := by
  intro m hm
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul p q hm)
  rw [wt_add]
  exact add_le_add (hp u hu) (hq v hv)

lemma WtGE.neg (hp : WtGE w a p) : WtGE w a (-p) := by
  intro m hm
  apply hp
  simpa using hm

lemma WtGE.sum {α : Type*} (s : Finset α) (f : α → MvPolynomial ι ℤ)
    (h : ∀ x ∈ s, WtGE w a (f x)) : WtGE w a (∑ x ∈ s, f x) := by
  intro m hm
  obtain ⟨x, hx, hmx⟩ := Finset.mem_biUnion.1 (MvPolynomial.support_sum hm)
  exact h x hx m hmx

lemma WtGE.prod {α : Type*} (s : Finset α) (f : α → MvPolynomial ι ℤ) (c : α → ℝ)
    (h : ∀ x ∈ s, WtGE w (c x) (f x)) : WtGE w (∑ x ∈ s, c x) (∏ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using WtGE.one w
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact (h x (Finset.mem_insert_self x s)).mul
      (ih fun y hy => h y (Finset.mem_insert_of_mem hy))

lemma WtGE.det {n : Type*} [Fintype n] [DecidableEq n]
    (N : Matrix n n (MvPolynomial ι ℤ)) (c : n → ℝ)
    (h : ∀ x z, WtGE w (c x) (N x z)) : WtGE w (∑ x, c x) N.det := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply WtGE.sum
  intro σ _
  have hp : WtGE w (∑ x, c x) (∏ x, N x (σ x)) :=
    WtGE.prod _ _ _ (fun x _ => h x (σ x))
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs] using hp
  · simpa [hs] using hp.neg

/-! ### Minimal monomials and multiplication by a polynomial with constant term one -/

lemma exists_le_of_mem_support_mul (u q : MvPolynomial ι ℤ) (m : ι →₀ ℕ)
    (hm : m ∈ (u * q).support) : ∃ b ∈ q.support, b ≤ m := by
  obtain ⟨a, _, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul u q hm)
  exact ⟨b, hb, le_add_self⟩

lemma coeff_mul_of_minimal (u q : MvPolynomial ι ℤ) (hu : constantCoeff u = 1)
    (m : ι →₀ ℕ) (hm : Minimal (· ∈ q.support) m) : coeff m (u * q) = coeff m q := by
  classical
  have h0 : coeff 0 u = 1 := by
    rw [← MvPolynomial.constantCoeff_eq]
    exact hu
  rw [MvPolynomial.coeff_mul, Finset.sum_eq_single (0, m)]
  · simp [h0]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = m := Finset.HasAntidiagonal.mem_antidiagonal.1 hab
    by_cases hb : b ∈ q.support
    · have hbm : b ≤ m := hab' ▸ le_add_self
      have hbm' : b = m := le_antisymm hbm (hm.2 hb hbm)
      have ha : a = 0 := by
        rw [hbm'] at hab'
        simpa using hab'
      exact (hne (by rw [ha, hbm'])).elim
    · simp [MvPolynomial.notMem_support_iff.1 hb]
  · intro h
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add m)) h

lemma minimal_mul_iff (u q : MvPolynomial ι ℤ) (hu : constantCoeff u = 1) (m : ι →₀ ℕ) :
    Minimal (· ∈ (u * q).support) m ↔ Minimal (· ∈ q.support) m := by
  have fwd : ∀ m, Minimal (· ∈ q.support) m → Minimal (· ∈ (u * q).support) m := by
    intro m hm
    refine ⟨?_, ?_⟩
    · show m ∈ (u * q).support
      rw [MvPolynomial.mem_support_iff, coeff_mul_of_minimal u q hu m hm]
      exact MvPolynomial.mem_support_iff.1 hm.1
    · intro m' hm' hle
      obtain ⟨b, hb, hbm'⟩ := exists_le_of_mem_support_mul u q m' hm'
      exact (hm.2 hb (hbm'.trans hle)).trans hbm'
  refine ⟨fun hm => ?_, fwd m⟩
  obtain ⟨b, hb, hbm⟩ := exists_le_of_mem_support_mul u q m hm.1
  obtain ⟨b', hb'b, hb'⟩ := exists_minimal_le_of_wellFoundedLT (· ∈ q.support) b hb
  have h1 := fwd b' hb'
  have h2 : m ≤ b' := hm.2 h1.1 (hb'b.trans hbm)
  have h3 : b' = m := le_antisymm (hb'b.trans hbm) h2
  exact h3 ▸ hb'

/-! ### The matrix -/

lemma flipSet_empty (x : Cube ι) : flipSet x ∅ = x := by
  funext i
  simp [flipSet]

/-- The entry `∏_{i : x i = z i} X i`. -/
noncomputable def ent (x z : Cube ι) : MvPolynomial ι ℤ :=
  ∏ i, if x i = z i then X i else 1

lemma ent_wt (w : ι → ℝ) (x z : Cube ι) :
    WtGE w (∑ i, if x i = z i then w i else 0) (ent x z) := by
  unfold ent
  apply WtGE.prod
  intro i _
  split_ifs
  · exact WtGE.X w i
  · exact WtGE.one w

lemma fac (i : ι) (b c : Bool) :
    (-X i : MvPolynomial ι ℤ) * (if (!b) = c then X i else 1) + (if b = c then X i else 1)
      = if b = c then 0 else 1 - X i ^ 2 := by
  cases b <;> cases c <;> simp <;> ring

/-- The row identity (6). -/
lemma row_id (x z : Cube ι) (K : Finset ι) :
    ∑ S ∈ K.powerset, (∏ i ∈ S, (-X i : MvPolynomial ι ℤ)) * ent (flipSet x S) z
      = (∏ i ∈ K, (1 - X i ^ 2)) * (if K ⊆ diffSet x z then ent x z else 0) := by
  have h1 : ∀ S ∈ K.powerset,
      (∏ i ∈ S, (-X i : MvPolynomial ι ℤ)) * ent (flipSet x S) z
      = ((∏ i ∈ S, (-X i * (if (!(x i)) = z i then X i else 1)))
          * ∏ i ∈ K \ S, (if x i = z i then X i else 1))
        * ∏ i ∈ Kᶜ, (if x i = z i then X i else 1) := by
    intro S hS
    have hSK := Finset.mem_powerset.1 hS
    have e : ent (flipSet x S) z
        = ((∏ i ∈ K \ S, (if x i = z i then X i else 1 : MvPolynomial ι ℤ))
            * ∏ i ∈ S, (if (!(x i)) = z i then X i else 1))
          * ∏ i ∈ Kᶜ, (if x i = z i then X i else 1) := by
      unfold ent
      rw [← Finset.prod_mul_prod_compl K, ← Finset.prod_sdiff hSK]
      congr 1
      · congr 1
        · exact Finset.prod_congr rfl fun i hi => by
            simp [flipSet, (Finset.mem_sdiff.1 hi).2]
        · exact Finset.prod_congr rfl fun i hi => by simp [flipSet, hi]
      · exact Finset.prod_congr rfl fun i hi => by
          have : i ∉ S := fun h => (Finset.mem_compl.1 hi) (hSK h)
          simp [flipSet, this]
    rw [e, Finset.prod_mul_distrib]
    ring
  rw [Finset.sum_congr rfl h1, ← Finset.sum_mul, ← Finset.prod_add]
  have hent : ent x z = (∏ i ∈ K, (if x i = z i then X i else 1))
      * ∏ i ∈ Kᶜ, (if x i = z i then X i else 1) := by
    unfold ent
    rw [Finset.prod_mul_prod_compl]
  by_cases hK : K ⊆ diffSet x z
  · rw [if_pos hK, hent]
    have hne : ∀ i ∈ K, x i ≠ z i := fun i hi => by simpa [diffSet] using hK hi
    have hA : ∏ i ∈ K, ((-X i : MvPolynomial ι ℤ) * (if (!(x i)) = z i then X i else 1)
        + (if x i = z i then X i else 1)) = ∏ i ∈ K, (1 - X i ^ 2) :=
      Finset.prod_congr rfl fun i hi => by rw [fac, if_neg (hne i hi)]
    have hB : ∏ i ∈ K, (if x i = z i then X i else 1 : MvPolynomial ι ℤ) = 1 :=
      Finset.prod_eq_one fun i hi => if_neg (hne i hi)
    rw [hA, hB, one_mul]
  · rw [if_neg hK, mul_zero]
    obtain ⟨i, hi, hiz⟩ := Finset.not_subset.1 hK
    have hxz : x i = z i := by simpa [diffSet] using hiz
    have hA : ∏ i ∈ K, ((-X i : MvPolynomial ι ℤ) * (if (!(x i)) = z i then X i else 1)
        + (if x i = z i then X i else 1)) = 0 :=
      Finset.prod_eq_zero hi (by rw [fac, if_pos hxz])
    rw [hA, zero_mul]

/-- The true points of `g`. -/
abbrev V (g : Cube ι → Bool) := {x : Cube ι // g x = true}

variable (g : Cube ι → Bool) (T : Cube ι → Prop) [DecidablePred T] (K : Cube ι → Finset ι)

/-- The matrix `M`. -/
noncomputable def Mat : Matrix (V g) (V g) (MvPolynomial ι ℤ) :=
  fun x z => ent x.1 z.1

/-- The matrix obtained from `M` by replacing the rows in `T` by the (divided) row combination. -/
noncomputable def Mat' : Matrix (V g) (V g) (MvPolynomial ι ℤ) :=
  fun x z => if T x.1 then (if K x.1 ⊆ diffSet x.1 z.1 then ent x.1 z.1 else 0) else ent x.1 z.1

/-- The matrix of the row operations. -/
noncomputable def AMat : Matrix (V g) (V g) (MvPolynomial ι ℤ) :=
  fun x u => if T x.1 then
      ∑ S ∈ (K x.1).powerset, (if flipSet x.1 S = u.1 then ∏ i ∈ S, (-X i) else 0)
    else (if x = u then 1 else 0)

/-- The diagonal factors. -/
noncomputable def Dg : V g → MvPolynomial ι ℤ :=
  fun x => if T x.1 then ∏ i ∈ K x.1, (1 - X i ^ 2) else 1

lemma AMat_mul (hwing : ∀ x : V g, T x.1 → ∀ S : Finset ι, S ⊆ K x.1 → g (flipSet x.1 S) = true) :
    AMat g T K * Mat g = Matrix.diagonal (Dg g T K) * Mat' g T K := by
  apply Matrix.ext
  intro x z
  rw [Matrix.diagonal_mul, Matrix.mul_apply]
  by_cases hT : T x.1
  · simp only [AMat, Mat, Mat', Dg, if_pos hT]
    rw [← row_id]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro S hS
    have hS' := hwing x hT S (Finset.mem_powerset.1 hS)
    rw [Finset.sum_eq_single (⟨flipSet x.1 S, hS'⟩ : V g)]
    · simp
    · intro u _ hu
      have : flipSet x.1 S ≠ u.1 := fun h => hu (Subtype.ext h.symm)
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp only [AMat, Mat, Mat', Dg, if_neg hT]
    simp

lemma cc_det_AMat : constantCoeff (AMat g T K).det = 1 := by
  rw [RingHom.map_det]
  have h : (constantCoeff (R := ℤ) (σ := ι)).mapMatrix (AMat g T K) = 1 := by
    ext x u
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, AMat]
    by_cases hT : T x.1
    · rw [if_pos hT, map_sum (constantCoeff (R := ℤ) (σ := ι)), Finset.sum_eq_single ∅]
      · by_cases hxu : x = u
        · subst hxu
          simp [flipSet_empty]
        · have : ¬ (x.1 = u.1) := fun h => hxu (Subtype.ext h)
          simp [flipSet_empty, this, hxu]
      · intro S _ hS
        split_ifs
        · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.2 hS
          rw [map_prod]
          exact Finset.prod_eq_zero hi (by simp)
        · simp
      · intro h
        exact absurd (Finset.empty_mem_powerset _) h
    · rw [if_neg hT]
      by_cases hxu : x = u
      · subst hxu
        simp
      · simp [hxu]
  rw [h, Matrix.det_one]

lemma cc_Dg : constantCoeff (∏ x, Dg g T K x) = 1 := by
  rw [map_prod]
  apply Finset.prod_eq_one
  intro x _
  unfold Dg
  split_ifs <;> simp

/-- A minimal monomial of `det M` is a monomial of `det M'`. -/
lemma key (hwing : ∀ x : V g, T x.1 → ∀ S : Finset ι, S ⊆ K x.1 → g (flipSet x.1 S) = true)
    (m : ι →₀ ℕ) (hm : Minimal (· ∈ (Mat g).det.support) m) :
    m ∈ (Mat' g T K).det.support := by
  have h := congrArg Matrix.det (AMat_mul g T K hwing)
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at h
  have h1 := (minimal_mul_iff _ _ (cc_det_AMat g T K) m).2 hm
  rw [h] at h1
  exact ((minimal_mul_iff _ _ (cc_Dg g T K) m).1 h1).1

/-! ### `det M ≠ 0` -/

/-- Exponent vector of an entry. -/
noncomputable def ind (x z : Cube ι) : ι →₀ ℕ :=
  ∑ i, if x i = z i then Finsupp.single i 1 else 0

lemma ent_eq (x z : Cube ι) : ent x z = monomial (ind x z) 1 := by
  unfold ent ind
  rw [MvPolynomial.monomial_sum_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs
  · rfl
  · simp

lemma ind_apply (x z : Cube ι) (i : ι) : ind x z i = if x i = z i then 1 else 0 := by
  unfold ind
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · split_ifs <;> simp
  · intro j _ hj
    split_ifs <;> simp [hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma prod_ent (σ : Equiv.Perm (V g)) :
    ∏ x : V g, Mat g (σ x) x = monomial (∑ x : V g, ind (σ x).1 x.1) 1 := by
  simp only [Mat, ent_eq]
  rw [MvPolynomial.monomial_sum_one]

lemma det_coeff : coeff (∑ x : V g, ind x.1 x.1) (Mat g).det = 1 := by
  classical
  rw [Matrix.det_apply', MvPolynomial.coeff_sum, Finset.sum_eq_single 1]
  · rw [prod_ent]
    simp [coeff_monomial]
  · intro σ _ hσ
    rw [prod_ent]
    have hne : ∑ x : V g, ind (σ x).1 x.1 ≠ ∑ x : V g, ind x.1 x.1 := by
      intro heq
      apply hσ
      refine Equiv.ext fun x => ?_
      show σ x = x
      apply Subtype.ext
      funext i
      have h0 := DFunLike.congr_fun heq i
      rw [Finsupp.finsetSum_apply, Finsupp.finsetSum_apply] at h0
      have hi : ∑ y : V g, (if (σ y).1 i = y.1 i then 1 else 0 : ℕ) = ∑ y : V g, (1 : ℕ) :=
        calc ∑ y : V g, (if (σ y).1 i = y.1 i then 1 else 0 : ℕ)
            = ∑ y : V g, ind (σ y).1 y.1 i :=
              Finset.sum_congr rfl fun y _ => (ind_apply _ _ _).symm
          _ = ∑ y : V g, ind y.1 y.1 i := h0
          _ = ∑ y : V g, (1 : ℕ) :=
              Finset.sum_congr rfl fun y _ => by rw [ind_apply, if_pos rfl]
      have hle : ∀ y ∈ (Finset.univ : Finset (V g)),
          (if (σ y).1 i = y.1 i then 1 else 0 : ℕ) ≤ 1 := by
        intro y _
        split_ifs <;> simp
      have h2 := (Finset.sum_eq_sum_iff_of_le hle).1 hi x (Finset.mem_univ x)
      by_contra hcon
      rw [if_neg hcon] at h2
      exact zero_ne_one h2
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
      simp [hs, coeff_monomial, hne]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-! ### Assembly -/

lemma sum_anti (w : ι → ℝ) (x z : Cube ι) :
    ∑ i ∈ diffSet (antipode x) z, w i = ∑ i, if x i = z i then w i else 0 := by
  unfold diffSet antipode
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases x i <;> cases z i <;> simp

theorem main (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : Finset (Cube ι)) (K : Cube ι → Finset ι)
    (hwing : ∀ x ∈ P, ∀ S : Finset ι, S ⊆ K x → g (flipSet x S) = true)
    (hfar : ∀ x ∈ P, ∀ z : Cube ι, g z = true → K x ⊆ diffSet x z →
      1 ≤ ∑ i ∈ diffSet (antipode x) z, w i) :
    (P.card : ℝ) ≤ ∑ i, w i * (bdry g i : ℝ) := by
  classical
  have hsupp : ∃ m, m ∈ (Mat g).det.support :=
    ⟨_, MvPolynomial.mem_support_iff.2 (by rw [det_coeff]; exact one_ne_zero)⟩
  obtain ⟨m, hm⟩ := exists_minimal_of_wellFoundedLT (· ∈ (Mat g).det.support) hsupp
  -- (c)
  have hc : (P.card : ℝ) ≤ wt w m := by
    have hmem := key g (· ∈ P) K (fun x hx S hS => hwing x.1 hx S hS) m hm
    have hent : ∀ x z : V g,
        WtGE w (if x.1 ∈ P then 1 else 0) (Mat' g (· ∈ P) K x z) := by
      intro x z
      by_cases hx : x.1 ∈ P
      · simp only [Mat', if_pos hx]
        by_cases hK : K x.1 ⊆ diffSet x.1 z.1
        · rw [if_pos hK]
          refine (ent_wt w x.1 z.1).mono ?_
          rw [← sum_anti]
          exact hfar x.1 hx z.1 z.2 hK
        · rw [if_neg hK]
          exact WtGE.zero _ _
      · simp only [Mat', if_neg hx]
        refine (ent_wt w x.1 z.1).mono (Finset.sum_nonneg fun i _ => ?_)
        split_ifs
        · exact hw i
        · exact le_rfl
    have hW := WtGE.det _ _ hent m hmem
    have hcard : ∑ x : V g, (if x.1 ∈ P then (1 : ℝ) else 0) = P.card := by
      rw [← Finset.sum_subtype (Finset.univ.filter fun x => g x = true) (by simp)
        (fun x => if x ∈ P then (1 : ℝ) else 0), Finset.sum_boole]
      have hPf : (Finset.univ.filter fun x => g x = true).filter (· ∈ P) = P := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
        simpa [flipSet_empty] using hwing x h ∅ (Finset.empty_subset _)
      rw [hPf]
    rwa [hcard] at hW
  -- (b)
  have hb : ∀ i, (m i : ℝ) ≤ (bdry g i : ℝ) := by
    intro i
    have hmem := key g (fun x => g (flipSet x {i}) = true) (fun _ => {i}) (by
      intro x hx S hS
      rcases Finset.subset_singleton_iff.1 hS with rfl | rfl
      · rw [flipSet_empty]
        exact x.2
      · exact hx) m hm
    have hent : ∀ x z : V g,
        WtGE (fun j => if j = i then (-1 : ℝ) else 0)
          (if g (flipSet x.1 {i}) = true then 0 else -1)
          (Mat' g (fun x => g (flipSet x {i}) = true) (fun _ => {i}) x z) := by
      intro x z
      by_cases hx : g (flipSet x.1 {i}) = true
      · simp only [Mat', if_pos hx]
        by_cases hK : ({i} : Finset ι) ⊆ diffSet x.1 z.1
        · rw [if_pos hK]
          refine (ent_wt _ x.1 z.1).mono (le_of_eq ?_)
          have hxi : x.1 i ≠ z.1 i := by simpa [diffSet] using hK
          symm
          apply Finset.sum_eq_zero
          intro j _
          by_cases hj : j = i
          · rw [hj, if_neg hxi]
          · simp [hj]
        · rw [if_neg hK]
          exact WtGE.zero _ _
      · simp only [Mat', if_neg hx]
        refine (ent_wt _ x.1 z.1).mono ?_
        have h1 : (-1 : ℝ) = ∑ j, (if j = i then (-1 : ℝ) else 0) := by simp
        rw [h1]
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : j = i
        · rw [if_pos hj]
          split_ifs <;> norm_num
        · simp [hj]
    have hW := WtGE.det _ _ hent m hmem
    have hwt : wt (fun j => if j = i then (-1 : ℝ) else 0) m = -(m i : ℝ) := by
      simp [wt]
    have hsum : ∑ x : V g, (if g (flipSet x.1 {i}) = true then (0 : ℝ) else -1)
        = -(bdry g i : ℝ) := by
      rw [← Finset.sum_subtype (Finset.univ.filter fun x => g x = true) (by simp)
        (fun x => if g (flipSet x {i}) = true then (0 : ℝ) else -1)]
      unfold bdry
      rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const,
        Finset.filter_filter]
      simp
    rw [hwt, hsum] at hW
    linarith
  calc (P.card : ℝ) ≤ wt w m := hc
    _ = ∑ i, w i * (m i : ℝ) := rfl
    _ ≤ ∑ i, w i * (bdry g i : ℝ) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hb i) (hw i)

end AASolDet

theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (g : Cube ι → Bool) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (P : Finset (Cube ι)) (K : Cube ι → Finset ι)
    (hwing : ∀ x ∈ P, ∀ S : Finset ι, S ⊆ K x → g (flipSet x S) = true)
    (hfar : ∀ x ∈ P, ∀ z : Cube ι, g z = true → K x ⊆ diffSet x z →
      1 ≤ ∑ i ∈ diffSet (antipode x) z, w i) :
    (P.card : ℝ) ≤ ∑ i, w i * (bdry g i : ℝ) :=
  AASolDet.main g w hw P K hwing hfar
