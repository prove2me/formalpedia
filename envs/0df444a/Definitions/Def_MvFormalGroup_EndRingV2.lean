-- Prove2me | Definitions.Def_MvFormalGroup_EndRingV2
-- name    : MvFormalGroup_EndRingV2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/ea0d3037-d39c-5af5-a926-d73dc0d00e4c
-- title:
--   Endomorphism semiring of a multivariate formal group law
-- statement:
--   This module develops the additive and multiplicative structure on homomorphisms between multivariate formal group laws, where a law $F$ of dimension $g$ over a commutative ring $R$ is a $g$-tuple of power series in $2g$ variables with vanishing constant terms, linear coefficients $\delta_{ij}$ in each block, and the associativity identity as a structure field, and a homomorphism $F \to G$ is a $h$-tuple of series in $g$ variables with zero constant terms satisfying $\varphi(F(X,Y)) = G(\varphi(X),\varphi(Y))$.
--
--   A first group of results concerns substitution. For a family $c$ with zero constant coefficients, the order of $\prod_j c_j^{e_j}$ is at least $|e|$; if in addition the linear part of $c$ is the identity matrix, the degree-$|e|$ homogeneous component of this product is the monomial $X^e$, whence substitution by such a family is injective (`eq_zero_of_subst_eq_zero`, `subst_injective`, over a finite variable set). Also recorded: `coeff_single_subst`, expressing the linear coefficients of a composite as a matrix product, and consequently `linearPart_subst`, $\mathrm{lin}(b \circ a) = \mathrm{lin}(a)\,\mathrm{lin}(b)$, together with $\mathrm{lin}(F(a,b)) = \mathrm{lin}(a) + \mathrm{lin}(b)$, $\mathrm{lin}(X) = 1$, $\mathrm{lin}(0) = 0$.
--
--   From associativity and, where assumed, the commutativity class `IsComm`, one obtains $F(F(a,b),c) = F(a,F(b,c))$, $F(a,b) = F(b,a)$ and the medial law $F(F(a,b),F(c,d)) = F(F(a,c),F(b,d))$ for substitution families with zero constant terms, and the unit laws $F(X,0) = X$, $F(0,X) = X$, deduced from the rigidity statement that a tangent-identity family idempotent under self-substitution equals $X$.
--
--   These yield: the zero homomorphism; the sum $\varphi + \psi := G(\varphi,\psi)$ and an `AddCommMonoid` on `Hom F G` for commutative $G$; a `Monoid` on `End F` given by composition with unit $X$; a `Semiring` on `End F` for commutative $F$, in which the image of $n$ is the $n$-series $[n]_F$; and the ring homomorphism `linearPartHom` from `End F` to $g \times g$ matrices over $R$, sending $\varphi$ to its linear part, with $[n]_F \mapsto n \cdot 1$.
--
--   **Relation to Mathlib.** The substitution calculus for `MvPowerSeries` (`subst`, `HasSubst`, homogeneous components, order estimates) is Mathlib's; multivariate formal group laws, their homomorphisms and the semiring structure on endomorphisms are the project's own notions.
--
--   **Where it is used.** The endomorphism semiring, the $n$-series $[n]_F$ and the linear-part ring homomorphism are the vocabulary in which the formal group of an elliptic curve (and its torsion and height) is handled in the local analysis at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_EndRingV2.lean

import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]

section Subst

variable {σ τ : Type*}

theorem subst_zero_of_constantCoeff_eq_zero {f : MvPowerSeries σ R}
    (hf : f.constantCoeff = 0) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) f = 0 := by
  classical
  ext d
  rw [map_zero, coeff_subst HasSubst.zero, finsum_eq_zero_of_forall_eq_zero]
  intro e
  by_cases he : e = 0
  · subst he
    simp [coeff_zero_eq_constantCoeff_apply, hf]
  · obtain ⟨i, hi⟩ : ∃ i : σ, e i ≠ 0 := by
      by_contra hc
      exact he (Finsupp.ext fun a => not_ne_iff.mp fun hne => hc ⟨a, hne⟩)
    have hz : (e.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi) (by simp [zero_pow hi])
    rw [hz, map_zero, smul_zero]

theorem le_order_finsuppProd_pow {c : σ → MvPowerSeries τ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0) (e : σ →₀ ℕ) :
    (e.degree : ℕ∞) ≤ (e.prod fun j n => (c j) ^ n).order := by
  classical
  refine le_trans ?_ (le_order_prod _ _)
  rw [Finsupp.degree_apply, Nat.cast_sum]
  exact Finset.sum_le_sum fun j _ => le_order_pow_of_constantCoeff_eq_zero (e j) (hc0 j)

theorem homogeneousComponent_finsuppProd_pow [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0)
    (e : σ →₀ ℕ) :
    homogeneousComponent e.degree (e.prod fun j n => (c j) ^ n) =
      monomial e (1 : R) := by
  classical
  suffices H : ∀ n : ℕ, ∀ e : σ →₀ ℕ, e.degree = n →
      homogeneousComponent n (e.prod fun j m => (c j) ^ m) = monomial e (1 : R) by
    exact H e.degree e rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro e hen
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      have he : e = 0 := (Finsupp.degree_eq_zero_iff e).mp hen
      subst he
      rw [Finsupp.prod_zero_index]
      ext d
      rw [coeff_homogeneousComponent, coeff_monomial]
      by_cases hd : d = 0
      · subst hd
        simp
      · rw [if_neg (fun hcon => hd ((Finsupp.degree_eq_zero_iff d).mp hcon)), if_neg hd]
    · have he0 : e ≠ 0 := by
        intro hcon
        subst hcon
        rw [map_zero] at hen
        omega
      obtain ⟨j, hj⟩ : ∃ j : σ, e j ≠ 0 := by
        by_contra hc
        exact he0 (Finsupp.ext fun a => not_ne_iff.mp fun hne => hc ⟨a, hne⟩)
      set e' : σ →₀ ℕ := e - Finsupp.single j 1 with he'def
      have hsplit : Finsupp.single j 1 + e' = e :=
        add_tsub_cancel_of_le (Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hj))
      have hdeg' : e'.degree = n - 1 := by
        have hcongr := congrArg Finsupp.degree hsplit
        rw [map_add, Finsupp.degree_single] at hcongr
        omega
      have hP : (e.prod fun j' m => (c j') ^ m)
          = c j * (e'.prod fun j' m => (c j') ^ m) := by
        rw [← hsplit, Finsupp.prod_add_index' (fun _ => pow_zero _)
          (fun a b₁ b₂ => pow_add _ b₁ b₂),
          Finsupp.prod_single_index (h := fun s' n' => (c s') ^ n') (pow_zero (c j)),
          pow_one]
      have hone : (1 : ℕ∞) ≤ (c j).order :=
        one_le_order_iff_constCoeff_eq_zero.mpr (hc0 j)
      have hord' : ((n - 1 : ℕ) : ℕ∞) ≤ (e'.prod fun j' m => (c j') ^ m).order := by
        rw [← hdeg']
        exact le_order_finsuppProd_pow hc0 e'
      have hcomp : homogeneousComponent n (c j * e'.prod fun j' m => (c j') ^ m)
          = homogeneousComponent 1 (c j)
            * homogeneousComponent (n - 1) (e'.prod fun j' m => (c j') ^ m) := by
        have hmul := homogeneousComponent_mul_of_le_order (f := c j)
          (g := e'.prod fun j' m => (c j') ^ m) hone hord'
        rwa [show 1 + (n - 1) = n by omega] at hmul
      have hXj : homogeneousComponent 1 (c j) = monomial (Finsupp.single j 1) (1 : R) := by
        ext d
        rw [coeff_homogeneousComponent, coeff_monomial]
        by_cases hd : d.degree = 1
        · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = d := by
            have hmem : d ∈ {d' : σ →₀ ℕ | d'.degree = 1} := hd
            rw [← Finsupp.range_single_one] at hmem
            exact hmem
          rw [if_pos hd, hc1 j a]
          by_cases hja : j = a
          · subst hja
            simp
          · rw [if_neg hja, if_neg]
            intro hcon
            exact hja (Finsupp.single_left_injective one_ne_zero hcon).symm
        · rw [if_neg hd, if_neg]
          intro hcon
          subst hcon
          exact hd (Finsupp.degree_single j 1)
      rw [hP, hcomp, hXj, IH (n - 1) (by omega) e' hdeg', monomial_mul_monomial, one_mul,
        hsplit]

theorem coeff_finsuppProd_pow_of_degree_eq [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0)
    {d e : σ →₀ ℕ} (hde : d.degree = e.degree) :
    coeff d (e.prod fun j n => (c j) ^ n) = if d = e then 1 else 0 := by
  classical
  have h1 := congrArg (coeff d) (homogeneousComponent_finsuppProd_pow hc0 hc1 e)
  rwa [coeff_homogeneousComponent, if_pos hde, coeff_monomial] at h1

theorem eq_zero_of_subst_eq_zero [Finite σ] [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0)
    {p : MvPowerSeries σ R} (hp : subst c p = 0) : p = 0 := by
  classical
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  have key : ∀ n : ℕ, ∀ d : σ →₀ ℕ, d.degree = n → coeff d p = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro d hd
      have h0 : coeff d (subst c p) = 0 := by rw [hp, map_zero]
      rw [coeff_subst hsc] at h0
      rw [finsum_eq_single _ d (fun e hne => ?_)] at h0
      · rwa [coeff_finsuppProd_pow_of_degree_eq hc0 hc1 rfl, if_pos rfl, smul_eq_mul,
          mul_one] at h0
      · rcases lt_trichotomy e.degree n with hlt | heq | hgt
        · rw [IH e.degree hlt e rfl, zero_smul]
        · rw [coeff_finsuppProd_pow_of_degree_eq hc0 hc1 (by rw [hd, heq]),
            if_neg (fun hcon => hne hcon.symm), smul_zero]
        · have horder : ((Finsupp.degree d : ℕ) : ℕ∞)
              < (e.prod fun s' n' => (c s') ^ n').order := by
            refine lt_of_lt_of_le ?_ (le_order_finsuppProd_pow hc0 e)
            rw [hd]
            exact_mod_cast hgt
          have hcz : coeff d (e.prod fun s' n' => (c s') ^ n') = 0 :=
            coeff_of_lt_order horder
          rw [hcz, smul_zero]
  ext d
  rw [map_zero]
  exact key d.degree d rfl

theorem subst_injective [Finite σ] [DecidableEq σ] {c : σ → MvPowerSeries σ R}
    (hc0 : ∀ j, (c j).constantCoeff = 0)
    (hc1 : ∀ j j', coeff (Finsupp.single j' 1) (c j) = if j = j' then 1 else 0) :
    Function.Injective (subst (R := R) c) := by
  intro p q hpq
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  have hz : subst c (p - q) = 0 := by
    rw [← coe_substAlgHom hsc, map_sub, coe_substAlgHom hsc, hpq, sub_self]
  have := eq_zero_of_subst_eq_zero hc0 hc1 hz
  exact sub_eq_zero.mp this

theorem coeff_single_subst {σ' : Type*} [Fintype σ'] {c : σ' → MvPowerSeries τ R}
    (hc0 : ∀ s, (c s).constantCoeff = 0) (q : MvPowerSeries σ' R) (t : τ) :
    coeff (Finsupp.single t 1) (subst c q)
      = ∑ s : σ', coeff (Finsupp.single s 1) q * coeff (Finsupp.single t 1) (c s) := by
  classical
  have hsc : HasSubst c := hasSubst_of_constantCoeff_zero hc0
  rw [coeff_subst hsc,
    finsum_eq_finsetSum_of_support_subset _
      (s := Finset.univ.image fun s : σ' => Finsupp.single s 1) (fun e he => ?_),
    Finset.sum_image (fun a _ b _ hab => Finsupp.single_left_injective one_ne_zero hab)]
  · refine Finset.sum_congr rfl fun s _ => ?_
    show coeff (Finsupp.single s 1) q
        • coeff (Finsupp.single t 1) ((Finsupp.single s 1).prod fun s' n => (c s') ^ n)
      = coeff (Finsupp.single s 1) q * coeff (Finsupp.single t 1) (c s)
    rw [Finsupp.prod_single_index (h := fun s' n' => (c s') ^ n') (pow_zero (c s)),
      pow_one, smul_eq_mul]
  · by_contra hmem
    apply he
    rcases Nat.lt_trichotomy e.degree 1 with hlt | heq | hgt
    · have he0 : e = 0 := (Finsupp.degree_eq_zero_iff e).mp (by omega)
      subst he0
      rw [Finsupp.prod_zero_index, coeff_one,
        if_neg (Finsupp.single_ne_zero.mpr one_ne_zero), smul_zero]
    · obtain ⟨a, rfl⟩ : ∃ a, Finsupp.single a 1 = e := by
        have hmem' : e ∈ {d' : σ' →₀ ℕ | d'.degree = 1} := heq
        rw [← Finsupp.range_single_one] at hmem'
        exact hmem'
      exact absurd (Finset.mem_image_of_mem _ (Finset.mem_univ a)) hmem
    · have horder : (((Finsupp.single t 1).degree : ℕ) : ℕ∞)
          < (e.prod fun s' n' => (c s') ^ n').order := by
        refine lt_of_lt_of_le ?_ (le_order_finsuppProd_pow hc0 e)
        rw [Finsupp.degree_single]
        exact_mod_cast hgt
      have hcz : coeff (Finsupp.single t 1) (e.prod fun s' n' => (c s') ^ n') = 0 :=
        coeff_of_lt_order horder
      rw [hcz, smul_zero]

end Subst

section LinearPart

@[simp]
theorem linearPart_zero :
    linearPart (fun _ : Fin h => (0 : MvPowerSeries (Fin g) R)) = 0 := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.zero_apply]
  exact map_zero _

@[simp]
theorem linearPart_X :
    linearPart (fun i : Fin g => (X i : MvPowerSeries (Fin g) R)) = 1 := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.one_apply]
  rw [coeff_X]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [if_neg (fun hcon => hij (Finsupp.single_left_injective one_ne_zero hcon).symm),
      if_neg hij]

theorem linearPart_subst {m n : ℕ} {b : Fin m → MvPowerSeries (Fin n) R}
    (hb : ∀ s, (b s).constantCoeff = 0) (a : Fin h → MvPowerSeries (Fin m) R) :
    linearPart (fun i => subst b (a i)) = linearPart a * linearPart b := by
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.mul_apply]
  exact coeff_single_subst hb (a i) j

theorem linearPart_subst_elim {m : ℕ} (F : MvFormalGroup g R)
    {a b : Fin g → MvPowerSeries (Fin m) R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    linearPart (fun i => subst (Sum.elim a b) (F.toPowerSeries i))
      = linearPart a + linearPart b := by
  classical
  have hab : ∀ s : Fin g ⊕ Fin g, ((Sum.elim a b) s).constantCoeff = 0 := by
    rintro (s | s)
    exacts [ha s, hb s]
  ext i j
  simp only [linearPart, Matrix.of_apply, Matrix.add_apply]
  rw [coeff_single_subst hab (F.toPowerSeries i) j, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, F.coeff_single_inl, F.coeff_single_inr,
    ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq, Finset.sum_ite_eq]
  simp

end LinearPart

section Transport

variable {τ : Type*} (F : MvFormalGroup g R)

theorem hasSubst_elim {n : ℕ} {τ' : Type*} {a b : Fin n → MvPowerSeries τ' R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) :
    HasSubst (Sum.elim a b) :=
  hasSubst_of_constantCoeff_zero (by rintro (s | s); exacts [ha s, hb s])

theorem constantCoeff_subst_elim {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) (i : Fin g) :
    (subst (Sum.elim a b) (F.toPowerSeries i)).constantCoeff = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_elim ha hb)
    (by rintro (s | s); exacts [ha s, hb s]) (F.constantCoeff_eq_zero i)

theorem subst_elim_assoc {a b c : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c)
        (F.toPowerSeries i)
      = subst (Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j))
        (F.toPowerSeries i) := by
  have hT0 : ∀ s : Fin g ⊕ (Fin g ⊕ Fin g),
      ((Sum.elim a (Sum.elim b c)) s).constantCoeff = 0 := by
    rintro (j | j | j)
    exacts [ha j, hb j, hc j]
  have hT : HasSubst (Sum.elim a (Sum.elim b c)) := hasSubst_of_constantCoeff_zero hT0
  have hzB : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hzC : ∀ s : Fin g ⊕ Fin g, ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> simp [constantCoeff_X]
  have hB := hasSubst_of_constantCoeff_zero hzB
  have hC := hasSubst_of_constantCoeff_zero hzC
  have hA : HasSubst (Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_subst_eq_zero hB hzB (F.constantCoeff_eq_zero j)
    · exact constantCoeff_X _
  have hA' : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) := by
    apply hasSubst_of_constantCoeff_zero
    rintro (j | j)
    · exact constantCoeff_X _
    · exact constantCoeff_subst_eq_zero hC hzC (F.constantCoeff_eq_zero j)
  have key := congrArg (subst (R := R) (Sum.elim a (Sum.elim b c))) (F.assoc i)
  rw [subst_comp_subst_apply hA hT, subst_comp_subst_apply hA' hT] at key
  have hBfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inl l))) t)) = Sum.elim a b := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hCfam : (fun t => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun l => X (Sum.inr (Sum.inr l))) t)) = Sum.elim b c := by
    funext t
    rcases t with l | l <;> simp [subst_X hT]
  have hAfam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
      fun j => X (Sum.inr (Sum.inr j))) s))
      = Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j)) c := by
    funext s
    rcases s with j | j
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inl l))) (F.toPowerSeries j))
        = subst (Sum.elim a b) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hB hT, hBfam]
    · simp [subst_X hT]
  have hA'fam : (fun s => subst (Sum.elim a (Sum.elim b c)) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
        fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j)) s))
      = Sum.elim a fun j => subst (Sum.elim b c) (F.toPowerSeries j) := by
    funext s
    rcases s with j | j
    · simp [subst_X hT]
    · show subst (Sum.elim a (Sum.elim b c)) (subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin g ⊕ (Fin g ⊕ Fin g)) R))
          fun l => X (Sum.inr (Sum.inr l))) (F.toPowerSeries j))
        = subst (Sum.elim b c) (F.toPowerSeries j)
      rw [subst_comp_subst_apply hC hT, hCfam]
  rw [hAfam, hA'fam] at key
  exact key

theorem subst_elim_comm [IsComm F] {a b : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim a b) (F.toPowerSeries i)
      = subst (Sum.elim b a) (F.toPowerSeries i) := by
  have hT : HasSubst (Sum.elim b a) := hasSubst_elim hb ha
  have hswap : HasSubst (Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) :=
    hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [constantCoeff_X])
  have key := congrArg (subst (R := R) (Sum.elim b a)) (IsComm.comm (F := F) i)
  rw [subst_comp_subst_apply hswap hT] at key
  have hfam : (fun s => subst (Sum.elim b a) ((Sum.elim
      (fun j => (X (Sum.inr j) : MvPowerSeries (Fin g ⊕ Fin g) R))
      fun j => X (Sum.inl j)) s)) = Sum.elim a b := by
    funext s
    rcases s with j | j <;> simp [subst_X hT]
  rw [hfam] at key
  exact key

theorem subst_elim_exchange [IsComm F] {a b c d : Fin g → MvPowerSeries τ R}
    (ha : ∀ i, (a i).constantCoeff = 0) (hb : ∀ i, (b i).constantCoeff = 0)
    (hc : ∀ i, (c i).constantCoeff = 0) (hd : ∀ i, (d i).constantCoeff = 0) (i : Fin g) :
    subst (Sum.elim (fun j => subst (Sum.elim a b) (F.toPowerSeries j))
        fun j => subst (Sum.elim c d) (F.toPowerSeries j)) (F.toPowerSeries i)
      = subst (Sum.elim (fun j => subst (Sum.elim a c) (F.toPowerSeries j))
        fun j => subst (Sum.elim b d) (F.toPowerSeries j)) (F.toPowerSeries i) := by
  have hcd : ∀ j, (subst (Sum.elim c d) (F.toPowerSeries j)).constantCoeff = 0 :=
    constantCoeff_subst_elim F hc hd
  have hbd : ∀ j, (subst (Sum.elim b d) (F.toPowerSeries j)).constantCoeff = 0 :=
    constantCoeff_subst_elim F hb hd
  rw [subst_elim_assoc F ha hb hcd i]
  have hinner : ∀ j, subst (Sum.elim b fun j' => subst (Sum.elim c d) (F.toPowerSeries j'))
      (F.toPowerSeries j)
      = subst (Sum.elim c fun j' => subst (Sum.elim b d) (F.toPowerSeries j'))
        (F.toPowerSeries j) := by
    intro j
    rw [← subst_elim_assoc F hb hc hd j]
    have hswap : (fun j' => subst (Sum.elim b c) (F.toPowerSeries j'))
        = fun j' => subst (Sum.elim c b) (F.toPowerSeries j') :=
      funext fun j' => subst_elim_comm F hb hc j'
    rw [hswap]
    exact subst_elim_assoc F hc hb hd j
  have houter : (fun j => subst (Sum.elim b fun j' => subst (Sum.elim c d)
      (F.toPowerSeries j')) (F.toPowerSeries j))
      = fun j => subst (Sum.elim c fun j' => subst (Sum.elim b d) (F.toPowerSeries j'))
        (F.toPowerSeries j) :=
    funext hinner
  rw [houter]
  exact (subst_elim_assoc F ha hc hbd i).symm

end Transport

section Unit

variable (F : MvFormalGroup g R)

theorem eq_X_of_subst_self {σ : Type*} [Finite σ] [DecidableEq σ]
    {u : σ → MvPowerSeries σ R}
    (hu0 : ∀ j, (u j).constantCoeff = 0)
    (hu1 : ∀ j j', coeff (Finsupp.single j' 1) (u j) = if j = j' then 1 else 0)
    (hidem : ∀ j, subst u (u j) = u j) (i : σ) : u i = X i := by
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu0
  have hv : subst u (u i - X i) = 0 := by
    rw [← coe_substAlgHom hsu, map_sub, coe_substAlgHom hsu, hidem i, subst_X hsu,
      sub_self]
  exact sub_eq_zero.mp (eq_zero_of_subst_eq_zero hu0 hu1 hv)

theorem subst_elim_X_zero (i : Fin g) :
    subst (Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R)) fun _ => 0)
      (F.toPowerSeries i) = X i := by
  have hXz : ∀ s : Fin g ⊕ Fin g, ((Sum.elim (fun j => (X j : MvPowerSeries (Fin g) R))
      fun _ => (0 : MvPowerSeries (Fin g) R)) s).constantCoeff = 0 := by
    rintro (j | j)
    · simp [constantCoeff_X]
    · simp
  have hzero : ∀ j : Fin g,
      ((fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) j).constantCoeff = 0 :=
    fun _ => map_zero _
  have hu0 : ∀ j, (subst (Sum.elim (fun j' => (X j' : MvPowerSeries (Fin g) R)) fun _ => 0)
      (F.toPowerSeries j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hXz) hXz
      (F.constantCoeff_eq_zero j)
  have hu1 : ∀ j j', coeff (Finsupp.single j' 1)
      (subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j)) = if j = j' then 1 else 0 := by
    have hlin := linearPart_subst_elim F (a := fun j => (X j : MvPowerSeries (Fin g) R))
      (b := fun _ => 0) (fun j => constantCoeff_X j) (fun _ => map_zero _)
    rw [linearPart_X, linearPart_zero, add_zero] at hlin
    intro j j'
    simpa [linearPart, Matrix.of_apply, Matrix.one_apply]
      using congrFun (congrFun hlin j) j'
  have hz2 : (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      = fun _ : Fin g ⊕ Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext s
    rcases s with s | s <;> rfl
  have hFzz : (fun j => subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ => 0) (F.toPowerSeries j)) = fun _ : Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext j
    rw [hz2]
    exact subst_zero_of_constantCoeff_eq_zero (F.constantCoeff_eq_zero j)
  have hsu2 : HasSubst (Sum.elim (fun j' => (X j' : MvPowerSeries (Fin g) R)) fun _ => 0) :=
    hasSubst_of_constantCoeff_zero hXz
  have hsut : HasSubst (fun j' => subst (Sum.elim
      (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j')) :=
    hasSubst_of_constantCoeff_zero hu0
  have hassoc' : ∀ j, subst (Sum.elim (fun j' => subst (Sum.elim
      (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j'))
      fun _ => 0) (F.toPowerSeries j)
      = subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j) := by
    intro j
    have h1 := subst_elim_assoc F (a := fun j'' => (X j'' : MvPowerSeries (Fin g) R))
      (b := fun _ => 0) (c := fun _ => 0) (fun j'' => constantCoeff_X j'') hzero hzero j
    rwa [hFzz] at h1
  have hidem : ∀ j, subst (fun j' => subst (Sum.elim
      (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j'))
      (subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j))
      = subst (Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
        (F.toPowerSeries j) := by
    intro j
    rw [subst_comp_subst_apply hsu2 hsut]
    have hfam : (fun s => subst (fun j' => subst (Sum.elim
        (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0) (F.toPowerSeries j'))
        ((Sum.elim (fun j'' => (X j'' : MvPowerSeries (Fin g) R))
          (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))) s))
        = Sum.elim (fun j' => subst (Sum.elim
            (fun j'' => (X j'' : MvPowerSeries (Fin g) R)) fun _ => 0)
            (F.toPowerSeries j')) (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) := by
      funext s
      rcases s with j' | j'
      · simp only [Sum.elim_inl]
        exact subst_X hsut j'
      · simp only [Sum.elim_inr]
        rw [← coe_substAlgHom hsut, map_zero]
    rw [hfam]
    exact hassoc' j
  exact eq_X_of_subst_self hu0 hu1 hidem i

theorem subst_elim_zero_X (i : Fin g) :
    subst (Sum.elim (fun _ => 0) fun j => (X j : MvPowerSeries (Fin g) R))
      (F.toPowerSeries i) = X i := by
  have hzX : ∀ s : Fin g ⊕ Fin g, ((Sum.elim (fun _ => (0 : MvPowerSeries (Fin g) R))
      fun j => (X j : MvPowerSeries (Fin g) R)) s).constantCoeff = 0 := by
    rintro (j | j)
    · simp
    · simp [constantCoeff_X]
  have hzero : ∀ j : Fin g,
      ((fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) j).constantCoeff = 0 :=
    fun _ => map_zero _
  have hu0 : ∀ j, (subst (Sum.elim (fun _ => 0) fun j' => (X j' : MvPowerSeries (Fin g) R))
      (F.toPowerSeries j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hzX) hzX
      (F.constantCoeff_eq_zero j)
  have hu1 : ∀ j j', coeff (Finsupp.single j' 1)
      (subst (Sum.elim (fun _ => 0) fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j)) = if j = j' then 1 else 0 := by
    have hlin := linearPart_subst_elim F (a := fun _ => 0)
      (b := fun j => (X j : MvPowerSeries (Fin g) R)) (fun _ => map_zero _)
      (fun j => constantCoeff_X j)
    rw [linearPart_X, linearPart_zero, zero_add] at hlin
    intro j j'
    simpa [linearPart, Matrix.of_apply, Matrix.one_apply]
      using congrFun (congrFun hlin j) j'
  have hz2 : (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      = fun _ : Fin g ⊕ Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext s
    rcases s with s | s <;> rfl
  have hFzz : (fun j => subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun _ => 0) (F.toPowerSeries j)) = fun _ : Fin g => (0 : MvPowerSeries (Fin g) R) := by
    funext j
    rw [hz2]
    exact subst_zero_of_constantCoeff_eq_zero (F.constantCoeff_eq_zero j)
  have hsu2 : HasSubst (Sum.elim (fun _ => (0 : MvPowerSeries (Fin g) R))
      fun j' => (X j' : MvPowerSeries (Fin g) R)) :=
    hasSubst_of_constantCoeff_zero hzX
  have hsut : HasSubst (fun j' => subst (Sum.elim (fun _ => 0)
      fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j')) :=
    hasSubst_of_constantCoeff_zero hu0
  have hassoc' : ∀ j, subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
      fun j' => subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
        fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j')) (F.toPowerSeries j)
      = subst (Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
        fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j) := by
    intro j
    have h1 := subst_elim_assoc F (a := fun _ => 0) (b := fun _ => 0)
      (c := fun j'' => (X j'' : MvPowerSeries (Fin g) R)) hzero hzero
      (fun j'' => constantCoeff_X j'') j
    rw [hFzz] at h1
    exact h1.symm
  have hidem : ∀ j, subst (fun j' => subst (Sum.elim (fun _ => 0)
      fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j'))
      (subst (Sum.elim (fun _ => 0) fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j))
      = subst (Sum.elim (fun _ => 0) fun j'' => (X j'' : MvPowerSeries (Fin g) R))
        (F.toPowerSeries j) := by
    intro j
    rw [subst_comp_subst_apply hsu2 hsut]
    have hfam : (fun s => subst (fun j' => subst (Sum.elim (fun _ => 0)
        fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j'))
        ((Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
          fun j'' => (X j'' : MvPowerSeries (Fin g) R)) s))
        = Sum.elim (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
            fun j' => subst (Sum.elim (fun _ => 0)
              fun j'' => (X j'' : MvPowerSeries (Fin g) R)) (F.toPowerSeries j') := by
      funext s
      rcases s with j' | j'
      · simp only [Sum.elim_inl]
        rw [← coe_substAlgHom hsut, map_zero]
      · simp only [Sum.elim_inr]
        exact subst_X hsut j'
    rw [hfam]
    exact hassoc' j
  exact eq_X_of_subst_self hu0 hu1 hidem i

end Unit

namespace Hom

variable {F : MvFormalGroup g R} {G : MvFormalGroup h R}

def zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) : Hom F G where
  toPowerSeries := fun _ => 0
  constantCoeff_eq_zero := fun _ => map_zero _
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    show subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R)
      = subst (Sum.elim
          (fun _ : Fin h => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R))
          fun _ : Fin h => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R))
        (G.toPowerSeries i)
    have hL : subst F.toPowerSeries (0 : MvPowerSeries (Fin g) R) = 0 := by
      rw [← coe_substAlgHom F.hasSubst_toPowerSeries, map_zero]
    have hfam : (Sum.elim
        (fun _ : Fin h => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (0 : MvPowerSeries (Fin g) R))
        fun _ : Fin h => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
          (0 : MvPowerSeries (Fin g) R))
        = fun _ : Fin h ⊕ Fin h => (0 : MvPowerSeries (Fin g ⊕ Fin g) R) := by
      funext s
      rcases s with j | j
      · show subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXl, map_zero]
      · show subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (0 : MvPowerSeries (Fin g) R) = 0
        rw [← coe_substAlgHom hXr, map_zero]
    rw [hL, hfam,
      subst_zero_of_constantCoeff_eq_zero (G.constantCoeff_eq_zero i)]

@[simp]
theorem toPowerSeries_zero (F : MvFormalGroup g R) (G : MvFormalGroup h R) :
    (Hom.zero F G).toPowerSeries = fun _ => 0 := rfl

def add [IsComm G] (φ ψ : Hom F G) : Hom F G where
  toPowerSeries := fun i =>
    subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i)
  constantCoeff_eq_zero := fun i =>
    constantCoeff_subst_elim G φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero i
  subst_eq := by
    intro i
    have hXl : HasSubst (fun l : Fin g => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hXr : HasSubst (fun l : Fin g => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
      hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
    have hφψ : HasSubst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) :=
      hasSubst_elim φ.constantCoeff_eq_zero ψ.constantCoeff_eq_zero
    have hφL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
    have hφR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (φ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (φ.constantCoeff_eq_zero j)
    have hψL : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (ψ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
        (ψ.constantCoeff_eq_zero j)
    have hψR : ∀ j, (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        (ψ.toPowerSeries j)).constantCoeff = 0 :=
      fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
        (ψ.constantCoeff_eq_zero j)
    show subst F.toPowerSeries
        (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i))
      = subst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
        (G.toPowerSeries i)
    rw [subst_comp_subst_apply hφψ F.hasSubst_toPowerSeries]
    have hLfam : (fun s => subst F.toPowerSeries
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s))
        = Sum.elim (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
          fun j => subst F.toPowerSeries (ψ.toPowerSeries j) := by
      funext s
      rcases s with j | j <;> rfl
    rw [hLfam]
    have hφeq : (fun j => subst F.toPowerSeries (φ.toPowerSeries j))
        = fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j')) (G.toPowerSeries j) :=
      funext fun j => φ.subst_eq j
    have hψeq : (fun j => subst F.toPowerSeries (ψ.toPowerSeries j))
        = fun j => subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j) :=
      funext fun j => ψ.subst_eq j
    rw [hφeq, hψeq, subst_elim_exchange G hφL hφR hψL hψR i]
    have hfinL : (fun s' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s'))
        = Sum.elim (fun j' => subst
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j') := by
      funext s'
      rcases s' with j' | j' <;> rfl
    have hfinR : (fun s' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
        ((Sum.elim φ.toPowerSeries ψ.toPowerSeries) s'))
        = Sum.elim (fun j' => subst
            (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j') := by
      funext s'
      rcases s' with j' | j' <;> rfl
    have hfinal : (Sum.elim
        (fun j => subst (Sum.elim
          (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j')) (G.toPowerSeries j))
        fun j => subst (Sum.elim
          (fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (φ.toPowerSeries j'))
          fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (ψ.toPowerSeries j')) (G.toPowerSeries j))
        = Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j)) := by
      funext s
      rcases s with j | j
      · show subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXl, hfinL]
      · show subst (Sum.elim
            (fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (φ.toPowerSeries j'))
            fun j' => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (ψ.toPowerSeries j')) (G.toPowerSeries j)
          = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries j))
        rw [subst_comp_subst_apply hφψ hXr, hfinR]
    rw [hfinal]

@[simp]
theorem toPowerSeries_add [IsComm G] (φ ψ : Hom F G) :
    (Hom.add φ ψ).toPowerSeries
      = fun i => subst (Sum.elim φ.toPowerSeries ψ.toPowerSeries) (G.toPowerSeries i) :=
  rfl

instance instZero : Zero (Hom F G) := ⟨Hom.zero F G⟩

@[simp]
theorem toPowerSeries_zero' : (0 : Hom F G).toPowerSeries = fun _ => 0 := rfl

instance instAdd [IsComm G] : Add (Hom F G) := ⟨Hom.add⟩

instance instAddCommMonoid [IsComm G] : AddCommMonoid (Hom F G) where
  add := (· + ·)
  zero := 0
  nsmul := nsmulRec
  add_assoc a b c := by
    apply Hom.ext
    funext i
    show subst (Sum.elim
        (fun j => subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries j))
        c.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim a.toPowerSeries
        fun j => subst (Sum.elim b.toPowerSeries c.toPowerSeries) (G.toPowerSeries j))
        (G.toPowerSeries i)
    exact subst_elim_assoc G a.constantCoeff_eq_zero b.constantCoeff_eq_zero
      c.constantCoeff_eq_zero i
  zero_add a := by
    apply Hom.ext
    funext i
    show subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i)
      = a.toPowerSeries i
    have hsa : HasSubst a.toPowerSeries := a.hasSubst_toPowerSeries
    have h0X : HasSubst (Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin h) R))
        fun j => (X j : MvPowerSeries (Fin h) R)) :=
      hasSubst_elim (fun _ => map_zero _) fun j => constantCoeff_X j
    have hfam : (fun s => subst a.toPowerSeries
        ((Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin h) R))
          fun j => (X j : MvPowerSeries (Fin h) R)) s))
        = Sum.elim (fun _ : Fin h => (0 : MvPowerSeries (Fin g) R)) a.toPowerSeries := by
      funext s
      rcases s with j | j
      · show subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
      · show subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
    have h1 : subst a.toPowerSeries (subst (Sum.elim (fun _ => 0)
        fun j => (X j : MvPowerSeries (Fin h) R)) (G.toPowerSeries i))
        = subst (Sum.elim (fun _ => 0) a.toPowerSeries) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply h0X hsa, hfam]
    rw [← h1, subst_elim_zero_X G i, subst_X hsa]
  add_zero a := by
    apply Hom.ext
    funext i
    show subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i)
      = a.toPowerSeries i
    have hsa : HasSubst a.toPowerSeries := a.hasSubst_toPowerSeries
    have hX0 : HasSubst (Sum.elim (fun j => (X j : MvPowerSeries (Fin h) R))
        fun _ : Fin h => (0 : MvPowerSeries (Fin h) R)) :=
      hasSubst_elim (fun j => constantCoeff_X j) fun _ => map_zero _
    have hfam : (fun s => subst a.toPowerSeries
        ((Sum.elim (fun j => (X j : MvPowerSeries (Fin h) R))
          fun _ : Fin h => (0 : MvPowerSeries (Fin h) R)) s))
        = Sum.elim a.toPowerSeries fun _ : Fin h => (0 : MvPowerSeries (Fin g) R) := by
      funext s
      rcases s with j | j
      · show subst a.toPowerSeries (X j) = a.toPowerSeries j
        exact subst_X hsa j
      · show subst a.toPowerSeries (0 : MvPowerSeries (Fin h) R) = 0
        rw [← coe_substAlgHom hsa, map_zero]
    have h1 : subst a.toPowerSeries (subst (Sum.elim
        (fun j => (X j : MvPowerSeries (Fin h) R)) fun _ => 0) (G.toPowerSeries i))
        = subst (Sum.elim a.toPowerSeries fun _ => 0) (G.toPowerSeries i) := by
      rw [subst_comp_subst_apply hX0 hsa, hfam]
    rw [← h1, subst_elim_X_zero G i, subst_X hsa]
  add_comm a b := by
    apply Hom.ext
    funext i
    show subst (Sum.elim a.toPowerSeries b.toPowerSeries) (G.toPowerSeries i)
      = subst (Sum.elim b.toPowerSeries a.toPowerSeries) (G.toPowerSeries i)
    exact subst_elim_comm G a.constantCoeff_eq_zero b.constantCoeff_eq_zero i

end Hom

namespace End

variable (F : MvFormalGroup g R)

instance instMonoid : Monoid (End F) where
  mul φ ψ := Hom.comp φ ψ
  one := Hom.id F
  mul_assoc φ ψ χ := by
    apply Hom.ext
    funext i
    show subst (Hom.toPowerSeries χ) (subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i))
      = subst (fun j => subst (Hom.toPowerSeries χ) (Hom.toPowerSeries ψ j))
        (Hom.toPowerSeries φ i)
    rw [subst_comp_subst_apply (Hom.hasSubst_toPowerSeries ψ)
      (Hom.hasSubst_toPowerSeries χ)]
  one_mul φ := by
    apply Hom.ext
    funext i
    show subst (Hom.toPowerSeries φ) (X i) = Hom.toPowerSeries φ i
    exact subst_X (Hom.hasSubst_toPowerSeries φ) i
  mul_one φ := by
    apply Hom.ext
    funext i
    show subst (fun j => (X j : MvPowerSeries (Fin g) R)) (Hom.toPowerSeries φ i)
      = Hom.toPowerSeries φ i
    exact congrFun subst_self (Hom.toPowerSeries φ i)

@[simp]
theorem toPowerSeries_one :
    Hom.toPowerSeries (1 : End F) = fun i => (X i : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_mul (φ ψ : End F) :
    Hom.toPowerSeries (φ * ψ)
      = fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i) := rfl

instance instAddCommMonoid [IsComm F] : AddCommMonoid (End F) :=
  inferInstanceAs (AddCommMonoid (Hom F F))

instance instSemiring [IsComm F] : Semiring (End F) :=
  { End.instAddCommMonoid F, End.instMonoid F with
    left_distrib := fun a b c => by
      apply Hom.ext
      funext i
      show subst (fun j => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          (F.toPowerSeries j)) (Hom.toPowerSeries a i)
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
          (F.toPowerSeries i)
      have hbc : HasSubst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero b) (Hom.constantCoeff_eq_zero c)
      have hXl : HasSubst (fun l : Fin g =>
          (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have hXr : HasSubst (fun l : Fin g =>
          (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R)) :=
        hasSubst_of_constantCoeff_zero fun l => constantCoeff_X _
      have haLR : HasSubst (Sum.elim
          (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j))
          fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
            (Hom.toPowerSeries a j)) :=
        hasSubst_elim
          (fun j => constantCoeff_subst_eq_zero hXl (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j))
          fun j => constantCoeff_subst_eq_zero hXr (fun l => constantCoeff_X _)
            (Hom.constantCoeff_eq_zero a j)
      rw [← subst_comp_subst_apply F.hasSubst_toPowerSeries hbc, Hom.subst_eq a i,
        subst_comp_subst_apply haLR hbc]
      have hbfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inl l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries b := by
        funext l
        show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inl l)) = Hom.toPowerSeries b l
        rw [subst_X hbc]
        rfl
      have hcfam : (fun l => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((fun l' => (X (Sum.inr l') : MvPowerSeries (Fin g ⊕ Fin g) R)) l))
          = Hom.toPowerSeries c := by
        funext l
        show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
            (X (Sum.inr l)) = Hom.toPowerSeries c l
        rw [subst_X hbc]
        rfl
      have hfam : (fun s => subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
          ((Sum.elim
            (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j))
            fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
              (Hom.toPowerSeries a j)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j) := by
        funext s
        rcases s with j | j
        · show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries b) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXl hbc, hbfam]
        · show subst (Sum.elim (Hom.toPowerSeries b) (Hom.toPowerSeries c))
              (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin g ⊕ Fin g) R))
                (Hom.toPowerSeries a j))
            = subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j)
          rw [subst_comp_subst_apply hXr hbc, hcfam]
      rw [hfam]
    right_distrib := fun a b c => by
      apply Hom.ext
      funext i
      show subst (Hom.toPowerSeries c)
          (subst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b))
            (F.toPowerSeries i))
        = subst (Sum.elim
            (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j))
          (F.toPowerSeries i)
      have hab : HasSubst (Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) :=
        hasSubst_elim (Hom.constantCoeff_eq_zero a) (Hom.constantCoeff_eq_zero b)
      rw [subst_comp_subst_apply hab (Hom.hasSubst_toPowerSeries c)]
      have hfam : (fun s => subst (Hom.toPowerSeries c)
          ((Sum.elim (Hom.toPowerSeries a) (Hom.toPowerSeries b)) s))
          = Sum.elim (fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries a j))
            fun j => subst (Hom.toPowerSeries c) (Hom.toPowerSeries b j) := by
        funext s
        rcases s with j | j <;> rfl
      rw [hfam]
    zero_mul := fun a => by
      apply Hom.ext
      funext i
      show subst (Hom.toPowerSeries a) (0 : MvPowerSeries (Fin g) R) = 0
      rw [← coe_substAlgHom (Hom.hasSubst_toPowerSeries a), map_zero]
    mul_zero := fun a => by
      apply Hom.ext
      funext i
      show subst (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R))
          (Hom.toPowerSeries a i) = 0
      exact subst_zero_of_constantCoeff_eq_zero (Hom.constantCoeff_eq_zero a i) }

@[simp]
theorem toPowerSeries_natCast [IsComm F] (n : ℕ) :
    Hom.toPowerSeries ((n : End F)) = F.nthSeries n := by
  induction n with
  | zero =>
    rw [Nat.cast_zero, nthSeries_zero]
    rfl
  | succ n ih =>
    rw [Nat.cast_succ]
    funext i
    show subst (Sum.elim (Hom.toPowerSeries ((n : End F)))
        (Hom.toPowerSeries (1 : End F))) (F.toPowerSeries i)
      = F.nthSeries (n + 1) i
    rw [ih, nthSeries_succ]
    rfl

@[simp]
theorem toPowerSeries_zero [IsComm F] :
    Hom.toPowerSeries (0 : End F) = fun _ => (0 : MvPowerSeries (Fin g) R) := rfl

@[simp]
theorem toPowerSeries_add [IsComm F] (φ ψ : End F) :
    Hom.toPowerSeries (φ + ψ)
      = fun i => subst (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ))
        (F.toPowerSeries i) := rfl

end End

theorem constantCoeff_nthSeries (F : MvFormalGroup g R) (n : ℕ) :
    ∀ i, (F.nthSeries n i).constantCoeff = 0 := by
  induction n with
  | zero =>
    intro i
    rw [nthSeries_zero]
    exact map_zero _
  | succ n ih =>
    intro i
    rw [nthSeries_succ]
    exact constantCoeff_subst_elim F ih (fun j => constantCoeff_X j) i

theorem linearPart_nthSeries (F : MvFormalGroup g R) (n : ℕ) :
    linearPart (F.nthSeries n) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  induction n with
  | zero =>
    rw [nthSeries_zero, zero_smul]
    exact linearPart_zero
  | succ n ih =>
    rw [nthSeries_succ,
      linearPart_subst_elim F (constantCoeff_nthSeries F n) (fun j => constantCoeff_X j),
      ih, linearPart_X, succ_nsmul]

def linearPartHom (F : MvFormalGroup g R) [IsComm F] :
    End F →+* Matrix (Fin g) (Fin g) R where
  toFun φ := linearPart (Hom.toPowerSeries φ)
  map_one' := by
    show linearPart (fun i => (X i : MvPowerSeries (Fin g) R)) = 1
    exact linearPart_X
  map_mul' φ ψ := by
    show linearPart (fun i => subst (Hom.toPowerSeries ψ) (Hom.toPowerSeries φ i)) = _
    exact linearPart_subst (Hom.constantCoeff_eq_zero ψ) (Hom.toPowerSeries φ)
  map_zero' := by
    show linearPart (fun _ : Fin g => (0 : MvPowerSeries (Fin g) R)) = 0
    exact linearPart_zero
  map_add' φ ψ := by
    show linearPart (fun i => subst
        (Sum.elim (Hom.toPowerSeries φ) (Hom.toPowerSeries ψ)) (F.toPowerSeries i)) = _
    exact linearPart_subst_elim F (Hom.constantCoeff_eq_zero φ)
      (Hom.constantCoeff_eq_zero ψ)

@[simp]
theorem linearPartHom_apply (F : MvFormalGroup g R) [IsComm F] (φ : End F) :
    linearPartHom F φ = linearPart (Hom.toPowerSeries φ) := rfl

@[simp]
theorem linearPartHom_natCast (F : MvFormalGroup g R) [IsComm F] (n : ℕ) :
    linearPartHom F ((n : End F)) = n • (1 : Matrix (Fin g) (Fin g) R) := by
  rw [linearPartHom_apply, End.toPowerSeries_natCast, linearPart_nthSeries]

end MvFormalGroup


