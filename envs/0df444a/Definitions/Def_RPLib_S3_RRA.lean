-- Prove2me | Definitions.Def_RPLib_S3_RRA
-- name    : RPLib_S3_RRA
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:42.508997+00:00
-- url     : https://prove2.me/theorems/ddb55f2f-0dcd-4a3f-827d-20ffdf807b72
-- title:
--   Weight-two Ramanujan-Petersson library: the abstract repartition (adele) calculus
-- statement:
--   The abstract repartition (adele) calculus.
--
--   Weil's proof of Riemann-Roch (Stichtenoth, *Algebraic Function Fields and Codes*, ch. 1) with
--   repartitions whose entries lie in `F` itself (no completions).  Everything here is ABSTRACT:
--   a field `F` over a finite field `Fq` with a family `v : ι → Valuation F ℤᵐ⁰` of valuations
--   (the places) and degrees `deg : ι → ℕ`.  The axioms used are collected in `Data.Axioms`;
--   part C discharges them for function fields (`RamanujanPetersson.Places`).
--
--   All index bookkeeping is done with `AddSubgroup.relIndex` (unconditionally multiplicative,
--   `0` encodes an infinite index) and converted to `Module.finrank` only for `L(D)`.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., GTM 254, Springer 2009, Chapters 1 and 5; E. Bombieri, Counting points on curves over finite fields (d'après S. A. Stepanov), Séminaire Bourbaki 430 (1973); A. Weil, Sur les courbes algébriques et les variétés qui s'en déduisent, Hermann 1948

import Mathlib

/-!
# Riemann-Roch, part A: the abstract repartition (adele) calculus

Weil's proof of Riemann-Roch (Stichtenoth, *Algebraic Function Fields and Codes*, ch. 1) with
repartitions whose entries lie in `F` itself (no completions).  Everything here is ABSTRACT:
a field `F` over a finite field `Fq` with a family `v : ι → Valuation F ℤᵐ⁰` of valuations
(the places) and degrees `deg : ι → ℕ`.  The axioms used are collected in `Data.Axioms`;
part C discharges them for function fields (`RamanujanPetersson.Places`).

All index bookkeeping is done with `AddSubgroup.relIndex` (unconditionally multiplicative,
`0` encodes an infinite index) and converted to `Module.finrank` only for `L(D)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open WithZero

namespace RamanujanPetersson.RR

/-! ### Group-theoretic index lemmas -/

section Index

/-- Relative index of two submodules, as additive subgroups. -/
noncomputable def rI {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (H K : Submodule R V) : ℕ :=
  H.toAddSubgroup.relIndex K.toAddSubgroup

theorem inf_toAddSubgroup' {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] (H K : Submodule R V) :
    (H ⊓ K).toAddSubgroup = H.toAddSubgroup ⊓ K.toAddSubgroup := rfl

/-- `[H' : H] = [H' ∩ K : H ∩ K] [H' + K : H + K]` for `H ≤ H'` in an abelian group. -/
theorem relIndex_split {G : Type*} [AddCommGroup G] {H H' : AddSubgroup G} (K : AddSubgroup G)
    (h : H ≤ H') :
    H.relIndex H' = (H ⊓ K).relIndex (H' ⊓ K) * (H ⊔ K).relIndex (H' ⊔ K) := by
  have h1 : H ≤ H ⊔ (H' ⊓ K) := le_sup_left
  have h2 : H ⊔ (H' ⊓ K) ≤ H' := sup_le h inf_le_left
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ h1 h2]
  congr 1
  · rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right H (H' ⊓ K),
      ← AddSubgroup.inf_relIndex_right (H ⊓ K) (H' ⊓ K)]
    congr 1
    ext x
    simp only [AddSubgroup.mem_inf]
    constructor
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, c⟩, b, c⟩
    · rintro ⟨⟨a, c⟩, b, _⟩; exact ⟨a, b, c⟩
  · have hmod : H ⊔ (H' ⊓ K) = H' ⊓ (H ⊔ K) := by
      apply le_antisymm
      · exact sup_le (le_inf h le_sup_left) (inf_le_inf_left _ le_sup_right)
      · intro x hx
        rw [AddSubgroup.mem_inf] at hx
        obtain ⟨hx1, hx2⟩ := hx
        obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hx2
        have hb' : b ∈ H' := by simpa using H'.sub_mem hx1 (h ha)
        exact AddSubgroup.mem_sup.2 ⟨a, ha, b, AddSubgroup.mem_inf.2 ⟨hb', hb⟩, rfl⟩
    rw [hmod, AddSubgroup.inf_relIndex_left, ← AddSubgroup.relIndex_sup_left H' (H ⊔ K)]
    congr 1
    apply le_antisymm
    · exact sup_le (sup_le (h.trans le_sup_left) le_sup_right) le_sup_left
    · exact sup_le le_sup_right (le_sup_right.trans le_sup_left)

/-- `|K| = |H| [K : H]` for `H ≤ K`. -/
theorem card_mul_relIndex {G : Type*} [AddCommGroup G] {H K : AddSubgroup G} (h : H ≤ K) :
    Nat.card H * H.relIndex K = Nat.card K := by
  have := (H.addSubgroupOf K).card_mul_index
  rw [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe h).toEquiv] at this
  exact this

theorem rI_split {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H H' : Submodule R V}
    (K : Submodule R V) (h : H ≤ H') :
    rI H H' = rI (H ⊓ K) (H' ⊓ K) * rI (H ⊔ K) (H' ⊔ K) := by
  unfold rI
  rw [Submodule.sup_toAddSubgroup, Submodule.sup_toAddSubgroup, inf_toAddSubgroup',
    inf_toAddSubgroup']
  exact relIndex_split _ h

theorem rI_mul_rI {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H K L : Submodule R V}
    (hHK : H ≤ K) (hKL : K ≤ L) : rI H K * rI K L = rI H L :=
  AddSubgroup.relIndex_mul_relIndex _ _ _ hHK hKL

theorem card_mul_rI {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H K : Submodule R V}
    (h : H ≤ K) : Nat.card H * rI H K = Nat.card K :=
  card_mul_relIndex (H := H.toAddSubgroup) (K := K.toAddSubgroup) h

theorem rI_eq_one_iff {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {H K : Submodule R V} :
    rI H K = 1 ↔ K ≤ H := by
  unfold rI
  rw [AddSubgroup.relIndex_eq_one]
  rfl

end Index

/-! ### Exponential helpers -/

theorem exp_mul_le_exp_iff {a b : ℤ} {x : ℤᵐ⁰} : exp a * x ≤ exp b ↔ x ≤ exp (b - a) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [← exp_log hx, ← exp_add, exp_le_exp, exp_le_exp]; omega

theorem pow_eq_pow_mul {q a b : ℕ} (hq : 1 < q) {r : ℕ} (h : q ^ a * r = q ^ b) :
    a ≤ b ∧ r = q ^ (b - a) := by
  have hab : a ≤ b := (Nat.pow_dvd_pow_iff_le_right hq).1 ⟨r, h.symm⟩
  refine ⟨hab, ?_⟩
  have hpos : 0 < q ^ a := pow_pos (by omega) a
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h, ← pow_add, Nat.add_sub_cancel' hab]

/-! ### Abstract data -/

/-- Abstract data for Riemann-Roch: valuations `v i` on `F` (the places), trivial on `Fq`,
with degrees `deg i`, such that a nonzero `f` has `v i f ≠ 1` for finitely many `i`. -/
structure Data (Fq F ι : Type*) [Field Fq] [Field F] [Algebra Fq F] where
  v : ι → Valuation F ℤᵐ⁰
  deg : ι → ℕ
  v_algebraMap : ∀ i (c : Fq), c ≠ 0 → v i (algebraMap Fq F c) = 1
  finite_ne_one : ∀ f : F, f ≠ 0 → {i | v i f ≠ 1}.Finite

namespace Data

variable {Fq F ι : Type*} [Field Fq] [Field F] [Algebra Fq F] (d : Data Fq F ι)

/-! #### Divisors -/

/-- The degree of a divisor. -/
def degD (D : ι →₀ ℤ) : ℤ := D.sum fun i n => n * (d.deg i : ℤ)

theorem degD_add (D E : ι →₀ ℤ) : d.degD (D + E) = d.degD D + d.degD E := by
  unfold degD; rw [Finsupp.sum_add_index'] <;> intros <;> ring

theorem degD_neg (D : ι →₀ ℤ) : d.degD (-D) = -d.degD D := by
  unfold degD
  rw [Finsupp.sum_neg_index (fun _ => by ring), Finsupp.sum, Finsupp.sum, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem degD_sub (D E : ι →₀ ℤ) : d.degD (D - E) = d.degD D - d.degD E := by
  rw [sub_eq_add_neg, degD_add, degD_neg, sub_eq_add_neg]

theorem degD_single (i : ι) (n : ℤ) : d.degD (Finsupp.single i n) = n * d.deg i := by
  unfold degD; rw [Finsupp.sum_single_index (by ring)]

@[simp] theorem degD_zero : d.degD 0 = 0 := by simp [degD]

theorem degD_nsmul (n : ℕ) (D : ι →₀ ℤ) : d.degD (n • D) = n * d.degD D := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, degD_add, ih]; push_cast; ring

theorem degD_nonneg {E : ι →₀ ℤ} (hE : 0 ≤ E) : 0 ≤ d.degD E := by
  unfold degD
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hE i) (Nat.cast_nonneg _)

theorem degD_mono {D E : ι →₀ ℤ} (h : D ≤ E) : d.degD D ≤ d.degD E := by
  have := d.degD_nonneg (sub_nonneg.2 h)
  rw [degD_sub] at this; linarith

/-- With positive degrees, an effective divisor of degree `0` is zero. -/
theorem eq_zero_of_degD_eq_zero (hdeg : ∀ i, 0 < d.deg i) {E : ι →₀ ℤ} (hE : 0 ≤ E)
    (h0 : d.degD E = 0) : E = 0 := by
  unfold degD Finsupp.sum at h0
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => mul_nonneg (hE i) (Nat.cast_nonneg _))] at h0
  ext i
  by_cases hi : i ∈ E.support
  · rcases mul_eq_zero.1 (h0 i hi) with h | h
    · exact h
    · have := hdeg i; omega
  · simpa using hi

/-! #### Balls, adeles and Riemann-Roch spaces -/

theorem v_smul (i : ι) {c : Fq} (hc : c ≠ 0) (f : F) : d.v i (c • f) = d.v i f := by
  rw [Algebra.smul_def, map_mul, d.v_algebraMap i c hc, one_mul]

/-- The ball `{f | v_i f ≤ exp n}` (functions with a pole of order at most `n` at `i`). -/
def ball (i : ι) (n : ℤ) : Submodule Fq F where
  carrier := {f | d.v i f ≤ exp n}
  add_mem' {a b} ha hb := ((d.v i).map_add a b).trans (max_le ha hb)
  zero_mem' := by simp
  smul_mem' c f hf := by
    by_cases hc : c = 0
    · simp [hc]
    · show d.v i (c • f) ≤ exp n
      rw [d.v_smul i hc]; exact hf

@[simp] theorem mem_ball {i : ι} {n : ℤ} {f : F} : f ∈ d.ball i n ↔ d.v i f ≤ exp n := Iff.rfl

theorem ball_mono (i : ι) {m n : ℤ} (h : m ≤ n) : d.ball i m ≤ d.ball i n :=
  fun _ hf => (d.mem_ball.1 hf).trans (exp_le_exp.2 h)

/-- The space `A(D)` of repartitions `α` with `v_i (α i) ≤ exp (D i)` for all `i`. -/
def AD (D : ι →₀ ℤ) : Submodule Fq (ι → F) := Submodule.pi Set.univ fun i => d.ball i (D i)

theorem mem_AD {D : ι →₀ ℤ} {α : ι → F} : α ∈ d.AD D ↔ ∀ i, d.v i (α i) ≤ exp (D i) := by
  simp [AD, Submodule.mem_pi]

theorem AD_mono {D E : ι →₀ ℤ} (h : D ≤ E) : d.AD D ≤ d.AD E := fun _ hα =>
  d.mem_AD.2 fun i => (d.mem_AD.1 hα i).trans (exp_le_exp.2 (h i))

/-- The adeles (repartitions): `α : ι → F` with `v_i (α i) ≤ 1` for almost all `i`. -/
def adeles : Submodule Fq (ι → F) where
  carrier := {α | {i | 1 < d.v i (α i)}.Finite}
  add_mem' {a b} ha hb := (ha.union hb).subset fun i hi => by
    simp only [Set.mem_setOf_eq, Pi.add_apply] at hi
    by_contra h
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_lt] at h
    exact absurd (((d.v i).map_add _ _).trans (max_le h.1 h.2)) (not_le.2 hi)
  zero_mem' := by simp
  smul_mem' c a ha := by
    by_cases hc : c = 0
    · simp [hc]
    · refine ha.subset fun i hi => ?_
      simp only [Set.mem_setOf_eq, Pi.smul_apply] at hi ⊢
      rwa [d.v_smul i hc] at hi

theorem mem_adeles {α : ι → F} : α ∈ d.adeles ↔ {i | 1 < d.v i (α i)}.Finite := Iff.rfl

theorem AD_le_adeles (D : ι →₀ ℤ) : d.AD D ≤ d.adeles := by
  intro α hα
  refine D.support.finite_toSet.subset fun i hi => ?_
  by_contra h
  have h0 : D i = 0 := by simpa using h
  have h1 := d.mem_AD.1 hα i
  rw [h0, exp_zero] at h1
  exact absurd h1 (not_le.2 hi)

/-- The diagonal embedding `F → ι → F`. -/
def const (_ : Data Fq F ι) : F →ₗ[Fq] (ι → F) := LinearMap.pi fun _ => LinearMap.id

@[simp] theorem const_apply (f : F) (i : ι) : d.const f i = f := rfl

theorem const_injective [Nonempty ι] : Function.Injective d.const := fun f g h => by
  have := congr_fun h (Classical.arbitrary ι)
  simpa using this

/-- The principal repartitions. -/
def Fs : Submodule Fq (ι → F) := LinearMap.range d.const

theorem Fs_le_adeles : d.Fs ≤ d.adeles := by
  rintro _ ⟨f, rfl⟩
  by_cases hf : f = 0
  · subst hf; simp
  · refine (d.finite_ne_one f hf).subset fun i hi => ?_
    exact ne_of_gt hi

/-- The Riemann-Roch space `L(D) = {f | v_i f ≤ exp (D i) for all i}`. -/
def LD (D : ι →₀ ℤ) : Submodule Fq F := (d.AD D).comap d.const

theorem mem_LD {D : ι →₀ ℤ} {f : F} : f ∈ d.LD D ↔ ∀ i, d.v i f ≤ exp (D i) := by
  simp [LD, mem_AD]

theorem LD_mono {D E : ι →₀ ℤ} (h : D ≤ E) : d.LD D ≤ d.LD E :=
  Submodule.comap_mono (d.AD_mono h)

/-- `ℓ(D) = dim_Fq L(D)`. -/
noncomputable def ell (D : ι →₀ ℤ) : ℕ := Module.finrank Fq (d.LD D)

theorem map_LD (D : ι →₀ ℤ) : (d.LD D).map d.const = d.AD D ⊓ d.Fs := by
  rw [LD, Submodule.map_comap_eq, inf_comm]
  rfl

theorem rI_LD [Nonempty ι] (D E : ι →₀ ℤ) :
    rI (d.LD D) (d.LD E) = rI (d.AD D ⊓ d.Fs) (d.AD E ⊓ d.Fs) := by
  rw [← d.map_LD, ← d.map_LD]
  unfold rI
  rw [Submodule.map_toAddSubgroup, Submodule.map_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ d.const_injective]

/-! #### Divisors of functions -/

/-- The divisor of `f` (`0` for `f = 0`): `(div f) i = -log (v_i f)`. -/
noncomputable def div (f : F) : ι →₀ ℤ :=
  Finsupp.ofSupportFinite (fun i => -log (d.v i f)) (by
    by_cases hf : f = 0
    · subst hf; simp
    · refine (d.finite_ne_one f hf).subset fun i hi h1 => hi ?_
      simp [h1])

theorem div_apply (f : F) (i : ι) : d.div f i = -log (d.v i f) := by
  simp [div, Finsupp.ofSupportFinite_coe]

theorem v_eq_exp {f : F} (hf : f ≠ 0) (i : ι) : d.v i f = exp (-(d.div f i)) := by
  rw [div_apply, neg_neg, exp_log ((map_ne_zero _).2 hf)]

theorem div_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : d.div (f * g) = d.div f + d.div g := by
  ext i
  simp only [div_apply, Finsupp.coe_add, Pi.add_apply, map_mul]
  rw [log_mul ((map_ne_zero _).2 hf) ((map_ne_zero _).2 hg)]; ring

theorem div_inv {f : F} (hf : f ≠ 0) : d.div f⁻¹ = -d.div f := by
  have h := d.div_mul (inv_ne_zero hf) hf
  rw [inv_mul_cancel₀ hf] at h
  have h1 : d.div (1 : F) = 0 := by ext i; simp [div_apply]
  rw [h1] at h
  exact eq_neg_of_add_eq_zero_left h.symm

theorem mem_LD_iff_div {D : ι →₀ ℤ} {f : F} (hf : f ≠ 0) : f ∈ d.LD D ↔ 0 ≤ d.div f + D := by
  rw [mem_LD, Finsupp.le_def]
  refine forall_congr' fun i => ?_
  rw [d.v_eq_exp hf, exp_le_exp, Finsupp.coe_add, Pi.add_apply, Finsupp.coe_zero, Pi.zero_apply]
  omega

/-- Multiplication by `z ≠ 0` maps `L(D + div z)` onto `L(D)`. -/
theorem map_mul_LD {z : F} (hz : z ≠ 0) (D : ι →₀ ℤ) :
    (d.LD (D + d.div z)).map (LinearMap.mulLeft Fq z) = d.LD D := by
  have key : ∀ (E : ι →₀ ℤ) (g : F), g ∈ d.LD (E + d.div z) ↔ z * g ∈ d.LD E := by
    intro E g
    simp only [mem_LD, map_mul, d.v_eq_exp hz, exp_mul_le_exp_iff, Finsupp.coe_add, Pi.add_apply]
    refine forall_congr' fun i => ?_
    rw [sub_neg_eq_add]
  ext f
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩; exact (key D g).1 hg
  · intro hf
    refine ⟨z⁻¹ * f, (key D _).2 ?_, ?_⟩
    · rwa [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
    · rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]

theorem ell_add_div {z : F} (hz : z ≠ 0) (D : ι →₀ ℤ) : d.ell (D + d.div z) = d.ell D := by
  have hinj : Function.Injective (LinearMap.mulLeft Fq z) := fun a b h => by
    simpa [LinearMap.mulLeft_apply, hz] using h
  unfold ell
  rw [← d.map_mul_LD hz D]
  exact (LinearEquiv.finrank_eq
    (Submodule.equivMapOfInjective (LinearMap.mulLeft Fq z) hinj (d.LD (D + d.div z))))

/-! #### The local-to-global index computation -/

theorem rI_AD_single (D : ι →₀ ℤ) (i : ι) :
    rI (d.AD D) (d.AD (D + Finsupp.single i 1)) = rI (d.ball i (D i)) (d.ball i (D i + 1)) := by
  classical
  set D' := D + Finsupp.single i 1 with hD'
  have hsi : ∀ j, j ≠ i → D' j = D j := fun j hj => by
    simp [hD', Ne.symm hj]
  have hii : D' i = D i + 1 := by simp [hD']
  let ev : (ι → F) →+ F := Pi.evalAddMonoidHom (fun _ => F) i
  have hAD : (d.AD D).toAddSubgroup =
      (d.ball i (D i)).toAddSubgroup.comap ev ⊓ (d.AD D').toAddSubgroup := by
    ext α
    simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_inf, AddSubgroup.mem_comap, mem_AD,
      Submodule.mem_toAddSubgroup, mem_ball, ev, Pi.evalAddMonoidHom_apply]
    constructor
    · intro h
      refine ⟨h i, fun j => (h j).trans (exp_le_exp.2 ?_)⟩
      by_cases hj : j = i
      · subst hj; rw [hii]; omega
      · rw [hsi j hj]
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj; exact h1
      · simpa [hsi j hj] using h2 j
  have hmap : (d.AD D').toAddSubgroup.map ev = (d.ball i (D i + 1)).toAddSubgroup := by
    ext f
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, mem_AD, mem_ball, ev,
      Pi.evalAddMonoidHom_apply]
    constructor
    · rintro ⟨α, hα, rfl⟩; simpa [hii] using hα i
    · intro hf
      refine ⟨Pi.single i f, fun j => ?_, by simp⟩
      by_cases hj : j = i
      · subst hj; simpa [hii] using hf
      · simp [hj]
  unfold rI
  rw [hAD, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, hmap]

/-! #### The axioms and the global index of `A(D) ⊆ A(D')` -/

variable [Fintype Fq]

/-- The local axioms of the abstract theory (discharged for function fields in part C):
places exist and have positive degree, the local index `[ball i (n+1) : ball i n] = q ^ deg i`,
the product formula and `L(0)` finite. -/
structure Axioms0 : Prop where
  nonempty : Nonempty ι
  deg_pos : ∀ i, 0 < d.deg i
  localIndex : ∀ i (n : ℤ), rI (d.ball i n) (d.ball i (n + 1)) = Fintype.card Fq ^ d.deg i
  deg_div : ∀ f : F, f ≠ 0 → d.degD (d.div f) = 0
  finite_L0 : Finite (d.LD 0)

/-- The axioms: the local axioms plus the input for Riemann's inequality (for function fields:
`B` the pole divisor of a separating element `x`, `C` a pole bound for an integral basis). -/
structure Axioms extends Axioms0 d : Prop where
  riemannInput : ∃ B : ι →₀ ℤ, 0 ≤ B ∧ 0 < d.degD B ∧ ∃ C : ι →₀ ℤ, 0 ≤ C ∧
    ∃ c : ℤ, ∀ n : ℕ, (n : ℤ) * d.degD B - c ≤ d.ell (n • B + C)

variable {d}

theorem one_lt_q : 1 < Fintype.card Fq := Fintype.one_lt_card

theorem rI_AD_add_single_nat (hd : d.Axioms0) (D : ι →₀ ℤ) (i : ι) (n : ℕ) :
    rI (d.AD D) (d.AD (D + Finsupp.single i (n : ℤ))) = Fintype.card Fq ^ (n * d.deg i) := by
  induction n with
  | zero => simp [rI, AddSubgroup.relIndex_self]
  | succ n ih =>
    have e : D + Finsupp.single i ((n + 1 : ℕ) : ℤ) =
        (D + Finsupp.single i (n : ℤ)) + Finsupp.single i 1 := by
      rw [Nat.cast_succ, Finsupp.single_add, add_assoc]
    rw [e, ← rI_mul_rI (d.AD_mono (le_add_of_nonneg_right
        (Finsupp.single_nonneg.2 (Nat.cast_nonneg _))))
      (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 zero_le_one))), ih,
      d.rI_AD_single, hd.localIndex, ← pow_add]
    congr 1; ring

theorem rI_AD_add (hd : d.Axioms0) {E : ι →₀ ℤ} (hE : 0 ≤ E) (D : ι →₀ ℤ) :
    rI (d.AD D) (d.AD (D + E)) = Fintype.card Fq ^ (d.degD E).toNat := by
  classical
  induction E using Finsupp.induction generalizing D with
  | zero => simp [rI, AddSubgroup.relIndex_self]
  | single_add a b f ha hb ih =>
    have hfa : f a = 0 := Finsupp.notMem_support_iff.1 ha
    have hb0 : 0 ≤ b := by have := hE a; simpa [hfa] using this
    have hf0 : 0 ≤ f := fun j => by
      by_cases hj : j = a
      · subst hj; simp [hfa]
      · have := hE j; simpa [Finsupp.single_apply, Ne.symm hj] using this
    obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hb0
    rw [← add_assoc, ← rI_mul_rI (d.AD_mono (le_add_of_nonneg_right (Finsupp.single_nonneg.2 hb0)))
      (d.AD_mono (le_add_of_nonneg_right hf0)), rI_AD_add_single_nat hd, ih hf0, ← pow_add,
      degD_add, degD_single]
    congr 1
    have hdf := d.degD_nonneg hf0
    have hm : ((k : ℤ) * (d.deg a : ℤ)) = ((k * d.deg a : ℕ) : ℤ) := by push_cast; ring
    rw [hm]
    generalize k * d.deg a = m
    omega

/-- `[A(D') : A(D)] = q ^ (deg D' - deg D)`. -/
theorem rI_AD_le (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    rI (d.AD D) (d.AD D') = Fintype.card Fq ^ (d.degD D' - d.degD D).toNat := by
  have := rI_AD_add hd (sub_nonneg.2 h) D
  rwa [add_sub_cancel, degD_sub] at this

theorem card_LD_mul {D D' : ι →₀ ℤ} (h : D ≤ D') :
    Nat.card (d.LD D) * rI (d.LD D) (d.LD D') = Nat.card (d.LD D') :=
  card_mul_rI (d.LD_mono h)

theorem rI_LD_mul (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    rI (d.LD D) (d.LD D') * rI (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      Fintype.card Fq ^ (d.degD D' - d.degD D).toNat := by
  have := hd.nonempty
  rw [d.rI_LD, ← rI_split _ (d.AD_mono h), rI_AD_le hd h]

theorem finite_LD (hd : d.Axioms0) (D : ι →₀ ℤ) : Finite (d.LD D) := by
  have := hd.finite_L0
  have h1 : (0 : ι →₀ ℤ) ≤ D ⊔ 0 := le_sup_right
  have h2 : D ≤ D ⊔ 0 := le_sup_left
  have hne : rI (d.LD 0) (d.LD (D ⊔ 0)) ≠ 0 := by
    intro h0
    have := rI_LD_mul hd h1
    rw [h0, zero_mul] at this
    exact absurd this.symm (pow_ne_zero _ Fintype.card_ne_zero)
  have hc : Nat.card (d.LD (D ⊔ 0)) ≠ 0 := by
    rw [← card_LD_mul h1]
    exact mul_ne_zero Nat.card_pos.ne' hne
  have : Finite (d.LD (D ⊔ 0)) := Nat.finite_of_card_ne_zero hc
  exact Finite.of_injective (Submodule.inclusion (d.LD_mono h2)) (Submodule.inclusion_injective _)

/-- `|L(D)| = q ^ ℓ(D)`. -/
theorem card_LD (hd : d.Axioms0) (D : ι →₀ ℤ) : Nat.card (d.LD D) = Fintype.card Fq ^ d.ell D := by
  have := finite_LD hd D
  have : Module.Finite Fq (d.LD D) := Module.Finite.of_finite
  rw [ell, Module.natCard_eq_pow_finrank (K := Fq), Nat.card_eq_fintype_card]

theorem ell_le_of_le (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    d.ell D ≤ d.ell D' ∧ rI (d.LD D) (d.LD D') = Fintype.card Fq ^ (d.ell D' - d.ell D) := by
  have := card_LD_mul (d := d) h
  rw [card_LD hd, card_LD hd] at this
  exact pow_eq_pow_mul (one_lt_q (Fq := Fq)) this

/-- `ℓ(D') - ℓ(D) ≤ deg D' - deg D` for `D ≤ D'`, and the index of `A(D) + F` in `A(D') + F`. -/
theorem ell_sub_le (hd : d.Axioms0) {D D' : ι →₀ ℤ} (h : D ≤ D') :
    (d.ell D' : ℤ) - d.ell D ≤ d.degD D' - d.degD D ∧
    rI (d.AD D ⊔ d.Fs) (d.AD D' ⊔ d.Fs) =
      Fintype.card Fq ^ ((d.degD D' - d.degD D).toNat - (d.ell D' - d.ell D)) := by
  obtain ⟨hle, hr⟩ := ell_le_of_le hd h
  have := rI_LD_mul hd h
  rw [hr] at this
  obtain ⟨h1, h2⟩ := pow_eq_pow_mul (one_lt_q (Fq := Fq)) this
  refine ⟨?_, h2⟩
  have := d.degD_mono h
  omega

end Data

end RamanujanPetersson.RR


