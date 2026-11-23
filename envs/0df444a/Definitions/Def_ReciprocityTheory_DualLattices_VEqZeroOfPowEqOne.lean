-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
-- name    : ReciprocityTheory_DualLattices_VEqZeroOfPowEqOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:44.193855+00:00
-- url     : https://prove2.me/theorems/05daa4d2-6123-44ef-be8d-125ea2b9cac2
-- title:
--   VEq Zero Of Pow Eq One
-- statement:
--   Definitions and structural lemmas for VEq Zero Of Pow Eq One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/VEqZeroOfPowEqOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.PGsh
open MvPowerSeries
noncomputable section
variable {C : Type*} [Field C]
def IsIntV (v : AddValuation C (WithTop ℝ)) (x : C) : Prop := 0 ≤ v x
def MvIsInt (v : AddValuation C (WithTop ℝ)) {σ : Type*} (f : MvPowerSeries σ C) : Prop :=
  ∀ α, IsIntV v (coeff α f)
def PsIsInt (v : AddValuation C (WithTop ℝ)) (f : PowerSeries C) : Prop :=
  ∀ n, IsIntV v (PowerSeries.coeff n f)
theorem v_eq_zero_of_pow_eq_one {v : AddValuation C (WithTop ℝ)} {z : C} {N : ℕ} (hN : N ≠ 0)
    (hz : z ^ N = 1) : v z = 0 := by
  have h1 : N • v z = 0 := by rw [← AddValuation.map_pow, hz, AddValuation.map_one]
  generalize v z = x at h1 ⊢
  induction x using WithTop.recTopCoe with
  | top =>
    exfalso
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
    rw [succ_nsmul, WithTop.add_top] at h1
    exact WithTop.top_ne_zero h1
  | coe r =>
    rw [← WithTop.coe_nsmul] at h1
    have h2 : N • r = 0 := WithTop.coe_eq_zero.mp h1
    rw [nsmul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Nat.cast_eq_zero.mp h) hN
    · rw [h]; rfl
structure LogFGL (v : AddValuation C (WithTop ℝ)) (d : ℕ) where
  lg : Fin d → MvPowerSeries (Fin d) C
  lg_const : ∀ a, constantCoeff (lg a) = 0
  lg_lin : ∀ a b, coeff (Finsupp.single b 1) (lg a) = if a = b then 1 else 0
  F : Fin d → MvPowerSeries (Fin d ⊕ Fin d) C
  F_int : ∀ a, MvIsInt v (F a)
  F_const : ∀ a, constantCoeff (F a) = 0
  lg_F : ∀ a, subst F (lg a) =
    subst (fun b => X (Sum.inl b)) (lg a) + subst (fun b => X (Sum.inr b)) (lg a)
def IsCurve (v : AddValuation C (WithTop ℝ)) {d : ℕ} (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a, PowerSeries.constantCoeff (ga a) = 0 ∧ PsIsInt v (ga a)
def tangent {d : ℕ} (ga : Fin d → PowerSeries C) : Fin d → C :=
  fun a => PowerSeries.coeff 1 (ga a)
def rescaleCurve {d : ℕ} (x : C) (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => PowerSeries.rescale x (ga a)
namespace LogFGL
variable {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d)
def lgCurve (ga : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst ga (G.lg a)
def add (ga gb : Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  fun a => subst (Sum.elim ga gb) (G.F a)
def sumList (G : LogFGL v d) : List (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | [] => 0
  | g :: l => G.add g (sumList G l)
def sumF {m : ℕ} (g : Fin m → Fin d → PowerSeries C) : Fin d → PowerSeries C :=
  G.sumList (List.ofFn g)
def nsmulF (G : LogFGL v d) : ℕ → (Fin d → PowerSeries C) → (Fin d → PowerSeries C)
  | 0, _ => 0
  | n + 1, ga => G.add ga (nsmulF G n ga)
def lc (p : ℕ) (ga : Fin d → PowerSeries C) (n : ℕ) : Fin d → C :=
  fun a => PowerSeries.coeff (p ^ n) (G.lgCurve ga a)
def IsPTypical (p : ℕ) (ga : Fin d → PowerSeries C) : Prop :=
  ∀ a m, (∀ n, m ≠ p ^ n) → PowerSeries.coeff m (G.lgCurve ga a) = 0
def IsOfType (p : ℕ) {h : ℕ} (ty : Fin d → ZMod h) (i : ZMod h)
    (ga : Fin d → PowerSeries C) : Prop :=
  G.IsPTypical p ga ∧ ∀ (n : ℕ) a, ty a ≠ i + (n : ZMod h) → G.lc p ga n a = 0
end LogFGL
structure MuAction {v : AddValuation C (WithTop ℝ)} {d : ℕ} (G : LogFGL v d) (p h : ℕ)
    (ty : Fin d → ZMod h) where
  mul : C → Fin d → MvPowerSeries (Fin d) C
  mul_int : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a, MvIsInt v (mul z a)
  mul_const : ∀ z a, constantCoeff (mul z a) = 0
  lg_mul : ∀ z, z ^ (p ^ h - 1) = 1 → ∀ a,
    subst (mul z) (G.lg a) = (z ^ (p ^ (ty a).val)) • G.lg a
def additive (v : AddValuation C (WithTop ℝ)) (d : ℕ) : LogFGL v d where
  lg a := X a
  lg_const a := by simp
  lg_lin a b := by
    rw [coeff_X]
    by_cases h : a = b
    · subst h; simp
    · have : Finsupp.single b 1 ≠ Finsupp.single a 1 := by
        intro e; exact h (Finsupp.single_left_injective one_ne_zero e).symm
      simp [h, this]
  F a := X (Sum.inl a) + X (Sum.inr a)
  F_int a α := by
    unfold IsIntV
    rw [map_add]
    refine le_trans (le_min ?_ ?_) (v.map_add _ _) <;> (rw [coeff_X]; split_ifs <;> simp)
  F_const a := by simp
  lg_F a := by
    rw [subst_X (hasSubst_of_constantCoeff_zero (by simp)),
      subst_X (hasSubst_of_constantCoeff_zero (by simp)),
      subst_X (hasSubst_of_constantCoeff_zero (by simp))]
def additiveMu (v : AddValuation C (WithTop ℝ)) (d p h : ℕ) (hph : p ^ h - 1 ≠ 0)
    (ty : Fin d → ZMod h) : MuAction (additive v d) p h ty where
  mul z a := (z ^ (p ^ (ty a).val)) • X a
  mul_int z hz a α := by
    unfold IsIntV
    rw [coeff_smul, coeff_X]
    split_ifs
    · rw [mul_one, v.map_pow, v_eq_zero_of_pow_eq_one hph hz, smul_zero]
    · simp
  mul_const z a := by simp
  lg_mul z hz a := by
    simp only [additive]
    rw [subst_X (hasSubst_of_constantCoeff_zero (by simp))]
def expComp [CharZero C] (Ω : C) (lg : PowerSeries C) : PowerSeries C :=
  PowerSeries.mk fun m => ∑ n ∈ Finset.range (m + 1),
    Ω ^ n / (n.factorial : C) * PowerSeries.coeff m (lg ^ n)
def lgSum {d M : ℕ} (p : ℕ) (c : Fin d → ℕ → Fin d → C)
    (t : Fin d → MvPowerSeries (Fin M) C) (b : Fin d) : MvPowerSeries (Fin M) C :=
  fun α => ∑ n ∈ Finset.range (Finsupp.degree α + 1), ∑ a, c a n b * coeff α (t a ^ (p ^ n))
def OrdGe (v : AddValuation C (WithTop ℝ)) {M : ℕ} (ρ : Fin M → ℝ) (g : MvPowerSeries (Fin M) C)
    (r : ℝ) : Prop :=
  ∀ α : Fin M →₀ ℕ, (((r - ∑ m, ρ m * α m : ℝ)) : WithTop ℝ) ≤ v (coeff α g)
def radius (p : ℕ) (k : ℤ) : ℝ := (1 + (p : ℝ) ^ (-(2 * k + 1))) / ((p : ℝ) ^ 2 - 1)
end
end ReciprocityTheory.PGsh


