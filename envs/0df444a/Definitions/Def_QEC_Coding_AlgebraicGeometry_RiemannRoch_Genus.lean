-- Prove2me | Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
-- name    : QEC_Coding_AlgebraicGeometry_RiemannRoch_Genus
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T19:08:24.2297+00:00
-- url     : https://prove2.me/theorems/1b957619-c35d-4b8e-9449-537ab8269dac
-- title:
--   Genus
-- statement:
--   Definitions and structural lemmas for Genus, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/RiemannRoch/Genus.lean

import Mathlib.Data.Int.LeastGreatest
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Divisors_GlobalPrincipalDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PolarDegree
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_nonnegative
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_sub
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_Divisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_coe_constantsToValuationRing
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_finiteDimensional_riemannRochSubmodule
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_chartVariable_degree_eq_finrank
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_polarDivisor_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_principalDivisor_degree_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_order
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackageEquiv_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_repackage_valuation
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_basis_polarFamily_lower_bound
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_le_add_degree_of_le
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_principal_add
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_riemannRochDimension_zero
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_apply
import Theorems.Thm_QEC_Coding_AlgebraicGeometry_RatFuncDerivation_rationalDerivationEquiv_symm_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.Divisor.degree_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.coe_constantsToValuationRing
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.polarDivisor_zero
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_order
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackageEquiv_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.GlobalPlace.repackage_valuation
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_apply
attribute [local simp] QEC.Coding.AlgebraicGeometry.RatFuncDerivation.rationalDerivationEquiv_symm_apply


set_option autoImplicit false
namespace QEC.Coding.AlgebraicGeometry
open Polynomial Submodule
open scoped Polynomial RatFunc
noncomputable section
variable (k F : Type*) [Field k] [Finite k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F]
variable [s : Algebra.IsSeparable (RatFunc k) F]
noncomputable local instance riemannRochGenusAlgebra : Algebra k F :=
  @AffinePlace.constantAlgebra k F _ _ π
attribute [local instance] riemannRochGenusAlgebra
local instance riemannRochGenusScalarTower :
    IsScalarTower k (RatFunc k) F :=
  directConstantScalarTower (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
attribute [local instance] riemannRochGenusScalarTower
namespace GlobalPlace
local instance riemannRochGenusFiniteDimensional
    (G : Divisor (GlobalPlace k F)) :
    FiniteDimensional k (riemannRochSubmodule G) :=
  finiteDimensional_riemannRochSubmodule
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F G
attribute [local instance] riemannRochGenusFiniteDimensional
variable [IsFullConstantField k F]
noncomputable def riemannRochDefect
    (D : Divisor (GlobalPlace k F)) : ℤ :=
  Divisor.degree (residueDegree (k := k) (F := F)) D + 1 -
    riemannRochDimension D
theorem riemannRochDefect_mono
    {D E : Divisor (GlobalPlace k F)} (hDE : D ≤ E) :
    riemannRochDefect (k := k) (F := F) D ≤
      riemannRochDefect (k := k) (F := F) E := by
  have hnonnegative : Divisor.Nonnegative (E - D) := by
    intro P
    exact sub_nonneg.mpr (hDE P)
  have hdegreeNonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) (E - D) :=
    Divisor.degree_nonnegative _ _ hnonnegative
  have hdimension := riemannRochDimension_le_add_degree_of_le
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hdimensionInt : (riemannRochDimension E : ℤ) ≤
      (riemannRochDimension D : ℤ) +
        ((Divisor.degree (residueDegree (k := k) (F := F))
          (E - D)).toNat : ℤ) := by
    exact_mod_cast hdimension
  rw [Int.toNat_of_nonneg hdegreeNonnegative] at hdimensionInt
  have hdegree :
      Divisor.degree (residueDegree (k := k) (F := F)) E =
        Divisor.degree (residueDegree (k := k) (F := F)) D +
          Divisor.degree (residueDegree (k := k) (F := F)) (E - D) := by
    rw [Divisor.degree_sub]
    ring
  simp only [riemannRochDefect]
  omega
theorem riemannRochDefect_principal_add
    (u : Fˣ) (D : Divisor (GlobalPlace k F)) :
    riemannRochDefect (k := k) (F := F)
        (principalDivisor (k := k) (F := F) u + D) =
      riemannRochDefect (k := k) (F := F) D := by
  simp only [riemannRochDefect, Divisor.degree_add,
    principalDivisor_degree_zero (k := k) (F := F), zero_add,
    riemannRochDimension_principal_add (k := k) (F := F)]
theorem le_add_principal_of_mem_riemannRochSubmodule
    {D₀ D₁ : Divisor (GlobalPlace k F)} {f : F} (hf : f ≠ 0)
    (hmem : f ∈ riemannRochSubmodule (D₁ - D₀)) :
    D₀ ≤ D₁ + principalDivisor (k := k) (F := F) (Units.mk0 f hf) := by
  intro P
  have hP :=
    (mem_riemannRochSubmodule_iff_order_add_nonnegative (D₁ - D₀) hf).mp
      hmem P
  simp only [Finsupp.sub_apply] at hP
  rw [Finsupp.add_apply, principalDivisor_apply]
  simp only [Units.val_mk0]
  omega
theorem riemannRochDimension_sub_nonnegative_sub_ge
    {D E : Divisor (GlobalPlace k F)} (hE : Divisor.Nonnegative E) :
    (riemannRochDimension (D + E) : ℤ) -
        Divisor.degree (residueDegree (k := k) (F := F)) E ≤
      riemannRochDimension D := by
  have hDE : D ≤ D + E := by
    intro P
    simp only [Finsupp.add_apply]
    exact le_add_of_nonneg_right (hE P)
  have hdimension := riemannRochDimension_le_add_degree_of_le
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDE
  have hdegreeNonnegative : 0 ≤
      Divisor.degree (residueDegree (k := k) (F := F)) E :=
    Divisor.degree_nonnegative _ _ hE
  have hdifference : (D + E) - D = E := by
    ext P
    simp only [Finsupp.sub_apply, Finsupp.add_apply]
    omega
  rw [hdifference] at hdimension
  have hdimensionInt : (riemannRochDimension (D + E) : ℤ) ≤
      (riemannRochDimension D : ℤ) +
        ((Divisor.degree (residueDegree (k := k) (F := F)) E).toNat : ℤ) := by
    exact_mod_cast hdimension
  rw [Int.toNat_of_nonneg hdegreeNonnegative] at hdimensionInt
  omega
theorem riemannRochDefect_le_of_family
    (B C : Divisor (GlobalPlace k F)) (c₀ : ℤ)
    (hbounded : ∀ r : ℕ,
      riemannRochDefect (k := k) (F := F) (C + r • B) ≤ c₀)
    (hgrow : ∀ m : ℤ, ∃ r : ℕ,
      m ≤ (riemannRochDimension (C + r • B) : ℤ)) :
    ∀ D : Divisor (GlobalPlace k F),
      riemannRochDefect (k := k) (F := F) D ≤ c₀ := by
  intro D
  let Dpos := D ⊔ (0 : Divisor (GlobalPlace k F))
  have hDle : D ≤ Dpos := le_sup_left
  have hDposNonnegative : Divisor.Nonnegative Dpos := by
    intro P
    exact le_max_right (D P) 0
  obtain ⟨r, hr⟩ := hgrow
    (Divisor.degree (residueDegree (k := k) (F := F)) Dpos + 1)
  let Dr := C + r • B
  have hsub := riemannRochDimension_sub_nonnegative_sub_ge
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
    (D := Dr - Dpos) (E := Dpos) hDposNonnegative
  rw [sub_add_cancel] at hsub
  have hpositive : 0 < riemannRochDimension (Dr - Dpos) := by
    linarith
  have hpositiveFinrank :
      0 < Module.finrank k (riemannRochSubmodule (Dr - Dpos)) := by
    simpa only [riemannRochDimension] using hpositive
  obtain ⟨f, hf⟩ :=
    (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp hpositiveFinrank
  let fF : F := f
  have hfF : fF ≠ 0 := by
    intro hzero
    apply hf
    exact Subtype.ext hzero
  have hmem : fF ∈ riemannRochSubmodule (Dr - Dpos) := f.property
  have hDposLe : Dpos ≤
      Dr + principalDivisor (k := k) (F := F) (Units.mk0 fF hfF) :=
    le_add_principal_of_mem_riemannRochSubmodule
      (k := k) (F := F) hfF hmem
  have hDle' : D ≤
      Dr + principalDivisor (k := k) (F := F) (Units.mk0 fF hfF) :=
    hDle.trans hDposLe
  calc
    riemannRochDefect (k := k) (F := F) D ≤
        riemannRochDefect (k := k) (F := F)
          (Dr + principalDivisor (k := k) (F := F) (Units.mk0 fF hfF)) :=
      riemannRochDefect_mono
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F hDle'
    _ = riemannRochDefect (k := k) (F := F)
        (principalDivisor (k := k) (F := F) (Units.mk0 fF hfF) + Dr) := by
      rw [add_comm]
    _ = riemannRochDefect (k := k) (F := F) Dr :=
      riemannRochDefect_principal_add
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F _ Dr
    _ ≤ c₀ := hbounded r
theorem divisorDegree_nsmul
    (n : ℕ) (D : Divisor (GlobalPlace k F)) :
    Divisor.degree (residueDegree (k := k) (F := F)) (n • D) =
      (n : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) D := by
  simpa only [Divisor.degree, nsmul_eq_mul] using
    (Divisor.degreeHom (residueDegree (k := k) (F := F))).map_nsmul n D
theorem riemannRochDefect_le_chart_family
    (D : Divisor (GlobalPlace k F)) :
    riemannRochDefect (k := k) (F := F) D ≤
      Divisor.degree (residueDegree (k := k) (F := F))
          (basisPoleBound (k := k) (F := F)
            (Module.finBasis (RatFunc k) F)) + 1 -
        Module.finrank (RatFunc k) F := by
  let n := Module.finrank (RatFunc k) F
  let b : Module.Basis (Fin n) (RatFunc k) F := Module.finBasis (RatFunc k) F
  let C := basisPoleBound (k := k) (F := F) b
  let B := polarDivisor (k := k) (F := F)
    (chartVariable (k := k) (F := F))
  let c₀ := Divisor.degree (residueDegree (k := k) (F := F)) C + 1 - (n : ℤ)
  have hBdegree :
      Divisor.degree (residueDegree (k := k) (F := F)) B = (n : ℤ) := by
    exact polarDivisor_chartVariable_degree_eq_finrank
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F
  have hbounded : ∀ r : ℕ,
      riemannRochDefect (k := k) (F := F) (C + r • B) ≤ c₀ := by
    intro r
    have hdegree :
        Divisor.degree (residueDegree (k := k) (F := F)) (C + r • B) =
          Divisor.degree (residueDegree (k := k) (F := F)) C +
            (r : ℤ) * Divisor.degree (residueDegree (k := k) (F := F)) B := by
      rw [Divisor.degree_add, divisorDegree_nsmul]
    have hlower := riemannRochDimension_basis_polarFamily_lower_bound
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (r := r) b
    have hlowerInt : ((n * (r + 1) : ℕ) : ℤ) ≤
        (riemannRochDimension (C + r • B) : ℤ) := by
      exact_mod_cast hlower
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hlowerInt
    simp only [riemannRochDefect]
    rw [hdegree, hBdegree]
    dsimp only [c₀]
    nlinarith
  have hn : 0 < n := Module.finrank_pos
  have hgrow : ∀ m : ℤ, ∃ r : ℕ,
      m ≤ (riemannRochDimension (C + r • B) : ℤ) := by
    intro m
    by_cases hm : m ≤ 0
    · refine ⟨0, ?_⟩
      exact hm.trans (Int.ofNat_nonneg _)
    · have hmpos : 0 < m := lt_of_not_ge hm
      let mnat := m.toNat
      have hmcast : (mnat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hmpos)
      refine ⟨mnat, ?_⟩
      have hlower := riemannRochDimension_basis_polarFamily_lower_bound
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F (r := mnat) b
      have hlowerInt : ((n * (mnat + 1) : ℕ) : ℤ) ≤
          (riemannRochDimension (C + mnat • B) : ℤ) := by
        exact_mod_cast hlower
      have hnOne : (1 : ℤ) ≤ (n : ℤ) := by
        exact_mod_cast hn
      have hmBound : m ≤ ((n * (mnat + 1) : ℕ) : ℤ) := by
        rw [← hmcast]
        push_cast
        nlinarith
      exact hmBound.trans hlowerInt
  have hbound := riemannRochDefect_le_of_family
    (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F B C c₀
      hbounded hgrow D
  simpa only [n, b, C, c₀] using hbound
theorem exists_max_riemannRochDefect :
    ∃ g : ℕ,
      (∀ D : Divisor (GlobalPlace k F),
        riemannRochDefect (k := k) (F := F) D ≤ (g : ℤ)) ∧
      ∃ D : Divisor (GlobalPlace k F),
        riemannRochDefect (k := k) (F := F) D = (g : ℤ) := by
  let b := Module.finBasis (RatFunc k) F
  let n := Module.finrank (RatFunc k) F
  let C := basisPoleBound (k := k) (F := F) b
  let c₀ := Divisor.degree (residueDegree (k := k) (F := F)) C + 1 - (n : ℤ)
  have hbound : ∀ D : Divisor (GlobalPlace k F),
      riemannRochDefect (k := k) (F := F) D ≤ c₀ := by
    intro D
    exact riemannRochDefect_le_chart_family
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F D
  have hzero : riemannRochDefect (k := k) (F := F)
      (0 : Divisor (GlobalPlace k F)) = 0 := by
    simp only [riemannRochDefect, Divisor.degree_zero,
      riemannRochDimension_zero
        (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F]
    omega
  have hinhabited : ∃ z : ℤ, ∃ D : Divisor (GlobalPlace k F),
      riemannRochDefect (k := k) (F := F) D = z :=
    ⟨0, 0, hzero⟩
  have hbounded : ∃ upper : ℤ, ∀ z : ℤ,
      (∃ D : Divisor (GlobalPlace k F),
        riemannRochDefect (k := k) (F := F) D = z) → z ≤ upper := by
    refine ⟨c₀, ?_⟩
    intro z ⟨D, hD⟩
    simpa only [← hD] using hbound D
  obtain ⟨g, hg, hgmax⟩ := Int.exists_greatest_of_bdd hbounded hinhabited
  have hgNonnegative : 0 ≤ g := hgmax 0 ⟨0, hzero⟩
  refine ⟨g.toNat, ?_, ?_⟩
  · intro D
    calc
      riemannRochDefect (k := k) (F := F) D ≤ g :=
        hgmax _ ⟨D, rfl⟩
      _ = (g.toNat : ℤ) := (Int.toNat_of_nonneg hgNonnegative).symm
  · obtain ⟨D, hD⟩ := hg
    refine ⟨D, ?_⟩
    rw [Int.toNat_of_nonneg hgNonnegative]
    exact hD
noncomputable def functionFieldGenus : ℕ :=
  Classical.choose
    (exists_max_riemannRochDefect
      (π := π) (ρ := ρ) (τ := τ) (φ := φ) (s := s) k F)
noncomputable def riemannRochIndexOfSpecialty
    (D : Divisor (GlobalPlace k F)) : ℕ :=
  ((riemannRochDimension D : ℤ) -
    (Divisor.degree (residueDegree (k := k) (F := F)) D + 1 -
      (functionFieldGenus (π := π) (ρ := ρ) (τ := τ)
        (φ := φ) (s := s) k F : ℤ))).toNat
end GlobalPlace
end
end QEC.Coding.AlgebraicGeometry


