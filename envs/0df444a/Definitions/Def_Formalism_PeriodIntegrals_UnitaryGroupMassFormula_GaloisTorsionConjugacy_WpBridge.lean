-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GaloisTorsionConjugacy_WpBridge
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:52.520808+00:00
-- url     : https://prove2.me/theorems/be425ba6-8ec1-4a4e-a343-c22e07145e37
-- title:
--   Wp Bridge
-- statement:
--   Definitions and structural lemmas for Wp Bridge, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/GaloisTorsionConjugacy/WpBridge.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GalTorsConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.GalTorsConj.W
open PI.GalTorsConj
def addX {K : Type*} [Field K] (x y x₂ y₂ : K) : K :=
  ((y - y₂) / (x - x₂)) ^ 2 / 4 - x - x₂
def addY {K : Type*} [Field K] (x y x₂ y₂ : K) : K :=
  (y - y₂) / (x - x₂) * (x - addX x y x₂ y₂) - y
def dblX {K : Type*} [Field K] (x y g : K) : K :=
  ((6 * x ^ 2 - g / 2) / y) ^ 2 / 4 - 2 * x
def dblY {K : Type*} [Field K] (x y g : K) : K :=
  (6 * x ^ 2 - g / 2) / y * (x - dblX x y g) - y
def AddLaw : Prop :=
  ∀ (L : PeriodPair) (z w : ℂ), z ∉ L.lattice → w ∉ L.lattice → z - w ∉ L.lattice →
    z + w ∉ L.lattice →
    L.weierstrassP (z + w) = addX (L.weierstrassP z) (L.derivWeierstrassP z)
        (L.weierstrassP w) (L.derivWeierstrassP w) ∧
    L.derivWeierstrassP (z + w) = addY (L.weierstrassP z) (L.derivWeierstrassP z)
        (L.weierstrassP w) (L.derivWeierstrassP w)
def DblLaw : Prop :=
  ∀ (L : PeriodPair) (z : ℂ), z ∉ L.lattice → 2 * z ∉ L.lattice →
    L.weierstrassP (2 * z) = dblX (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂ ∧
    L.derivWeierstrassP (2 * z) = dblY (L.weierstrassP z) (L.derivWeierstrassP z) L.g₂
def POnto : Prop :=
  ∀ (L : PeriodPair) (x y : ℂ), y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃ →
    ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = x ∧ L.derivWeierstrassP z = y
def LatOfInv : Prop :=
  ∀ Λ : AddSubgroup ℂ, g2 Λ ^ 3 - 27 * g3 Λ ^ 2 ≠ 0 →
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = Λ
def InvExist : Prop :=
  ∀ a b : ℂ, a ^ 3 - 27 * b ^ 2 ≠ 0 → ∃ Λ : AddSubgroup ℂ, g2 Λ = a ∧ g3 Λ = b
def RankTwoLatticePair : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∃ L : PeriodPair, L.lattice.toAddSubgroup = lat2 w₁ w₂
def WpBridge : Prop :=
  ∀ L : PeriodPair, wpF L.lattice.toAddSubgroup = L.weierstrassP ∧
    wpD L.lattice.toAddSubgroup = L.derivWeierstrassP ∧
    g2 L.lattice.toAddSubgroup = L.g₂ ∧ g3 L.lattice.toAddSubgroup = L.g₃
def MulStep : Prop :=
  ∀ w₁ w₂ : ℂ, ((starRingEnd ℂ) w₁ * w₂).im ≠ 0 →
    ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
      g2 (lat2 w₁ w₂) ∈ M → g3 (lat2 w₁ w₂) ∈ M →
      ∀ c : ℂ, (∀ t ∈ lat2 w₁ w₂, c * t ∈ lat2 w₁ w₂) → c ∈ M → cj M ρ c = c →
        ∀ t t', StarPt M ρ (lat2 w₁ w₂) t t' → StarPt M ρ (lat2 w₁ w₂) (c * t) (c * t')
end PI.GalTorsConj.W
end


