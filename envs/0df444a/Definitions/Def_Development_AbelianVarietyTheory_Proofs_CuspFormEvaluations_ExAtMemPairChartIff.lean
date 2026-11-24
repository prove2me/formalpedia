-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExAtMemPairChartIff
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T16:12:19.149656+00:00
-- url     : https://prove2.me/theorems/9fab2ea6-7445-44a7-8ae9-c9f217ac0583
-- title:
--   Ex At Mem Pair Chart Iff
-- statement:
--   Definitions and structural lemmas for Ex At Mem Pair Chart Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExAtMemPairChartIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Theorems.Thm_GlobalTheory_CubeValues_ex_zero
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_add_period

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
section Fibre
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
def IsPullConst {m : T ⊗ A ⟶ A} (Φ : (Fin g → ℂ) → Fin g → ℂ) (a b : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -b])) (c : ℂ) : Prop :=
  ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L ![(snd T A).left, m.left] j →
    valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, m.left] j) (α.s j).val *
      u.fr (j 1) (Φ z) ^ b = c * u.fr (j 0) z ^ a
variable {u p}
theorem map_mem_period {m : T ⊗ A ⟶ A} {Φ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hΦ : ∀ z, exAt u p z ≫ m.left = (u.ex (Φ z)).left) {l : Fin g → ℂ} (hl : l ∈ u.Λ) :
    Φ l ∈ u.Λ := by
  have h := hΦ (0 + l)
  rw [exAt_add_period u p 0 l hl, hΦ, map_zero, zero_add, ex_zero] at h
  exact (u.ker _).1 (Over.OverMorphism.ext h.symm)
end Fibre
end GlobalTheory.ThetaFn


