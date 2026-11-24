-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
-- name    : Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T15:21:20.466793+00:00
-- url     : https://prove2.me/theorems/b14c467c-50a1-4665-95e0-a75b6369fc9e
-- title:
--   Has An Const Theta Grp Zero Iff
-- statement:
--   Definitions and structural lemmas for Has An Const Theta Grp Zero Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/HasAnConstThetaGrpZeroIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
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
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
def fockFactor (Hm : Matrix (Fin g) (Fin g) ℂ) (k : ℤ) (x z : Fin g → ℂ) : ℂ :=
  Complex.exp (-(k * Real.pi * hermForm Hm z x) - k * Real.pi * hermForm Hm x x / 2)
def HasAnConst (Hm : Matrix (Fin g) (Fin g) ℂ) {k : ℤ} (Θ : ThetaGrp A L k T) (x : Fin g → ℂ)
    (c : ℂ) : Prop :=
  p ≫ Θ.pt = u.ex x ∧
    ∀ (j : Fin 2 → L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U (j 0) →
      ⊤ ≤ (u.ex (z + x)).left ⁻¹ᵁ L.U (j 1) →
      valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] j) (Θ.φ.s j).val *
        u.fr (j 1) (z + x) ^ k = c * fockFactor Hm k x z * u.fr (j 0) z ^ k
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
variable (L) in

def thetaGrpZero (y : T ⟶ A) : ThetaGrp A L 0 T where
  pt := y
  φ := ⟨fun _ => 1⟩
  isGen j j' := by
    have : (thetaLB A L 0 y).g j j' = 1 := by
      unfold thetaLB LB.LinComb
      dsimp only
      exact Finset.prod_eq_one fun i _ => by fin_cases i <;> exact zpow_zero _
    rw [this, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm
end GlobalTheory.ThetaFn


