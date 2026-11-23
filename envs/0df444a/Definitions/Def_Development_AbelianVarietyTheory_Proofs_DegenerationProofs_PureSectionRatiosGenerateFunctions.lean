-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:06:22.520865+00:00
-- url     : https://prove2.me/theorems/2e42b498-c35b-4413-a166-642722203225
-- title:
--   Pure Section Ratios Generate Functions
-- statement:
--   Definitions and structural lemmas for Pure Section Ratios Generate Functions, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
namespace GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
section Alg
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
include hb
end Alg
variable {k : Type} [Field k] (Φ : FibPre k)
def satur {C C' : Type} [CommRing C] [CommRing C'] (σ : C →+* C') (F : C) (R : Subring C) (hF : F ∈ R) :
    Subring C' where
  carrier := {c | ∃ n : ℕ, ∃ r ∈ R, σ F ^ n * c = σ r}
  zero_mem' := ⟨0, 0, R.zero_mem, by simp⟩
  one_mem' := ⟨0, 1, R.one_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨n, r, hr, e⟩ ⟨m, s, hs, e'⟩
    refine ⟨n + m, F ^ m * r + F ^ n * s,
      R.add_mem (R.mul_mem (R.pow_mem hF _) hr) (R.mul_mem (R.pow_mem hF _) hs), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e, ← e']
    ring
  mul_mem' := by
    rintro a b ⟨n, r, hr, e⟩ ⟨m, s, hs, e'⟩
    refine ⟨n + m, r * s, R.mul_mem hr hs, ?_⟩
    rw [map_mul, ← e, ← e']
    ring
  neg_mem' := by
    rintro a ⟨n, r, hr, e⟩
    exact ⟨n, -r, R.neg_mem hr, by rw [map_neg, ← e, mul_neg]⟩
end GlobalTheory.ZH.WtGen
end


