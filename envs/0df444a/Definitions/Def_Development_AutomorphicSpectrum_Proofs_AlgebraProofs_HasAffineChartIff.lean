-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
-- name    : Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:41:46.303542+00:00
-- url     : https://prove2.me/theorems/95a206c1-8ec6-4c08-9025-232e4e861c1e
-- title:
--   Has Affine Chart Iff
-- statement:
--   Definitions and structural lemmas for Has Affine Chart Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/AlgebraProofs/HasAffineChartIff.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Algebra__RegularHypothesesAndConclusion_0659ccbe52365dd5
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_AlgebraProofs_HasAffineChartId
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.FreeQuotProof GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.FreeQuot
namespace GlobalTheory.CompanionTheory.FreeQuotGlue
def IsChart {P X Y : Scheme.{0}} (a b : P ⟶ X) (V : X.Opens) (q : V.toScheme ⟶ Y) : Prop :=
  a ⁻¹ᵁ V = b ⁻¹ᵁ V ∧ IsFinite q ∧ Flat q ∧ LocallyOfFinitePresentation q ∧ Surjective q ∧
    ∃ a' : (b ⁻¹ᵁ V).toScheme ⟶ V.toScheme,
      a' ≫ V.ι = (b ⁻¹ᵁ V).ι ≫ a ∧ IsPullback a' (b ∣_ V) q q
variable {P X Y : Scheme.{0}} {a b : P ⟶ X} {V : X.Opens} {q : V.toScheme ⟶ Y}
end GlobalTheory.CompanionTheory.FreeQuotGlue


