-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_ExistsDensity
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:45:57.941875+00:00
-- url     : https://prove2.me/theorems/4160ae21-5a8d-4e4a-ab4e-c63d6abee326
-- title:
--   Exists Density
-- statement:
--   Definitions and structural lemmas for Exists Density, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/ExistsDensity.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HasStrictFDerivAtExpZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Filter Topology Metric NormedSpace Set
open scoped ENNReal NNReal
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
structure Chart (V : Submodule ℝ 𝔸) (G : Type*) [Group G] [TopologicalSpace G] where
  mat : G →* 𝔸
  emb : IsEmbedding mat
  H1 : ∀ X : V, ∃ g, mat g = exp (X : 𝔸)
  H2 : ∀ᶠ Z in 𝓝 (0 : 𝔸), (∃ g, mat g = exp Z) → Z ∈ V
namespace Chart
variable {V : Submodule ℝ 𝔸} {G : Type*} [Group G] [TopologicalSpace G] (C : Chart V G)
def expG (X : V) : G := (C.H1 X).choose
def img (s : Set V) : Set G := {g | ∃ X ∈ s, C.mat g = exp ((X : V) : 𝔸)}
variable {ρ : ℝ} (hR : ∀ Z : 𝔸, ‖Z‖ < ρ → logA 𝔸 (exp Z) = Z ∧ ((∃ g, C.mat g = exp Z) → Z ∈ V))
variable [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [MeasurableSpace G] [BorelSpace G]
def nu (ρ : ℝ) (μ : Measure G) : Measure V :=
  (μ.comap (fun x : ball (0 : V) ρ => C.expG x.1)).map Subtype.val
variable (μ : Measure G)
variable [IsTopologicalGroup G] [μ.IsHaarMeasure]
end Chart
end Formalism.BasicNotions.Examples₂.CD


