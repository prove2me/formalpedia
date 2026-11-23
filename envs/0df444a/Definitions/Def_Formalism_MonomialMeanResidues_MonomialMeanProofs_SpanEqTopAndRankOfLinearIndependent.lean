-- Prove2me | Definitions.Def_Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- name    : Formalism_MonomialMeanResidues_MonomialMeanProofs_SpanEqTopAndRankOfLinearIndependent
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:40:56.776283+00:00
-- url     : https://prove2.me/theorems/3a1fca98-0426-469a-a0eb-2cef9b4477d9
-- title:
--   Span Eq Top And Rank Of Linear Independent
-- statement:
--   Definitions and structural lemmas for Span Eq Top And Rank Of Linear Independent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/MonomialMeanProofs/SpanEqTopAndRankOfLinearIndependent.lean

import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
namespace Formalism.HermiteSiegelSlopes
open Formalism.HN
section GammaDefs
variable {K : Type} [Field K] [NumberField K]
def stepLat {n δ : ℕ} (w : Fin n → Fin δ → K) (Λ : Submodule (𝓞 K) (Fin δ → K)) :
    Submodule (𝓞 K) (Fin δ → K) :=
  ⨆ k, Λ.map (LinearMap.mulLeft (𝓞 K) (w k))
def ptLat {n δ : ℕ} (w : Fin n → Fin δ → K) (y : Fin δ) : Submodule (𝓞 K) (Fin 1 → K) :=
  Submodule.span (𝓞 K) (Set.range fun k => (fun _ : Fin 1 => w k y))
end GammaDefs
section BCDefs
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
def bcMap (x : ι → F) : ι → E := fun i => algebraMap F E (x i)
def bcLat (M : Submodule (𝓞 F) (ι → F)) : Submodule (𝓞 E) (ι → E) :=
  Submodule.span (𝓞 E) ((bcMap (E := E)) '' (M : Set (ι → F)))
end BCDefs
open scoped nonZeroDivisors
open IsDedekindDomain
section W1
variable {K : Type} [Field K] [NumberField K]
def w1I {n δ : ℕ} (w : Fin n → Fin δ → K) (y : Fin δ) : FractionalIdeal (𝓞 K)⁰ K :=
  FractionalIdeal.spanFinset (𝓞 K) Finset.univ (fun k => w k y)
end W1
section W2a
variable {K : Type} [Field K] [NumberField K]
end W2a
section PullbackHopfOrder
variable {K : Type} [Field K] [NumberField K] [StarRing K]
end PullbackHopfOrder
section W3
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end W3
section W3b
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
section Maj
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
end Maj
variable [StarRing F] [StarRing E]
end W3b
section W4gen
variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
end W4gen
section W4
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end W4
section W4scale
variable {K ι : Type} [Field K] [NumberField K] [Fintype ι]
end W4scale
section W4final
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Fintype ι] [DecidableEq ι]
end W4final
section W5
variable {F E ι : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end W5
end Formalism.HermiteSiegelSlopes


