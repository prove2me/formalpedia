-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_PiSumForallInsertOnly
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:44.739472+00:00
-- url     : https://prove2.me/theorems/ed8659f6-6d2f-47ef-9fea-f9b79963be38
-- title:
--   Pi Sum Forall Insert Only
-- statement:
--   Definitions and structural lemmas for Pi Sum Forall Insert Only, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/PiSumForallInsertOnly.lean

import Definitions.Def_Formalism_HarderNarasimhan_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SatBasic
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermod
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_PolygonSlopeSum
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_DiscreteTopologyOfLe
import Definitions.Def_Formalism_LatticeSlopes_LatticeSlopesProofs_ShortVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Submodule
noncomputable section
namespace Formalism.HN
section
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
def piSum_emb (E : ι → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (i : ι) : E i →ₗ[ℝ] PiLp 2 E :=
  (WithLp.linearEquiv 2 ℝ (∀ j, E j)).symm.toLinearMap.comp (LinearMap.single ℝ E i)
variable (ρ : ∀ i, V i →+ E i)
variable [∀ i, FiniteDimensional ℝ (E i)]
def piSumS (L : ∀ i, Submodule R (V i)) (i : ι) : Submodule R (∀ i, V i) :=
  (L i).map (LinearMap.single R V i)
def piSumT (L : ∀ i, Submodule R (V i)) (s : Finset ι) : Submodule R (∀ i, V i) :=
  ⨆ i ∈ s, piSumS L i
end
section
variable {R : Type*} [Ring R] {ι : Type*} [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)]
end
section
variable {R : Type*} [Ring R] {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
  [∀ i, AddCommGroup (V i)] [∀ i, Module R (V i)] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
end
end Formalism.HN
namespace Formalism.HN
universe uR uι uV uE uS
end Formalism.HN


