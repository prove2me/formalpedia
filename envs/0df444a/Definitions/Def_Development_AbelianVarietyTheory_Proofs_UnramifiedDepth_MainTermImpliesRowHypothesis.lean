-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
-- name    : Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MainTermImpliesRowHypothesis
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:14:31.144982+00:00
-- url     : https://prove2.me/theorems/d65053ac-6599-46be-811b-2b54f902bdd6
-- title:
--   Main Term Implies Row Hypothesis
-- statement:
--   Definitions and structural lemmas for Main Term Implies Row Hypothesis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MainTermImpliesRowHypothesis.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds
noncomputable section
open scoped BigOperators
open Classical MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
namespace GlobalTheory.MainToRows
variable {C : Type} [Field C]
def eps {n0 n : ℕ} (hn : n0 ≤ n) : Fin n0 ⊕ Fin n0 ↪ Fin n0 ⊕ Fin n :=
  Function.Embedding.sumMap (Function.Embedding.refl _) (Fin.castLEEmb hn)
def rowE {n0 : ℕ} (ρ : Fin n0) : Fin n0 ⊕ Fin n0 ↪ PVar n0 :=
  Function.Embedding.sumMap (Function.Embedding.sectR ρ (Fin n0)) (Function.Embedding.sectR ρ (Fin n0))
end GlobalTheory.MainToRows


