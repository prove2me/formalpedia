-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IndexEmbeddingBijective
-- name    : ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_IndexEmbeddingBijective
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T15:56:32.948982+00:00
-- url     : https://prove2.me/theorems/1bec38a6-dc4b-4a54-b68a-273e1d536ef6
-- title:
--   Index Embedding Bijective
-- statement:
--   Definitions and structural lemmas for Index Embedding Bijective, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/DiscreteSeries/TailIntegrals/IndexEmbeddingBijective.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TailIntegrals_DelFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped ComplexConjugate
namespace ReciprocityTheory.ChartRestriction.DS.Xi
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2
namespace FormulaFAux
def rotF (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ :=
  Function.update (Function.update y (wI k r' 0) (cc * (y (wI k r' 0) - y (wI k r' (Fin.last k)))))
    (wI k r' (Fin.last k)) (cc * (y (wI k r' 0) + y (wI k r' (Fin.last k))))
def ix2 (k r' : ℕ) : Fin (1 + r') ⊕ (Fin (1 + r') ⊕ Fin (k - 1)) → Fin (2 * r' + k + 1)
  | Sum.inl t => ⟨t.val, by omega⟩
  | Sum.inr (Sum.inl t) => ⟨2 * r' + k - t.val, by omega⟩
  | Sum.inr (Sum.inr i) => ⟨r' + i.val + 1, by omega⟩
def permF (k r' : ℕ) (z : Fin (2 * r' + k + 1) → ℂ) : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ) :=
  (fun j => z (ix2 k r' (Sum.inl j)), fun j => z (ix2 k r' (Sum.inr (Sum.inl j))),
    fun i => z (ix2 k r' (Sum.inr (Sum.inr i))))
def imF (k r' : ℕ) (q : (Fin (1 + r') → ℂ) × (Fin (1 + r') → ℂ) × (Fin (k - 1) → ℂ)) : ℝ :=
  (∑ j, q.2.1 j * star (q.1 j)).im
end FormulaFAux
end ReciprocityTheory.ChartRestriction.DS.Xi


