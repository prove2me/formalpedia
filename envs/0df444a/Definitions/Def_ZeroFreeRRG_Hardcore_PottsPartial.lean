-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_PottsPartial
-- name    : ZeroFreeRRG_Hardcore_PottsPartial
-- status  : Definition
-- author  : @wcysai
-- created : 2026-11-13T08:43:23.098194+00:00
-- url     : https://prove2.me/theorems/c5285a9c-08ca-4830-bb21-4bf9a84cb92b
-- title:
--   Potts partition sum with fixed vertex colors
-- statement:
--   For a finite graph and a prescribed partial coloring on $S$, this is the sum of $\beta^{m(\sigma)}$ over all full colorings extending that prescription.
-- source:
--   Auxiliary definition for Chen–Wang–Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/1461.pdf, Lemma 5.7.

import Definitions.Def_ZeroFreeRRG_Hardcore_Models
import Mathlib
open scoped Classical BigOperators
namespace ZeroFreeRRG.Hardcore

/-- Potts partition sum restricted to colorings matching an assignment on a finite set. -/
noncomputable def pottsPartialZ {V : Type} [Fintype V] (q : ℕ) (G : SimpleGraph V)
    (β : ℂ) (S : Finset V) (τ : V → Fin q) : ℂ :=
  ∑ σ : V → Fin q, if ∀ v ∈ S, σ v = τ v then β ^ monoEdges G σ else 0

end ZeroFreeRRG.Hardcore


