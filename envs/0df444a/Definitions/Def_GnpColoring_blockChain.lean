-- Prove2me | Definitions.Def_GnpColoring_blockChain
-- name    : GnpColoring_blockChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:32.557901+00:00
-- url     : https://prove2.me/theorems/ce13a741-e60b-4ca6-a86e-68dce86b6358
-- title:
--   The exact block dynamics as a chain
-- statement:
--   On proper colourings, pick a singleton $s\in S$ or a block $B\in\mathcal B$ uniformly at random and apply its heat-bath update. This is the jump chain of the continuous-time block dynamics with generator $L$; it has the same possible transitions.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.2, p.15; Lemma 5.9, p.54

import Mathlib
import Definitions.Def_GnpColoring_heatBathMatrix
import Definitions.Def_GnpColoring_blocks
import Definitions.Def_mm_transport

open scoped Classical
open Finset

namespace GnpColoring

/-- **The exact block dynamics** as a chain on proper colourings: pick a singleton `s ∈ S` or a block
`B ∈ 𝓑` uniformly at random and apply its heat-bath update.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.2, p.15 (generator `L = Σ_s L_s + Σ_B L_B`), and Lemma 5.9, p.54 ("its exact block
dynamics are irreducible").

**Formalization Note** This is the jump chain of the continuous-time block dynamics with rate one
per singleton and per block; positive rescaling does not change which transitions have positive
probability, so its irreducibility is that of the block dynamics. -/
noncomputable def blockChain {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (S : Finset (Fin n)) :
    Matrix {c : Fin n → Fin q // MarkovMixing.IsProperColoring G c}
      {c : Fin n → Fin q // MarkovMixing.IsProperColoring G c} ℝ :=
  MarkovMixing.subChain
    (((S.card : ℝ) + ((blocks G S).card : ℝ))⁻¹ •
      (∑ s ∈ S, heatBathMatrix (MarkovMixing.properColoringDist G q) {s} +
        ∑ B ∈ blocks G S, heatBathMatrix (MarkovMixing.properColoringDist G q) B))
    fun c => MarkovMixing.IsProperColoring G c

end GnpColoring


