-- Prove2me | Definitions.Def_PelagicFF_rademacherLaw
-- name    : PelagicFF_rademacherLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:54:47.553197+00:00
-- url     : https://prove2.me/theorems/28d075eb-becd-4c06-b1a7-403e40ca3760
-- title:
--   Law of a normalized sum of $s$ independent uniform signs
-- statement:
--   For $s\in\mathbb N$, the law on $\mathbb R$ of
--   $$s^{-1/2}\sum_{i=1}^s\xi_i,\qquad \xi_1,\dots,\xi_s\in\{-1,1\}\ \text{independent and uniform}.$$
--
--   This is the law of the term $S$ in Lemma 3.6 and Lemma 4.3.
--
--   **Formalization Note** The pushforward of the uniform law on `Fin s → Bool` under $\xi\mapsto(\sum_i\mathrm{sign}\,\xi_i)/\sqrt s$.
-- source:
--   Anselm, Ding, Gilboa, Grewal, Optimal and Verifiable Quantum Advantages in Communication Complexity, arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.6, p.23; Lemma 4.3, p.28

import Mathlib
import Definitions.Def_Cotype

open OAI.Cotype MeasureTheory

namespace PelagicFF

/-- The law on `ℝ` of `s^{−1/2} ∑_{i=1}^s ξᵢ` for independent uniform signs `ξᵢ ∈ {−1,1}`: the
pushforward of the uniform law on `{−1,1}^s` (encoded as `Fin s → Bool`) under
`ξ ↦ (∑ᵢ sign ξᵢ)/√s`.

arXiv:2610.05585 (held version, sha256 4564aef3…), Lemma 3.6, p.23 and Lemma 4.3, p.28 ("S is
distributed as N^{−1/2} ∑_{i=1}^N ξᵢ for independent uniform signs ξᵢ ∈ {−1,1}"). -/
noncomputable def rademacherLaw (s : ℕ) : Measure ℝ :=
  (PMF.uniformOfFintype (Fin s → Bool)).toMeasure.map
    (fun ξ => (∑ i, sign (ξ i)) / Real.sqrt s)

end PelagicFF


