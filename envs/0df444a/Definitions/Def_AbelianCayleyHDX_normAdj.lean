-- Prove2me | Definitions.Def_AbelianCayleyHDX_normAdj
-- name    : AbelianCayleyHDX_normAdj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:25:39.808995+00:00
-- url     : https://prove2.me/theorems/1e73d6bb-d228-498c-8b1f-3b29bc18eaaf
-- title:
--   Normalized adjacency operator $P_S$ of $\mathrm{Cay}(\mathbb F_2^n,S)$
-- statement:
--   For a finite $S \subseteq \mathbb F_2^n$, the **normalized adjacency operator** of $\mathrm{Cay}(\mathbb F_2^n, S)$ acts on real functions by
--   $$(P_S f)(x) = \frac{1}{|S|} \sum_{s \in S} f(x + s).$$
--   It is the random-walk operator of the Cayley graph.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.1, p.9

import Mathlib
import Definitions.Def_ReplParity_Vec
open ReplParity (Vec)

namespace AbelianCayleyHDX

/-- **The normalized adjacency operator `P_S` of `Cay(𝔽₂ⁿ, S)`** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Lemma 2.1, p.9):
`(P_S f)(x) = (1/|S|) ∑_{s ∈ S} f(x + s)` for `f : 𝔽₂ⁿ → ℝ`. -/
noncomputable def normAdj {n : ℕ} (S : Finset (Vec n)) (f : Vec n → ℝ) (x : Vec n) : ℝ :=
  (1 / (S.card : ℝ)) * ∑ s ∈ S, f (x + s)

end AbelianCayleyHDX


