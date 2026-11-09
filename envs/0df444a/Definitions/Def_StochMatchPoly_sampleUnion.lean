-- Prove2me | Definitions.Def_StochMatchPoly_sampleUnion
-- name    : StochMatchPoly_sampleUnion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:20:45.898208+00:00
-- url     : https://prove2.me/theorems/0c50f12e-f5a6-4639-be5b-e6c277c1e4dd
-- title:
--   Algorithm 1 (Sample-and-Union): maximum-matching rules and the output subgraph
-- statement:
--   Let $G=(V,E)$ be a finite graph. A **maximum-matching rule** for $G$ is a fixed map $\mathrm{MM}$ that assigns to every subgraph $F\subseteq E$ a maximum matching of $F$: a matching $\mathrm{MM}(F)\subseteq F$ with $|\mathrm{MM}(F)|=\mu(F)$.
--
--   **Algorithm 1 (Sample-and-Union).** Given $G$, a survival probability $p$ and a number of samples $R$: draw independent samples $G^{(1)},\dots,G^{(R)}\sim G_p$, let $M_i=\mathrm{MM}(G^{(i)})$, and output the subgraph $H$ on the vertex set $V$ with edge set
--
--   $$E(H)=M_1\cup M_2\cup\dots\cup M_R .$$
--
--   Given the samples, the output is deterministic; its randomness is that of the samples.
--
--   **Formalization Note** `sampleUnion MM S` is the edge set of $H$ for samples `S : Fin R → Finset (Sym2 V)`; the independent sampling is put in by the expectation `sampleExpect` of the edge-law module.
-- source:
--   S. Behnezhad, Stochastic Matching with Polynomial Degree, arXiv:2611.03367 (preprint, held version, sha256 409beb43bd8ab862a4a4a595be9c08afd92590790382102cb640d81d9b564017), Algorithm 1, p.9 (PDF p.10); §2 p.2 (PDF p.3); §4.1 p.9

import Mathlib
import Definitions.Def_StochMatchPoly_mu

open Classical

namespace StochMatchPoly

/-! # Algorithm 1 (Sample-and-Union)

S. Behnezhad, *Stochastic Matching with Polynomial Degree*, arXiv:2611.03367 (held version,
sha256 409beb43…), Algorithm 1, p.9 (PDF p.10); §2 p.2 ("Fix a deterministic maximum matching
algorithm MM(·)"); §4.1 p.9 ("MM(K) for the matching chosen by the fixed rule").

"Input: Graph G = (V, E), survival probability p, number of samples R. Output: A subgraph H ⊆ G
with maximum degree at most R. 1 H ← (V, ∅). 2 for i = 1, …, R do 3 Sample G(i) ∼ Gp
independently. 4 Let Mi = MM(G(i)) be a maximum matching of G(i). 5 E(H) ← E(H) ∪ Mi.
6 return H."

**Formalization Note.** A maximum-matching rule on the subgraphs of the graph with edge set `E`
is a function `MM` that sends every `F ⊆ E` to a matching `MM F ⊆ F` of cardinality `µ(F)`.
Algorithm 1 is deterministic given the samples: on samples `S : Fin R → Finset (Sym2 V)` its
output `H` is the vertex set `V` with edge set `⋃_i MM(S i)`, which is `sampleUnion MM S`. The
randomness of the samples is put in by `sampleExpect` (independent copies of the edge law). -/

variable {V : Type*}

/-- `MM` is a maximum-matching rule for the subgraphs of the graph with edge set `E`: for every
`F ⊆ E`, `MM F` is a matching contained in `F` of maximum cardinality `µ(F)`. -/
def IsMaxMatchingRule (E : Finset (Sym2 V)) (MM : Finset (Sym2 V) → Finset (Sym2 V)) : Prop :=
  ∀ F ⊆ E, MM F ⊆ F ∧ IsMatchingSet (MM F) ∧ (MM F).card = mu F

/-- The edge set of the output `H` of Algorithm 1 on samples `S 0, …, S (R − 1)`:
`E(H) = MM(S 0) ∪ ⋯ ∪ MM(S (R − 1))`. -/
noncomputable def sampleUnion {R : ℕ} (MM : Finset (Sym2 V) → Finset (Sym2 V))
    (S : Fin R → Finset (Sym2 V)) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i => MM (S i)

end StochMatchPoly


