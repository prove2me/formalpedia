-- Prove2me | Definitions.Def_VDCyclePack_sampleProb
-- name    : VDCyclePack_sampleProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:18.426421+00:00
-- url     : https://prove2.me/theorems/b6c71bcb-e64c-4807-b0c2-d9b0877ce68c
-- title:
--   Probability of a sample $Q\subseteq R$ under independent inclusion with probability $x_C/2$
-- statement:
--   Let $R$ be a finite family of cycles with weights $x$, and let $Q$ be obtained by including each $C\in R$ independently with probability $x_C/2$. For $Q\subseteq R$,
--   $$
--   \Pr[\text{sample}=Q]=\prod_{C\in Q}\frac{x_C}{2}\ \prod_{C\in R\setminus Q}\Bigl(1-\frac{x_C}{2}\Bigr).
--   $$
--
--   **Formalization Note** The product law on the subsets of $R$; Lemma 5.1 depends only on this law.
-- source:
--   Kundu–Lochet, Nearly Tight Approximation for Vertex-Disjoint Cycle Packing (STOC 2027 submission manuscript, preprint basis, sha256 95f2e61a…cacb1), Lemma 5.1, p.15

import Mathlib

namespace VDCyclePack

open Classical in
/-- **Probability of a sample Q ⊆ R under independent inclusion with probability x_C/2.**
Kundu–Lochet, *Nearly Tight Approximation for Vertex-Disjoint Cycle Packing* (STOC 2027
submission manuscript), Lemma 5.1, p.15: "let Q be obtained by including each C ∈ R independently with
probability x_C/2."

For `Q ⊆ R`, `sampleProb R x Q = Π_{C∈Q} (x C / 2) · Π_{C∈R∖Q} (1 − x C / 2)`, the probability that
the random subfamily equals `Q`.

**Formalization Note.** The sampling law is the product law on the subsets of `R`; Lemma 5.1's
claim depends only on this law. -/
noncomputable def sampleProb {V : Type*} {G : SimpleGraph V} (R : Finset G.Subgraph)
    (x : G.Subgraph → ℝ) (Q : Finset G.Subgraph) : ℝ :=
  (∏ C ∈ Q, x C / 2) * ∏ C ∈ R \ Q, (1 - x C / 2)

end VDCyclePack


