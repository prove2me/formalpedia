-- Prove2me | Definitions.Def_HypClass1_randSubProb
-- name    : HypClass1_randSubProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:17:42.805795+00:00
-- url     : https://prove2.me/theorems/abbadc53-a84e-4baf-bf81-b58bccff99b2
-- title:
--   Random inhomogeneous subset $G_\varphi$
-- statement:
--   Let $G$ be a finite set and $\varphi : G \to [0,1]$ a weight function. The **random inhomogeneous subset** $G_\varphi$ contains each $e \in G$ independently with probability $\varphi(e)$. For a property $E$ of subsets of $G$,
--   $$
--   \mathbb P[E(G_\varphi)] = \sum_{A \subseteq G} [E(A)] \prod_{e \in A} \varphi(e) \prod_{e \in G \setminus A} (1 - \varphi(e)).
--   $$
--   With constant weight $q$ this is the random homogeneous subgraph $H_q$ of a 3-graph $H$; with $G = K^{(3)}_n$ and weight $p$ it is the binomial random 3-graph; on $2^X$ it is the product measure $\mu_p$ of §8.4.
--
--   **Formalization Note** The law of independent coins is written as this finite sum; it is a probability when $0 \le \varphi \le 1$. Events are arbitrary propositions.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §4 p.9 (B_φ), p.10 (H_q), Definition 5.1 (C3) p.12, §8.4 p.42 (µ_p)

import Mathlib

namespace HypClass1

open Classical in
/-- **Random inhomogeneous subset** `G_φ`: each element `e` of the finite ground set `G` is kept
independently with probability `φ(e)`; `randSubProb G φ E` is the probability that the random subset
has property `E`. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), §4 p.9 (`B_φ`: "each edge is chosen independently with probability
P({x, y} ∈ B_φ) = φ(x, y)"), p.10 (the random homogeneous 3-graph `H_q`, `φ ≡ q`), Definition 5.1 (C3)
p.12, and §8.4 p.42 (the product measure `µ_p` on `2^X`).

`P[E(G_φ)] = Σ_{A ⊆ G} [E(A)] · Π_{e ∈ A} φ(e) · Π_{e ∈ G∖A} (1 − φ(e))`.

**Formalization Note.** The law of independent coins on the finite set `G` is written as this finite
sum over subsets; it is a probability whenever `0 ≤ φ ≤ 1` on `G` (the sum over all events is
`Π_{e∈G}(φ e + 1 − φ e) = 1`). Events are arbitrary propositions (classical decidability). -/
noncomputable def randSubProb {α : Type*} [DecidableEq α] (G : Finset α) (φ : α → ℝ)
    (E : Finset α → Prop) : ℝ :=
  ∑ A ∈ G.powerset, if E A then (∏ e ∈ A, φ e) * ∏ e ∈ G \ A, (1 - φ e) else 0

end HypClass1


