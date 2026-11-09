-- Prove2me | Definitions.Def_HypClass1_IsPseudorandomBip
-- name    : HypClass1_IsPseudorandomBip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:17:46.326096+00:00
-- url     : https://prove2.me/theorems/be8a5833-b5ab-487e-801c-6be737c1bff4
-- title:
--   $(\varepsilon,p,n)$-pseudorandom bipartite graph
-- statement:
--   Let $\varepsilon, p \in [0,1]$ and let $B$ be a bipartite graph with parts $X, Y$, $|X| = |Y| = n$; write $e_B(S,T)$ for the number of edges between $S \subseteq X$ and $T \subseteq Y$. $B$ is **$(\varepsilon, p, n)$-pseudorandom** if:
--   1. (A1) every vertex $z \in X \cup Y$ has $\deg_B(z) = (1\pm\varepsilon)pn$;
--   2. (A2) for $S \subseteq X$, $T \subseteq Y$ with $|S|, |T| \ge \varepsilon n$, $e_B(S,T) = (1\pm\varepsilon)p|S||T|$;
--   3. (A3) if $|S| < \varepsilon n$ and $|T| = 2|S|$, then $e_B(S,T) \le 4\varepsilon pn|S|$;
--   4. (A4) if $|T| < \varepsilon n$ and $|S| = 2|T|$, then $e_B(S,T) \le 4\varepsilon pn|T|$.
--
--   These are the graphs on which the randomized 1-factorization algorithm of §6 runs.
--
--   **Formalization Note** A bipartite graph with parts $X \subseteq \alpha$, $Y \subseteq \beta$ is a set of pairs $B \subseteq X \times Y$; the definition includes $B \subseteq X \times Y$ and $|X| = |Y|$, with $n = |X|$. The module also defines the part degrees and $e_B(S,T)$.
-- source:
--   Chatterjee, Ferber, Sales, Shurman, Almost Every 3-Uniform Hypergraph is Class 1, manuscript (STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), Definition 4.1, p.9

import Mathlib

namespace HypClass1

/-- Degree `deg_B(x)` of a vertex `x` of the first part of a bipartite graph `B ⊆ X × Y`. -/
def ldeg {α β : Type*} [DecidableEq α] (B : Finset (α × β)) (x : α) : ℕ :=
  (B.filter (fun e => e.1 = x)).card

/-- Degree `deg_B(y)` of a vertex `y` of the second part of a bipartite graph `B ⊆ X × Y`. -/
def rdeg {α β : Type*} [DecidableEq β] (B : Finset (α × β)) (y : β) : ℕ :=
  (B.filter (fun e => e.2 = y)).card

/-- `e_B(S, T)`: the number of edges of `B` between `S ⊆ X` and `T ⊆ Y`. -/
def eB {α β : Type*} [DecidableEq α] [DecidableEq β] (B : Finset (α × β)) (S : Finset α)
    (T : Finset β) : ℕ :=
  (B.filter (fun e => e.1 ∈ S ∧ e.2 ∈ T)).card

/-- **(ε, p, n)-pseudorandom bipartite graph**, Definition 4.1. Chatterjee, Ferber, Sales, Shurman, *Almost Every 3-Uniform Hypergraph is Class 1*, manuscript
(STOC 2027 submission, version of 2026-11-03, sha256 ce3bba9d…), p.9:
"Let ε, p ∈ [0, 1] and let B be a bipartite graph with parts X, Y with |X| = |Y| = n. We say that B
is (ε, p, n)-pseudorandom if the following hold:
(A1) For every z ∈ V(B), we have deg_B(z) = (1 ± ε)pn;
(A2) For every S ⊆ X, T ⊆ Y such that |S|, |T| ≥ εn, it holds e_B(S, T) = (1 ± ε)p|S||T|;
(A3) For every S ⊆ X, T ⊆ Y such that |S| < εn and |T| = 2|S|, it holds e_B(S, T) ≤ 4εpn|S|;
(A4) For every S ⊆ X, T ⊆ Y such that |T| < εn and |S| = 2|T|, it holds e_B(S, T) ≤ 4εpn|T|."

**Formalization Note.** A bipartite graph with parts `X ⊆ α`, `Y ⊆ β` is a set of pairs
`B ⊆ X × Y`; the first two clauses say `B` has these parts and `|X| = |Y|`, and `n = |X|`.
`V(B) = X ∪ Y`, so (A1) bounds the degree of every vertex of both parts. `x = (1 ± ε)y` means
`(1 − ε)y ≤ x ≤ (1 + ε)y`. -/
def IsPseudorandomBip {α β : Type*} [DecidableEq α] [DecidableEq β] (ε p : ℝ) (X : Finset α)
    (Y : Finset β) (B : Finset (α × β)) : Prop :=
  B ⊆ X ×ˢ Y ∧ X.card = Y.card ∧
  (∀ x ∈ X, (1 - ε) * p * X.card ≤ ldeg B x ∧ (ldeg B x : ℝ) ≤ (1 + ε) * p * X.card) ∧
  (∀ y ∈ Y, (1 - ε) * p * X.card ≤ rdeg B y ∧ (rdeg B y : ℝ) ≤ (1 + ε) * p * X.card) ∧
  (∀ S ⊆ X, ∀ T ⊆ Y, ε * X.card ≤ S.card → ε * X.card ≤ T.card →
      (1 - ε) * p * S.card * T.card ≤ eB B S T ∧
        (eB B S T : ℝ) ≤ (1 + ε) * p * S.card * T.card) ∧
  (∀ S ⊆ X, ∀ T ⊆ Y, (S.card : ℝ) < ε * X.card → T.card = 2 * S.card →
      (eB B S T : ℝ) ≤ 4 * ε * p * X.card * S.card) ∧
  (∀ S ⊆ X, ∀ T ⊆ Y, (T.card : ℝ) < ε * X.card → S.card = 2 * T.card →
      (eB B S T : ℝ) ≤ 4 * ε * p * X.card * T.card)

end HypClass1


