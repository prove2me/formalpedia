-- Prove2me | Definitions.Def_PDSEquiv_Supplement_Advice
-- name    : PDSEquiv_Supplement_Advice
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:50:31.156638+00:00
-- url     : https://prove2.me/theorems/66bb583f-1832-455f-886d-ebc4ccb9db53
-- title:
--   Randomized polynomial-time algorithms with $O(\log N)$ bits of advice, and cliques of a graph
-- statement:
--   An **algorithm with $O(\log N)$ bits of advice** (Remark 8.3) is a single randomized program $A$ together with a fixed integer $h\ge 0$. On an $N$-vertex graph $G$ it also receives a string $\alpha_N\in\{0,1\}^*$ of length at most $h\lceil\log_2 N\rceil$ that depends only on $N$; the sequence $(\alpha_N)$ need not be computable. The program must run in polynomial time for **every** graph, every string of the allowed length and every random choice:
--   $$
--   \exists c\;\forall N\;\forall G\in\mathcal G_N\;\forall s\in\{0,1\}^*,\ |s|\le h\lceil\log_2 N\rceil:\quad A(G,s)\ \text{halts within cost}\ (N+2)^c\ \text{on every random branch},
--   $$
--   and it calls no oracle.
--
--   A set $T$ of vertices is a **clique** of $G$ if every two distinct vertices of $T$ are adjacent in $G$.
--
--   These are the two objects that Theorem 1.3 uses beyond the laws and the machine of the base mission: item (3) of Theorem 1.3 quantifies over advice algorithms, and item (1) asks for a $k$-clique.
--
--   **Formalization Note** The machine is the published `PDSEquiv.Machine` (a randomized log-cost RAM; polynomial time is worst case on every branch, as in `PolyTimeAlg`). The input of a program with advice is the graph encoding `enc G`, then the length of $s$, then the bits of $s$ (as $1$/$0$); the length cell makes $(G,s)$ recoverable from the input. $\lceil\log_2 N\rceil$ is `Nat.clog 2 N`, which is $0$ for $N\le 1$. The advice sequence is not part of the definition; statements quantify over an arbitrary function $\mathbb N\to\{0,1\}^*$ with the length bound.
-- source:
--   Hirahara, Shimizu, Planted Dense Subgraph Conjectures Are Equivalent, STOC 2027 submission (manuscript sha256 f849d438…), Remark 8.3, p.35 (PDF p.37); Theorem 1.3, p.3 (PDF p.5); §1.1, p.3 ("an algorithm with O(log N) bits of advice receives, together with the graph, a string of O(log N) bits that depends only on N")

import Mathlib
import Definitions.Def_PDSEquiv_Laws
import Definitions.Def_PDSEquiv_Machine

set_option autoImplicit false

namespace PDSEquiv.Supplement

open PDSEquiv

noncomputable section

/-!
# Algorithms with `O(log N)` bits of advice, and cliques

S. Hirahara, N. Shimizu, *Planted Dense Subgraph Conjectures Are Equivalent*, STOC 2027 submission
(manuscript sha256 f849d438…), Remark 8.3, p.35 (PDF p.37), and Theorem 1.3, p.3 (PDF p.5).

Remark 8.3: "Such an algorithm receives a string `α_N ∈ {0,1}*` of length at most `h ⌈log₂ N⌉` for a
fixed integer `h ≥ 0`; the string depends only on `N`, and its sequence need not be computable. A single
program must run in polynomial time for every such string, graph, and random choice."

**Formalization Note.** The machine is the published `PDSEquiv.Machine`. A program with advice reads
the input cells `enc G`, then the length of the advice string, then its bits (`1` for `true`, `0` for
`false`); the length cell makes the pair `(G, s)` recoverable from the input, since memory beyond the
input reads `0`. `⌈log₂ N⌉` is `Nat.clog 2 N` (`0` at `N ≤ 1`). The polynomial time bound is the one of
`PolyTimeAlg`, log-cost `(N + 2)^c` on every random branch, now required for every graph and every
string of the allowed length, not only for the advice string actually supplied. The advice sequence
itself is not part of this definition: a statement quantifies over an arbitrary function
`ℕ → List Bool` with the length bound, so it need not be computable.
-/

/-- The input of a program with advice on graph `G` and advice string `s`: `enc G`, then `s.length`,
then the bits of `s`. -/
def adviceInput {N : ℕ} (G : Graph N) (s : List Bool) : List ℕ :=
  enc G ++ (s.length :: s.map fun b => if b then 1 else 0)

/-- A randomized polynomial-time algorithm with advice strings of length at most `h ⌈log₂ N⌉`,
Remark 8.3: it calls no oracle, and there is `c` such that for every `N`, every graph on `[N]` and every
string `s` with `|s| ≤ h ⌈log₂ N⌉`, on every random branch it halts within log-cost `(N + 2)^c`. -/
def PolyTimeAdviceAlg (P : Program) (h : ℕ) : Prop :=
  IsAlgorithm P ∧ ∃ c : ℕ, ∀ (N : ℕ) (G : Graph N) (s : List Bool),
    s.length ≤ h * Nat.clog 2 N → HaltsWithin P noOracle (adviceInput G s) ((N + 2) ^ c) 0

/-- `T` is a clique of `G`: every two distinct vertices of `T` are adjacent in `G`. -/
def IsCliqueSet {N : ℕ} (G : Graph N) (T : Finset (Fin N)) : Prop :=
  ∀ u ∈ T, ∀ v ∈ T, u ≠ v → gAdj G u v = true

end

end PDSEquiv.Supplement


