-- Prove2me | Definitions.Def_AtomicDynFlow_IDNE_Selection
-- name    : AtomicDynFlow_IDNE_Selection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:27.749437+00:00
-- url     : https://prove2.me/theorems/0a1cf6b4-7bf5-4636-9a39-6e00946aa38b
-- title:
--   §4.1, p. 14; EC.2, pp. ec3–ec5 — ideal arrival times, the pruning (S1)–(S3), special prefixes and special sequences
-- statement:
--   These are the objects of the constructive proof of Theorem 1 (§4.1, p. 14; Algorithm 2, p. ec5).
--
--   **Restricted and combined profiles.** For a path profile $q$ and a set $S$ of agents, $q_S$ lets the agents of $S$ take their $q$-paths and removes every other agent. For an ordered list $L=((a_1,P_1),\dots,(a_m,P_m))$, its profile puts each $a_n$ on $P_n$ and removes everyone else.
--
--   **Ideal arrival time.** Given the agents already identified, on their paths (a partial profile $\varphi$), the ideal arrival time of an unidentified agent $j$ at $v$ is
--   $$\ell^v_j=\min\{t^v_j(\varphi,R_j):R_j\in\mathcal P_j\},$$
--   the earliest time $j$ can reach $v$ when the only other agents in the network are the identified ones; it is $\infty$ if $j$ cannot reach $v$.
--
--   **The pruning (S1)–(S3)** (p. 14). Candidates are the pairs $(j,P_j)$ with $j$ unidentified and $P_j\in\mathcal P_j$. Starting from $u=d$: (S1) keep the candidates whose agent has the earliest ideal arrival time at $u$ and whose path achieves it; (S2) keep those whose incoming edge to $u$ has the highest priority; (S3) if several remain they share their incoming edge $e$ to $u$, so move $u$ to its tail and repeat. If the remaining agents all start at $u$ at the same time (same initial queue, or same inflow $\Delta_{r,u}$), keep the one with the highest initial-queue rank or original rank. The pair left is *selected*.
--
--   **Special prefixes and sequences.** A list of (agent, path) pairs is a *special prefix* if each pair is the selected one given the pairs before it. A *special sequence* is a reindexing $\sigma$ of all agents by an initial segment of $\mathbb N$ together with a path profile $p$ such that each agent $a$ with path $p_a$ is the selected pair given the agents of smaller index on their $p$-paths.
--
--   **Formalization Note.** The pruning is encoded as a pairwise comparison `Before` of two candidates, read backwards from $d$ along their paths: at the current vertex $u$, the earlier arrival time of the pair at $u$ wins, each computed with only the identified agents and that pair's agent present; on a tie, a path starting at $u$ beats any incoming edge (an origin entrant outranks through-traffic, (R3); this is (T2) of p. ec2), otherwise the incoming edge with the higher priority wins; on a shared incoming edge the comparison moves to its tail; two paths starting at $u$ at the same time are compared by position in their common source list. A pair is selected iff it beats every other candidate. Comparing each pair's own arrival time at $u$ replaces the two-part condition of (S1): all candidates still compared share the part of their paths from $u$ to $d$, and a prefix optimal for $j$ up to $u$ can be glued to that common part, so the pairs of minimal arrival time at $u$ are exactly those whose agent has the earliest ideal time and whose path achieves it. Incoming-edge rank is the position in the priority list (0 = highest).
-- source:
--   Cao, Chen, Chen, Wang, Atomic dynamic flow games: adaptive versus nonadaptive agents, accepted manuscript (Operations Research, Oct. 2020; WRAP 143835), p. 14 (PDF 15), §4.1 (ideal arrival time, (S1)–(S3)); pp. ec2–ec5 (PDF 34–37), (T2), EC.2 Algorithm, Algorithm 2

import Mathlib
import Definitions.Def_AtomicDynFlow_IDNE_Model

namespace AtomicDynFlow.IDNE

/-- The partial path profile of an ordered list of (agent, path) pairs: an agent listed takes
the path paired with him (first occurrence), every other agent is absent (`none`). -/
def prefixProfile {E A : Type} [DecidableEq A] : List (A × List E) → A → Option (List E)
  | [], _ => none
  | (b, P) :: L, a => if a = b then some P else prefixProfile L a

/-- `overlay φ ψ`: the agents of `φ` take their `φ`-paths, the others follow `ψ`. -/
def overlay {E A : Type} (φ ψ : A → Option (List E)) : A → Option (List E) :=
  fun b => match φ b with
    | some P => some P
    | none => ψ b

/-- `restrictTo q S = q_S`: the agents of `S` take their `q`-paths, every other agent is absent. -/
noncomputable def restrictTo {E A : Type} (q : A → List E) (S : Set A) : A → Option (List E) :=
  fun b => by classical exact if b ∈ S then some (q b) else none

namespace Instance

variable {V E A : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [DecidableEq A]
variable (G : Instance V E A)

/-- The ideal arrival time `ℓ^v_j` (p. 14; p. ec4): the earliest time agent `j` can reach `v`
when the only other agents in the network are those of `φ` on their `φ`-paths; `⊤` if `j` cannot
reach `v`. -/
noncomputable def ideal (φ : A → Option (List E)) (j : A) (v : V) : ℕ∞ :=
  ⨅ (R : List E) (_ : G.IsStrategy j R), G.arrival (Function.update φ j (some R)) j v

/-- Position of the edge `e` in the priority list of its head: `0` is the highest priority. -/
def incRank (e : E) : ℕ := (G.inc (G.head e)).idxOf e

/-- `Before φ j P i Q u rp rq`: the candidate pair `(j, P)` survives the pruning (S1)–(S3) of
p. 14 against `(i, Q)` from the vertex `u` backwards, where `rp`, `rq` are the reversed parts of
`P`, `Q` before `u` (both paths share their parts from `u` to `d`). At `u`:
* (S1) the earlier arrival at `u` wins, each pair's time being computed with only the agents of
  `φ` and that pair's agent present;
* (S2) on a tie, the pair whose path starts at `u` wins (an origin entrant ranks above every
  incoming edge, (R3) and (T2) p. ec2), otherwise the higher-priority incoming edge to `u` wins;
* (S3) if both use the same incoming edge `e`, move to `tail e`;
* if both paths start at `u` at the same time (same initial queue, or same inflow `Δ_{r,u}`),
  the agent with the higher initial-queue rank or original rank wins. -/
def Before (φ : A → Option (List E)) (j : A) (P : List E) (i : A) (Q : List E) :
    V → List E → List E → Prop
  | u, rp, rq =>
    G.arrival (Function.update φ j (some P)) j u < G.arrival (Function.update φ i (some Q)) i u ∨
    (G.arrival (Function.update φ j (some P)) j u = G.arrival (Function.update φ i (some Q)) i u ∧
      match rp, rq with
      | [], [] => ∃ s, List.Sublist [j, i] (srcList G.Q0 G.inflow s)
      | [], _ :: _ => True
      | _ :: _, [] => False
      | e :: rp', e' :: rq' =>
          G.incRank e < G.incRank e' ∨ (e = e' ∧ Before φ j P i Q (G.tail e) rp' rq'))

/-- `IsSelected φ j P`: given the agents already identified (present in `φ` on their dominant
paths), the pair `(j, P)` is the one left by the pruning (S1)–(S3) of §4.1, p. 14: `j` is not yet
identified, `P ∈ 𝒫_j`, and `(j, P)` beats every other candidate pair `(i, Q)` (`i` not
identified, `Q ∈ 𝒫_i`) when compared backwards from `d`. -/
def IsSelected (φ : A → Option (List E)) (j : A) (P : List E) : Prop :=
  φ j = none ∧ G.IsStrategy j P ∧
  ∀ (i : A) (Q : List E), φ i = none → G.IsStrategy i Q → (i, Q) ≠ (j, P) →
    G.Before φ j P i Q G.d P.reverse Q.reverse

/-- A special prefix: a list of (agent, dominant path) pairs in which each pair is the one
selected given the pairs before it (the first `k` iterations of the construction of p. 14). -/
def IsSpecialPrefix (L : List (A × List E)) : Prop :=
  ∀ (n : ℕ) (h : n < L.length),
    G.IsSelected (prefixProfile (L.take n)) (L[n]'h).1 (L[n]'h).2

/-- A special iteratively dominant sequence: `σ` reindexes all agents (injective, range an initial
segment of `ℕ`), and each agent `a` with his path `p a` is the pair selected given the agents of
smaller index on their `p`-paths. -/
def IsSpecialSeq (σ : A → ℕ) (p : A → List E) : Prop :=
  Function.Injective σ ∧ (∀ (a : A) (n : ℕ), n < σ a → ∃ b, σ b = n) ∧
  ∀ a : A, G.IsSelected (fun b => if σ b < σ a then some (p b) else none) a (p a)

end Instance

end AtomicDynFlow.IDNE


