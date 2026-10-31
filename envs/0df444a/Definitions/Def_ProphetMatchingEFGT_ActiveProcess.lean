-- Prove2me | Definitions.Def_ProphetMatchingEFGT_ActiveProcess
-- name    : ProphetMatchingEFGT_ActiveProcess
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:51:23.514917+00:00
-- url     : https://prove2.me/theorems/6a7c3c92-388b-4435-86fa-d8fa69695b12
-- title:
--   §5 — the active-edge process of Algorithm 3: $\alpha_e$, greedy on active edges, candidates and witnesses
-- statement:
--   Fix a constant $c$, marginals $x\in\mathcal F_M$, and the edges $e_1,e_2,\dots$ arriving before a given edge, in order.
--
--   1. **Algorithm 3** (p. 12) matches an arriving realized edge $(uv)$ with probability
--   $$\alpha_{(uv)}=\frac{c}{\Pr[u,v\text{ are unmatched at }(uv)]}\qquad(7)$$
--   when both $u$ and $v$ are unmatched.
--   2. **Active edges** (p. 14). For the analysis, each edge $e$ is **active** independently with probability $\alpha_e x_e$, and active edges are picked greedily in arrival order (an active edge is picked if both its ends are unmatched). The probabilities $\alpha_e x_e$ are computed recursively along the order, each from the process of the earlier edges.
--   3. **"Unmatched at $e$".** $\Pr[u,v\text{ are unmatched at }(uv)]$ is the probability that greedy on the earlier edges leaves both $u$ and $v$ unmatched. Algorithm 3 is **well defined** on a list of edges if $c\le\Pr[\text{both ends of }e\text{ unmatched at }e]$, i.e. $\alpha_e\le1$, for each of them.
--   4. **Candidates** (p. 14). The sampler $\pi_u$ keeps the true activation $\widetilde E_u$ of the edges at $u$, resamples the other edges independently with the same probabilities, runs greedy in order, and returns the partner of $u$; "$u^*$ candidate of $u$" is the event that it returns $u^*$.
--   5. **Witnesses** (p. 14). $u^*$ is a witness of $u$ if $(uu^*)$ is active and is the only active edge of $u^*$; $|\widetilde E\cap E_{r}|$ is the number of active edges at $r$.
--   6. $x_{us}$ is the marginal of the edge $(us)$ among the earlier edges, and $0$ if $(us)$ is not one of them (the paper removes $(uv)$ and the later edges from $E$).
--
--   These are the quantities of eqs. (8), (10)–(15) and Lemmas 5.2, 5.4 and 5.5.
--
--   **Formalization Note** An activation pattern is a list of (edge, active?) pairs in arrival order; expectations over patterns are finite sums (`bern`). The recursion uses the real quotient $c/P$, which is $0$ when $P=0$; theorems never assume $\alpha_e\le1$ but the equivalent, junk-free $c\le P$.
-- source:
--   Ezra–Feldman–Gravin–Tang, Online Stochastic Max-Weight Matching: prophet inequality for vertex and edge arrival models, arXiv:2002.09807v2, §5 Algorithm 3 and eq. (7) p. 12, §5.3 pp. 14–16 (active edges, sampler π_u, witnesses)

import Mathlib
import Definitions.Def_ProphetMatchingEFGT_EdgeArrival

namespace ProphetMatchingEFGT

/-! # The active-edge process of Algorithm 3 (§5, pp. 12–16, Ezra–Feldman–Gravin–Tang,
arXiv:2002.09807v2)

Fix `c` and `x ∈ FM`, and let `e₁, e₂, …` be the edges arriving before a given edge, in order.
Algorithm 3 (p. 12) matches a realized edge `e_k` with probability `α_{e_k} = c / Pr[both ends of
e_k are unmatched at e_k]` when both its ends are unmatched. "For the purpose of analysis" (p. 14)
the realization and the coin are unified: each `e` is **active** independently with probability
`α_e · x_e`, and active edges are picked greedily in arrival order. This module defines that
process as finite sums over activation patterns, the probabilities `α_e x_e` recursively along the
order, the candidate sampler `π_u` (p. 14) and witnesses (p. 14).

**Formalization Note.** An activation pattern is a list of `(edge, active?)` pairs in arrival
order. `bern ps f` is the expectation of `f` when the edges of `ps = [(e₁, a₁), …]` are active
independently with probabilities `a_i`; `prob ps P` is the probability of the event `P`. The
recursion `α_e = c / Pr[…]` is the real quotient, which is `0` when the probability is `0`; every
theorem that uses it assumes `c ≤ Pr[both ends unmatched at e]` (the paper's `α_e ≤ 1`) for the
edges concerned, never `α_e ≤ 1` itself. -/

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

open Classical in
/-- Greedy on an activation pattern (p. 14, step 2): scan in order and pick an active edge when
both its ends are unmatched. -/
noncomputable def greedy (l : List (Edge G × Bool)) : Finset (Edge G) :=
  l.foldl (fun M p => if p.2 = true ∧ endsFree M p.1 then insert p.1 M else M) ∅

/-- The expectation of `f` over activation patterns of the edges of `ps = [(e₁, a₁), …, (e_k, a_k)]`,
each `e_i` active independently with probability `a_i`. -/
noncomputable def bern : List (Edge G × ℝ) → (List (Edge G × Bool) → ℝ) → ℝ
  | [], f => f []
  | (e, a) :: ps, f => a * bern ps (fun l => f ((e, true) :: l)) +
      (1 - a) * bern ps (fun l => f ((e, false) :: l))

open Classical in
/-- The probability of an event of the activation pattern. -/
noncomputable def prob (ps : List (Edge G × ℝ)) (P : List (Edge G × Bool) → Prop) : ℝ :=
  bern ps (fun l => if P l then 1 else 0)

open Classical in
/-- The probability of an event of two independent activation patterns with the same law. -/
noncomputable def prob2 (ps : List (Edge G × ℝ))
    (P : List (Edge G × Bool) → List (Edge G × Bool) → Prop) : ℝ :=
  bern ps (fun l => bern ps (fun l' => if P l l' then 1 else 0))

open Classical in
/-- The probability of an event of three independent activation patterns with the same law. -/
noncomputable def prob3 (ps : List (Edge G × ℝ))
    (P : List (Edge G × Bool) → List (Edge G × Bool) → List (Edge G × Bool) → Prop) : ℝ :=
  bern ps (fun l => bern ps (fun l' => bern ps (fun l'' => if P l l' l'' then 1 else 0)))

/-- `Pr[u, v are unmatched at e]` for `e = (uv)` arriving after the edges of `ps`. -/
noncomputable def unmatchedProb (ps : List (Edge G × ℝ)) (e : Edge G) : ℝ :=
  prob ps (fun l => endsFree (greedy l) e)

/-- The activation probabilities `a_e = α_e · x_e` of the edges `es` (in arrival order) under
Algorithm 3 with constant `c` and marginals `x`, with `α_e = c / Pr[both ends of e unmatched at e]`
(eq. (7), p. 12), computed along the order. -/
noncomputable def actProbs (c : ℝ) (x : Edge G → ℝ) (es : List (Edge G)) : List (Edge G × ℝ) :=
  es.foldl (fun ps e => ps ++ [(e, c / unmatchedProb ps e * x e)]) []

/-- `Pr[u, v are unmatched at e]` under Algorithm 3 with constant `c` and marginals `x`, when the
edges arriving before `e = (uv)` are `es`, in this order. -/
noncomputable def unmatchedAt (c : ℝ) (x : Edge G → ℝ) (es : List (Edge G)) (e : Edge G) : ℝ :=
  unmatchedProb (actProbs c x es) e

/-- Algorithm 3 is well defined on the edges `es` (in this order): for every edge `e_k` of `es`,
`c ≤ Pr[both ends of e_k unmatched at e_k]`, i.e. `α_{e_k} ≤ 1` (p. 12, "It remains to show that
Algorithm 3 is well-defined, i.e., that α_e ≤ 1"). -/
def WellDefinedOn (c : ℝ) (x : Edge G → ℝ) (es : List (Edge G)) : Prop :=
  ∀ k : Fin es.length, c ≤ unmatchedAt c x (es.take k) (es.get k)

/-- The vertex `u` is matched at the end of the pattern `l`. -/
def matchedIn (l : List (Edge G × Bool)) (u : V) : Prop :=
  ∃ f ∈ greedy l, u ∈ (f : Sym2 V)

/-- The edge `(ui)` is active in `l` (it is not active when `(ui)` is not an edge listed in `l`). -/
def isActive (l : List (Edge G × Bool)) (u i : V) : Prop :=
  ∃ p ∈ l, p.2 = true ∧ (p.1 : Sym2 V) = s(u, i)

open Classical in
/-- The number `|Ẽ ∩ E_r|` of active edges at the vertex `r`. -/
noncomputable def activeDegree (l : List (Edge G × Bool)) (r : V) : ℕ :=
  l.countP (fun p => p.2 && decide (r ∈ (p.1 : Sym2 V)))

/-- `x_{us}`: the marginal of the edge `(us)` if it is an edge among `es`, and `0` otherwise (the
paper removes `(uv)` and the later edges from `E`, p. 14). -/
noncomputable def xPair (x : Edge G → ℝ) (es : List (Edge G)) (u s : V) : ℝ := by
  classical
  exact if h : G.Adj u s then
    (if (⟨s(u, s), G.mem_edgeSet.2 h⟩ : Edge G) ∈ es then x ⟨s(u, s), G.mem_edgeSet.2 h⟩ else 0)
  else 0

/-- The pattern seen by the sampler `π_u` (p. 14): the true activation `Ẽ_u` on the edges at `u`
(taken from `l`) and an independent resampling `Ê_{-u}` on the other edges (taken from `l'`). -/
def mixAt (u : V) (l l' : List (Edge G × Bool)) : List (Edge G × Bool) :=
  List.zipWith (fun p p' => if u ∈ (p.1 : Sym2 V) then p else p') l l'

/-- "`s` candidate of `u`" (p. 14): greedy on `Ẽ_u ∪ Ê_{-u}` matches `u` with `s`. -/
def IsCandidate (u : V) (l l' : List (Edge G × Bool)) (s : V) : Prop :=
  ∃ f ∈ greedy (mixAt u l l'), (f : Sym2 V) = s(u, s)

/-- `r` is a witness of `u` in `l` (p. 14): `(ur)` is active and is the only active edge of `r`. -/
def IsWitness (l : List (Edge G × Bool)) (u r : V) : Prop :=
  isActive l u r ∧ activeDegree l r = 1

/-- `u` and `v` have witnesses (p. 14). -/
def HaveWitnesses (l : List (Edge G × Bool)) (u v : V) : Prop :=
  (∃ a, IsWitness l u a) ∧ ∃ b, IsWitness l v b

end ProphetMatchingEFGT


