-- Prove2me | Definitions.Def_BFAlmostLinear_flagInit
-- name    : BFAlmostLinear_flagInit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:35.379774+00:00
-- url     : https://prove2.me/theorems/58bf653d-28e2-4b4b-8f9b-32d980803e1f
-- title:
--   Input and output layouts of the hop-bounded and search algorithms
-- statement:
--   **Input.** For a weighted graph with frozen flags on $V=\{0,\dots,n-1\}$ with $m$ arcs, a vertex $s$, a hop bound $h$ and vertex weights $\lambda$: integer cells hold $n,m,s$, the tails, the heads, the flags $\mathrm{neg}(e)$ and $\mathrm{aux}(e)$, and $h$; real cells hold $w(e)$ and $\lambda(v)$; all other cells are $0$.
--
--   **Hop-bounded output.** For every $t$, integer cell $-1-t$ is $0$ if $d^h(s,t)=+\infty$, and otherwise it is $1$ and real cell $-1-t$ holds $d^h(s,t)$.
--
--   **Search output.** A list of entries $(r,x,\text{side})$, and a real $\Delta_r$ for each negative vertex $r$. The listed sets are $V^{\mathrm{in}}_r$ (side $0$) and $V^{\mathrm{out}}_r$ (side $1$).
--
--   1. *Lemma 4.6 form:* $V^{\mathrm{in}}_r=\{x: d^0(x,r)<\Delta_r\}$ and $V^{\mathrm{out}}_r=\{x: d^1(r,x)<-\Delta_r\}$, each entry carrying the distance $d^0(x,r)$ or $d^1(r,x)$.
--   2. *Lemma 4.8 form:* $\tilde V^{\mathrm{in}}_r$ contains every vertex on a walk of at most $h$ hops (auxiliary arcs allowed) that ends at $r$ and has weight $<\Delta_r$; $\tilde V^{\mathrm{out}}_r$ contains every vertex on a walk of at most $h+1$ hops that starts at $r$ and has weight $<-\Delta_r$.
--
--   **Formalization Note** $\Delta_r$ is a finite real. The paper's search may set $\Delta_r=\infty$ when a side is exhausted; a large enough finite value gives the same sets. Writing the list costs one step per entry, so an unlisted vertex costs nothing.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), §1.1, p.2; Lemma 4.6, p.16; Lemma 4.8, pp.18–19

import Mathlib
import Definitions.Def_BFAlmostLinear_WGraph
import Definitions.Def_BFAlmostLinear_sampleMass

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-!
# Input and output layouts of the milestones that mention the machine

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), §1.1, p.2, Lemma 4.6, p.16 and Lemma 4.8, p.18.

**Formalization Note.**
* **Input.** Integer memory: cell `0` is `n`, cell `1` is `m`, cell `2` is `s`, cells `3 + e` are the tails,
  `3 + m + e` the heads, `3 + 2m + e` the flag `neg e`, `3 + 3m + e` the flag `aux e`, and cell `3 + 4m` is the
  hop bound `h`. Real memory: cell `e` is `w e`, cell `m + v` is `λ v`. All other cells are `0`.
* **Search output.** Integer cell `−1` is the number `L` of entries. Entry `j < L` lists a negative vertex `r`
  in integer cell `−2 − 3j`, a vertex `x` in cell `−3 − 3j`, and in cell `−4 − 3j` the side: `0` for `V^in_r`, `1`
  for `V^out_r`. Real cell `−2 − 2j` is the distance listed with the entry, and real cell `−1 − 2r` is `∆_r`.
  Writing the list costs one step per entry, with no cost for an unlisted vertex.
-/

/-- Flags as integer cells. -/
def flagCells {m : ℕ} (f : Fin m → Bool) : List ℤ := List.ofFn fun e => if f e then 1 else 0

/-- The initial state on the input `(G, s, h, λ)`. -/
noncomputable def flagInit {n m : ℕ} (G : WGraph (Fin n) (Fin m)) (s h : ℕ) (lam : Fin n → ℝ) :
    Machine.State :=
  Machine.initState
    (memOfList 0 (graphCells G.net s ++ flagCells G.neg ++ flagCells G.aux ++ [(h : ℤ)]))
    (memOfList 0 (List.ofFn G.w ++ List.ofFn lam))

/-- Output of `h`-hop single-source shortest paths: for each `t`, integer cell `−1 − t` is `0` if
`d^h(s, t) = ∞`, and otherwise it is `1` and real cell `−1 − t` is `d^h(s, t)`. -/
def IsHopOutput {n m : ℕ} (G : WGraph (Fin n) (Fin m)) (h : ℕ) (s : Fin n)
    (σ : Machine.State) : Prop :=
  ∀ t : Fin n,
    (G.dH h s t = ⊤ → σ.imem (-1 - ((t : ℕ) : ℤ)) = 0) ∧
    (G.dH h s t ≠ ⊤ → σ.imem (-1 - ((t : ℕ) : ℤ)) = 1 ∧
      ((σ.rmem (-1 - ((t : ℕ) : ℤ)) : ℝ) : EReal) = G.dH h s t)

/-- `∆_r`, as read from real cell `−1 − 2r`. -/
def deltaCell {n : ℕ} (σ : Machine.State) (r : Fin n) : ℝ := σ.rmem (-1 - 2 * ((r : ℕ) : ℤ))

/-- Entry `j` of the search output is `(r, x, side)`. -/
def IsEntry {n : ℕ} (σ : Machine.State) (j : ℕ) (r x : Fin n) (side : ℤ) : Prop :=
  (j : ℤ) < σ.imem (-1) ∧
    σ.imem (-2 - 3 * (j : ℤ)) = ((r : ℕ) : ℤ) ∧
    σ.imem (-3 - 3 * (j : ℤ)) = ((x : ℕ) : ℤ) ∧
    σ.imem (-4 - 3 * (j : ℤ)) = side

open Classical in
/-- The set listed for the negative vertex `r` on the given side: `V^in_r` for side `0`, `V^out_r` for side `1`. -/
noncomputable def listed {n : ℕ} (σ : Machine.State) (side : ℤ) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => ∃ j : ℕ, IsEntry σ j r x side

/-- Output of Lemma 4.6, p.16: for every negative vertex `r`, a real `∆_r` with
`V^in_r = {x : d⁰(x, r) < ∆_r}` and `V^out_r = {x : d¹(r, x) < −∆_r}`, along with the distances.

**Formalization Note.** `∆_r` is a finite real. The proof sets `∆_r = d_in`, possibly `∞` when a search is
exhausted; a finite real large enough gives the same sets. -/
def IsSearchOutput {n m : ℕ} (G : WGraph (Fin n) (Fin m)) (σ : Machine.State) : Prop :=
  ∀ r : Fin n, G.IsNegVertex r →
    (∀ x, x ∈ listed σ 0 r ↔ G.dH 0 x r < ((deltaCell σ r : ℝ) : EReal)) ∧
    (∀ x, x ∈ listed σ 1 r ↔ G.dH 1 r x < ((-(deltaCell σ r) : ℝ) : EReal)) ∧
    (∀ j x, IsEntry σ j r x 0 → ((σ.rmem (-2 - 2 * (j : ℤ)) : ℝ) : EReal) = G.dH 0 x r) ∧
    (∀ j x, IsEntry σ j r x 1 → ((σ.rmem (-2 - 2 * (j : ℤ)) : ℝ) : EReal) = G.dH 1 r x)

/-- Output of Lemma 4.8, p.18: for every negative vertex `r`, a real `∆_r` with a set `Ṽ^in_r` that contains
all vertices on any `h`-hop walk (auxiliary arcs allowed) that ends at `r` and has total weight less than
`∆_r`, and a set `Ṽ^out_r` that contains all vertices on any `(h + 1)`-hop walk that begins at `r` and has total
weight less than `−∆_r`. Lemma 4.8 says "contains", and the sets are limited only through the weight bound. -/
def IsHopSearchOutput {n m : ℕ} (G : WGraph (Fin n) (Fin m)) (h : ℕ) (σ : Machine.State) : Prop :=
  ∀ r : Fin n, G.IsNegVertex r →
    (∀ (s u : Fin n) (P : List (Fin m)), G.net.IsPathFrom s r P → G.hops P ≤ h →
      G.Visits s P u → ((pathWeight G.w P : ℝ) < deltaCell σ r) → u ∈ listed σ 0 r) ∧
    (∀ (t u : Fin n) (P : List (Fin m)), G.net.IsPathFrom r t P → G.hops P ≤ h + 1 →
      G.Visits r P u → ((pathWeight G.w P : ℝ) < -(deltaCell σ r)) → u ∈ listed σ 1 r)

end BFAlmostLinear


