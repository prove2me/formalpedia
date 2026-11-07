-- Prove2me | Definitions.Def_BFAlmostLinear_WGraph
-- name    : BFAlmostLinear_WGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:10.249784+00:00
-- url     : https://prove2.me/theorems/89d99bd0-03a8-4b47-8243-9a2c718fc0b0
-- title:
--   Weighted digraph with frozen negative arcs, auxiliary arcs, $d^h$, $\tilde d^h$, valid potentials, fixing
-- statement:
--   A **weighted graph with frozen flags** is a directed multigraph $(V,E)$ with weights $w:E\to\mathbb R$, a flag $\mathrm{neg}(e)$ marking the **frozen negative arcs** and a flag $\mathrm{aux}(e)$ marking the **auxiliary arcs** $E_{\mathrm{fake}}$; the others are **real** arcs. For a potential $\phi:V\to\mathbb R$, the reweighted graph $G_\phi$ has weights $w_\phi(u,v)=w(u,v)+\phi(u)-\phi(v)$ and the same flags.
--
--   1. The **hops** of a walk are its flagged arcs, with multiplicity.
--   2. The **$h$-negative hop distance** $d^h(s,t)$ is the infimum of the weights of the walks of real arcs from $s$ to $t$ with at most $h$ hops ($+\infty$ if there is none); $\tilde d^h(s,t)$ is the same infimum over walks that may also use auxiliary arcs. $d(s,t)$ is the infimum over all real walks.
--   3. A vertex is **negative** if it is the tail of a real flagged arc; $N$ is the set of negative vertices.
--   4. $\phi$ is **valid** if every unflagged arc has $w_\phi\ge0$.
--   5. For hop bounds $h_1,h_2$, $\phi$ **fixes** $U\subseteq V$ if $d^{h_1}_\phi(s,r)+d^{h_2}_\phi(r,t)\ge0$ for all $s,t\in V$ and $r\in U$; and $(s,r,t)\in\mathcal X_\phi$ if $d^{h_1}_\phi(s,r)+d^{h_2}_\phi(r,t)<0$.
--
--   **Formalization Note** Flags never change under reweighting, which is the paper's "freezing": an arc negative before the reweighting still counts as a hop after it. The hypothesis `Frozen` (every arc of negative weight is flagged) is stated in theorems, not bundled here. The paper's distances are over paths; these are over walks, which agree when no closed walk of at most $h$ hops is negative. Distances live in `EReal`; under `Frozen` they are never $-\infty$. The pair $(h_1,h_2)$ generalizes the paper's $h_1=h_2=h$; Lemma 4.6's proof applies §2 with $(0,1)$.
-- source:
--   Hair, Li, Li, Zhang, Bellman-Ford in Almost-Linear Time, STOC 2027 submission (manuscript sha256 873b9acb…), §1.1, p.2 (negative vertices, h-negative hop distance, potentials, validity, freezing); §2, pp.5–6 (fixing, X_ϕ); §3, p.10 (auxiliary edges, d̃^h)

import Mathlib
import Definitions.Def_AtomicDynRouting_ResidenceTime_Network
import Definitions.Def_BFAlmostLinear_IsSSSPOutput

namespace BFAlmostLinear

open AtomicDynRouting.ResidenceTime

/-- A weighted directed multigraph with frozen negative arcs and auxiliary arcs.

Hair, Li, Li, Zhang, *Bellman-Ford in Almost-Linear Time*, STOC 2027 submission (manuscript sha256
873b9acb…), §1.1, p.2 and §3, p.10.

**Formalization Note.**
* `neg` flags the **frozen** negative arcs (§1.1, p.2: "even if a negative edge in G is non-negative after
  the reweighting ϕ, we will still call this edge negative … and count it towards hops"). A reweighting
  changes `w` and never `neg`.
* `aux` flags the auxiliary arcs `E_fake` (§3, p.10). An arc with `aux e = false` is a real arc.
* That every arc of negative weight is flagged is the hypothesis `Frozen`, not a field, because a
  reweighting by an arbitrary potential need not keep it. -/
structure WGraph (V E : Type) where
  net : Network V E
  w : E → ℝ
  neg : E → Bool
  aux : E → Bool

namespace WGraph

variable {V E : Type} (G : WGraph V E)

/-- The graph `G_ϕ` (§1.1, p.2): each arc `(u, v)` has new weight `w(u, v) + ϕ(u) − ϕ(v)`. The flags of
the arcs do not change. -/
def reweight (ϕ : V → ℝ) : WGraph V E :=
  { G with w := fun e => G.w e + ϕ (G.net.tail e) - ϕ (G.net.head e) }

/-- The number of frozen negative arcs on `P`, with multiplicity. -/
def hops (P : List E) : ℕ := P.countP fun e => G.neg e

/-- `P` is a walk from `s` to `t` of real arcs. -/
def IsRealWalk (s t : V) (P : List E) : Prop :=
  G.net.IsPathFrom s t P ∧ ∀ e ∈ P, G.aux e = false

/-- The distance `d(s, t)` in the graph without auxiliary arcs: the infimum over real walks, in `EReal`. -/
noncomputable def dist (s t : V) : EReal :=
  ⨅ (P : List E) (_ : G.IsRealWalk s t P), ((pathWeight G.w P : ℝ) : EReal)

/-- The `h`-negative hop distance `d^h(s, t)` (§1.1, p.2): the infimum of the weight of the real walks from
`s` to `t` with at most `h` frozen negative arcs. It is `⊤` if there is no such walk.

**Formalization Note.** The paper says "path"; the infimum is over walks. With no negative closed walk
of at most `h` hops the two agree, and Subclaim 4.4, p.15 works with closed walks. If `Frozen` holds, the
value is never `⊥`: a walk of at most `h` hops has at most `h` arcs of negative weight, and the bound is
preserved by any reweighting, whose effect telescopes. -/
noncomputable def dH (h : ℕ) (s t : V) : EReal :=
  ⨅ (P : List E) (_ : G.IsRealWalk s t P ∧ G.hops P ≤ h), ((pathWeight G.w P : ℝ) : EReal)

/-- The distance `d̃^h(s, t)` (§3, p.10): "the h-hop shortest path distance that may use auxiliary edges as
hops". The infimum is over walks of real and auxiliary arcs with at most `h` frozen negative arcs. -/
noncomputable def dHt (h : ℕ) (s t : V) : EReal :=
  ⨅ (P : List E) (_ : G.net.IsPathFrom s t P ∧ G.hops P ≤ h), ((pathWeight G.w P : ℝ) : EReal)

/-- `d̃^h(v, V) = min_{x ∈ V} d̃^h(v, x)` (§1.1, p.2, "the distance between a set and a point"). -/
noncomputable def dHtFrom [Fintype V] (h : ℕ) (v : V) : EReal := ⨅ x, G.dHt h v x

/-- `d̃^h(V, v) = min_{x ∈ V} d̃^h(x, v)`. -/
noncomputable def dHtTo [Fintype V] (h : ℕ) (v : V) : EReal := ⨅ x, G.dHt h x v

/-- Every arc of negative weight, real or auxiliary, is flagged. -/
def Frozen : Prop := ∀ e, G.w e < 0 → G.neg e = true

/-- `ϕ` is a valid potential (§1.1, p.2): an unflagged arc stays nonnegative after reweighting.

**Formalization Note.** The paper's condition is on the arcs with `w(u, v) ≥ 0`. When `neg e` holds exactly
for `w e < 0`, the two are the same. For a graph with frozen flags, it is the unflagged arcs that must stay
nonnegative. Auxiliary arcs are included. -/
def IsValid (ϕ : V → ℝ) : Prop := ∀ e, G.neg e = false → 0 ≤ (G.reweight ϕ).w e

/-- `r` is a negative vertex (§1.1, p.2): it is the tail of a real flagged arc. -/
def IsNegVertex (r : V) : Prop := ∃ e, G.net.tail e = r ∧ G.neg e = true ∧ G.aux e = false

open Classical in
/-- The set `N` of negative vertices. -/
noncomputable def negVertices [Fintype V] : Finset V := Finset.univ.filter G.IsNegVertex

/-- The negative vertices as a type. -/
def NegVertex : Type := {r : V // G.IsNegVertex r}

/-- A real flagged arc. Under invariant (I1) it is determined by its tail `r`, and its head is `r′`. -/
def NegArc : Type := {e : E // G.neg e = true ∧ G.aux e = false}

/-- `ϕ` fixes `U` (§2, p.5) for the hop pair `(h₁, h₂)`: for all `s, t ∈ V` and `r ∈ U`,
`d^{h₁}_ϕ(s, r) + d^{h₂}_ϕ(r, t) ≥ 0`.

**Formalization Note.** The printed form is `h₁ = h₂ = h`. The pair is needed because Lemma 4.6's proof,
p.18 applies Corollary 2.8 under the hypothesis `d⁰_ϕ + d¹_ϕ ≥ 0`, and §2 only uses additivity. -/
def Fixes (h₁ h₂ : ℕ) (U : Finset V) (ϕ : V → ℝ) : Prop :=
  ∀ r ∈ U, ∀ s t, 0 ≤ (G.reweight ϕ).dH h₁ s r + (G.reweight ϕ).dH h₂ r t

/-- The sign condition `(s, r, t) ∈ X_ϕ` of §2, p.6: `d^{h₁}_ϕ(s, r) + d^{h₂}_ϕ(r, t) < 0`. -/
def InX (h₁ h₂ : ℕ) (ϕ : V → ℝ) (s r t : V) : Prop :=
  (G.reweight ϕ).dH h₁ s r + (G.reweight ϕ).dH h₂ r t < 0

/-- The vertex `u` lies on the walk `P` that starts at `s`. -/
def Visits (s : V) (P : List E) (u : V) : Prop := u = s ∨ ∃ e ∈ P, G.net.head e = u

/-- The arcs a walk may use in invariant (I3) and Lemma 4.16: real arcs and flagged auxiliary arcs. -/
def Usable (e : E) : Prop := G.aux e = false ∨ G.neg e = true

/-- The graph with no auxiliary arcs whose flagged arcs are exactly those of negative weight. This is the
input graph of Theorem 1.1 and Lemma 1.2. -/
noncomputable def ofWeights (N : Network V E) (w : E → ℝ) : WGraph V E where
  net := N
  w := w
  neg := fun e => by classical exact decide (w e < 0)
  aux := fun _ => false

end WGraph

end BFAlmostLinear


