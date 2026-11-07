-- Prove2me | Definitions.Def_BetheKS_vertexFieldGraph
-- name    : BetheKS_vertexFieldGraph
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:51.642975+00:00
-- url     : https://prove2.me/theorems/61f43035-3178-421a-b140-8a6aec23a4b8
-- title:
--   Boundary messages $b^{(L,M)}_{u\to v}$, vertex fields $V^{(L,M)}$, $V^{(L)}$, balls and rooted labelled graphs
-- statement:
--   On a locally finite graph $G$ with labels $\sigma:V(G)\to[r]$ and $X_u=\phi(\sigma(u))$, the **truncated messages** are
--   $$
--   b^{(0,M)}_{u\to v}:=X_u,\qquad b^{(L+1,M)}_{u\to v}:=(\Gamma_u^{(v)})^{(M)}\sum_{w\sim u,\,w\ne v}b^{(L,M)}_{w\to u},
--   $$
--   and $b^{(L)}_{u\to v}$ is defined the same way with the limit weights $\Gamma_u^{(v)}$ (Definition 5.2). The **vertex fields** (Definition D.1) are
--   $$
--   V^{(L,M)}(u):=\frac{t\sum_{v\sim u}b^{(L,M)}_{v\to u}}{t^2+\deg(u)-1+\delta-t\sum_{v\sim u}(\Gamma_v^{(u)})^{(M)}},\qquad V^{(L)}(u):=\frac{t\sum_{v\sim u}b^{(L)}_{v\to u}}{t^2+\deg(u)-1+\delta-t\sum_{v\sim u}\Gamma_v^{(u)}} .
--   $$
--   The file also defines the action of the Bethe Hessian on functions, $(H(\tau,G)f)(u)=(\tau^2-1+\deg u)f(u)-\tau\sum_{w\sim u}f(w)$, the ball $B_k(G,u)$ of vertices at distance at most $k$, rooted labelled graphs, and isomorphism of rooted labelled balls ("determined by the ball").
--
--   **Formalization Note** A sign $s\in\{\pm1\}$ multiplies every weight and the numerator $t$; $s=1$ is the paper's definition, and $s=-1$ is the variant "use $-\Gamma_\delta$ in place of $\Gamma_\delta$ and $-t$ in place of $t$; the denominator is unchanged" of the proof of Theorem 2.2 (p.12). Graph distances are extended, so other components are outside every ball.
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Definition 5.2, p.9; Definition D.1, p.20; proof of Theorem 2.2, p.12

import Mathlib
import Definitions.Def_BetheKS_cavityIter

set_option autoImplicit false

namespace BetheKS

variable {V : Type} [DecidableEq V] {r : ℕ}

/-- **Truncated boundary messages `b^{(L,M)}_{u→v}`** — Dong, McKenzie, arXiv:2610.41802 (held
version, sha256 4da41e16…), Definition 5.2, p.9 (PDF p.10): on a graph `G` with labels `σ`, and
`X_u = ϕ(σ(u))`, `b^{(0,M)}_{u→v} := X_u` and
`b^{(L+1,M)}_{u→v} := (Γ_u^{(v)})^{(M)} ∑_{w∼u, w≠v} b^{(L,M)}_{w→u}`.

**Formalization Note.** `msgIter G σ ϕ s t δ M L u v` is `b^{(L,M)}_{u→v}`. The sign `s ∈ {±1}`
multiplies every weight: `s = 1` is Definition 5.2; `s = −1` is the variant "use `−Γ_δ` in place of
`Γ_δ`" of the proof of Theorem 2.2 (p.12) for negative planted eigenvalues. -/
noncomputable def msgIter (G : SimpleGraph V) [G.LocallyFinite] (σ : V → Fin r) (ϕ : Fin r → ℝ)
    (s t δ : ℝ) (M : ℕ) : ℕ → V → V → ℝ
  | 0, u, _ => ϕ (σ u)
  | L + 1, u, v => s * cavIter G t δ M u v *
      ∑ w ∈ (G.neighborFinset u).erase v, msgIter G σ ϕ s t δ M L w u

/-- **Boundary messages `b^{(L)}_{u→v}`** (Definition 5.2, p.9), with the limit weights `Γ_u^{(v)}`:
`b^{(0)}_{u→v} := X_u`, `b^{(L+1)}_{u→v} := Γ_u^{(v)} ∑_{w∼u, w≠v} b^{(L)}_{w→u}` (sign `s` as in
`msgIter`). -/
noncomputable def msg (G : SimpleGraph V) [G.LocallyFinite] (σ : V → Fin r) (ϕ : Fin r → ℝ)
    (s t δ : ℝ) : ℕ → V → V → ℝ
  | 0, u, _ => ϕ (σ u)
  | L + 1, u, v => s * cav G t δ u v * ∑ w ∈ (G.neighborFinset u).erase v, msg G σ ϕ s t δ L w u

/-- **The vertex field `V^{(L,M)}`** (Definition D.1, p.20, PDF p.21):
`V^{(L,M)}(u) := t ∑_{v∼u} b^{(L,M)}_{v→u} / (t² + deg(u) − 1 + δ − t ∑_{v∼u} (Γ_v^{(u)})^{(M)})`.

**Formalization Note.** With the sign `s`, the numerator is `s t ∑ …` ("`−t` in place of `t`",
proof of Theorem 2.2, p.12); "the denominator in the vertex-field formula is unchanged". -/
noncomputable def vfIter (G : SimpleGraph V) [G.LocallyFinite] (σ : V → Fin r) (ϕ : Fin r → ℝ)
    (s t δ : ℝ) (L M : ℕ) (u : V) : ℝ :=
  s * t * (∑ v ∈ G.neighborFinset u, msgIter G σ ϕ s t δ M L v u) /
    (t ^ 2 + (G.degree u : ℝ) - 1 + δ - t * ∑ v ∈ G.neighborFinset u, cavIter G t δ M v u)

/-- **The vertex field `V^{(L)}`** (Definition D.1, p.20):
`V^{(L)}(u) := t ∑_{v∼u} b^{(L)}_{v→u} / (t² + deg(u) − 1 + δ − t ∑_{v∼u} Γ_v^{(u)})` (sign as in
`vfIter`). -/
noncomputable def vf (G : SimpleGraph V) [G.LocallyFinite] (σ : V → Fin r) (ϕ : Fin r → ℝ)
    (s t δ : ℝ) (L : ℕ) (u : V) : ℝ :=
  s * t * (∑ v ∈ G.neighborFinset u, msg G σ ϕ s t δ L v u) /
    (t ^ 2 + (G.degree u : ℝ) - 1 + δ - t * ∑ v ∈ G.neighborFinset u, cav G t δ v u)

/-- The Bethe Hessian acting on a function `f : V → ℝ` of a locally finite graph:
`(H(τ, G) f)(u) = (τ² − 1 + deg(u)) f(u) − τ ∑_{w∼u} f(w)` (§1, p.1; Lemma D.2's proof, p.20). -/
noncomputable def bhApply (G : SimpleGraph V) [G.LocallyFinite] (τ : ℝ) (f : V → ℝ) (u : V) : ℝ :=
  (τ ^ 2 - 1 + (G.degree u : ℝ)) * f u - τ * ∑ w ∈ G.neighborFinset u, f w

/-- The ball `B_k(G, u)`: the vertices at graph distance at most `k` from `u` (Definition D.1, p.20).

**Formalization Note.** Distances are extended (`SimpleGraph.edist`, `⊤` between different
components), so unreachable vertices are not in the ball. -/
def ball (G : SimpleGraph V) (u : V) (k : ℕ) : Set V := {v | G.edist u v ≤ k}

/-- A rooted, vertex-labelled, locally finite graph `(G, u)` with labels in `[r]`. -/
structure RLGraph (r : ℕ) where
  /-- the vertex type -/
  V : Type
  [decEq : DecidableEq V]
  /-- the graph -/
  G : SimpleGraph V
  [lf : G.LocallyFinite]
  /-- the vertex labels -/
  lab : V → Fin r
  /-- the root -/
  root : V

/-- Two rooted labelled graphs have isomorphic labelled balls of radius `k`: a graph isomorphism of
the induced subgraphs on `B_k` that maps root to root and preserves labels. This is what
"determined by the ball `B_k(G, u)`" means (Lemma D.2, p.20; Lemma E.1, p.24). -/
def BallIso {r : ℕ} (X Y : RLGraph r) (k : ℕ) : Prop :=
  ∃ φ : X.G.induce (ball X.G X.root k) ≃g Y.G.induce (ball Y.G Y.root k),
    (∀ x : ball X.G X.root k, x.val = X.root → (φ x).val = Y.root) ∧
    ∀ x : ball X.G X.root k, Y.lab (φ x).val = X.lab x.val

/-- `|B_k(G, u)|`, the number of vertices of the ball (finite for a locally finite graph). -/
noncomputable def ballCard {r : ℕ} (X : RLGraph r) (k : ℕ) : ℕ := Nat.card (ball X.G X.root k)

/-- The rooted labelled graph `(G, u)` for a graph on `[n]` with labels `σ`. -/
noncomputable def finRL {n : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Fin r) (u : Fin n) :
    RLGraph r := by
  classical
  exact { V := Fin n, G := G, lab := σ, root := u }

end BetheKS


