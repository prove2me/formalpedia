-- Prove2me | Definitions.Def_TwoOptAllExp_TSP_Supplement_GraphObjective
-- name    : TwoOptAllExp_TSP_Supplement_GraphObjective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T04:42:52.247205+00:00
-- url     : https://prove2.me/theorems/dab02caa-0c22-4bc4-8ced-90f1f336ce6c
-- title:
--   Weighted graph objectives, the signed difference $\Delta_x$, $B_x(y)$ and the following relation $x\leftarrow\varphi$
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph with edge weights $w:E\to\mathbb Z$ and vertex weights $b:V\to\mathbb Z$. For an assignment $\sigma:V\to\{0,1\}$ the objective is
--
--   $$\Phi(\sigma)=\sum_{uv\in E}w(uv)\,[\sigma(u)\ne\sigma(v)]+\sum_{v\in V}b_v\,\sigma(v).$$
--
--   For a vertex $x$ the **signed difference** is $\Delta_x(\sigma)=\Phi(\sigma[x\mapsto1])-\Phi(\sigma[x\mapsto0])$, and for a neighbor $y$ of $x$ the **residual incident weight** is $B_x(y)=\sum_{ux\in E,\,u\ne y}|w(xu)|$.
--
--   For a Boolean function $\varphi$ of assignments and a set $S$ of assignments, **$x$ follows $\varphi$ on $S$**, written $x\leftarrow\varphi$ on $S$, if for every $\sigma\in S$ we have $\Delta_x(\sigma)>0$ when $\varphi(\sigma)=1$ and $\Delta_x(\sigma)<0$ when $\varphi(\sigma)=0$; when $S$ is the set of all assignments we write $x\leftarrow\varphi$. For Lemma 17 the term $r=w(zt)(1-2\sigma(t))$ if a further neighbor $t$ of $z$ exists, and $r=0$ otherwise, is also defined.
--
--   These are the representation and the local primitive used for the $(2,3,2)$-MCA construction of Section 5.
--
--   **Formalization Note** Edge weights are a function on unordered pairs (`Sym2 V`); only its values on edges enter. The optional neighbor $t$ is an `Option V`.
-- source:
--   Heimann, Hoang and Hougardy, Closing All-Exp Gaps in Local Search for the Traveling Salesman Problem and Maximum Constraint Assignment, November 2, 2026 preprint, STOC 2027 submission #112, SHA-256 9ac9fdf5ac1be95dff40e95db1590649f15b4eeb94559413175c88f9a42bff60, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/112.pdf, §5.1–5.2, pp. 24–25; Lemma 17, p. 26

import Mathlib
import Definitions.Def_TwoOptAllExp_TSP_Supplement_MCA

namespace TwoOptAllExp.TSP.Supplement

/-! # Weighted graph representation of binary MCA and the "following" primitive

Heimann, Hoang and Hougardy, November 2, 2026 preprint (STOC 2027 submission #112), §5.1–5.2,
pp. 24–25. -/

/-- A weighted graph objective (§5.1, p. 25): a finite simple undirected graph `G = (V, E)`, edge
weights `w : E → ℤ` (the values of `w` off `E` play no role) and vertex weights `b : V → ℤ`. -/
structure WGraph (V : Type) [Fintype V] [DecidableEq V] where
  /-- The graph `G`. -/
  G : SimpleGraph V
  /-- Adjacency in `G` is decidable. -/
  decAdj : DecidableRel G.Adj
  /-- The edge weights `w(uv)`. -/
  w : Sym2 V → ℤ
  /-- The vertex weights `b_v`. -/
  b : V → ℤ

namespace WGraph

variable {V : Type} [Fintype V] [DecidableEq V] (W : WGraph V)

instance : DecidableRel W.G.Adj := W.decAdj

/-- `[σ(u) ≠ σ(v)]` for the edge `uv`. -/
def cut (σ : V → Bool) (e : Sym2 V) : ℤ :=
  Sym2.lift ⟨fun u v => if σ u = σ v then 0 else 1, fun u v => by simp [eq_comm]⟩ e

/-- The objective `Φ(σ) = ∑_{uv ∈ E} w(uv) [σ(u) ≠ σ(v)] + ∑_{v ∈ V} b_v σ(v)` (§5.1, p. 25). -/
def Φ (σ : V → Bool) : ℤ :=
  ∑ e ∈ W.G.edgeFinset, W.w e * cut σ e + ∑ v, W.b v * b2i (σ v)

/-- The signed difference `Δ_x(σ) = Φ(σ[x ↦ 1]) - Φ(σ[x ↦ 0])` (§5.1, p. 25). -/
def Δ (x : V) (σ : V → Bool) : ℤ :=
  W.Φ (Function.update σ x true) - W.Φ (Function.update σ x false)

/-- The residual incident weight `B_x(y) = ∑_{ux ∈ E, u ≠ y} |w(xu)|` (§5.2, p. 25). -/
def B (x y : V) : ℤ :=
  ∑ u ∈ (W.G.neighborFinset x).erase y, |W.w s(x, u)|

/-- `x ← φ on S` (§5.2, p. 25): for every assignment `σ ∈ S`, `Δ_x(σ) > 0` when `φ(σ) = 1` and
`Δ_x(σ) < 0` when `φ(σ) = 0`. With `S` the set of all assignments this is `x ← φ`. -/
def FollowsOn (x : V) (φ : (V → Bool) → Bool) (S : Set (V → Bool)) : Prop :=
  ∀ σ ∈ S, (φ σ = true → 0 < W.Δ x σ) ∧ (φ σ = false → W.Δ x σ < 0)

/-- `x ← φ` (§5.2, p. 25): `x` follows `φ` on the set of all assignments. -/
def Follows (x : V) (φ : (V → Bool) → Bool) : Prop :=
  W.FollowsOn x φ Set.univ

/-- The term `r` of Lemma 17 (p. 26): `r = w(zt)(1 - 2σ(t))` if the further neighbor `t` exists
(`t = some t₀`), and `r = 0` otherwise (`t = none`). -/
def tieTerm (z : V) (t : Option V) (σ : V → Bool) : ℤ :=
  match t with
  | none => 0
  | some t₀ => W.w s(z, t₀) * (1 - 2 * b2i (σ t₀))

end WGraph

end TwoOptAllExp.TSP.Supplement


