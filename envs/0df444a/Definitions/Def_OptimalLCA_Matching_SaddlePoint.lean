-- Prove2me | Definitions.Def_OptimalLCA_Matching_SaddlePoint
-- name    : OptimalLCA_Matching_SaddlePoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:46:09.352479+00:00
-- url     : https://prove2.me/theorems/fb866931-473f-40e9-aede-d3d77e978b50
-- title:
--   §3–§4 — Q, X, loads, P(q), F(x,q), g, ψ, R_α, Bregman divergence D^α_z, K_p, area convexity (Definition 4.1), the box response (Algorithm 1)
-- statement:
--   For a graph $G$ on $V$, the index set $I=\{(u,a): a\in I_u\}$, $I_u=N(u)\cup\{\perp_u\}$, is $V\oplus\mathrm{Dart}(G)$: the dummy coordinate $(u,\perp_u)$ and, for each ordered edge $(u,v)$, the coordinate $q_{uv}$ (mass proposed by $u$ to $v$).
--   - $Q=\{q\in\mathbb R^I_{\ge0}:\sum_{a\in I_u}q_{ua}=1\ \forall u\}$, $Q^\circ$ its relative interior (all coordinates positive), $X=[-1,1]^V$, $Z=X\times Q$; an interior base is $z\in(-1,1)^V\times Q^\circ$.
--   - Load $\ell_v(q)=\sum_{u\in N(v)}q_{uv}$ (3.1); accepted mass $P(q)=\sum_v\min\{1,\ell_v(q)\}$; objective $F(x,q)=\sum_v[x_v+\ell_v(q)(1-x_v)]$ (3.3).
--   - $L^*x$: $(L^*x)_{uv}=x_v$, $(L^*x)_{u\perp}=0$; $b=L^*\mathbf 1$; $g(x,q)=(\mathbf 1-Lq,\ L^*x-b)$ (4.2); $\langle(x,p),(y,h)\rangle=\langle x,y\rangle+\langle p,h\rangle$.
--   - $\psi(x)=\tfrac12[(1+x)\log(1+x)+(1-x)\log(1-x)]$ (4.4), natural logarithms, $0\log0=0$.
--   - For a vertex set $S$: $R^S_\alpha(x,q)=2\sum_{v\in S}(1+\ell_v(q))\psi(x_v)+\alpha\sum_{(u,a):u\in S}q_{ua}\log q_{ua}$. With $S=V$ this is $R_\alpha$ of §4.2; §5 takes $S$ = the nonisolated vertices.
--   - $D_z(w)=R(w)-R(z)-\langle\nabla R(z),w-z\rangle$, the gradient being the derivative of the formula above on $\mathbb R^V\times\mathbb R^I$ at the interior base $z$.
--   - $K_p(h)=\sum h_{ua}\log(h_{ua}/p_{ua})$ (terms with $h_{ua}=0$ vanish).
--   - **Definition 4.1.** A continuous convex $R$ on $Z$ is $\eta$-area convex for $g$ if for all $z,z',z^+\in Z$ with centroid $c$,
--   $$\eta\langle g(z')-g(z),z'-z^+\rangle\le R(z)+R(z')+R(z^+)-3R(c).$$
--   - **Algorithm 1** (box response): $\mathrm{Resp}_{z,v}(h)_j=\tanh(A_j\operatorname{atanh}x_j+B_j)$, $A=\frac{1+\ell(q)}{1+\ell(h)}$, $B=-\frac{v_x}{2(1+\ell(h))}$, for $z=(x,q)$, $v=(v_x,v_q)$.
--   - $r_8(x,q)=qx^2+8q\log q$ (Lemma 4.2).
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), pp. 13–14, 16–20, §3, §4.1–§4.4, (3.1), (3.3), (4.2), (4.4), Definition 4.1, Algorithm 1

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Graph

/-!
# The saddle-point formulation and the area-convex regularizer (Cohen–Roghani, §3–§4)

For a finite simple graph `G` on `V`:

* `Idx G = V ⊕ G.Dart` is the paper's index set `I = {(u, a) : a ∈ I_u}`,
  `I_u = N(u) ∪ {⊥_u}`: `Sum.inl u` is the dummy coordinate `(u, ⊥_u)` and `Sum.inr d`
  is the coordinate `(u, v)` of the dart `d = (u, v)` (mass proposed by `u` to `v`);
  `owner i` is the vertex `u` of the block containing `i`.
* `InQ G q` (`q ∈ Q`): `q ≥ 0` with `∑_{a ∈ I_u} q_{ua} = 1` for every `u`;
  `InQInterior G q` (`q ∈ Q°`): all coordinates positive and the block sums `1`;
  `InX x` (`x ∈ X = [-1, 1]^V`); `InZ G z` (`z ∈ Z = X × Q`).
* `load G q v = ℓ_v(q) = ∑_{u ∈ N(v)} q_{uv}` (3.1), `acceptedMass G q = P(q)`,
  `objF G x q = F(x, q)` (3.3), `adjL G x = L* x` (`(L* x)_{uv} = x_v`, `(L* x)_{u⊥} = 0`),
  `bvec G = L* 1`, `gOp G z = g(x, q) = (1 - Lq, L* x - b)` (4.2), `ip G` the inner product.
* `psi` is `ψ(x) = ((1 + x) log(1 + x) + (1 - x) log(1 - x)) / 2` (4.4), with natural
  logarithms; `Real.log 0 = 0` gives the convention `0 log 0 = 0`.
* `regR G S α z = 2 ∑_{v ∈ S} (1 + ℓ_v(q)) ψ(x_v) + α ∑_{owner i ∈ S} q_i log q_i`; with
  `S = univ` this is `R_α` of §4.2, and §5 uses `S` = the nonisolated vertices.
* `bregman G S α z w = R(w) - R(z) - ⟨∇R(z), w - z⟩` (the derivative is `fderiv` of the
  formula of `R` on `(V → ℝ) × (Idx G → ℝ)`), `D^α_z(w)` for an interior base `z`.
* `relEnt G S p h = K_p(h) = ∑ h_i log(h_i / p_i)`.
* `IsAreaConvex G η R`: Definition 4.1 on `Z`.
* `resp G z v h = Resp_{z,v}(h)` (Algorithm 1): `y = tanh(A artanh x + B)` with
  `A = (1 + ℓ(q)) / (1 + ℓ(h))`, `B = -v_x / (2 (1 + ℓ(h)))`.
* `r8 x q = q x² + 8 q log q` (Lemma 4.2).
-/

namespace OptimalLCA.Matching

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The index set `I`: dummies `inl u` and darts `inr (u, v)`. -/
abbrev Idx (G : SimpleGraph V) := V ⊕ G.Dart

/-- The vertex whose block contains the index. -/
def owner {G : SimpleGraph V} : Idx G → V
  | .inl u => u
  | .inr d => d.fst

/-- The state space `ℝ^V × ℝ^I`. -/
abbrev StateSpace (G : SimpleGraph V) := (V → ℝ) × (Idx G → ℝ)

/-- `ψ(x) = ((1 + x) log(1 + x) + (1 - x) log(1 - x)) / 2` (4.4). -/
noncomputable def psi (x : ℝ) : ℝ :=
  ((1 + x) * Real.log (1 + x) + (1 - x) * Real.log (1 - x)) / 2

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `q ∈ Q`: a probability vector on every block `I_u`. -/
def InQ (q : Idx G → ℝ) : Prop :=
  (∀ i, 0 ≤ q i) ∧ ∀ u : V, ∑ i ∈ univ.filter (fun i : Idx G => owner i = u), q i = 1

/-- `q ∈ Q°`: all coordinates positive, block sums one. -/
def InQInterior (q : Idx G → ℝ) : Prop :=
  (∀ i, 0 < q i) ∧ ∀ u : V, ∑ i ∈ univ.filter (fun i : Idx G => owner i = u), q i = 1

/-- `x ∈ X = [-1, 1]^V`. -/
def InX (x : V → ℝ) : Prop := ∀ v, x v ∈ Set.Icc (-1 : ℝ) 1

/-- `z ∈ Z = X × Q`. -/
def InZ (z : StateSpace G) : Prop := InX z.1 ∧ InQ G z.2

/-- An interior base `z ∈ (-1, 1)^V × Q°`. -/
def IsInteriorBase (z : StateSpace G) : Prop :=
  (∀ v, z.1 v ∈ Set.Ioo (-1 : ℝ) 1) ∧ InQInterior G z.2

/-- The load `ℓ_v(q) = ∑_{u ∈ N(v)} q_{uv}` (3.1). -/
def load (q : Idx G → ℝ) (v : V) : ℝ :=
  ∑ d ∈ univ.filter (fun d : G.Dart => d.snd = v), q (Sum.inr d)

/-- The accepted mass `P(q) = ∑_v min{1, ℓ_v(q)}`. -/
noncomputable def acceptedMass (q : Idx G → ℝ) : ℝ :=
  ∑ v, min 1 (load G q v)

/-- The objective `F(x, q) = ∑_v [x_v + ℓ_v(q)(1 - x_v)]` (3.3). -/
def objF (x : V → ℝ) (q : Idx G → ℝ) : ℝ :=
  ∑ v, (x v + load G q v * (1 - x v))

/-- The adjoint `L*`: `(L* x)_{uv} = x_v`, `(L* x)_{u⊥} = 0`. -/
def adjL (x : V → ℝ) : Idx G → ℝ
  | .inl _ => 0
  | .inr d => x d.snd

/-- `b = L* 1`, the indicator of the non-dummy coordinates. -/
def bvec : Idx G → ℝ := adjL G (fun _ => 1)

/-- The descent–ascent operator `g(x, q) = (1 - Lq, L* x - b)` (4.2). -/
def gOp (z : StateSpace G) : StateSpace G :=
  (fun v => 1 - load G z.2 v, fun i => adjL G z.1 i - bvec G i)

/-- The inner product `⟨(x, p), (y, h)⟩ = ⟨x, y⟩ + ⟨p, h⟩`. -/
def ip (z w : StateSpace G) : ℝ :=
  ∑ v, z.1 v * w.1 v + ∑ i, z.2 i * w.2 i

/-- The regularizer `2 ∑_{v ∈ S} (1 + ℓ_v(q)) ψ(x_v) + α ∑_{owner i ∈ S} q_i log q_i`;
`S = univ` gives `R_α` (§4.2). -/
noncomputable def regR (S : Finset V) (α : ℝ) (z : StateSpace G) : ℝ :=
  2 * ∑ v ∈ S, (1 + load G z.2 v) * psi (z.1 v) +
    α * ∑ i ∈ univ.filter (fun i : Idx G => owner i ∈ S), z.2 i * Real.log (z.2 i)

/-- The Bregman divergence `D_z(w) = R(w) - R(z) - ⟨∇R(z), w - z⟩` of `regR G S α`. -/
noncomputable def bregman (S : Finset V) (α : ℝ) (z w : StateSpace G) : ℝ :=
  regR G S α w - regR G S α z - fderiv ℝ (regR G S α) z (w - z)

/-- The relative entropy `K_p(h) = ∑_{owner i ∈ S} h_i log(h_i / p_i)`. -/
noncomputable def relEnt (S : Finset V) (p h : Idx G → ℝ) : ℝ :=
  ∑ i ∈ univ.filter (fun i : Idx G => owner i ∈ S), h i * Real.log (h i / p i)

/-- Definition 4.1: a continuous convex `R` on `Z` is `η`-area convex for `g`. -/
def IsAreaConvex (η : ℝ) (R : StateSpace G → ℝ) : Prop :=
  ContinuousOn R {z | InZ G z} ∧ ConvexOn ℝ {z | InZ G z} R ∧
    ∀ z z' zp : StateSpace G, InZ G z → InZ G z' → InZ G zp →
      η * ip G (gOp G z' - gOp G z) (z' - zp) ≤
        R z + R z' + R zp - 3 * R ((1 / 3 : ℝ) • (z + z' + zp))

/-- The box response `Resp_{z,v}(h)` of Algorithm 1:
`y = tanh(A artanh x + B)`, `A = (1 + ℓ(q)) / (1 + ℓ(h))`, `B = -v_x / (2 (1 + ℓ(h)))`. -/
noncomputable def resp (z v : StateSpace G) (h : Idx G → ℝ) : V → ℝ := fun j =>
  Real.tanh ((1 + load G z.2 j) / (1 + load G h j) * Real.artanh (z.1 j) +
    -(v.1 j) / (2 * (1 + load G h j)))

end Defs

/-- `r₈(x, q) = q x² + 8 q log q` (Lemma 4.2). -/
noncomputable def r8 (x q : ℝ) : ℝ := q * x ^ 2 + 8 * q * Real.log q

end OptimalLCA.Matching


