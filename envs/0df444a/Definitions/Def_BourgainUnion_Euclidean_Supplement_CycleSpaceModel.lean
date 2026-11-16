-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_Supplement_CycleSpaceModel
-- name    : BourgainUnion_Euclidean_Supplement_CycleSpaceModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:48.424533+00:00
-- url     : https://prove2.me/theorems/cf547dcd-e3ac-4a0f-9d2e-0ccdcba11290
-- title:
--   The cycle-space construction of Section 5
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with an orientation: every edge $e=(u,v)$ goes from $u$ to $v$. On $\mathbb R^E$:
--
--   1. the **net inflow** $\partial:\mathbb R^E\to\mathbb R^V$, $(\partial x)_w=\sum_{e\text{ into }w}x_e-\sum_{e\text{ out of }w}x_e$, and the **cycle space** $Z=\ker\partial$;
--   2. the norm (20), with $g$ the girth of $G$:
--   $$\|x\|_W=\inf_{z\in Z}\Bigl(\|z\|_2+\frac{\|x-z\|_1}{\sqrt g}\Bigr);$$
--   3. the family $\mathcal P$ of linear maps $P:\mathbb R^E\to Z$ fixing $Z$, the norm $\|P\|_{W\to Z}=\sup_{w\ne0}\|Pw\|_W/\|w\|_W$ (where $Z$ carries the norm inherited from $W$), and the **relative projection constant** $\lambda(Z,W)=\inf_{P\in\mathcal P}\|P\|_{W\to Z}$.
--
--   Given a spanning tree $T$ of $G$ and a root $o$: $p_v\in\mathbb R^E$ is the signed indicator of the tree path from $o$ to $v$ ($+1$ on edges traversed along their orientation, $-1$ against it); $D$ is the depth of $T$ from $o$; for each non-tree edge $e_j=(u_j,v_j)$, $c_j=p_{u_j}+e_j-p_{v_j}$, and $Ca=\sum_j a_jc_j$ for integer vectors $a$ indexed by the non-tree edges. For an integer $N\ge1$, the cells are $U_{v,N}=\{p_v+Ca: a\in\{-N,\dots,N\}^r\}$, $X_N=\bigcup_vU_{v,N}$ with the metric of $\|\cdot\|_W$, and $A_N=U_{o,N}$. Finally $e(A_N)$ is the least $L\ge0$ for which some $F:X_N\to Z$ with $F(Ca)=Ca$ on $A_N$ satisfies $\|F(x)-F(y)\|_W\le L\|x-y\|_W$ on $X_N$.
--
--   **Formalization Note** The orientation picks one dart per edge. The tree path is the unique path of the tree, obtained from Mathlib's `IsTree.existsUnique_path`. The non-tree edges index the coordinates of $\mathbb Z^r$ directly. $\|P\|_{W\to Z}$, $\lambda(Z,W)$ and $e(A_N)$ are computed in $[0,\infty]$.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 23–24, §§5.1–5.4, equation (20), definitions of P, λ(Z, W), p_v, c_j, C, B_N, U_{v,N}, X_N, A_N, e(A_N)

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean.Supplement

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- §5.1, p. 23: an orientation of the simple graph `G` picks, for each edge, one of its two
darts; the edge then goes from the dart's first vertex (its tail) to its second (its head). -/
structure Orientation (G : SimpleGraph V) where
  dart : G.edgeSet → G.Dart
  edge_eq : ∀ e, (dart e).edge = e

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The net inflow map `∂ : ℝ^E → ℝ^V`, `(∂x)_w = Σ_{e into w} x_e − Σ_{e out of w} x_e`. -/
def inflow (O : Orientation G) : (G.edgeSet → ℝ) →ₗ[ℝ] (V → ℝ) :=
  LinearMap.pi fun w => ∑ e : G.edgeSet,
    ((if (O.dart e).snd = w then (1:ℝ) else 0) - (if (O.dart e).fst = w then (1:ℝ) else 0)) •
      LinearMap.proj e

/-- The cycle space `Z = ker ∂ ⊆ ℝ^E`. -/
def cycleSpace (O : Orientation G) : Submodule ℝ (G.edgeSet → ℝ) := LinearMap.ker (inflow O)

/-- The Euclidean norm `‖x‖₂` on `ℝ^E`. -/
def l2 (x : G.edgeSet → ℝ) : ℝ := Real.sqrt (∑ e, x e ^ 2)

/-- The `ℓ₁` norm `‖x‖₁` on `ℝ^E`. -/
def l1 (x : G.edgeSet → ℝ) : ℝ := ∑ e, |x e|

/-- The norm (20), p. 24: `‖x‖_W = inf_{z ∈ Z} (‖z‖₂ + ‖x − z‖₁ / √g)`, `g` the girth of `G`. -/
def normW (O : Orientation G) (x : G.edgeSet → ℝ) : ℝ :=
  ⨅ z : cycleSpace O, (l2 (z : G.edgeSet → ℝ) + l1 (x - (z : G.edgeSet → ℝ)) / Real.sqrt (G.girth : ℝ))

/-- The family `𝒫` of §5.3: linear maps `ℝ^E → Z` that fix `Z` (written as endomorphisms of
`ℝ^E` with range in `Z`). -/
def IsCycleProjection (O : Orientation G) (P : (G.edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ)) : Prop :=
  (∀ w, P w ∈ cycleSpace O) ∧ ∀ z ∈ cycleSpace O, P z = z

/-- `‖P‖_{W→Z} = sup_{w ≠ 0} ‖Pw‖ / ‖w‖_W` (p. 23), with `Z` carrying the norm inherited from
`W`; computed in `ℝ≥0∞`. -/
def opNormW (O : Orientation G) (P : (G.edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ)) : ℝ≥0∞ :=
  ⨆ w : {w : G.edgeSet → ℝ // w ≠ 0}, ENNReal.ofReal (normW O (P w) / normW O w)

/-- The relative projection constant `λ(Z, W) = inf_{P ∈ 𝒫} ‖P‖_{W→Z}` (p. 23). -/
def projConst (O : Orientation G) : ℝ≥0∞ :=
  ⨅ P : {P : (G.edgeSet → ℝ) →ₗ[ℝ] (G.edgeSet → ℝ) // IsCycleProjection O P}, opNormW O P.1

/-- The indicator vector of an edge, `e ∈ ℝ^E`. -/
def edgeVec (e : G.edgeSet) : G.edgeSet → ℝ := Pi.single e 1

/-- The signed indicator in `ℝ^E` of a walk: `+1` per traversal of an edge along its orientation,
`−1` per traversal against it. -/
def walkVec (O : Orientation G) {a b : V} (p : G.Walk a b) : G.edgeSet → ℝ :=
  fun e => (p.darts.map fun d =>
    if d = O.dart e then (1:ℝ) else if d = (O.dart e).symm then -1 else 0).sum

/-- `p_v` (p. 23): the signed indicator of the path from the root `o` to `v` in the spanning tree
`T ≤ G`. -/
def pathVec (O : Orientation G) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (o v : V) :
    G.edgeSet → ℝ :=
  walkVec O (((hT.existsUnique_path o v).exists.choose).mapLe hTG)

/-- The depth of the spanning tree `T` from the root `o`. -/
def treeDepth (T : SimpleGraph V) (o : V) : ℕ := Finset.univ.sup fun v => T.dist o v

/-- The non-tree edges `e_j`, indexing the coordinates of `ℤ^r`. -/
abbrev NonTree (G : SimpleGraph V) (T : SimpleGraph V) : Type _ := {e : G.edgeSet // e.1 ∉ T.edgeSet}

open Classical in
/-- `C a = Σ_j a_j c_j` with `c_j = p_{u_j} + e_j − p_{v_j}` for the non-tree edge
`e_j = (u_j, v_j)` (p. 23). -/
def cycleComb (O : Orientation G) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (o : V)
    (a : NonTree G T → ℤ) : G.edgeSet → ℝ :=
  ∑ j : NonTree G T, (a j : ℝ) • (pathVec O hTG hT o (O.dart j.1).fst + edgeVec j.1 -
      pathVec O hTG hT o (O.dart j.1).snd)

/-- The cell `U_{v,N} = {p_v + C a : a ∈ {−N, …, N}^r}` (p. 24). -/
def cell (O : Orientation G) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (o : V) (N : ℕ)
    (v : V) : Set (G.edgeSet → ℝ) :=
  {x | ∃ a : NonTree G T → ℤ, (∀ j, |a j| ≤ (N : ℤ)) ∧
    x = pathVec O hTG hT o v + cycleComb O hTG hT o a}

/-- `X_N = ⋃_v U_{v,N}`. -/
def cellUnion (O : Orientation G) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (o : V)
    (N : ℕ) : Set (G.edgeSet → ℝ) :=
  ⋃ v, cell O hTG hT o N v

/-- `e(A_N)` (p. 24): the optimal Lipschitz constant, for the metric of `‖·‖_W`, of an extension
`F : X_N → Z` of `ϕ(Ca) = Ca` from `A_N = U_{o,N}`; computed in `ℝ≥0∞`. -/
def cellExtConst (O : Orientation G) {T : SimpleGraph V} (hTG : T ≤ G) (hT : T.IsTree) (o : V)
    (N : ℕ) : ℝ≥0∞ :=
  sInf {q | ∃ L : ℝ, 0 ≤ L ∧ (∃ F : (G.edgeSet → ℝ) → (G.edgeSet → ℝ),
      (∀ x ∈ cellUnion O hTG hT o N, F x ∈ cycleSpace O) ∧
      (∀ x ∈ cell O hTG hT o N o, F x = x) ∧
      ∀ x ∈ cellUnion O hTG hT o N, ∀ y ∈ cellUnion O hTG hT o N,
        normW O (F x - F y) ≤ L * normW O (x - y)) ∧
    q = ENNReal.ofReal L}

end BourgainUnion.Euclidean.Supplement


