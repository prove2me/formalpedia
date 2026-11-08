-- Prove2me | Definitions.Def_ZeroExtensionGap_gapInstance
-- name    : ZeroExtensionGap_gapInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:04:26.13987+00:00
-- url     : https://prove2.me/theorems/e8901908-98c6-4ae9-9cd8-b3f4797a927e
-- title:
--   The integrality gap instance of §4.1 and its cost $\Phi(f)$
-- statement:
--   Let $X$ be the final graph of an expander tower with $N=n^t$ vertices, $\rho:=(\log n)^{(t-1)/(t+1)}$ and $A:=\sigma_1$. The graph $G$ adds, for every $x\in V(X)$, a distinct terminal $x_T$ and a **terminal edge** $\{x,x_T\}$. The terminal metric is $D(x_T,y_T):=d_X(x,y)$, and the weights are
--
--   $$w_e=\begin{cases}2\rho/\ell_1,& e\text{ a level-1 edge of }X,\\ 1/\ell_i,& e\text{ a level-}i\text{ edge of }X,\ 2\le i\le t,\\ 1/A,& e\text{ a terminal edge.}\end{cases}$$
--
--   For a labelling $f:V(X)\to V(X)$, which sends $x$ to the terminal $f(x)_T$, the cost is equation (3):
--
--   $$\Phi(f)=\frac{2\rho}{\ell_1}\sum_{\{x,y\}\in E_1}d_X(f(x),f(y))+\sum_{i=2}^t\frac1{\ell_i}\sum_{\{x,y\}\in E_i}d_X(f(x),f(y))+\frac1A\sum_{x\in V(X)}d_X(x,f(x)).$$
--
--   The lengths determine the metric and the weights determine the objective, and the two must not be confused.
--
--   **Formalization Note.** $V=V(X)\sqcup V(X)$ with terminals on the right. `D` is the real value of the `ℝ≥0∞` distance. On a valid tower $X$ is connected, so it is a metric. The workspace verification file proves that fact, and that the cost of the retraction attached to $f$ is $\Phi(f)$.
-- source:
--   Chen, Zhu, Almost Tight Hardness of Approximation for 0-Extension, STOC 2027 submission (manuscript sha256 0cdea87b…), §4.1, pp.19–20 (PDF pp.21–22); equation (3), p.29 (PDF p.31)

import Mathlib
import Definitions.Def_ZeroExtensionGap_towerGraph

namespace ZeroExtensionGap

/-- `ρ := (log n)^{(t-1)/(t+1)}`, §4.1, p.19 (PDF p.21) (Chen, Zhu, *Almost Tight Hardness of
Approximation for 0-Extension*, STOC 2027 submission, manuscript sha256 0cdea87b…). -/
noncomputable def rho (t n : ℕ) : ℝ := Real.log n ^ (((t : ℝ) - 1) / ((t : ℝ) + 1))

/-- The graph `G` of §4.1, p.19 (PDF p.21): `X` together with, for every vertex `x` of `X`, a distinct
terminal `x_T` and a terminal edge `{x, x_T}`. Vertices of `X` are `Sum.inl`, terminals `Sum.inr`. -/
def gapGraph {W : Type*} (X : SimpleGraph W) : SimpleGraph (W ⊕ W) where
  Adj
    | Sum.inl x, Sum.inl y => X.Adj x y
    | Sum.inl x, Sum.inr y => x = y
    | Sum.inr x, Sum.inl y => x = y
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro (x | x) (y | y) h
    · exact SimpleGraph.Adj.symm h
    · exact Eq.symm h
    · exact Eq.symm h
    · exact h⟩
  loopless := ⟨by
    rintro (x | x) h
    · exact X.irrefl h
    · exact h⟩

/-- The edge weights of §4.1, p.20 (PDF p.22), on an ordered pair of vertices: `2ρ/ℓ_1` on level-1
edges of `X`, `1/ℓ_i` on level-`i` edges (`2 ≤ i ≤ t`), and `1/A` on terminal edges, where
`A := σ_1`. Pairs that are not edges get `0`, and are never read. -/
noncomputable def gapWeight {n : ℕ} (t : ℕ) :
    TowerV n (t - 1) ⊕ TowerV n (t - 1) → TowerV n (t - 1) ⊕ TowerV n (t - 1) → ℝ
  | Sum.inl x, Sum.inl y =>
      if edgeLevel t (t - 1) x y = 1 then 2 * rho t n / ell t n 1
      else 1 / ell t n (edgeLevel t (t - 1) x y)
  | Sum.inl _, Sum.inr _ => 1 / sigma t n 1
  | Sum.inr _, Sum.inl _ => 1 / sigma t n 1
  | Sum.inr _, Sum.inr _ => 0

/-- The vertex of `X` underlying a vertex of `G`: `x` for both `x` and `x_T`. -/
def gapBase {W : Type*} : W ⊕ W → W := Sum.elim id id

/-- The 0-Extension instance `I := (G, w, T, D)` of §4.1, pp.19–20 (PDF pp.21–22), built from the tower
with base graph `H`, threshold `g` and realizations `φ`: `T := {x_T}` and `D(x_T, y_T) := d_X(x, y)`.
**Formalization Note.** `V = V(X) ⊕ V(X)` has `2N` vertices and `T` has `N = n^t` of them. `D` is the
real value of the `ℝ≥0∞` distance; on a valid tower `X` is connected, so the distance is finite and
`D` is a metric. -/
noncomputable def gapInstance {n : ℕ} (t : ℕ) (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n) :
    Instance (TowerV n (t - 1) ⊕ TowerV n (t - 1)) where
  G := gapGraph (towerGraph H g φ (t - 1))
  w e := gapWeight t (edgeTail e) (edgeHead e)
  T := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩
  D a b := (towerDist t H g φ (t - 1) (gapBase a.1) (gapBase b.1)).toReal

open Classical in
/-- `E_i`, the level-`i` edges of the final graph `X`, p.29 (PDF p.31). -/
noncomputable def levelEdges {n : ℕ} (t : ℕ) (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n)
    (i : ℕ) : Finset (Sym2 (TowerV n (t - 1))) :=
  (edgeFin (towerGraph H g φ (t - 1))).filter fun e =>
    edgeLevel t (t - 1) (edgeTail e) (edgeHead e) = i

/-- The cost `Φ(f)` of the integral assignment that sends `x` to the terminal `f(x)_T`, equation (3),
p.29 (PDF p.31):
`(2ρ/ℓ_1) ∑_{E_1} d_X(f x, f y) + ∑_{i=2}^t (1/ℓ_i) ∑_{E_i} d_X(f x, f y) + (1/A) ∑_x d_X(x, f x)`. -/
noncomputable def Phi {n : ℕ} (t : ℕ) (H : SimpleGraph (Fin n)) (g : ℕ) (φ : Realization n)
    (f : TowerV n (t - 1) → TowerV n (t - 1)) : ℝ :=
  2 * rho t n / ell t n 1 * ∑ e ∈ levelEdges t H g φ 1,
      (towerDist t H g φ (t - 1) (f (edgeTail e)) (f (edgeHead e))).toReal +
    ∑ i ∈ Finset.Icc 2 t, 1 / ell t n i * ∑ e ∈ levelEdges t H g φ i,
      (towerDist t H g φ (t - 1) (f (edgeTail e)) (f (edgeHead e))).toReal +
    1 / sigma t n 1 * ∑ x, (towerDist t H g φ (t - 1) x (f x)).toReal

end ZeroExtensionGap


