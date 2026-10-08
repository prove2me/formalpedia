-- Prove2me | Definitions.Def_GivenDegreeSeq_GraphLimit_HomDensity
-- name    : GivenDegreeSeq_GraphLimit_HomDensity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T05:42:53.20918+00:00
-- url     : https://prove2.me/theorems/2cd2e9b9-48c8-40e7-b546-9c106b8897b5
-- title:
--   Homomorphism densities $t(H,G)$, $t(H,W)$, graph-limit convergence, and the logistic graphon $W_g$
-- statement:
--   Let $H$ be a finite simple graph with vertex set $[k]=\{1,\dots,k\}$ and edge set $E(H)$, and $G$ a simple graph on $n$ vertices.
--
--   1. The **homomorphism density** of $H$ in $G$ is
--   $$t(H,G):=\frac{|\hom(H,G)|}{|V(G)|^{|V(H)|}}=\frac{|\hom(H,G)|}{n^k}, \tag{1}$$
--   where $\hom(H,G)$ is the set of edge-preserving maps $V(H)\to V(G)$.
--   2. For a function $W:[0,1]^2\to\mathbb R$,
--   $$t(H,W):=\int_{[0,1]^k}\prod_{\{i,j\}\in E(H)}W(x_i,x_j)\,dx_1\cdots dx_k,$$
--   with one factor for each edge of $H$.
--   3. A sequence of graphs $G_n$ on $n$ vertices **converges to the limit graph represented by $W$** if $t(H,G_n)\to t(H,W)$ as $n\to\infty$ for every finite simple graph $H$.
--   4. For $g:[0,1]\to\mathbb R$, the **logistic graphon** of $g$ is
--   $$W_g(x,y):=\frac{e^{g(x)+g(y)}}{1+e^{g(x)+g(y)}}.$$
--
--   These are the objects of the Lovász–Szegedy theory of dense graph limits as quoted on pp. 2–3 of the paper, together with the limit object of Theorem 1.1.
--
--   **Formalization Note** $H$ is a `SimpleGraph (Fin k)` and $G$ a `SimpleGraph (Fin n)`; every finite simple graph is isomorphic to one on some `Fin k` and $t(H,\cdot)$, $t(H,W)$ are invariant under relabelling $H$, so quantifying over graphs on `Fin k` loses nothing. $|\hom(H,G)|$ is the number of maps $\varphi:$ `Fin k → Fin n` with $H.\mathrm{Adj}\,i\,j\Rightarrow G.\mathrm{Adj}\,(\varphi i)\,(\varphi j)$. In $t(H,W)$ each edge $\{i,j\}$ contributes the single factor $W(x_i,x_j)$ with $i<j$; for symmetric $W$ (such as $W_g$) the orientation is immaterial. The integral is the Lebesgue integral over the cube $[0,1]^k\subseteq\mathbb R^k$; functions are `ℝ → ℝ → ℝ` and only their values on $[0,1]^2$ enter. At $n=0$ the density has the junk value $|\hom|/0^k$, which is irrelevant to limits.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 2–3 (§1.1, Eq. (1), t(H,W) and graph-limit convergence) and p. 5 (Theorem 1.1, W)

import Mathlib

namespace GivenDegreeSeq.GraphLimit

/-! Chatterjee, Diaconis & Sly, *Random Graphs with a Given Degree Sequence*,
arXiv:1005.1136v5, pp. 2–3 (quoting Lovász–Szegedy): homomorphism densities `t(H, G)` (1),
the densities `t(H, W)` of a symmetric function `W : [0,1]² → [0,1]`, convergence of a graph
sequence to the limit represented by `W`; p. 5: the logistic function
`W(x, y) = e^{g(x)+g(y)}/(1 + e^{g(x)+g(y)})` of Theorem 1.1.

A finite simple graph `H` with `V(H) = [k]` is `H : SimpleGraph (Fin k)`; a graph on `n`
vertices is `G : SimpleGraph (Fin n)`. Every finite simple graph is isomorphic to one on some
`Fin k`, and `t(H, ·)` is invariant under relabelling `H`, so this loses nothing. -/

open Classical in
/-- The homomorphism density (1), p. 3:
`t(H, G) = |hom(H, G)| / |V(G)|^{|V(H)|}`, where `hom(H, G)` is the set of edge-preserving maps
`V(H) → V(G)`, i.e. maps `φ : Fin k → Fin n` with `H.Adj i j → G.Adj (φ i) (φ j)` (these are
exactly Mathlib's graph homomorphisms `H →g G`). -/
noncomputable def homDensity {k n : ℕ} (H : SimpleGraph (Fin k)) (G : SimpleGraph (Fin n)) : ℝ :=
  ((Finset.univ.filter
      (fun φ : Fin k → Fin n => ∀ i j, H.Adj i j → G.Adj (φ i) (φ j))).card : ℝ) /
    (n : ℝ) ^ k

open Classical in
/-- `t(H, W) = ∫_{[0,1]^k} ∏_{(i,j) ∈ E(H)} W(x_i, x_j) dx_1 ⋯ dx_k` (p. 3), with one factor per
(unordered) edge of `H`: the edge `{i, j}` is listed once, as the ordered pair with `i < j`. For a
symmetric `W` the choice of orientation is immaterial. The integral is the Lebesgue integral over
the cube `[0,1]^k ⊆ ℝ^k`. -/
noncomputable def tW {k : ℕ} (H : SimpleGraph (Fin k)) (W : ℝ → ℝ → ℝ) : ℝ :=
  ∫ x in Set.pi Set.univ (fun _ : Fin k => Set.Icc (0 : ℝ) 1),
    ∏ i : Fin k, ∏ j : Fin k, (if i < j ∧ H.Adj i j then W (x i) (x j) else 1)

/-- A sequence of graphs `G_n` on `n` vertices **converges to the limit graph represented by `W`**
(p. 3, the definition of Lovász–Szegedy): `t(H, G_n) → t(H, W)` as `n → ∞` for every finite
simple graph `H`. -/
def ConvergesTo (Gs : (n : ℕ) → SimpleGraph (Fin n)) (W : ℝ → ℝ → ℝ) : Prop :=
  ∀ (k : ℕ) (H : SimpleGraph (Fin k)),
    Filter.Tendsto (fun n => homDensity H (Gs n)) Filter.atTop (nhds (tW H W))

/-- The logistic function of Theorem 1.1 (p. 5): `W(x, y) = e^{g(x)+g(y)}/(1 + e^{g(x)+g(y)})`.
It is symmetric and takes values in `(0, 1)`. -/
noncomputable def Wg (g : ℝ → ℝ) (x y : ℝ) : ℝ :=
  Real.exp (g x + g y) / (1 + Real.exp (g x + g y))

end GivenDegreeSeq.GraphLimit


