-- Prove2me | Definitions.Def_SpatialDemandEq_Optimal_Supplement_Model
-- name    : SpatialDemandEq_Optimal_Supplement_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T06:36:55.17845+00:00
-- url     : https://prove2.me/theorems/281f53ad-5acb-4bad-94fb-06c64d5d7453
-- title:
--   §3.2–3.3, pp. 7–11 — waiting cost f_k with value ∞, problem (4) and w̄, the bound w̄*, the box 𝒲, the map φ, ∂A_j/∂w_k and the matrix D
-- statement:
--   These objects extend the published spatial service model (region $\mathcal S$, demand $\nu$, distances $d_k$, weighted Voronoi cells $\mathcal A_k(w)$ with areas $A_k(w) = \nu(\mathcal A_k(w))$, constants $c,\lambda$, service rates $\mu \in \mathbb R^K$) by the objects of §3.2–3.3.
--
--   **Waiting cost.** For facility $k$, the scaled waiting-time function with values in $\overline{\mathbb R}$ is
--   $$f_k(A) = \begin{cases} \dfrac{c}{\mu_k - \lambda A} & \text{if } A < \mu_k/\lambda, \\[4pt] +\infty & \text{otherwise.} \end{cases}$$
--
--   **Problem (4).** With the simplex $\Delta = \{a \in \mathbb R^K : a \ge 0,\ \sum_k a_k = 1\}$, the optimal value of (4) is
--   $$\bar w = \sup_{a \in \Delta}\ \min_k f_k(a_k) \in \overline{\mathbb R}.$$
--
--   **The box and the map.** Let
--   $$\bar w^* = \max\Bigl\{1 + \bar w + \sup_{x \in \mathcal S,\ j,k} |d_j(x) - d_k(x)|,\ \max_k f_k(0)\Bigr\},$$
--   $\mathcal W = \{w \in \mathbb R^K : 0 \le w_k \le \bar w^*,\ k = 1,\dots,K\}$, and
--   $$\phi_k(w) = \min\{f_k(A_k(w)),\ \bar w^*\}.$$
--
--   **Derivatives and the matrix $D$.** At a weight vector $w$, $\partial A_j/\partial w_k$ is the derivative of the area map $w \mapsto A_j(w)$ at $w$ in the direction of the $k$-th unit vector, and
--   $$D_{jk} = \frac{\lambda c}{(\mu_j - \lambda A_j(w))^2}\,\frac{\partial A_j}{\partial w_k}.$$
--
--   These objects carry the existence argument of §3.2 (Lemma 2, Theorem 1) and the comparative statics of §3.3 (Lemma 1 parts 3–4, Lemma 4, Theorem 3).
--
--   **Formalization Note** $f_k$ takes values in `EReal` and equals $+\infty$ exactly when $\lambda A \ge \mu_k$ (no junk real value). $\bar w$ and the spread $\sup|d_j - d_k|$ are suprema in `EReal`; $\bar w^*$ is formed in `EReal` and then converted to a real number, which is faithful whenever it is finite: under $\mu_k > 0$ and $\sum_k \mu_k > \lambda$ (Lemma 2) and for a metric distance, every term is finite (otherwise `toReal` would return $0$; Theorem 1 keeps those hypotheses). $\phi_k(w)$ is the real number $\min\{f_k(A_k(w)), \bar w^*\}$. $\partial A_j/\partial w_k$ is the Fréchet derivative applied to the basis vector `Pi.single k 1`; it is meaningful where the area map is differentiable, which every statement using it assumes. In $D_{jk}$, Lean's convention $x/0 = 0$ applies when $\mu_j = \lambda A_j(w)$, where the paper's formula is undefined.
-- source:
--   Carlsson, Peng & Ryzhov, Demand Equilibria in Spatial Service Systems, SSRN preprint 4794156 (version of 2024-04-14), p. 7 (f_k of (1)), p. 8 (∂A_k/∂w_j, Lemma 1), p. 9 (properties of f_k, problem (4), 𝒲, w̄*, φ), p. 11 (matrix D of Lemma 4)

import Mathlib
import Definitions.Def_SpatialDemandEq_Optimal_Model

namespace SpatialDemandEq.Optimal.Supplement

open MeasureTheory SpatialDemandEq.Optimal

/-- The scaled waiting-time function of facility `k` (p. 7 and p. 9), with values in the extended
reals: `f_k(A) = c/(μ_k − λA)` if `A < μ_k/λ` (written `λA < μ_k`), and `f_k(A) = +∞` otherwise. -/
noncomputable def waitCost {K : ℕ} (c lam : ℝ) (μ : Fin K → ℝ) (k : Fin K) (A : ℝ) : EReal :=
  if lam * A < μ k then ((c / (μ k - lam * A) : ℝ) : EReal) else ⊤

/-- The feasible set of problem (4), p. 9: vectors `a ∈ ℝ^K` with `a ≥ 0` and `∑_k a_k = 1`. -/
def simplex (K : ℕ) : Set (Fin K → ℝ) :=
  {a | (∀ k, 0 ≤ a k) ∧ ∑ k, a k = 1}

/-- The optimal value `w̄` of problem (4), p. 9: `max_a min_k f_k(a_k)` over the simplex, taken
as a supremum in the extended reals. -/
noncomputable def wbar {K : ℕ} (c lam : ℝ) (μ : Fin K → ℝ) : EReal :=
  ⨆ a ∈ simplex K, ⨅ k, waitCost c lam μ k (a k)

/-- `sup_{x ∈ S, j, k} |d_j(x) − d_k(x)|` (p. 9), in the extended reals. -/
noncomputable def distSpread {n K : ℕ} (S : Set (E n)) (d : Fin K → E n → ℝ) : EReal :=
  ⨆ x ∈ S, ⨆ j, ⨆ k, ((|d j x - d k x| : ℝ) : EReal)

/-- The bound `w̄* = max{1 + w̄ + sup_{x∈S,j,k} |d_j(x) − d_k(x)|, max_k f_k(0)}` of p. 9, formed
in the extended reals and converted to a real number (it is finite whenever `w̄ < ∞`, all
`μ_k > 0` and the spread is finite). -/
noncomputable def wbarStar {n K : ℕ} (S : Set (E n)) (d : Fin K → E n → ℝ) (c lam : ℝ)
    (μ : Fin K → ℝ) : ℝ :=
  (max (1 + wbar c lam μ + distSpread S d) (⨆ k, waitCost c lam μ k 0)).toReal

/-- The compact set `𝒲 = {w ∈ ℝ^K : 0 ≤ w_k ≤ w̄*, k = 1, …, K}` of p. 9. -/
def boxW {n K : ℕ} (S : Set (E n)) (d : Fin K → E n → ℝ) (c lam : ℝ) (μ : Fin K → ℝ) :
    Set (Fin K → ℝ) :=
  {w | ∀ k, 0 ≤ w k ∧ w k ≤ wbarStar S d c lam μ}

/-- The truncated map `φ_k(w) = min{f_k(A_k(w)), w̄*}` of p. 9, where
`A_k(w) = ν(𝒜_k(w))` is the area of the weighted Voronoi cell. -/
noncomputable def phi {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (d : Fin K → E n → ℝ)
    (c lam : ℝ) (μ : Fin K → ℝ) (w : Fin K → ℝ) (k : Fin K) : ℝ :=
  (min (waitCost c lam μ k (area ν (cell S d w k))) ((wbarStar S d c lam μ : ℝ) : EReal)).toReal

/-- The partial derivative `∂A_j/∂w_k` at `w` (p. 8): the Fréchet derivative of the area map
`w ↦ A_j(w) = ν(𝒜_j(w))` at `w`, applied to the `k`-th basis vector. -/
noncomputable def partialArea {n K : ℕ} (ν : Measure (E n)) (S : Set (E n))
    (d : Fin K → E n → ℝ) (w : Fin K → ℝ) (j k : Fin K) : ℝ :=
  fderiv ℝ (fun w' : Fin K → ℝ => area ν (cell S d w' j)) w (Pi.single k 1)

/-- The matrix `D` of Lemma 4, p. 11:
`D_jk = λc/(μ_j − λA_j(w))² · ∂A_j/∂w_k`. -/
noncomputable def Dmat {n K : ℕ} (ν : Measure (E n)) (S : Set (E n)) (d : Fin K → E n → ℝ)
    (c lam : ℝ) (μ : Fin K → ℝ) (w : Fin K → ℝ) : Matrix (Fin K) (Fin K) ℝ :=
  Matrix.of fun j k =>
    lam * c / (μ j - lam * area ν (cell S d w j)) ^ 2 * partialArea ν S d w j k

end SpatialDemandEq.Optimal.Supplement


