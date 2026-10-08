-- Prove2me | Definitions.Def_NesterovRCD_Adaptive_RACDM
-- name    : NesterovRCD_Adaptive_RACDM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:37.951288+00:00
-- url     : https://prove2.me/theorems/5f2f62a3-a343-4779-8d3a-4926a28b028a
-- title:
--   RACDM$(x_0)$ (6.1): trial points, the doubling loop, one iteration, the run along given draws, and the count $N_k$
-- statement:
--   These are the objects of §6.1 of Nesterov's paper, the **random adaptive coordinate descent method** RACDM$(x_0)$. Throughout, $f:\mathbb R^n\to\mathbb R$ is differentiable, $\nabla_i f(x)=\partial f/\partial x_i(x)$, and $e_i$ is the $i$-th standard basis vector. The method does not know the coordinate Lipschitz constants $L_i$ of (2.2); it keeps estimates $\hat L_1,\dots,\hat L_n$, which start at given values $\hat L_i:=L_i^0$.
--
--   1. **Trial point.** For a point $x$, a coordinate $i$ and an estimate $\ell$,
--   $$T(x,i,\ell)=x-\ell^{-1}\,\nabla_i f(x)\,e_i .$$
--   2. **Doubling loop (step 2 of (6.1)).** Starting from the estimate $\ell=\hat L_i$, the method replaces $\ell$ by $2\ell$ as long as $\nabla_i f(x)\cdot\nabla_i f(T(x,i,\ell))<0$. The number of doublings is therefore
--   $$d(x,i,\ell)=\min\{d\ge0:\ \nabla_i f(x)\cdot\nabla_i f(T(x,i,2^d\ell))\ge0\}.$$
--   The test compares the signs of the same partial derivative at $x$ and at the trial point; it uses no function values.
--   3. **One iteration.** From the state $(x_k,\hat L)$ with drawn coordinate $i=i_k$, let $\ell=2^{d(x_k,i,\hat L_i)}\hat L_i$ be the accepted estimate. Then
--   $$x_{k+1}=T(x_k,i,\ell),\qquad \hat L_i:=\tfrac12\,\ell,$$
--   and the other estimates are unchanged (step 3).
--   4. **The run.** Given the drawn coordinates $i_0,\dots,i_{k-1}$, the run produces the iterate $x_k$ and the estimates $\hat L$ at the beginning of iteration $k$, starting from $(x_0,L^0)$. The paper draws $i_k$ with the uniform counter $\mathcal R_0$ (probability $1/n$ each, (2.5) with $\alpha=0$); the draws enter only through the expectation $\mathbb E$ over them, the published `rcdExpect` with weights $p_0(i)=1/n$.
--   5. **The count $N_k$.** For the draws $i_0,\dots,i_k$, iteration $j$ with $d_j$ doublings computes the partial derivative $\nabla_{i_j}f$ at $d_j+1$ trial points, and
--   $$N_k=\sum_{j=0}^{k}(d_j+1).$$
--
--   These objects are used by every statement of the mission (Theorem 7 and the bounds of its proof).
--
--   **Formalization Note** $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` (scalar coordinates: the paper sets $N=n$ in §6.1), coordinates are indexed $0,\dots,n-1$ for the paper's $1,\dots,n$, and the gradient is an explicit map $g$ with $g(x)=\nabla f(x)$, as in the published definition `ConvexOptAlg_CoordDescent_Defs` that this mission reuses (its `IsCoordSmooth f g L` is (2.2) with one-dimensional blocks and $|\cdot|$ as block norm; it includes differentiability). The paper's step 3 reads "Set $L_{i_k}:=\frac12L_{i_k}$"; this is a typo for $\hat L_{i_k}:=\frac12\hat L_{i_k}$ (the proof says "after execution of Step 3, we have again $\hat L_{i_k}\le L_{i_k}$", and uses $\hat L'_i=\frac12\cdot2^{p_i(j)-1}\hat L_i$ on p. 19); the true constants never change. The number of doublings is a minimum over $\mathbb N$ (`sInf`); it would be $0$ if no $d$ passed the test, but under (2.2) and $0<\hat L_i\le L_i$ the loop terminates (milestone (6.4)). The count $N_k$ counts the evaluations of $\nabla_{i_j}f$ at trial points, $p_{i_j}(j)=d_j+1$, which is the count fixed by the proof of Theorem 7 ($\hat L'_i=\frac12\cdot2^{p_i(j)-1}\hat L_i$); counting $\nabla_{i_j}f(x_j)$ as well would add one per iteration.
-- source:
--   Nesterov, Efficiency of coordinate descent methods on huge-scale optimization problems, CORE Discussion Paper 2010/2, pp. 17–19, §6.1: Method RACDM(x_0) (6.1), p. 18; the count N_k of Theorem 7, item 3, and p_i(j) in its proof, pp. 18–19

import Mathlib
import Definitions.Def_ConvexOptAlg_CoordDescent_Defs

namespace NesterovRCD.Adaptive

open ConvexOptAlg.CoordDescent

/-- ℝⁿ with scalar coordinates ("For the sake of notation, we assume that N = n", p. 18):
the Euclidean space of the published `ConvexOptAlg.CoordDescent` objects. Coordinates are
indexed by `Fin n` (0-based) for the paper's `1, …, n`. -/
abbrev Vec (n : ℕ) := EuclideanSpace ℝ (Fin n)

variable {n : ℕ}

/-- The trial point `x − ℓ⁻¹ · ∇_i f(x) · e_i` of step 2 of RACDM (6.1), p. 18, where
`g x = ∇f(x)` and `ℓ` is the current estimate `L̂_i`. -/
noncomputable def trial (g : Vec n → Vec n) (x : Vec n) (i : Fin n) (ℓ : ℝ) : Vec n :=
  x - (ℓ⁻¹ * g x i) • EuclideanSpace.single i 1

/-- The number of doublings performed by the inner `while` loop of step 2 of RACDM (6.1), p. 18,
started at the estimate `ℓ`: the least `d ≥ 0` such that the loop test
`∇_i f(x) · ∇_i f(x − (2^d ℓ)⁻¹ ∇_i f(x) e_i) < 0` fails (the loop doubles the estimate exactly
while the test holds). `ℕ`'s `sInf` is `0` on the empty set; under the hypotheses of Theorem 7 the
set is nonempty (milestone (6.4)). -/
noncomputable def doublings (g : Vec n → Vec n) (x : Vec n) (i : Fin n) (ℓ : ℝ) : ℕ :=
  sInf {d : ℕ | ¬ (g x i * g (trial g x i (2 ^ d * ℓ)) i < 0)}

/-- One iteration of RACDM (6.1), p. 18, on the drawn coordinate `i`, from the state
`(x_k, L̂)`: step 2 accepts the estimate `ℓ = 2^d · L̂_i` (`d` = `doublings`) and sets
`x_{k+1} = x_k − ℓ⁻¹ ∇_i f(x_k) e_i`; step 3 (read as `L̂_i := ½ L̂_i`, see the note) stores
`ℓ / 2` as the new estimate of coordinate `i`; the other estimates are unchanged. -/
noncomputable def racdmStep (g : Vec n → Vec n) (s : Vec n × (Fin n → ℝ)) (i : Fin n) :
    Vec n × (Fin n → ℝ) :=
  let ℓ := 2 ^ doublings g s.1 i (s.2 i) * s.2 i
  (trial g s.1 i ℓ, Function.update s.2 i (ℓ / 2))

/-- RACDM(x₀) (6.1), p. 18, along given draws: `racdm g L0 x0 k idx = (x_k, L̂)` is the iterate
and the vector of estimates at the beginning of iteration `k`, when the coordinates drawn are
`i_0 = idx 0, …, i_{k−1} = idx (k − 1)`; the setup is `L̂ := L⁰`. -/
noncomputable def racdm (g : Vec n → Vec n) (L0 : Fin n → ℝ) (x0 : Vec n) :
    (k : ℕ) → (Fin k → Fin n) → Vec n × (Fin n → ℝ)
  | 0, _ => (x0, L0)
  | k + 1, idx => racdmStep g (racdm g L0 x0 k (Fin.init idx)) (idx (Fin.last k))

/-- The number `N_k` of computations of directional derivatives in the iterations `0, …, k` of
RACDM (6.1) (Theorem 7, item 3, p. 18), along the draws `idx : Fin (k + 1) → Fin n`: iteration `j`
on coordinate `i_j` with `d` doublings costs `p_{i_j}(j) = d + 1` computations of
`∇_{i_j} f(x_{j+1})`, one per trial point tested, as fixed by the proof (p. 19,
`L̂′_i = ½ · 2^{p_i(j)−1} · L̂_i`). -/
noncomputable def numDerivs (g : Vec n → Vec n) (L0 : Fin n → ℝ) (x0 : Vec n) (k : ℕ)
    (idx : Fin (k + 1) → Fin n) : ℕ :=
  ∑ j : Fin (k + 1),
    (doublings g (racdm g L0 x0 j (fun s => idx (Fin.castLE (le_of_lt j.isLt) s))).1 (idx j)
        ((racdm g L0 x0 j (fun s => idx (Fin.castLE (le_of_lt j.isLt) s))).2 (idx j)) + 1)

end NesterovRCD.Adaptive


