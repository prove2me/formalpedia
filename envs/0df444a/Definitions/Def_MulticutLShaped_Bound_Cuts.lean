-- Prove2me | Definitions.Def_MulticutLShaped_Bound_Cuts
-- name    : MulticutLShaped_Bound_Cuts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T07:54:59.574986+00:00
-- url     : https://prove2.me/theorems/9f158843-d400-4ef2-b908-a0f7d4478d64
-- title:
--   Simplex-optimal bases of (7) and of the Step 2 LP, the optimality cuts (15)–(16), and the finite cut set of each scenario
-- statement:
--   Fix a two-stage stochastic linear program with fixed recourse and finitely many scenarios $k=1,\dots,K$: first-stage data $A\in\mathbb R^{m_1\times n_1}$, $b$, $c$, recourse matrix $W\in\mathbb R^{m_2\times n_2}$, and for each scenario a cost $q_k\in\mathbb R^{n_2}$, a right-hand side $h_k\in\mathbb R^{m_2}$, a technology matrix $T_k\in\mathbb R^{m_2\times n_1}$ and a probability $p_k$. Vectors multiplying a matrix from the left are row vectors, as in the paper ("transposes have been eliminated").
--
--   **Simplex-optimal basis of Problem $k$ of type (7).** Problem $k$ at the first-stage point $x$ is
--   $$\min\{\,q_k y \mid W y = h_k - T_k x,\ y\ge 0\,\}.$$
--   A basis is an ordered choice of $m_2$ distinct columns of $W$, with basic submatrix $W_B$. It is *simplex-optimal at $x$* when
--   1. $W_B$ is invertible;
--   2. the basic solution is primal feasible: $W_B^{-1}(h_k - T_k x)\ge 0$;
--   3. its simplex multiplier $\pi = q_{k,B} W_B^{-1}$ is dual feasible: $\pi W\le q_k$ componentwise (all reduced costs are nonnegative).
--
--   This is the certificate with which the simplex method stops, and $\pi$ is "the simplex multipliers associated with the optimal solution of Problem $k$".
--
--   **Simplex-optimal basis of the Step 2 feasibility LP.** The feasibility LP of scenario $k$ at $x$ is
--   $$\min\{\,e v^+ + e v^- \mid W y + I v^+ - I v^- = h_k - T_k x,\ y, v^+, v^-\ge 0\,\},\qquad e=(1,\dots,1).$$
--   A basis of $[W\mid I\mid -I]$ is simplex-optimal at $x$ when its basic submatrix is invertible, its basic solution is nonnegative, and its multiplier $\sigma$ satisfies $\sigma[W\mid I\mid -I]\le (0,e,e)$, i.e. $\sigma W\le 0$ and $-1\le\sigma_i\le 1$.
--
--   **Optimality cut.** For a basis $B$ of Problem $k$ with multiplier $\pi$, the cut (15)–(16) is the pair
--   $$E = p_k\,\pi T_k,\qquad e = p_k\,\pi h_k,$$
--   standing for the constraint $E x + \theta_k\ge e$.
--
--   **Cut set of scenario $k$.** $\mathcal C_k$ is the finite set of cuts $(p_k\pi T_k,\ p_k\pi h_k)$ of all bases that are simplex-optimal for Problem $k$ at some $x\in K_1=\{x\mid Ax=b,\ x\ge 0\}$. It is finite because there are finitely many bases.
--
--   These objects are what Step 2 and Step 3 of the multicut algorithm compute, and $\mathcal C_k$ is the set of "facets of $Q_k$" that the iteration bound counts.
--
--   **Formalization Note** Bases, multipliers $\pi=(W_B^{\mathsf T})^{-1}q_{k,B}$, the matrix $[W\mid I\mid -I]$, its cost vector and its multiplier $\sigma$ are taken from the published `StochasticProg_LShaped_Bases`. Its predicates `IsOptimalAt` / `IsFeasBasisOptimalAt` are *not* used: they only require the basis's value to equal the optimal value, and under primal degeneracy such a basis can have a dual-infeasible multiplier whose cut is invalid. The cut set is a `Finset`, so its cardinality is the number of distinct cuts.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), pp. 386-387, Section 2 Step 2 and Eq. (7), Section 3 Eqs. (14)-(16)

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_LShaped_Bases

namespace MulticutLShaped.Bound

open StochasticProg.Recourse StochasticProg.LShaped
open scoped Matrix

variable {n1 n2 m1 m2 K : ℕ}

/-- A simplex-optimal basis of Problem `k` of type (7) at the first-stage point `x`
(Birge–Louveaux 1988, p. 386): `min q_k y` s.t. `W y = h_k − T_k x`, `y ≥ 0`.
The basic submatrix `W_b` is invertible, the basic solution `W_b⁻¹ (h_k − T_k x)` is
nonnegative (primal feasible), and the simplex multiplier `π = q_b W_b⁻¹` satisfies
`π W ≤ q_k` componentwise (all reduced costs nonnegative: dual feasible). This is the
optimality certificate with which the simplex method terminates. -/
def IsSimplexOptimal (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2)
    (x : Fin n1 → ℝ) : Prop :=
  IsUnit (inst.W.submatrix id b.1).det ∧
  (∀ j, 0 ≤ ((inst.W.submatrix id b.1)⁻¹ *ᵥ (inst.h k - inst.T k *ᵥ x)) j) ∧
  (∀ j, (multiplier inst b (inst.q k) ᵥ* inst.W) j ≤ inst.q k j)

/-- A simplex-optimal basis of the Step 2 feasibility LP at `x` for scenario `k`
(p. 386): `min e v⁺ + e v⁻` s.t. `W y + I v⁺ − I v⁻ = h_k − T_k x`, `y, v⁺, v⁻ ≥ 0`.
The basic submatrix of `[W | I | −I]` is invertible, the basic solution is nonnegative,
and the multiplier `σ` satisfies `σ [W | I | −I] ≤ (0, e, e)` componentwise, i.e.
`σ W ≤ 0` and `−1 ≤ σ_i ≤ 1`. -/
def IsFeasSimplexOptimal (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : FeasBasis n2 m2)
    (x : Fin n1 → ℝ) : Prop :=
  IsUnit ((feasMatrix inst).submatrix id b.1).det ∧
  (∀ j, 0 ≤ (((feasMatrix inst).submatrix id b.1)⁻¹ *ᵥ (inst.h k - inst.T k *ᵥ x)) j) ∧
  (∀ c, (feasMultiplier inst b ᵥ* feasMatrix inst) c ≤ feasCost c)

/-- The optimality cut (15)–(16) of scenario `k` generated by the basis `b` (p. 387):
`(E, e) = (p_k π T_k, p_k π h_k)` with `π` the simplex multiplier of `b` for cost `q_k`.
The cut reads `E x + θ_k ≥ e`. -/
noncomputable def optCut (inst : Instance n1 n2 m1 m2 K) (k : Fin K) (b : Basis n2 m2) :
    (Fin n1 → ℝ) × ℝ :=
  (inst.p k • (multiplier inst b (inst.q k) ᵥ* inst.T k),
   inst.p k * (multiplier inst b (inst.q k) ⬝ᵥ inst.h k))

open Classical in
/-- The finite set of all optimality cuts (15)–(16) that Step 3 can generate for scenario
`k`: the cuts `optCut inst k b` of bases `b` that are simplex-optimal for Problem `k` of
type (7) at some first-stage point `x ∈ K₁`. It is a `Finset` because there are finitely
many bases. -/
noncomputable def cutSet (inst : Instance n1 n2 m1 m2 K) (k : Fin K) :
    Finset ((Fin n1 → ℝ) × ℝ) :=
  (Finset.univ.filter (fun b : Basis n2 m2 => ∃ x ∈ K1 inst, IsSimplexOptimal inst k b x)).image
    (optCut inst k)

end MulticutLShaped.Bound


