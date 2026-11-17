-- Prove2me | Definitions.Def_MatrixLewis_Supplement_TwoPhase
-- name    : MatrixLewis_Supplement_TwoPhase
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:07:39.572515+00:00
-- url     : https://prove2.me/theorems/7cc69448-6d3f-4a91-98d6-148ae5f84577
-- title:
--   Algorithm 4 — two-phase path following; size bounds $R_{\mathcal D}$, $R_S$
-- statement:
--   For an instance with domain $\mathcal D$, the **size bounds** are
--   $$R_{\mathcal D}:=\sup_{x\in\mathcal D}\|x\|_\infty,\qquad R_S:=\sup_{x\in\mathcal D}\|S_x\|_{\mathrm{op}},$$
--   with $\|\cdot\|_{\mathrm{op}}$ the spectral norm. Both are finite for a **bounded instance**, that is, one that satisfies Assumption 3.1 and has $\mathcal D$ nonempty and bounded.
--
--   **Algorithm 4** (two-phase path following) takes a point $x_0\in\mathcal D$, numbers $\bar a$ and $\bar R_{\mathcal D}$, an objective $c\in\mathbb R^m\setminus\{0\}$ and $\mu_f>0$, together with $K$, $\kappa$ and the parameters of Equation (47). It runs as follows.
--
--   1. Set $\mu_{\mathrm{top}}\leftarrow16K\bar am/\bar\lambda$ and $\mu_1\leftarrow8K\bar R_{\mathcal D}\|c\|_1/\bar\lambda$.
--   2. Query $x_0$ without a metric request, and receive $g_0$.
--   3. Halt with FAIL if this answer is FAIL.
--   4. Phase I: $x\leftarrow\mathrm{PF}(-g_0,x_0,1\to\mu_{\mathrm{top}})$.
--   5. Phase II: $x\leftarrow\mathrm{PF}(c,x,\mu_1\to\mu_f)$.
--   6. Return $x$.
--
--   The defined objects are the query made at each step, numbered from $0$ (the query at $x_0$), and the output. Each is given as a function of the answers.
--
--   Phase I follows the path of the auxiliary objective $-g_0$, the oracle's answer at the known point. Phase II follows the path of the true objective, so Algorithm 4 starts path following without a nearly central point.
--
--   **Formalization Note** $\|x\|_\infty$ is the sup norm of the coordinates, $\|c\|_1=\sum_i|c_i|$, and $\|\cdot\|_{\mathrm{op}}$ is the published `LiqPremiaEq.opNorm`. The size bounds are real suprema, and they take the paper's values on a bounded instance.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), App. A.1, p.62 (bounded instance, size bounds, Algorithm 4)

import Mathlib
import Definitions.Def_LiqPremiaEq_opNorm
import Definitions.Def_MatrixLewis_Supplement_PathFollowing

namespace MatrixLewis

namespace Supplement

/-- The size bound `R_𝒟 := sup_{x∈𝒟} ‖x‖_∞` of a bounded instance (Kelner–Jiang–Sidford–Zhang,
*Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027
submission (manuscript sha256 31ce765b…), App. A.1, p.62).

**Formalization Note** `‖x‖_∞` is Mathlib's sup norm on `Fin m → ℝ`, applied to the coordinates of
`x`. A real supremum; it is the paper's value when `𝒟` is nonempty and bounded (a bounded instance). -/
noncomputable def sizeBoundD {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun x : EuclideanSpace ℝ (Fin m) => ‖WithLp.ofLp x‖) '' dom A C)

/-- The size bound `R_S := sup_{x∈𝒟} ‖S_x‖_op` of a bounded instance (Kelner–Jiang–Sidford–Zhang,
STOC 2027 submission (manuscript sha256 31ce765b…), App. A.1, p.62), with `‖·‖_op` the spectral
(ℓ² operator) norm, the published `LiqPremiaEq.opNorm`.

**Formalization Note** A real supremum; it is the paper's value when `𝒟` is nonempty and bounded. -/
noncomputable def sizeBoundS {n m : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup ((fun x => LiqPremiaEq.opNorm (slack A C x)) '' dom A C)

/-- `μ_top := 16Kām/λ̄` (Algorithm 4, line 1; Kelner–Jiang–Sidford–Zhang, STOC 2027 submission
(manuscript sha256 31ce765b…), p.62). -/
noncomputable def muTop (pr : PFParams) (abar : ℝ) : ℝ :=
  16 * pr.K * abar * pr.m / pr.lamBar

/-- `μ₁ := 8K R̄_𝒟 ‖c‖₁/λ̄` (Algorithm 4, line 1, p.62), with `‖c‖₁ = ∑ᵢ |cᵢ|`. -/
noncomputable def muOne {m : ℕ} (pr : PFParams) (Rbar : ℝ) (c : EuclideanSpace ℝ (Fin m)) : ℝ :=
  8 * pr.K * Rbar * (∑ i, |c i|) / pr.lamBar

/-- **Algorithm 4** (Two-phase path following; Kelner–Jiang–Sidford–Zhang, STOC 2027 submission
(manuscript sha256 31ce765b…), p.62), query by query, under the answerer `R` (see `pfState`):
1. `μ_top ← 16Kām/λ̄` and `μ₁ ← 8K R̄_𝒟 ‖c‖₁/λ̄`;
2. query `x₀` without a metric request and receive `g₀` (query `0`);
3. halt with `FAIL` if this answer is `FAIL`;
4. `x ← PF(−g₀, x₀, 1 → μ_top)` (Phase I; queries `1, …, (P_I + 1)τ_blk`);
5. `x ← PF(c, x, μ₁ → μ_f)` (Phase II; the next `(P_II + 1)τ_blk` queries);
6. return `x`.

`twoPhaseQuery … R t` is `some (u, flag)` if the run makes a `t`-th query (counting from `0`), at `u`
with a metric request iff `flag`, and `none` otherwise. -/
noncomputable def twoPhaseQuery {m : ℕ} (pr : PFParams) (x0 : EuclideanSpace ℝ (Fin m))
    (abar Rbar : ℝ) (c : EuclideanSpace ℝ (Fin m)) (μf : ℝ) (R : ℕ → Query m → Answer m) (t : ℕ) :
    Option (Query m) :=
  let a0 := R 0 (x0, false)
  let n1 := (pr.numP 1 (muTop pr abar) + 1) * pr.tauBlk
  let R1 : ℕ → Query m → Answer m := fun u => R (u + 1)
  let R2 : ℕ → Query m → Answer m := fun u => R (u + 1 + n1)
  if t = 0 then some (x0, false)
  else if a0.fail = true then none
  else if t - 1 < n1 then pfQuery pr (-a0.grad) x0 1 (muTop pr abar) R1 (t - 1)
  else
    match pfOutput pr (-a0.grad) x0 1 (muTop pr abar) R1 with
    | none => none
    | some x => pfQuery pr c x (muOne pr Rbar c) μf R2 (t - 1 - n1)

/-- The output of **Algorithm 4** (p.62) under the answerer `R`: `some x` for the returned point,
`none` if the run halts with `FAIL`. -/
noncomputable def twoPhaseOutput {m : ℕ} (pr : PFParams) (x0 : EuclideanSpace ℝ (Fin m))
    (abar Rbar : ℝ) (c : EuclideanSpace ℝ (Fin m)) (μf : ℝ) (R : ℕ → Query m → Answer m) :
    Option (EuclideanSpace ℝ (Fin m)) :=
  let a0 := R 0 (x0, false)
  let n1 := (pr.numP 1 (muTop pr abar) + 1) * pr.tauBlk
  let R1 : ℕ → Query m → Answer m := fun u => R (u + 1)
  let R2 : ℕ → Query m → Answer m := fun u => R (u + 1 + n1)
  if a0.fail = true then none
  else
    match pfOutput pr (-a0.grad) x0 1 (muTop pr abar) R1 with
    | none => none
    | some x => pfOutput pr c x (muOne pr Rbar c) μf R2

end Supplement

end MatrixLewis


