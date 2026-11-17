-- Prove2me | Definitions.Def_MatrixLewis_Supplement_PathFollowing
-- name    : MatrixLewis_Supplement_PathFollowing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:06:43.173396+00:00
-- url     : https://prove2.me/theorems/ff77a92b-edbf-48e3-a160-cb8d7fad1c80
-- title:
--   Equation (47) and Algorithm 2 — the parameters, Block and PF$(c',x,\mu_s\to\mu_e)$
-- statement:
--   Let $c_0,c_e,C_{\mathrm{blk}}$ be constants, $q>2$, $K\ge1$ a self-concordance constant of $f_q$, $\kappa\ge1$ and $m\ge1$. The parameters of **Equation (47)** are
--   $$\bar\lambda:=\frac{c_0}{K},\quad L_{\mathrm{sm}}:=4(q+1)\kappa,\quad \tau_{\mathrm{blk}}:=\bigl\lceil C_{\mathrm{blk}}(q+1)\kappa^2\bigr\rceil,\quad \theta:=\frac{\bar\lambda}{4\sqrt m},\quad e_{\mathrm{PA}}:=\frac{c_e\bar\lambda}{\sqrt{q+1}\,\kappa}.$$
--
--   **Algorithm 2.** $\mathrm{Block}(c',\mu,x)$ sets $x_0\leftarrow x$ and, for $t=0,\dots,\tau_{\mathrm{blk}}-1$: at $t=0$ it queries $x_0$ with a metric request and receives $g_0$ and $N$; at $t\ge1$ it queries $x_t$ without a metric request and receives $g_t$. It halts with FAIL if the answer is FAIL, or if $t=0$ and $N\not\succ0$, and otherwise sets
--   $$x_{t+1}\leftarrow x_t-L_{\mathrm{sm}}^{-1}N^{-1}\Bigl(\frac{c'}{\mu}+g_t\Bigr),$$
--   with $N$ frozen for the block; it returns $x_{\tau_{\mathrm{blk}}}$. $\mathrm{PF}(c',x,\mu_s\to\mu_e)$ sets $P\leftarrow\lceil|\log(\mu_e/\mu_s)|/\log(1+\theta)\rceil$ and, for $k=0,1,\dots,P$, sets $\mu_k\leftarrow\mu_s(\mu_e/\mu_s)^{k/P}$ ($\mu_0=\mu_s$ if $P=0$) and $x\leftarrow\mathrm{Block}(c',\mu_k,x)$; it returns $x$. A halt with FAIL stops the whole method.
--
--   The method is deterministic given the answers. A run is described query by query: query $t$ is step $t\bmod\tau_{\mathrm{blk}}$ of block $\lfloor t/\tau_{\mathrm{blk}}\rfloor$. The objects defined are the query made at each step (or none), and the output (or FAIL), for a given way of answering the queries.
--
--   This is the short-step path-following method with approximate answers of Section 4.1. Each Newton step is replaced by a block of preconditioned gradient steps.
--
--   **Formalization Note** A run is a function of an answerer $R$, where $R(t,Q)$ is the answer to the $t$-th query $Q$. Any answer stream, adaptive or not, is the run of some $R$, and the random run of an oracle is $R=O(\cdot,\omega)$. `PFParams` bundles $(c_0,c_e,C_{\mathrm{blk}},q,K,\kappa,m)$, and $\log$ is natural.
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Equation (47) and Algorithm 2, p.37

import Mathlib
import Definitions.Def_MatrixLewis_Supplement_Oracle

namespace MatrixLewis

namespace Supplement

/-- The inputs of the parameters of **Equation (47)** (Kelner–Jiang–Sidford–Zhang, *Matrix Lewis
Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission
(manuscript sha256 31ce765b…), p.37): the absolute constants `c₀, c_e, C_blk` of Lemma 4.4, the
exponent `q`, the self-concordance constant `K`, the metric factor `κ` and the dimension `m`. -/
structure PFParams where
  /-- `c₀` (Lemma 4.4) -/
  c0 : ℝ
  /-- `c_e` (Lemma 4.4) -/
  ce : ℝ
  /-- `C_blk` (Lemma 4.4) -/
  Cblk : ℝ
  /-- the exponent `q` -/
  q : ℝ
  /-- the self-concordance constant `K` -/
  K : ℝ
  /-- the metric factor `κ` -/
  κ : ℝ
  /-- the number `m` of variables -/
  m : ℕ

namespace PFParams

/-- `λ̄ := c₀/K` (Equation (47)). -/
noncomputable def lamBar (pr : PFParams) : ℝ := pr.c0 / pr.K

/-- `L_sm := 4(q + 1)κ` (Equation (47)). -/
noncomputable def Lsm (pr : PFParams) : ℝ := 4 * (pr.q + 1) * pr.κ

/-- `τ_blk := ⌈C_blk(q + 1)κ²⌉`, the block length (Equation (47)). -/
noncomputable def tauBlk (pr : PFParams) : ℕ := ⌈pr.Cblk * (pr.q + 1) * pr.κ ^ 2⌉₊

/-- `θ := λ̄/(4√m)` (Equation (47)). -/
noncomputable def theta (pr : PFParams) : ℝ := pr.lamBar / (4 * Real.sqrt pr.m)

/-- `e_PA := c_e λ̄/(√(q + 1) κ)`, the allowed gradient error (Equation (47)). -/
noncomputable def ePA (pr : PFParams) : ℝ := pr.ce * pr.lamBar / (Real.sqrt (pr.q + 1) * pr.κ)

/-- `P := ⌈|log(μ_e/μ_s)| / log(1 + θ)⌉` (Algorithm 2, line 15); `log` is natural. -/
noncomputable def numP (pr : PFParams) (μs μe : ℝ) : ℕ :=
  ⌈|Real.log (μe / μs)| / Real.log (1 + pr.theta)⌉₊

/-- `μ_k := μ_s (μ_e/μ_s)^{k/P}`, with `μ₀ = μ_s` if `P = 0` (Algorithm 2, line 17). -/
noncomputable def muK (pr : PFParams) (μs μe : ℝ) (k : ℕ) : ℝ :=
  if pr.numP μs μe = 0 then μs else μs * (μe / μs) ^ ((k : ℝ) / (pr.numP μs μe : ℝ))

end PFParams

/-- The vector `N v` for `N ∈ ℝ^{m×m}` and `v ∈ ℝᵐ = EuclideanSpace ℝ (Fin m)`. -/
noncomputable def matVec {m : ℕ} (N : Matrix (Fin m) (Fin m) ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 (N.mulVec (WithLp.ofLp v))

open Classical in
/-- One query of **Algorithm 2** (Kelner–Jiang–Sidford–Zhang, STOC 2027 submission (manuscript sha256
31ce765b…), p.37) inside `PF(c′, x, μ_s → μ_e)`. Query number `t` is step `s = t mod τ_blk` of block
`k = ⌊t/τ_blk⌋`, which runs `Block(c′, μ_k, ·)`. The state is the current point `x_s` and the matrix
`N` frozen at the block's first query. Given the answer `a` to query `t` (made at the current point,
with a metric request exactly when `s = 0`):
* if `s = 0`: halt (`none`) if `a` is `FAIL` or `N := a.metric` is not positive definite, else
  `x_{s+1} := x_s − L_sm⁻¹ N⁻¹(c′/μ_k + g)` and `N` is frozen for the block;
* if `s ≥ 1`: halt if `a` is `FAIL`, else `x_{s+1} := x_s − L_sm⁻¹ N⁻¹(c′/μ_k + g)`.

At `s = τ_blk − 1` the new point is the block's output `x_{τ_blk}`, which is the next block's `x₀`. -/
noncomputable def pfStep {m : ℕ} (pr : PFParams) (c' : EuclideanSpace ℝ (Fin m)) (μs μe : ℝ)
    (t : ℕ) (st : EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ) (a : Answer m) :
    Option (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ) :=
  let μ := pr.muK μs μe (t / pr.tauBlk)
  if t % pr.tauBlk = 0 then
    if a.fail = false ∧ a.metric.PosDef then
      some (st.1 - pr.Lsm⁻¹ • matVec a.metric⁻¹ (μ⁻¹ • c' + a.grad), a.metric)
    else none
  else
    if a.fail = false then
      some (st.1 - pr.Lsm⁻¹ • matVec st.2⁻¹ (μ⁻¹ • c' + a.grad), st.2)
    else none

/-- The state of `PF(c′, x, μ_s → μ_e)` (Algorithm 2) before query `t`, when query `u` is answered by
`R u (query u)`: `none` once the method has halted with `FAIL`, else the current point and the frozen
matrix. The run makes the `(P + 1)τ_blk` queries `t = 0, …, (P + 1)τ_blk − 1` (blocks `k = 0, …, P`)
unless it halts.

**Formalization Note** The method is deterministic given the answers, so a run is a function of an
*answerer* `R : ℕ → Query m → Answer m`. Every answer stream, chosen adaptively from the history or
not, is the run of some answerer, so statements "for every answer stream" quantify over all `R`; a
random oracle run is the run of `R = O · ω` (Definition 4.1). -/
noncomputable def pfState {m : ℕ} (pr : PFParams) (c' x : EuclideanSpace ℝ (Fin m)) (μs μe : ℝ)
    (R : ℕ → Query m → Answer m) :
    ℕ → Option (EuclideanSpace ℝ (Fin m) × Matrix (Fin m) (Fin m) ℝ)
  | 0 => some (x, 0)
  | t + 1 =>
    match pfState pr c' x μs μe R t with
    | none => none
    | some st =>
      if t < (pr.numP μs μe + 1) * pr.tauBlk then
        pfStep pr c' μs μe t st (R t (st.1, decide (t % pr.tauBlk = 0)))
      else some st

/-- Query `t` of `PF(c′, x, μ_s → μ_e)` (Algorithm 2) under the answerer `R`: `some (u, flag)` if the
run makes a `t`-th query (counting from `0`), at the point `u`, with a metric request iff
`flag = true`; `none` if it makes no `t`-th query (it halted before, or `t ≥ (P + 1)τ_blk`). -/
noncomputable def pfQuery {m : ℕ} (pr : PFParams) (c' x : EuclideanSpace ℝ (Fin m)) (μs μe : ℝ)
    (R : ℕ → Query m → Answer m) (t : ℕ) : Option (Query m) :=
  if t < (pr.numP μs μe + 1) * pr.tauBlk then
    (pfState pr c' x μs μe R t).map fun st => (st.1, decide (t % pr.tauBlk = 0))
  else none

/-- The output of `PF(c′, x, μ_s → μ_e)` (Algorithm 2) under the answerer `R`: `some x` for the
returned point, `none` if the run halts with `FAIL`. -/
noncomputable def pfOutput {m : ℕ} (pr : PFParams) (c' x : EuclideanSpace ℝ (Fin m)) (μs μe : ℝ)
    (R : ℕ → Query m → Answer m) : Option (EuclideanSpace ℝ (Fin m)) :=
  (pfState pr c' x μs μe R ((pr.numP μs μe + 1) * pr.tauBlk)).map Prod.fst

end Supplement

end MatrixLewis


