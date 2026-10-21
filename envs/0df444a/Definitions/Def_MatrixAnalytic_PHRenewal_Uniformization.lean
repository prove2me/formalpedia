-- Prove2me | Definitions.Def_MatrixAnalytic_PHRenewal_Uniformization
-- name    : MatrixAnalytic_PHRenewal_Uniformization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-20T15:41:32.984105+00:00
-- url     : https://prove2.me/theorems/0c3e1a61-5b9f-463b-a3f5-917e76c7aeec
-- title:
--   Uniformization data of Lemma 3.2.3: $P = c^{-1}T + I$, $\boldsymbol p = c^{-1}\boldsymbol t$ and the matrices $K_{m,\nu}$
-- statement:
--   Let $(\boldsymbol\tau, T)$ be a PH representation with exit vector $\boldsymbol t = -T\mathbf 1$, and let $c$ be a real number (in Lemma 3.2.3, $c=\max_i|T_{ii}|$). Define the uniformized matrix and vector
--   $$P = c^{-1}T + I, \qquad \boldsymbol p = c^{-1}\boldsymbol t,$$
--   and the $n\times n$ matrices $K_{m,\nu}$, $m,\nu\ge 0$, by (3.7)–(3.9):
--   $$K_{m,0} = P^m,\qquad K_{0,\nu+1} = 0,\qquad K_{m+1,\nu+1} = P K_{m,\nu+1} + \boldsymbol p\boldsymbol\tau K_{m,\nu}.$$
--
--   $(K_{m,\nu})_{ij}$ is the probability that the uniformized discrete-time chain started in phase $i$ is in phase $j$ right after its $m$th transition, having made $\nu$ instantaneous visits to the absorbing state. Lemma 3.2.3 expresses $P(\nu,x)$ as a Poisson mixture of these matrices.
--
--   **Formalization Note** The book states (3.7) as $K_{m,\nu}=0$ for all $m<\nu$; the recursion here imposes only $K_{0,\nu+1}=0$, and $K_{m,\nu}=0$ for $m<\nu$ follows from it by induction, so the family is the book's. $\boldsymbol p\boldsymbol\tau$ is the outer product.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 67, Lemma 3.2.3, Eqs. (3.7)–(3.9)

import Mathlib
import Definitions.Def_MatrixAnalytic_PHRenewal_PHRep

open Matrix

namespace MatrixAnalytic.PHRenewal

/-- The uniformized transition matrix `P = c⁻¹T + I` of Lemma 3.2.3. -/
noncomputable def unifP {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (c : ℝ) : Matrix ι ι ℝ :=
  c⁻¹ • T + 1

/-- The uniformized exit vector `p = c⁻¹t` of Lemma 3.2.3. -/
noncomputable def unifExit {ι : Type*} [Fintype ι] (T : Matrix ι ι ℝ) (c : ℝ) : ι → ℝ :=
  c⁻¹ • exitVec T

/-- The matrices `K_{m,ν}` of Lemma 3.2.3, defined by (3.7)–(3.9):
`K_{m,0} = P^m`, `K_{0,ν+1} = 0` (an instance of (3.7)), and
`K_{m+1,ν+1} = P K_{m,ν+1} + p τ K_{m,ν}`. -/
noncomputable def unifK {ι : Type*} [Fintype ι] [DecidableEq ι]
    (τ : ι → ℝ) (T : Matrix ι ι ℝ) (c : ℝ) : ℕ → ℕ → Matrix ι ι ℝ
  | m, 0 => unifP T c ^ m
  | 0, _ + 1 => 0
  | m + 1, ν + 1 =>
      unifP T c * unifK τ T c m (ν + 1) + vecMulVec (unifExit T c) τ * unifK τ T c m ν

end MatrixAnalytic.PHRenewal


