-- Prove2me | Definitions.Def_MDPFinance_IndifferencePricing_IndexTrackingRiccati
-- name    : MDPFinance_IndifferencePricing_IndexTrackingRiccati
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:10:36.285007+00:00
-- url     : https://prove2.me/theorems/cb8a75da-3097-4628-9dd5-fa197c3a0c5a
-- title:
--   The Riccati-type recursion of Theorem 2.6.3, instantiated to the index-tracking model
-- statement:
--   The cost matrix $Q:=\begin{pmatrix}1&-1\\-1&1\end{pmatrix}$ (so
--   $(x-\hat s)^2 = (x,\hat s)Q(x,\hat s)^\top$), the random system matrices
--   $A_{n+1} := \mathrm{diag}(1+i_{n+1},\hat R_{n+1})$ and $B_{n+1}$ (top row
--   $(1+i_{n+1})R_{n+1}^\top$, bottom row $0$), and the predicate `QRecursion` asserting that a
--   sequence $(Q_n)$ satisfies $Q_N = Q$ and, for $n<N$,
--   $$Q_n = Q + \mathbb{E}[A_{n+1}^\top Q_{n+1}A_{n+1}] - \mathbb{E}[A_{n+1}^\top Q_{n+1}B_{n+1}]
--   \big(\mathbb{E}[B_{n+1}^\top Q_{n+1}B_{n+1}]\big)^{-1}\mathbb{E}[B_{n+1}^\top Q_{n+1}A_{n+1}],$$
--   the general stochastic-LQ Riccati recursion of Theorem 2.6.3 (proved elsewhere in the book, in
--   the deterministic-cost, random-coefficient linear-quadratic framework of §2.6.3), specialized to
--   this problem's own $A_{n+1},B_{n+1},Q$.
--
--   **Formalization Note.** Per hard rule 3 (declare shared machinery locally, do not import another
--   chunk's copy) this restates Theorem 2.6.3's recursion inline for this chunk's own system data,
--   rather than depending on a `02d` Lean module. The platform's `BertsekasDP.riccati_completion_of_square`
--   was checked and is not reused: its `A`,`B` are deterministic matrices with no expectation
--   anywhere in the statement, whereas this recursion's $A_{n+1},B_{n+1}$ are random and every term
--   is an expectation, matching this chunk brief's own flagged mismatch.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 51, PDF 65, Theorem 2.6.3, instantiated at p. 133-134, PDF 147-148

import Mathlib
import Definitions.Def_MDPFinance_IndifferencePricing_IndexTrackingMarket

open MeasureTheory ProbabilityTheory Matrix

namespace MDPFinance.IndifferencePricing

/-- The entrywise expectation of a matrix-valued random variable. -/
noncomputable def matExpect {Ω : Type*} [MeasurableSpace Ω] {m k : Type*} [Fintype m] [Fintype k]
    (measIP : Measure Ω) (A : Ω → Matrix m k ℝ) : Matrix m k ℝ :=
  Matrix.of (fun i j => ∫ ω, A ω i j ∂measIP)

/-- The cost matrix `Q := [[1,-1],[-1,1]]` of the tracking-error criterion `(x-ŝ)^2 = (x,ŝ)Q(x,ŝ)ᵀ`
(Bäuerle–Rieder, p. 133, PDF 147). -/
def Qcost : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; -1, 1]

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The random state-transition matrix `A_{n+1} := diag(1+i_{n+1}, R̂_{n+1})` of the index-tracking
model's linear-quadratic reformulation, matching Theorem 2.6.3's `A_{n+1}` (Bäuerle–Rieder,
p. 133-134, PDF 147-148). -/
noncomputable def IndexTrackingMarket.Amat (M : IndexTrackingMarket Ω d) (n : ℕ) (ω : Ω) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + M.i (n + 1), 0; 0, M.Rhat (n + 1) ω]

/-- The random action-transition matrix `B_{n+1}` (top row `(1+i_{n+1})R_{n+1}`, bottom row `0`)
of the index-tracking model's linear-quadratic reformulation, matching Theorem 2.6.3's `B_{n+1}`
(Bäuerle–Rieder, p. 133-134, PDF 147-148). -/
noncomputable def IndexTrackingMarket.Bmat (M : IndexTrackingMarket Ω d) (n : ℕ) (ω : Ω) :
    Matrix (Fin 2) (Fin d) ℝ :=
  Matrix.of (fun i j => if i = 0 then (1 + M.i (n + 1)) * M.R (n + 1) ω j else 0)

/-- `Q` satisfies the Riccati-type recursion of Theorem 2.6.3, instantiated to the index-tracking
model's cost matrix `Qcost` and random system matrices `Amat`, `Bmat` (Bäuerle–Rieder, p. 51,
PDF 65, Theorem 2.6.3, restated locally for this chunk's own system data per hard rule 3). -/
def IndexTrackingMarket.QRecursion (M : IndexTrackingMarket Ω d)
    (Q : ℕ → Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  Q M.N = Qcost ∧
    ∀ n < M.N,
      Q n = Qcost +
        matExpect M.measIP (fun ω => (M.Amat n ω)ᵀ * Q (n + 1) * M.Amat n ω) -
        matExpect M.measIP (fun ω => (M.Amat n ω)ᵀ * Q (n + 1) * M.Bmat n ω) *
          (matExpect M.measIP (fun ω => (M.Bmat n ω)ᵀ * Q (n + 1) * M.Bmat n ω))⁻¹ *
          matExpect M.measIP (fun ω => (M.Bmat n ω)ᵀ * Q (n + 1) * M.Amat n ω)

end MDPFinance.IndifferencePricing


