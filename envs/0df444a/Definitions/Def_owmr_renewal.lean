-- Prove2me | Definitions.Def_owmr_renewal
-- name    : owmr_renewal
-- status  : Definition
-- author  : @Ming Hu
-- created : 2026-11-16T02:42:11.181787+00:00
-- url     : https://prove2.me/theorems/1cd0829b-4292-4d61-9d25-5b8a1c0e93d6
-- title:
--   Renewal measure $U$ of i.i.d. demands
-- statement:
--   Let $D_1,D_2,\ldots$ be i.i.d. nonnegative demands with law $\rho$, and write $D^{(0)}=0$ and $D^{(n)}=D_1+\cdots+D_n$. The **renewal measure** of $\rho$ is the measure on $\mathbb R$ given by
--
--   $$U(A)=\sum_{n\ge0}\mathbb P\bigl(D^{(n)}\in A\bigr),$$
--
--   the expected number of partial sums of the demand sequence that lie in $A$. It is carried by $[0,\infty)$ and has an atom of mass at least $1$ at $0$, from $D^{(0)}=0$. The renewal function of the source is $M(w)=U[0,w)$.
--
--   **Formalization Note** `renewalMeasure ρ` is the sum over $n$ of the image of the product measure $\rho^{\otimes n}$ on `Fin n → ℝ≥0` under $z\mapsto\sum_j z_j$; the summand $n=0$ is the Dirac mass at $0$.
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Section 4.2 (The Renewal Measure and Short Intervals), eq. (9), p. 12.

import Definitions.Def_owmr_single_location

/-!
# The renewal measure of i.i.d. demands (equation (9))

Source: M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse
Multi-Retailer Systems", Section 4.2, equation (9).
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace OWMR

/-- The renewal measure `U(A) = ∑_{n ≥ 0} ℙ(D^{(n)} ∈ A)` of (9), where `D^{(n)}` is the sum of
`n` i.i.d. demands of law `ρ` (with `D^{(0)} = 0`). It is a measure on `ℝ` carried by `[0, ∞)`,
and `M(w) = U[0, w)`. -/
def renewalMeasure (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] : Measure ℝ :=
  Measure.sum fun n : ℕ => (Measure.pi fun _ : Fin n => ρ).map fun z => ∑ j, (z j : ℝ)

end OWMR


