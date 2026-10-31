-- Prove2me | Definitions.Def_SVFAppt_cost
-- name    : SVFAppt_cost
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:21:53.65498+00:00
-- url     : https://prove2.me/theorems/15d3c186-2039-4866-856e-da7b1d2493a1
-- title:
--   Cost function $C_\omega(B,\tau,x)$ (2): weighted expected idle and waiting time
-- statement:
--   For a weight $\omega$, service times $B=(B_1,\dots,B_n)$, a sequence $\tau$ and a schedule $x$, the **cost** is
--
--   $$C_\omega(B,\tau,x)=\omega\sum_{i=1}^n\mathbb E I_i+(1-\omega)\sum_{i=1}^n\mathbb E W_i,$$
--
--   where $W_i$ and $I_i$ are the waiting and idle times of slot $i$ given by the Lindley recursions (1), evaluated at the realized service times. It is a weighted average of the expected total idle time of the doctor and the expected total waiting time of the patients.
--
--   The approximation ratio of the smallest-variance-first rule is the ratio of this cost under the identity sequence to its minimum over all sequences, both under the mean-based schedule $x=\mu$.
--
--   **Formalization Note** The weight is called `wt` in Lean (the sample point is `s`). Slots are 0-based. The expectations are Bochner integrals; when every $B_j$ is integrable, every $W_i$ and $I_i$ is integrable (each is bounded by $\sum_j|B_j-x_j|$), so no junk value enters. The cost is defined from the recursion (1), not from any closed form.
-- source:
--   de Kemp, Mandjes, Olver, Performance of the Smallest-Variance-First Rule in Appointment Sequencing, arXiv:1812.01467v4, §2.1, eq. (2), p. 8

import Mathlib
import Definitions.Def_SVFAppt_lindley

open MeasureTheory

namespace SVFAppt

/-- **The cost function (2): weighted expected total idle time and total waiting time.**
de Kemp, Mandjes, Olver, arXiv:1812.01467v4, §2.1, eq. (2), p. 8:
"Cω(τ, x) := ω Σ_{i=1}^n EIi + (1 − ω) Σ_{i=1}^n EWi".

`cost P B wt τ x = wt · Σ_{i<n} E I_i + (1 − wt) · Σ_{i<n} E W_i`, where `W_i`, `I_i` are the
waiting and idle times of the Lindley recursion (1) (`wait`, `idle`) evaluated pathwise at the
service-time realization `(B_j s)_j` for each sample point `s`.

**Formalization Note**
* The weight `ω` of the paper is called `wt` (the sample point is `s`).
* Slots are 0-based; the sum over `i : Fin n` is the paper's sum over slots `1, …, n`.
* The expectations are Bochner integrals against `P`. When every `B_j` is integrable, every `W_i`
  and `I_i` is integrable (each is bounded by `Σ_j |B_j − x_j|`), so no junk value enters. -/
noncomputable def cost {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {n : ℕ}
    (B : Fin n → Ω → ℝ) (wt : ℝ) (τ : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : ℝ :=
  wt * ∑ i : Fin n, ∫ s, idle τ x (fun j => B j s) i ∂P
    + (1 - wt) * ∑ i : Fin n, ∫ s, wait τ x (fun j => B j s) i ∂P

end SVFAppt


