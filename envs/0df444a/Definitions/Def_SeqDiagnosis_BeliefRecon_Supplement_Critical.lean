-- Prove2me | Definitions.Def_SeqDiagnosis_BeliefRecon_Supplement_Critical
-- name    : SeqDiagnosis_BeliefRecon_Supplement_Critical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T06:20:21.680991+00:00
-- url     : https://prove2.me/theorems/4aad1c74-1499-45b9-97e2-000f3b4cac64
-- title:
--   §2, §4.2 — zero-one costs, uniform prior, infinite-horizon value, critical stopping time, degree of confusion $n_s$
-- statement:
--   This file adds the objects of Theorem 3 (§4.2).
--
--   1. The **zero-one cost structure** (p. 6): $a_{ii}=0$, $a_{ij}=1$ for $j\ne i$, and $c_i=c$ for every class.
--   2. The **uninformative prior** $\theta_i=1/(N+1)$.
--   3. The **infinite-horizon value** $V_\infty(\Pi)=\inf_{k\in\mathbb N}W_k(\Pi)$, the infimum over horizons of the finite-horizon optimal cost (on the simplex $W_k$ is nonincreasing in $k$, so this is also the limit).
--   4. A period $t_c$ is a **critical stopping time** if at every belief reachable after exactly $t_c$ observations stopping is optimal:
--   $$\min_jV^j(\Pi_{t_c})\le\sum_i\pi_{i,t_c}c_i+\int V_\infty\bigl(\mathcal B(\Pi_{t_c},y)\bigr)\,\Pi_{t_c}F(y)\,d\mu(y)$$
--   for every observation sequence $y_1,\ldots,y_{t_c}$ (for $t_c=0$ this is the prior).
--   5. With $g_0(x)=0$ and $g_i(x)=\beta_{i0}+e_i\mathbb Rx$ for $i\ge1$ (the exponents of (3)), the **multiplicity** $|\{g_i(x), i\in\mathcal N\}|$ is the largest number of classes sharing one value of $g$ at $x$. The **degree of confusion** as printed is
--   $$n_s=\max_{t\ge1,\ x\in\Omega_t}\bigl|\{\beta_{i0}+e_i\mathbb Rx,\ i\in\mathcal N\}\bigr|,$$
--   and $\bar n_s$ is the same maximum over every $x\in\mathbb R^r$.
--
--   These are the objects in which Theorem 3 is stated; $\bar n_s$ is used by its corrected first clause.
--
--   **Formalization Note** The paper's infinite-horizon value is an infimum of expected costs over admissible policies; it is encoded here as the infimum of the finite-horizon values (the value of the best policy that stops by a deterministic deadline). Both maxima are suprema of sets of natural numbers bounded by $N+1$; $n_s$ keeps the printed maximum over the attained sets $\Omega_t$.
-- source:
--   Wang, Optimal Sequential Multi-class Diagnosis, arXiv:1506.08915v4, p. 6 (PDF 6) zero-one costs and uninformative prior; p. 15, p. 17 (PDF 15, 17) critical stopping time; p. 18 (PDF 18) and endnote 4, p. 34 (PDF 34), degree of confusion

import Mathlib
import Definitions.Def_SeqDiagnosis_BeliefRecon_Supplement_Value

open MeasureTheory Matrix

namespace SeqDiagnosis.BeliefRecon.Supplement

/-- Zero-one cost structure: `a i i = 0`, `a i j = 1` for `j ≠ i`, and `c i = c` for every `i`. -/
def zeroOne (N : ℕ) (c : ℝ) : Costs N where
  a := fun i j => if i = j then 0 else 1
  c := fun _ => c

/-- The uninformative prior `θᵢ = 1/(N+1)`. -/
noncomputable def uniformPrior (N : ℕ) : Fin (N + 1) → ℝ :=
  fun _ => 1 / ((N : ℝ) + 1)

/-- Infinite-horizon value: the infimum over horizons of the finite-horizon optimal value
(nonincreasing in the number of periods to go on `Sᴺ`, so this is also its limit). -/
noncomputable def valueInf {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (C : Costs N) (q : Fin (N + 1) → ℝ) : ℝ :=
  ⨅ k : ℕ, valueToGo M C k q

/-- `tc` is a critical stopping time of the infinite-horizon problem with prior `θ`: at every
belief reachable after exactly `tc` observations, diagnosing is optimal (the waiting region is
empty; ties count as stopping). For `tc = 0` this is the prior itself. -/
def IsCriticalTime {Y : Type*} [MeasurableSpace Y] {N p : ℕ}
    (M : Model Y N p) (C : Costs N) (θ : Fin (N + 1) → ℝ) (tc : ℕ) : Prop :=
  ∀ ys : List Y, ys.length = tc →
    termValue C (belief M.f θ ys) ≤ waitValue M C (valueInf M C) (belief M.f θ ys)

/-- The exponents `β_{i0} + e_iℝx` of (3); class `0` has `β_{00} = 0` and the null row `e_0`. -/
noncomputable def gExp {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (i : Fin (N + 1)) (x : Fin r → ℝ) : ℝ :=
  Fin.cases (motive := fun _ => ℝ) 0 (fun k => betaZero M R P k + (R *ᵥ x) k) i

/-- `|{β_{i0} + e_iℝx, i ∈ 𝒩}|`: the largest number of classes sharing one exponent value at `x`. -/
noncomputable def multiplicity {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ)
    (x : Fin r → ℝ) : ℕ :=
  Finset.univ.sup fun i =>
    (Finset.univ.filter fun j => gExp M R P j x = gExp M R P i x).card

/-- The degree of confusion `nₛ` as printed in §4.2: the maximum multiplicity over the attained
statistics `x ∈ Ω_t`, `t ≥ 1` (a bounded set of naturals, at most `N + 1`). -/
noncomputable def confusion {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ) : ℕ :=
  sSup {n | ∃ t : ℕ, 1 ≤ t ∧ ∃ x ∈ Omega M P t, multiplicity M R P x = n}

/-- The degree of confusion taken over every point `x ∈ ℝʳ` (used in the corrected Theorem 3). -/
noncomputable def confusionAll {Y : Type*} [MeasurableSpace Y] {N p r : ℕ}
    (M : Model Y N p) (R : Matrix (Fin N) (Fin r) ℝ) (P : Matrix (Fin r) (Fin p) ℝ) : ℕ :=
  sSup (Set.range (multiplicity M R P))

end SeqDiagnosis.BeliefRecon.Supplement


