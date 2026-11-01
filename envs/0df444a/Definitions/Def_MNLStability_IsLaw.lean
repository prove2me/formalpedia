-- Prove2me | Definitions.Def_MNLStability_IsLaw
-- name    : MNLStability_IsLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:26:18.424704+00:00
-- url     : https://prove2.me/theorems/1b69d1c8-05c0-4ead-bd21-4b95579196ae
-- title:
--   The law of the number of customers $M$, $\Pr[M\ge1]$, and the input length $L_M$
-- statement:
--   The number of customers $M$ is random, with a finitely supported law given explicitly as part of the input. A finitely supported function $p_M:\mathbb N\to\mathbb R$ is such a **law** when $p_M(m)\ge0$ for all $m$ and $\sum_m p_M(m)=1$.
--
--   The module also defines:
--
--   1. $\Pr[M\ge1]=\sum_{m\ge1}p_M(m)$;
--   2. $s$, the number of support points of $M$;
--   3. $L_M=\sum_{m\in\operatorname{supp}M}\bigl(1+\lfloor\log_2(m+1)\rfloor\bigr)$, the number of bits needed to list the support of $M$.
--
--   $L_M$ is not a quantity of the paper. It is the input-length factor of the corrected running time of Theorem 1, since a program has to read the law of $M$.
--
--   **Formalization Note** The law is a `ℕ →₀ ℝ` (`Finsupp`), whose support is a `Finset`.
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), §1.1, p.3 (finite support, "explicitly specified as part of the input")

import Mathlib

namespace MNLStability

/-- The law of the number of customers `M` (SSRN:3498325, §1.1, p.3): "this distribution has a finite
support, and … its probability mass function is explicitly specified as part of the input". A
finitely supported function `pM : ℕ →₀ ℝ` is such a law when its values are non-negative and sum
to `1`. -/
def IsLaw (pM : ℕ →₀ ℝ) : Prop := (∀ m, 0 ≤ pM m) ∧ pM.sum (fun _ p => p) = 1

/-- `Pr[M ≥ 1] = Σ_{m ∈ supp M, m ≥ 1} Pr[M = m]`. -/
noncomputable def probMpos (pM : ℕ →₀ ℝ) : ℝ := ∑ m ∈ pM.support.filter (1 ≤ ·), pM m

/-- `s`, the number of support points of the law of `M` (the entries a program has to read). -/
def supportSize (pM : ℕ →₀ ℝ) : ℕ := pM.support.card

/-- `L_M = Σ_{m ∈ supp M} (1 + ⌊log₂(m + 1)⌋)`, the number of bits needed to list the support of
`M`: the input-length factor of the corrected running time of Theorem 1.

**Formalization Note.** Not a quantity of the paper; it enters through the declared correction of
Theorem 1's time bound (the printed bound has no term for reading the law of `M`). -/
noncomputable def LM (pM : ℕ →₀ ℝ) : ℝ := ∑ m ∈ pM.support, (1 + (Nat.log 2 (m + 1) : ℝ))

end MNLStability


