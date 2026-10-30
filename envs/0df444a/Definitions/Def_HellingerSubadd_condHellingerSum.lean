-- Prove2me | Definitions.Def_HellingerSubadd_condHellingerSum
-- name    : HellingerSubadd_condHellingerSum
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T02:48:05.262195+00:00
-- url     : https://prove2.me/theorems/f041a1c1-8f53-403a-915c-161adef1367c
-- title:
--   Sum of conditional squared Hellinger distances along a trajectory
-- statement:
--   With kernels $\kappa_k,\eta_k$ from $\mathcal X_0\times\dots\times\mathcal X_k$ to $\mathcal X_{k+1}$ as in the definition of the sequential law, and a trajectory $x=(x_0,x_1,\dots,x_n)$, define
--
--   $$
--   S_n(x)=\sum_{i=1}^{n}D^2_{\mathrm H}\bigl(\kappa_{i-1}(\cdot\mid x_0,x_{1:i-1}),\ \eta_{i-1}(\cdot\mid x_0,x_{1:i-1})\bigr)\in[0,\infty].
--   $$
--
--   With $\kappa_{i-1}=P^{(i)}$ and $\eta_{i-1}=Q^{(i)}$ this is the integrand $\sum_{i=1}^nD^2_{\mathrm H}(P^{(i)}(\cdot\mid X_{1:i-1}),Q^{(i)}(\cdot\mid X_{1:i-1}))$ of the expectation in (97).
--
--   **Formalization Note** The $i$-th summand only looks at the coordinates $0,\dots,i-1$ of the trajectory (Lean's restriction `frestrictLe₂`). The order of the two kernel families is the order of the arguments of $D^2_{\mathrm H}$.
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.13, eq. (97), p. 73

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq

open MeasureTheory ProbabilityTheory Finset Preorder
open scoped ENNReal

namespace HellingerSubadd

/-- **Sum of conditional squared Hellinger distances along a trajectory**
`x ↦ Σ_{i=1}^n D²_H(P^(i)(· | x_{1:i−1}), Q^(i)(· | x_{1:i−1}))`.
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.13, eq. (97), p. 73 (the integrand of the expectation on the right).

For a trajectory `x = (x_0, x_1, …, x_n)`, the `k`-th summand (`k = 0, …, n − 1`, i.e. the
paper's `i = k + 1`) is `D²_H(κ k (x_0, …, x_k), η k (x_0, …, x_k))`.

**Formalization Note.** `frestrictLe₂ k.2.le x` restricts the trajectory `x` on coordinates
`0, …, n` to coordinates `0, …, k`. Coordinate `0` is the common initial point of `seqLaw`; the
paper's `x_{1:i−1}` are coordinates `1, …, i − 1`. Values in `ℝ≥0∞`. The order of the two kernel
families is the order of the arguments of `D²_H`. -/
noncomputable def condHellingerSum {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1))) (n : ℕ) :
    (Π i : Iic n, X i) → ℝ≥0∞ :=
  fun x => ∑ k : Fin n,
    hellingerSq (κ k (frestrictLe₂ (π := X) k.2.le x)) (η k (frestrictLe₂ (π := X) k.2.le x))

end HellingerSubadd


