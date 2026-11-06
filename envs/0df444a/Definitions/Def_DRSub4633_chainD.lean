-- Prove2me | Definitions.Def_DRSub4633_chainD
-- name    : DRSub4633_chainD
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:01:56.201048+00:00
-- url     : https://prove2.me/theorems/197c579e-c602-4e11-a7e6-bd5b8a9dba42
-- title:
--   The chain increments $d$
-- statement:
--   Fix $f$ and the state $x$. Let $\gamma_i=h(x_i)-\alpha_0x_i$ and let $\pi$ order the coordinates by nonincreasing $\gamma$, ties broken by index, with prefixes $C_0=\varnothing$, $C_\iota=\{\pi(1),\dots,\pi(\iota)\}$. The chain increments are
--   $$d_{\pi(\iota)}=f(\mathbf 1_{C_\iota})-f(\mathbf 1_{C_{\iota-1}}).$$
--   They are the coefficients of the greedy affine lower bound of $f$.
--
--   **Formalization Note** The dummy coordinate has increment $0$ and does not change the others; it is omitted.
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Section 4.1, Eq. (11), p.10

import Mathlib
import Definitions.Def_DRSub4633_hScalar
import Definitions.Def_DRSub4633_alpha0

namespace DRSub4633

/-- **The chain increments `d`.** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Section 4.1, Eq. (11), p.10: "The coefficients are
`γᵢ = h(xᵢ) − α₀xᵢ`, and the permutation `π(1), . . . , π(n)` orders them nonincreasingly, with ties
broken by index. The prefixes are `C₀ = ∅` and `C_ι = {π(1), . . . , π(ι)}` … `d_π(ι) = f(1_C_ι) −
f(1_C_(ι−1))`."

For a coordinate `j`, `C_ι` with `π(ι) = j` is the set of `k` with `k ⪯ j`, where `k ≺ j` means
`γ_k > γ_j`, or `γ_k = γ_j` and `k < j`; so `d_j = f(1_{k ⪯ j}) − f(1_{k ≺ j})`.

**Formalization Note.** The dummy coordinate's increment is zero and it does not change the other
increments (`f` does not depend on it, p.10), so it is omitted. -/
noncomputable def chainD {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (j : Fin n) : ℝ :=
  let γ : Fin n → ℝ := fun i => hScalar (x i) - alpha0 * x i
  f (WithLp.toLp 2 (fun k => if γ j < γ k ∨ (γ k = γ j ∧ k ≤ j) then 1 else 0)) -
    f (WithLp.toLp 2 (fun k => if γ j < γ k ∨ (γ k = γ j ∧ k < j) then 1 else 0))

end DRSub4633


