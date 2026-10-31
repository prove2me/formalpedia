-- Prove2me | Definitions.Def_GuoZhaoADRC_Xi
-- name    : GuoZhaoADRC_Xi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:37:58.544988+00:00
-- url     : https://prove2.me/theorems/de439320-4e1d-4941-af7d-5604e42fc0a1
-- title:
--   Gain-mismatch constant $\Xi^i=\sqrt m\sum_{k,l}|a_{ik}-b_{ik}|\,|b^*_{kl}|\,\Lambda^l_{n_l+1}$ (3.9)
-- statement:
--   For subsystem $i$,
--
--   $$\Xi^i=\sqrt m\sum_{k,l=1}^m|a_{ik}-b_{ik}|\,|b^*_{kl}|\,\Lambda^l_{n_l+1}.$$
--
--   It is the coefficient of $\|e\|/\varepsilon$ in the bound (3.9) on the derivative of the extended state: through the mismatch $a_{ik}-b_{ik}$, the fast observer state $\hat x^l_{n_l+1}$ enters the extended state $x^i_{n_i+1}$.
--
--   **Formalization Note** The page writes $\sup_{t\in[0,\infty)}|a_{ik}(w_i(t))-b_{ik}|\,b^*_{kl}$. With the corrections of Theorem 3.1 ($a_{ik}$ constant, $|b^*_{kl}|$ in (3.1)) the supremum is $|a_{ik}-b_{ik}|$ and $b^*_{kl}$ appears in absolute value.
-- source:
--   B.-Z. Guo, Z.-L. Zhao, On convergence of the nonlinear active disturbance rejection control for MIMO systems, SIAM J. Control Optim. 51(2) (2013) 1727–1757, doi:10.1137/110856824, eq. (3.9), p.1738

import Mathlib
import Definitions.Def_GuoZhaoADRC_ADRCData

namespace GuoZhaoADRC

/-- **The gain-mismatch constant `Ξ^i = √m ∑_{k,l} |a_ik − b_ik| |b*_kl| Λ^l_{n_l+1}`.**
Guo–Zhao, SIAM J. Control Optim. 51 (2013), eq. (3.9), p.1738 (corrected).

**Formalization Note.** The page writes `sup_{t∈[0,∞)} |a_ik(w_i(t)) − b_ik| b*_kl`; with the
corrections of GA2 (`a_ik` constant) and of (3.1) (`|b*_kl|`) the supremum is the constant
`|a_ik − b_ik|` and `b*_kl` appears in absolute value. `(b*_kl) = b⁻¹`. -/
noncomputable def Xi {m : ℕ} {n : Fin m → ℕ} {s : ℕ} (D : ADRCData m n s) (i : Fin m) : ℝ :=
  Real.sqrt m * ∑ k, ∑ l, |D.a i k - D.b i k| * |D.b⁻¹ k l| * D.Λ l (Fin.last (n l))

end GuoZhaoADRC


