-- Prove2me | Definitions.Def_MemQueryFeas_delta
-- name    : MemQueryFeas_delta
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:33:27.449889+00:00
-- url     : https://prove2.me/theorems/7ae9ea6e-d269-4c16-9bc7-ac8a744b4704
-- title:
--   The accuracies $\delta_p^{(i)}$
-- statement:
--   The accuracies of layer $p$ are
--   $$
--   \delta_p^{(i)}=d^{-1}\varepsilon^{\frac{p-1}{2P}}\lambda_p^{\,i},\qquad i=0,1,\dots,N_p .
--   $$
--
--   **Formalization Note** The printed range "$i\in[N_p]$" omits $i=0$, which Algorithm 1 and Lemma 4 use.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_MemQueryFeas_lam

namespace MemQueryFeas

/-- **The accuracies `δ_p^(i)`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), §3.1, p.7 (PDF p.8): "`δ_p^(i) = d^{−1} ϵ^{(p−1)/(2P)} λ_p^i`".

**Formalization Note.** Defined for every `i ≥ 0`; the construction uses `i = 0, …, N_p` (the printed
range "`∀i ∈ [N_p]`" omits `i = 0`, but Algorithm 1 and Lemma 4 use `δ_p^(0)`). -/
noncomputable def delta (d : ℕ) (ε : ℝ) (P p i : ℕ) : ℝ :=
  (d : ℝ)⁻¹ * ε ^ (((p : ℝ) - 1) / (2 * (P : ℝ))) * lam d p ^ i

end MemQueryFeas


