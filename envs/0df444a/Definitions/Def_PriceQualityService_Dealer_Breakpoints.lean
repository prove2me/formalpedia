-- Prove2me | Definitions.Def_PriceQualityService_Dealer_Breakpoints
-- name    : PriceQualityService_Dealer_Breakpoints
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T17:31:25.851608+00:00
-- url     : https://prove2.me/theorems/9a92d257-cb19-422c-a5bc-a8a3853b0a49
-- title:
--   The functions $h^l_i,h^s_i,h_i,H$ and the adjusted markup $x_i$ of the proof of Theorem 5
-- statement:
--   In the setting of the dealer's problem (13), define for each product $i$ and each real $r$
--
--   $$
--   h^l_i(r)=\big[p_i-c_iq_i^2-t_l(a_i-b_iq_i)-r\big]\exp(\alpha_iq_i-p_i+t_ls_i),\qquad h^s_i(r)=\big[p_i-c_iq_i^2-t_s(a_i-b_iq_i)-r\big]\exp(\alpha_iq_i-p_i+t_ss_i),
--   $$
--
--   $h_i(r)=\max\{h^l_i(r),h^s_i(r),0\}$ and $H(r)=\sum_{i\in\mathcal N}h_i(r)$. Define also
--
--   $$
--   A_i=\frac{t_l\exp(t_ls_i)-t_s\exp(t_ss_i)}{\exp(t_ls_i)-\exp(t_ss_i)},\qquad x_i=(p_i-c_iq_i^2)-A_i\,(a_i-b_iq_i),
--   $$
--
--   the **adjusted markup** of product $i$. The long- and short-service markups $y_i=p_i-c_iq_i^2-t_l(a_i-b_iq_i)$ and $z_i=p_i-c_iq_i^2-t_s(a_i-b_iq_i)$ are the markups of the model definition evaluated at $t_l$ and $t_s$.
--
--   These are the auxiliary functions through which the paper reduces the combinatorial problem (13) to a one-dimensional fixed-point equation $r=H(r)$; the adjusted markups order the products that should receive the long service.
--
--   **Formalization Note** When $s_i=0$ or $t_s=t_l$ the denominator of $A_i$ vanishes and Lean's convention $x/0=0$ gives $A_i=0$; every theorem that uses $A_i$ assumes $t_s<t_l$ and $s_i>0$, under which the denominator is positive.
-- source:
--   Wang, Ke & Cui, Product Price, Quality and Service Decisions under Consumer Choice Models, accepted manuscript (SSRN 3766191), p. 23 (A_i and adjusted markups); Online Supplement p. 8 (PDF p. 41), Proof of Theorem 5

import Mathlib
import Definitions.Def_PriceQualityService_Dealer_Model

namespace PriceQualityService.Dealer

open Finset

/-- `h^l_i(r) = [p_i − c_i q_i² − t_l(a_i − b_i q_i) − r] · exp(α_i q_i − p_i + t_l s_i)`
(Proof of Theorem 5, Online Supplement p. 8). -/
noncomputable def hLong {N : ℕ} (α a b c s p q : Fin N → ℝ) (tl : ℝ) (i : Fin N) (r : ℝ) : ℝ :=
  (markup a b c p q tl i - r) * attraction α s p q tl i

/-- `h^s_i(r) = [p_i − c_i q_i² − t_s(a_i − b_i q_i) − r] · exp(α_i q_i − p_i + t_s s_i)`
(Proof of Theorem 5, Online Supplement p. 8). -/
noncomputable def hShort {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts : ℝ) (i : Fin N) (r : ℝ) : ℝ :=
  (markup a b c p q ts i - r) * attraction α s p q ts i

/-- `h_i(r) = max{h^l_i(r), h^s_i(r), 0}` (Online Supplement p. 8). -/
noncomputable def hMax {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) (r : ℝ) :
    ℝ :=
  max (max (hLong α a b c s p q tl i r) (hShort α a b c s p q ts i r)) 0

/-- `H(r) = ∑_{i ∈ 𝒩} h_i(r)` (Online Supplement p. 8). -/
noncomputable def bigH {N : ℕ} (α a b c s p q : Fin N → ℝ) (ts tl : ℝ) (r : ℝ) : ℝ :=
  ∑ i, hMax α a b c s p q ts tl i r

/-- `A_i = (t_l exp(t_l s_i) − t_s exp(t_s s_i)) / (exp(t_l s_i) − exp(t_s s_i))` (p. 23).
The denominator vanishes when `s_i = 0` or `t_s = t_l`; there Lean's `x / 0 = 0` gives `A_i = 0`,
and every theorem using `A_i` assumes `t_s < t_l` and `0 < s_i`. -/
noncomputable def adjFactor {N : ℕ} (s : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  (tl * Real.exp (tl * s i) - ts * Real.exp (ts * s i)) /
    (Real.exp (tl * s i) - Real.exp (ts * s i))

/-- The adjusted markup `x_i = (p_i − c_i q_i²) − A_i (a_i − b_i q_i)` (p. 23; Online Supplement
p. 8). -/
noncomputable def adjustedMarkup {N : ℕ} (a b c s p q : Fin N → ℝ) (ts tl : ℝ) (i : Fin N) : ℝ :=
  (p i - c i * q i ^ 2) - adjFactor s ts tl i * (a i - b i * q i)

end PriceQualityService.Dealer


