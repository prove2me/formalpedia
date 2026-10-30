-- Prove2me | Definitions.Def_PorteusGenSS_hFn
-- name    : PorteusGenSS_hFn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:17:43.340861+00:00
-- url     : https://prove2.me/theorems/c87a7bfa-92bd-46c8-9586-8e5df1396d5e
-- title:
--   Expected cost-to-go $h_n$
-- statement:
--   $h_n=(m+\alpha f_{n-1})*\varphi$: the expected holding/shortage cost of the period plus the discounted optimal future cost, as a function of the inventory level after ordering (equation (3)).
--
--   **Formalization Note** The Lean index is shifted by one: index $n$ gives $h_{n+1}=(m+\alpha f_n)*\varphi$, so $n=0$ gives $h_1$.
-- source:
--   Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), eq. (3), p. 413

import Mathlib
import Definitions.Def_PorteusGenSS_conv
import Definitions.Def_PorteusGenSS_valueFn

namespace PorteusGenSS

/-- **The functions hₙ, equation (3).**
Porteus, On the Optimality of Generalized (s, S) Policies, Management Science 17(7):411–426 (1971), §III, eq. (3), p. 413: "hn = L + αfn−1∗φ = (m + αfn−1)∗φ."

`hFn c α φ m f0 n = (m + α fₙ) ∗ φ`, which is the paper's `h_{n+1}`.

**Formalization Note.** The Lean index is shifted by one: `hFn … n` is the paper's `h_{n+1}`
(period `n + 1`), so that no natural-number subtraction appears; `hFn … 0 = (m + α f₀)∗φ = h₁`.
The paper's second form `(m + αf_{n−1})∗φ` of (3) is used. -/
noncomputable def hFn (c : ℝ → ℝ) (α : ℝ) (φ m f0 : ℝ → ℝ) (n : ℕ) : ℝ → ℝ :=
  conv (fun x => m x + α * valueFn c α φ m f0 n x) φ

end PorteusGenSS


