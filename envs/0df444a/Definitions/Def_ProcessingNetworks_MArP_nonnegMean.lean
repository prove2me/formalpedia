-- Prove2me | Definitions.Def_ProcessingNetworks_MArP_nonnegMean
-- name    : ProcessingNetworks_MArP_nonnegMean
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:28:28.000716+00:00
-- url     : https://prove2.me/theorems/116e562b-ef51-4272-9a62-d4a7f5ff3cf4
-- title:
--   The mean $\pi(f)$ of a nonnegative function under a distribution (eq. (C.13))
-- statement:
--   For a probability distribution $\pi$ on a countable set $\mathcal S$ and a function $g:\mathcal S\to\mathbb R$, this is
--   $$
--   \sum_{i\in\mathcal S} g^+(i)\,\pi(i)\in[0,\infty],
--   $$
--   with $g^+=\max(g,0)$. For a nonnegative $f$ it is the book's $\pi(f)$ of (C.13), which can be infinite. Applied to $f$ and to $-f$ it gives the two quantities $\pi(f^+)$ and $\pi(f^-)$ whose difference defines $\pi(f)$ for a general function.
-- source:
--   Dai & Harrison, Processing Networks (pre-publication draft 2020-4-2, spnbook.org), eq. (C.13), p.280 (PDF p.296)

import Mathlib

open scoped ENNReal

namespace ProcessingNetworks.MArP

/-- The `π`-mean `π(g) = ∑_{i ∈ S} g(i) π(i)` of the nonnegative part of a function, eq. (C.13)
(Dai & Harrison, Processing Networks, pre-publication draft 2020-4-2, p.280, PDF p.296), which can
be infinite.

**Formalization Note.** The value lies in `ℝ≥0∞`. For a real function `g` the summand uses
`ENNReal.ofReal (g i) = max (g i) 0`, so `nonnegMean π f` is the book's `π(f⁺)` and
`nonnegMean π (fun i => -f i)` is the book's `π(f⁻)`. -/
noncomputable def nonnegMean {S : Type*} (π : PMF S) (g : S → ℝ) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (g i) * π i

end ProcessingNetworks.MArP


