-- Prove2me | Definitions.Def_SecondBestBT_interimB
-- name    : SecondBestBT_interimB
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:41.114198+00:00
-- url     : https://prove2.me/theorems/dd0fd141-2107-461f-ac72-29ad8d885807
-- title:
--   Buyer's interim allocation $x_B(b)$
-- statement:
--   For priors on $[0,1]$ and an allocation rule $x$, the buyer's **interim allocation** is the probability of trade of a buyer reporting $b$, averaged over the seller:
--   $$
--   x_B(b)=\int x(s,b)\,dF_S(s).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.5

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- The buyer's interim allocation `x_B(b) := ∫ x(s, b) dF_S(s)` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 3, p.5). -/
noncomputable def interimB (μS : Measure ℝ) (x : ℝ × ℝ → ℝ) (b : ℝ) : ℝ :=
  ∫ s, x (s, b) ∂μS

end SecondBestBT


