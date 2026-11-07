-- Prove2me | Definitions.Def_SecondBestBT_interimS
-- name    : SecondBestBT_interimS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:42:38.963194+00:00
-- url     : https://prove2.me/theorems/916176c5-b974-4a36-ae31-a12f40deb62b
-- title:
--   Seller's interim allocation $x_S(s)$
-- statement:
--   The seller's **interim allocation** is the probability of trade of a seller reporting $s$, averaged over the buyer:
--   $$
--   x_S(s)=\int x(s,b)\,dF_B(b).
--   $$
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 3, p.5

import Mathlib

open MeasureTheory

namespace SecondBestBT

/-- The seller's interim allocation `x_S(s) := ∫ x(s, b) dF_B(b)` (Liu–Qin–Ren–Wang,
arXiv:2606.03849, held version sha256 17184930…, Section 3, p.5). -/
noncomputable def interimS (μB : Measure ℝ) (x : ℝ × ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ b, x (s, b) ∂μB

end SecondBestBT


