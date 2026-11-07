-- Prove2me | Definitions.Def_SecondBestBT_R3N
-- name    : SecondBestBT_R3N
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:02.732189+00:00
-- url     : https://prove2.me/theorems/de28d90c-0763-470c-a8f4-4aaa62302cab
-- title:
--   Allocation class $R_3$ on $\mathbb Z_{\ge0}^2$
-- statement:
--   The class $R_3$ on the unbounded grid $\mathbb Z_{\ge0}^2$ consists of all $x:\mathbb Z_{\ge0}^2\to[0,1]$ that are weakly increasing in the buyer value, weakly decreasing in the seller value, and satisfy $x(s,b)=0$ whenever $s\ge b$.
-- source:
--   Liu–Qin–Ren–Wang, Second-Best Bilateral Trade is 1/2 Efficient, arXiv:2606.03849 (held version, sha256 17184930…), Section 4.4, p.13

import Mathlib

namespace SecondBestBT

/-- The class `R3` on the unbounded grid `Z²_{≥0}` (Liu–Qin–Ren–Wang, arXiv:2606.03849, held
version sha256 17184930…, Section 4.4, p.13: "We write R3 for the allocation class on Z²≥0"):
`x : ℕ² → [0, 1]`, weakly increasing in the buyer value, weakly decreasing in the seller value,
and `x(s, b) = 0` whenever `s ≥ b`. -/
def R3N : Set (ℕ → ℕ → ℝ) :=
  {x | (∀ s b, x s b ∈ Set.Icc (0 : ℝ) 1) ∧ (∀ s, Monotone (x s)) ∧
    (∀ b, Antitone (fun s => x s b)) ∧ ∀ s b, b ≤ s → x s b = 0}

end SecondBestBT


