-- Prove2me | Definitions.Def_MatrixSpencer_Param22
-- name    : MatrixSpencer_Param22
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:41:00.965167+00:00
-- url     : https://prove2.me/theorems/2f6ecfed-a262-43e8-bf40-db8dfacdf1ef
-- title:
--   The parameter assumption (2.2)
-- statement:
--   The parameters $p\in\mathbb N$ and $\alpha,\beta,\eta\in\mathbb R$ satisfy $p\ge2$ and
--   $$\alpha\ge\beta>0,\quad \alpha>2,\quad \Gamma:=\frac\alpha2(3/4)^{2p-2}\ge8,\quad \Gamma\beta\ge32,\quad \eta\le\frac1{64}.$$
--   This is the standing assumption of §2.2 of the paper.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8, (2.2)

import Mathlib

namespace MatrixSpencer

/-- **The parameter assumption (2.2).**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…), §2.2, p.8: "for parameters p ≥ 2 and α ≥ β > 0 we consider, … We assume throughout this section
that α ≥ β > 0, α > 2, Γ := (α/2)(3/4)^{2p−2} ≥ 8, Γβ ≥ 32, η ≤ 1/64. (2.2)"

**Formalization Note.** `p` is a natural number, because it indexes the series `r_p` and is used as
a power. The condition `p ≥ 2` is printed just before (2.2). -/
def Param22 (α β : ℝ) (p : ℕ) (η : ℝ) : Prop :=
  2 ≤ p ∧ β ≤ α ∧ 0 < β ∧ 2 < α ∧
    8 ≤ (α / 2) * (3 / 4 : ℝ) ^ (2 * p - 2) ∧
    32 ≤ (α / 2) * (3 / 4 : ℝ) ^ (2 * p - 2) * β ∧
    η ≤ 1 / 64

end MatrixSpencer


