-- Prove2me | Definitions.Def_MatroidOptGame_Supplement_heavyWeight
-- name    : MatroidOptGame_Supplement_heavyWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:48:23.817772+00:00
-- url     : https://prove2.me/theorems/f8ab9553-3540-4c58-beb5-f893276a3ffc
-- title:
--   Weights of the hard instances: $w(0)=w(1)=1$, $w(i)=0$ otherwise
-- statement:
--   On the ground set $E_n=\{0,1,\dots,2n-1\}$ of the hard instances of Section 2.2 the weight function is
--   $$
--   w(0)=w(1)=1,\qquad w(i)=0\quad (i\in E_n\setminus\{0,1\}).
--   $$
--   The two **heavy** elements $0,1$ are paired in every matroid of the families $\mathcal M_{n,S_0,\pi}$ and $\mathcal M_{n,H}$; a base costs $0$, $1$ or $2$ according to how many of them it contains.
--
--   **Formalization Note** The function is defined on $\mathrm{Fin}\,m$ for every $m$ (used with $m=2n$), with elements named by their value.
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, p.12 (also Section 2.2.2, p.15)

import Mathlib

namespace MatroidOptGame.Supplement

/-- The weights of the Section 2.2 hard instances on `E_n = {0, 1, …, 2n − 1}` (here `Fin m`,
`m = 2n`): `w(0) = w(1) = 1` and `w(i) = 0` for every other element.
Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, p.12 ("Set w(0) = w(1) = 1, and for all i ∈ E_n ∖ {0, 1} set w(i) = 0"),
reused in Section 2.2.2, p.15. -/
def heavyWeight {m : ℕ} (i : Fin m) : ℕ :=
  if i.val < 2 then 1 else 0

end MatroidOptGame.Supplement


