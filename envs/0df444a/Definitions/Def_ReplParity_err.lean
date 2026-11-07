-- Prove2me | Definitions.Def_ReplParity_err
-- name    : ReplParity_err
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:47.757844+00:00
-- url     : https://prove2.me/theorems/cccf0fe5-e876-44de-9e90-9db795f07542
-- title:
--   Error $\mathrm{err}_D(h)$ of a hypothesis
-- statement:
--   For a labeled distribution $D$ on $X\times\{0,1\}$ and a function $h:X\to\{0,1\}$,
--   $$\mathrm{err}_D(h)=\Pr_{(x,y)\sim D}[h(x)\ne y]=\sum_{(x,y):\,h(x)\ne y}D(x,y).$$
--
--   **Formalization Note** The domain $X$ is finite (the finite-bit model of §2.2) and labels are elements of $\mathbb F_2$.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), §2.1, p.10 (PDF p.12)

import Mathlib

namespace ReplParity

open Classical in
/-- **Error of a hypothesis.** Shen, Zhong, *Replicable Parity Learning: Cubic Sample Complexity
and a Geometric Characterization*, STOC 2027 submission (manuscript sha256 40424491…), §2.1, p.10
(PDF p.12): "The error of a function h: X → {0, 1} is err_D(h) = Pr_{(x,y)∼D}[h(x) ≠ y]."

**Formalization Note.** The domain `X` is finite (§2.2: "sample domains are finite") and the label
set `{0, 1}` is `ZMod 2`. -/
noncomputable def err {X : Type*} [Fintype X] (D : PMF (X × ZMod 2)) (h : X → ZMod 2) : ℝ :=
  ∑ e : X × ZMod 2, if h e.1 ≠ e.2 then (D e).toReal else 0

end ReplParity


