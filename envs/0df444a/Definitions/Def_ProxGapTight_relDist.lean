-- Prove2me | Definitions.Def_ProxGapTight_relDist
-- name    : ProxGapTight_relDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:47:37.548629+00:00
-- url     : https://prove2.me/theorems/50ac4b8a-b49f-4b59-a9b9-342c1618cffa
-- title:
--   Relative distance $\delta(C)=d(C)/n$
-- statement:
--   For a linear code $C\subseteq R^{\iota}$ of length $n=|\iota|$, the **relative distance** is
--   $$
--   \delta(C)=\frac{d(C)}{n},
--   $$
--   where $d(C)$ is the minimum distance.
--
--   The relative distance is the normalized parameter in which the proximity-gaps question is posed: the radii $J_{3/2}(\delta)$ and $\Gamma(\delta)$ are functions of it.
--
--   **Formalization Note** A real number, the quotient of the two natural numbers. For the zero code it is $0$ (see the minimum distance).
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display

import Mathlib
import Definitions.Def_ProxGapTight_minDist

namespace ProxGapTight

/-- **Relative distance** `δ(C) := d(C)/n` of a linear code `C ⊆ R^ι`, `n = |ι|`, Kominers, Thaler,
Zheng, manuscript (Sept. 2026), §2, p.6, display.

**Formalization Note.** Real division of the cast natural numbers. For `C = ⊥` the value is `0`
(see `minDist`); statements about produced codes assert `C ≠ ⊥`. -/
noncomputable def relDist {R ι : Type} [Semiring R] [DecidableEq R] [Fintype ι]
    (C : Submodule R (ι → R)) : ℝ :=
  (minDist C : ℝ) / (Fintype.card ι : ℝ)

end ProxGapTight


