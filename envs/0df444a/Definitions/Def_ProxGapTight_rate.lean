-- Prove2me | Definitions.Def_ProxGapTight_rate
-- name    : ProxGapTight_rate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:44:41.974633+00:00
-- url     : https://prove2.me/theorems/41a6726e-0bb9-467a-8ab3-56e23f43b519
-- title:
--   Rate $R(C)=\dim C/n$
-- statement:
--   For a linear code $C\subseteq R^{\iota}$ of length $n=|\iota|$, the **rate** is
--   $$
--   R(C)=\frac{\dim C}{n}.
--   $$
--
--   Together with the relative distance it measures the quality of a code; the Singleton bound gives $R(C)\le 1-\delta(C)+1/n$, and the main theorem produces codes whose rate is within $O(1/s)$ of $1-\delta(C)$.
--
--   **Formalization Note** $\dim C$ is the rank of $C$ as a module, and the quotient is taken in the reals.
-- source:
--   Kominers, Thaler, Zheng, The One-and-a-Half Johnson Bound Is Tight for Proximity Gaps of General Linear Codes, manuscript (Sept. 2026; STOC 2027 submission; sha256 ac050071…), §2, p.6, display

import Mathlib

namespace ProxGapTight

/-- **Rate** `R(C) := dim C / n` of a linear code `C ⊆ R^ι`, `n = |ι|`, Kominers, Thaler, Zheng,
manuscript (Sept. 2026), §2, p.6, display.

**Formalization Note.** `dim C` is `Module.finrank R C`; real division of the casts. -/
noncomputable def rate {R ι : Type} [Semiring R] [Fintype ι] (C : Submodule R (ι → R)) : ℝ :=
  (Module.finrank R C : ℝ) / (Fintype.card ι : ℝ)

end ProxGapTight


