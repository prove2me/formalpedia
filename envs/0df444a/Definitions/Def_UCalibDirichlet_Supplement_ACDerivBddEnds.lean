-- Prove2me | Definitions.Def_UCalibDirichlet_Supplement_ACDerivBddEnds
-- name    : UCalibDirichlet_Supplement_ACDerivBddEnds
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:11:23.025192+00:00
-- url     : https://prove2.me/theorems/29476fad-bbc9-4aec-b77d-d8632cca7128
-- title:
--   $F'$ absolutely continuous on $[0,1]$ with $F''$ bounded near $0$ and $1$
-- statement:
--   A function $F:[0,1]\to\mathbb R$ satisfies this condition when:
--
--   1. $F$ is differentiable on $[0,1]$ (one-sided at the endpoints), so that $F'$ is defined on $[0,1]$;
--   2. $F'$ is absolutely continuous on $[0,1]$;
--   3. $F''$ (the derivative of $F'$, which exists almost everywhere) is bounded near $0$ and $1$: there are $\eta\in(0,1/2)$ and $M$ with $|F''(x)|\le M$ for almost every $x\in[0,\eta]\cup[1-\eta,1]$.
--
--   This is the regularity hypothesis of Theorems 1.14 and E.1: it allows a curvature singularity in the interior of $[0,1]$ but none at the boundary.
--
--   **Formalization Note** Absolute continuity is Mathlib's notion on the interval $[0,1]$. Following the paper's convention, "curvature inequalities for an absolutely continuous derivative are understood a.e.", so the bound on $F''$ is an almost-everywhere bound.
-- source:
--   Frongillo, Luo, Mehta & Schneider, Near-Optimal Regret in U-Calibration for Every Proper Loss (manuscript, STOC 2027 submission), Theorem 1.14, p.8; Theorem E.1, p.41; App. E.1.1, p.40 (a.e. convention)

import Mathlib

open MeasureTheory

namespace UCalibDirichlet.Supplement

/-- **"`F′` is absolutely continuous on `[0, 1]` and `F″` is bounded near `0` and `1`".**
Frongillo, Luo, Mehta & Schneider (manuscript, STOC 2027 submission), Theorem 1.14, p.8: "Suppose
`F′` is absolutely continuous on `[0, 1]`, `F″` is bounded near 0 and 1"; Theorem E.1, p.41: "Let
`F′` be absolutely continuous on `[0, 1]`, …, and suppose `F″` is bounded on neighborhoods of 0 and
1"; App. E.1.1, p.40: "Curvature inequalities for an absolutely continuous derivative are
understood a.e."

`ACDerivBddEnds F` says:
1. `F` is differentiable within `[0, 1]` at every point of `[0, 1]` (one-sided at the endpoints),
   so `F′ = derivWithin F [0, 1]` is defined on `[0, 1]`;
2. `F′` is absolutely continuous on `[0, 1]`;
3. for some `η ∈ (0, 1/2)` and `M`, `|F″(x)| ≤ M` for almost every `x ∈ [0, η] ∪ [1 − η, 1]`, where
   `F″ = deriv F′` (which exists a.e. since `F′` is absolutely continuous).

**Formalization Note.** Absolute continuity is Mathlib's `AbsolutelyContinuousOnInterval`. Clause 1
makes explicit that `F′` exists on all of `[0, 1]`, which "F′ is absolutely continuous on [0, 1]"
presupposes. Clause 3 is the paper's a.e. reading of curvature bounds; at points where `F′` is not
differentiable `deriv` is the junk value `0`, but those points form a null set. -/
def ACDerivBddEnds (F : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, DifferentiableWithinAt ℝ F (Set.Icc 0 1) x) ∧
    AbsolutelyContinuousOnInterval (derivWithin F (Set.Icc 0 1)) 0 1 ∧
    ∃ η : ℝ, 0 < η ∧ η < 1 / 2 ∧ ∃ M : ℝ, ∀ᵐ x ∂volume,
      x ∈ Set.Icc 0 η ∪ Set.Icc (1 - η) 1 → |deriv (derivWithin F (Set.Icc 0 1)) x| ≤ M

end UCalibDirichlet.Supplement


