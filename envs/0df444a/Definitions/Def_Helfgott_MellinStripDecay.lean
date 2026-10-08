-- Prove2me | Definitions.Def_Helfgott_MellinStripDecay
-- name    : Helfgott_MellinStripDecay
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-05T18:20:00.107993+00:00
-- url     : https://prove2.me/theorems/77aa1501-a4cb-4547-b521-7075e75d756d
-- title:
--   Uniform polynomial Mellin decay on a strip with bounded additive phase
-- statement:
--   For a real smoothing $\eta$, a nonnegative integer order $n$, a real strip $[a,b]$ and a phase bound $W$, this predicate means there exists $C\ge0$ such that
--
--   $$
--   (1+|t|^n)\left|\mathcal M[\eta(u)e^{2\pi i\delta u}](\sigma+it)\right|\le C
--   $$
--
--   for every $a\le\sigma\le b$, $|\delta|\le W$ and $t\in\mathbb R$. It is only a definition of the full uniform decay property and does not assert that any smoothing satisfies it. No smoothing or transform tail is truncated. This named predicate supplies a compact theorem interface for the already prepared actual-smoothing decay proof.
-- source:
--   Helfgott, Major arcs for Goldbach’s problem, https://arxiv.org/abs/1305.2897; actual smoothing setup https://arxiv.org/html/1312.7748v2. Mathlib Mellin transform definition by David Loeffler. Named predicate for the existing complete arbitrary-order decay statement. Written by Codex.

import Mathlib.Analysis.MellinTransform

namespace Helfgott

/-- Uniform polynomial-order Mellin decay on a strip and bounded phase interval. -/
def MellinStripDecay (eta : Real → Real) (n : Nat) (a b W : Real) : Prop :=
  ∃ C : Real, 0 ≤ C ∧ ∀ sigma delta t : Real,
    a ≤ sigma → sigma ≤ b → abs delta ≤ W →
      ((1 : Real) + (abs t)^n) * norm (mellin
        (fun u : Real => (eta u : Complex) * Complex.exp
          (Complex.I * ((2 * Real.pi * delta : Real) : Complex) * (u : Complex)))
        ((sigma : Complex) + (t : Complex) * Complex.I)) ≤ C

end Helfgott


