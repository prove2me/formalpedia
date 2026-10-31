-- Prove2me | Definitions.Def_PlatformCournot_worstSlope
-- name    : PlatformCournot_worstSlope
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:26.471101+00:00
-- url     : https://prove2.me/theorems/87061cb2-1cc5-4fb8-a1c3-dbe015c1d247
-- title:
--   Slopes of the worst-case linear cost profile $\bar C^*$
-- statement:
--   For $n$ firms, a market with maximal willingness to pay $a$ and a slope $c_1$, the worst-case profile $\bar C^*$ of the proof of Theorem 1 has the linear costs $\bar C^*_1(s)=(c_1 s)^+$ and $\bar C^*_i(s)=(c^*_i s)^+$, $i=2,\dots,n$, with
--
--   $$c^*_i=a-\frac{2n+3}{3n+5}\,(a-c_1).$$
--
--   This function returns the slope of each firm: $c_1$ for firm 1 and $c^*_i$ for the others.
--
--   **Formalization Note** Firms are `Fin n`, 0-based: the paper's firm 1 is index 0.
-- source:
--   Pang, Lin, Fu, Kleeman, Bitar, Wierman, Transparency and Control in Platforms for Networked Markets, arXiv:1903.04574v3, Appendix A.3, p.29

import Mathlib

namespace PlatformCournot

/-- **Slopes of the worst-case linear cost profile `C̄*`.**
Pang et al., arXiv:1903.04574v3, Appendix A.3, p.29: "The optimal value of c2,...,cn is given by
c∗i = α1 − (2n + 3)/(3n + 5)(α1 − c1), for i = 2,...,n. … Define the cost function profile
C̄∗ = (C̄∗1,...,C̄∗n) according to C̄∗1(s1) = (c1s1)+ and C̄∗i(si) = (c∗i si)+ for i = 2,...,n."

`worstSlope n a c₁ i` is `c₁` for the first firm and `a − (2n+3)/(3n+5) · (a − c₁)` for every other
firm, where `a` is the market's maximal willingness to pay.

**Formalization Note** Firms are `Fin n`, 0-based: the paper's firm 1 is index `0`. -/
noncomputable def worstSlope (n : ℕ) (a c₁ : ℝ) (i : Fin n) : ℝ :=
  if (i : ℕ) = 0 then c₁ else a - (2 * (n : ℝ) + 3) / (3 * (n : ℝ) + 5) * (a - c₁)

end PlatformCournot


