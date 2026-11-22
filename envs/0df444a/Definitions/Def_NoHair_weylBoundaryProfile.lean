-- Prove2me | Definitions.Def_NoHair_weylBoundaryProfile
-- name    : NoHair_weylBoundaryProfile
-- status  : Definition
-- author  : @Igor Valuev
-- created : 2026-11-22T22:44:46.300432+00:00
-- url     : https://prove2.me/theorems/04f7678b-d203-4831-a377-ee5cb637675e
-- title:
--   Normalized axis and asymptotic estimates for a single horizon interval
-- statement:
--   For a horizon interval of half-length $\ell$, let $u$ be the mean of the two focal distances, $r=m+u$ and $c=z/u$. The two elementary reference functions are $A=(1-c^2)r^2$ and $Y_0=2J(3c-c^3)$. They give the vanishing scale for the axial norm and the two constant exterior-axis twist traces. For an Ernst pair $(X,Y)$ the estimates require $X/A$ bounded above and below by positive constants, $(Y-Y_0)/A$ bounded, and the two normalized quantities tending uniformly to $1$ and $0$ at spatial infinity. The factor $1-c^2$ retains control arbitrarily close to the axis. These definitions include the zero-length interval.
-- source:
--   S. Dain, A variational principle for stationary, axisymmetric solutions of Einstein’s equations, Appendix A, pp. 17–19, eqs. (90)–(94), (101)–(102), https://arxiv.org/abs/gr-qc/0508061. M. Visser, The Kerr spacetime: A brief introduction, eqs. (32)–(38), (53)–(57), https://arxiv.org/abs/0706.0622. P. T. Chruściel and J. L. Costa, §§6.4–6.7, including the normalized quadratures, https://arxiv.org/abs/0806.0016. P. T. Chruściel and J. L. Costa, On uniqueness of stationary vacuum black holes, §§6.4–6.7, eqs. (6.13)–(6.18), (6.45)–(6.47) and Cor. 6.3, https://arxiv.org/abs/0806.0016. For the degenerate end see Amsel et al., pp. 3–5, eqs. (6)–(16), https://arxiv.org/abs/0906.2367. For the global regularity hypotheses see Chruściel, Costa and Heusler, Def. 2.1 and Thm. 3.2, https://arxiv.org/abs/1205.6112.

import Definitions.Def_NoHair_kerrWeylModel

noncomputable section

namespace NoHair.Weyl

/-- The leading axial norm and normalized twist with a single horizon interval.
The polar factor keeps the estimates meaningful all the way to the rotation axis. -/
def rodBoundaryProfile (m ℓ J : ℝ) : ErnstPotentials :=
  let R := prolateRadius ℓ
  let c := fun p : OrbitPoint => p.2 / R p
  ⟨fun p => (1 - (c p)^2) * (m + R p)^2, fun p => 2*J*(3*c p - (c p)^3)⟩

/-- Global comparability of the axial norm, control of the twist on the same
scale, and uniform convergence of both normalized errors at spatial infinity. -/
def HasProfileEstimates (u b : ErnstPotentials) : Prop :=
  let X := fun p => u.normSq p / b.normSq p
  let Y := fun p => (u.twist p - b.twist p) / b.normSq p
  (∃ d B : ℝ, 0 < d ∧ ∀ p, d ≤ X p ∧ |X p - 1| ≤ B ∧ |Y p| ≤ B) ∧
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ p : OrbitPoint,
    R ≤ Real.exp (2*p.1) + p.2^2 → |X p - 1| ≤ ε ∧ |Y p| ≤ ε

end NoHair.Weyl


