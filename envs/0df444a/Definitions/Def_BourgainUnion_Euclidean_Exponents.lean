-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_Exponents
-- name    : BourgainUnion_Euclidean_Exponents
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:07.616629+00:00
-- url     : https://prove2.me/theorems/d7b3d7b7-ef81-4346-8533-5eed8f3b5114
-- title:
--   The two optimized extension exponents
-- statement:
--   The Euclidean exponent $\eta_0$ is the infimum of the roots $\eta\ge1$ of
--   $$\eta(\eta+2)(\eta^2+4\eta-4)=2\pi.$$
--   For $0\le z\le1$, define
--   $$D_\eta(z)=(1+\eta)^2(1-z^2)^2+(1+\eta/2)^2z^2(2-z^2)-\tfrac12(z+1)^2(2-z^2).$$
--   The one-point exponent $\eta_1$ is the infimum of nonnegative $\eta$ such that $D_\eta(z)\ge0$ for every $z\in[0,1]$. These are real infima; their admissible sets are nonempty and bounded below as established by the subsequent Lemma 1.5 item, which also certifies the root and minimizing properties and their rational intervals. Thus no default infimum value supplies a bound. These definitions preserve the proof's exact exponents before passing to the printed decimal bounds.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 20–22, equations (16), (18)–(19)

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Equation (16); the accompanying milestone establishes existence and the certified interval. -/
def eta0 : ℝ := sInf {η : ℝ | 1 ≤ η ∧ η*(η+2)*(η^2+4*η-4) = 2*Real.pi}

def exponentGap (η z : ℝ) : ℝ :=
  (1+η)^2 * (1-z^2)^2 + (1+η/2)^2 * z^2*(2-z^2) - (1/2)*(z+1)^2*(2-z^2)

/-- Equations (18)--(19); nonemptiness, minimality and the interval are theorem conclusions. -/
def eta1 : ℝ := sInf {η : ℝ | 0 ≤ η ∧ ∀ z ∈ Set.Icc (0:ℝ) 1, 0 ≤ exponentGap η z}

end BourgainUnion.Euclidean


