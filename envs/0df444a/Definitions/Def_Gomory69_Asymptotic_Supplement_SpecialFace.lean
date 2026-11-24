-- Prove2me | Definitions.Def_Gomory69_Asymptotic_Supplement_SpecialFace
-- name    : Gomory69_Asymptotic_Supplement_SpecialFace
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:22:48.502538+00:00
-- url     : https://prove2.me/theorems/ba0a04b7-437e-46f5-82fb-4e8262f780ce
-- title:
--   Special cyclic coefficients and the kernel–quotient combination
-- statement:
--   Let $H$ be a finite cyclic additive group of order $q$, and $H^+=H\setminus\{0\}$. Coefficients $\pi_2\in\mathbb R^{H^+}$ are special when there is a generator $h_1$ with
--   $$\pi_2(p h_1)=p/q\qquad(1\le p<q).$$
--   Allowing every generator includes every automorphic image of the displayed special face. The constant is $1$. This predicate specifies the coefficients directly; it does not assume that the desired combined inequality is a facet.
--
--   For a homomorphism $\psi:G\to H$ with kernel $K$, coefficients $\pi_1$ on $K^+$ and $\pi_2$ on $H^+$ combine as
--   $$\pi(g)=\begin{cases}\pi_1(g)&g\in K,\\\pi_2(\psi g)&g\notin K.\end{cases}$$
--   This is the piecewise coefficient vector used in Theorem 21. Every evaluation has a nonzero coordinate in its own group. The finite group order $q$ is positive, so division has no zero-denominator case.
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 490, special-face definition and THEOREM 21

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

/-- Special normalized coefficients of p. 490: all generator choices incorporate the
base special face and every automorphic image. This definition assumes no facet theorem. -/
def IsSpecial {H : Type*} [AddCommGroup H] [Fintype H] [DecidableEq H]
    (π : Gomory69.Lifting.Plus H → ℝ) : Prop :=
  ∃ h₁ : H, addOrderOf h₁ = Fintype.card H ∧
    ∀ p : ℕ, 0 < p → p < Fintype.card H →
      Gomory69.Lifting.ext π (p • h₁) = (p : ℝ) / (Fintype.card H : ℝ)

/-- Piecewise combination of the kernel coefficients and quotient coefficients (THEOREM 21).
Kernel membership is decided by `ψ g = 0`; the zero coordinate is never used. -/
def combineCoeff {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    [DecidableEq G] [DecidableEq H] (ψ : G →+ H)
    (π₁ : Gomory69.Lifting.Plus ψ.ker → ℝ)
    (π₂ : Gomory69.Lifting.Plus H → ℝ) : Gomory69.Lifting.Plus G → ℝ :=
  fun g => if hg : ψ (g : G) = 0 then
    π₁ ⟨⟨(g : G), hg⟩, by
      intro hz
      exact g.property (congrArg Subtype.val hz)⟩
    else π₂ ⟨ψ (g : G), hg⟩

end Gomory69.Asymptotic.Supplement


