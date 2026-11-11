-- Prove2me | Definitions.Def_SoSLinAlg_WeakRank_Z
-- name    : SoSLinAlg_WeakRank_Z
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T22:30:41.361538+00:00
-- url     : https://prove2.me/theorems/f31b5fc4-1563-498b-9269-beaae83e2ca1
-- title:
--   Rank-bounded real zero locus and polynomial evaluation
-- statement:
--   For nonnegative integers $n,r,d$, the real rank-bounded zero locus is
--   $$Z_d=\{(X,Y)\in\mathbb R^{n\times r}\times\mathbb R^{n\times r}:XY^\top=0,\ \operatorname{rank}X+\operatorname{rank}Y\le d\}.$$
--   The assignment map sends each formal $X$ coordinate to the corresponding entry of the first real matrix and each formal $Y$ coordinate to the corresponding entry of the second. A polynomial $f\in\mathbb R[X,Y]$ vanishes on $Z_d$ if
--   $$\forall (X,Y)\in Z_d,\qquad f(X,Y)=0.$$
--
--   Ranks are real matrix ranks. The definition includes $d=0$, where $Z_0=\{(0,0)\}$, as explicitly used by the source in the proofs of Propositions 4.1 and 4.2 and in Section 4.3. This module supplies the shared evaluation and vanishing predicates for the two auxiliary propositions.
-- source:
--   Dmitriy Kunisky, Xifan Yu, The sum-of-squares complexity of linear-algebraic principles, STOC 2027 submission #1181 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1181.pdf, §3, equation (1), PDF p.13 (printed p.11); d=0 used PDF pp.14,17–18 (printed pp.12,15–16)

import Mathlib
import Definitions.Def_SoSLinAlg_WeakRank_WRank

noncomputable section

namespace SoSLinAlg.WeakRank

/-- The real assignment of both matrices to their respective indeterminates. -/
def assignment {n r : ℕ} (X Y : Matrix (Fin n) (Fin r) ℝ) : Var n r → ℝ :=
  Sum.elim (fun ik => X ik.1 ik.2) (fun ik => Y ik.1 ik.2)

/-- Equation (1), PDF p.13 (printed p.11). Defined also at d = 0, as used
explicitly in Propositions 4.1 and 4.2 and in §4.3. -/
def Z (n r d : ℕ) : Set (Matrix (Fin n) (Fin r) ℝ × Matrix (Fin n) (Fin r) ℝ) :=
  {p | p.1 * p.2.transpose = 0 ∧ p.1.rank + p.2.rank ≤ d}

/-- Vanishing on precisely the real rank-bounded locus, not its complexification. -/
def VanishesOnZ {n r : ℕ} (d : ℕ) (f : Poly n r) : Prop :=
  ∀ X Y : Matrix (Fin n) (Fin r) ℝ, (X, Y) ∈ Z n r d →
    MvPolynomial.eval (assignment X Y) f = 0

end SoSLinAlg.WeakRank
end


