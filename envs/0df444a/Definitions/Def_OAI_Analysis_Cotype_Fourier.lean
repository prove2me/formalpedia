-- Prove2me | Definitions.Def_OAI_Analysis_Cotype_Fourier
-- name    : OAI_Analysis_Cotype_Fourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:25:36.863806+00:00
-- url     : https://prove2.me/theorems/a72cd525-de9f-4a13-b9cc-77ea75bef5d4
-- title:
--   Negation, parity and odd parts on the cube
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $\iota$ be finite.
--
--   1. **Negation.** $\varepsilon\mapsto-\varepsilon$ (flip all bits), an involution.
--   2. **Parity sign.** $(-1)^{|p|}$ for $p\in\{0,1\}^\iota$, the sign of $w_p$ under negation.
--   3. **Odd part and odd functions.**
--   $$
--   f^{\mathrm{odd}}(\varepsilon)=\tfrac12\bigl(f(\varepsilon)-f(-\varepsilon)\bigr),
--   $$
--   and $f$ is odd if $f(-\varepsilon)=-f(\varepsilon)$. The odd part keeps exactly the Fourier coefficients of odd degree.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/Fourier.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Fourier.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Cotype mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def negateCube (ε : ι → Bool) : ι → Bool := fun i => !(ε i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem negateCube_negateCube (ε : ι → Bool) :
    negateCube (negateCube ε) = ε := by funext i; simp [negateCube]

def negateEquiv : (ι → Bool) ≃ (ι → Bool) where
  toFun := negateCube
  invFun := negateCube
  left_inv := negateCube_negateCube
  right_inv := negateCube_negateCube

def paritySign (p : ι → Bool) : ℝ := ∏ i, if p i then -1 else 1

def oddPart (f : (ι → Bool) → ℝ) (ε : ι → Bool) : ℝ :=
  (f ε - f (negateCube ε)) / 2

def IsOdd (f : (ι → Bool) → ℝ) : Prop := ∀ ε, f (negateCube ε) = -f ε

end Cotype

end

end OAI


