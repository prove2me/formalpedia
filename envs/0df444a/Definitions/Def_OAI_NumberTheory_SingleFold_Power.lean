-- Prove2me | Definitions.Def_OAI_NumberTheory_SingleFold_Power
-- name    : OAI_NumberTheory_SingleFold_Power
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T16:28:42.971015+00:00
-- url     : https://prove2.me/theorems/f17577cf-0bb4-4806-a48e-b8e729477594
-- title:
--   A Pell-equation system for exponentiation with a growth bound
-- statement:
--   Let $g:\mathbb{N}\to\mathbb{N}$, and $\ell,u_0,b,n,c\in\mathbb{N}$.
--
--   1. The input is $u=(c+1)^\ell(n+1)(b+1)+u_0$.
--   2. The system for $w\in\mathbb{N}^9$ requires $b\ge2$, $w_0=u$, $w_1=g(w_0)$, and
--   $$
--   w_2^2+w_3^2=1+(bw_0)^2w_3^2,\qquad w_4^2+w_5^2=1+w_0^2w_5^2,
--   $$
--      together with $0<w_3<w_1$, $0<w_5<w_1$, $w_3=n+1+(bw_0-1)w_6$, $w_5=n+1+(w_0-1)w_7$, and $w_3=cw_5+w_8$ with $w_8<w_5$.
--   3. $p_x(a,n)$ and $p_y(a,n)$ are the Pell solutions of index $n$ for $a>1$, and $0$ otherwise.
--
--   The two Pell equations force $w_3$ and $w_5$ to be Pell $y$-values of index $n+1$ for the parameters $bw_0$ and $w_0$; their quotient $c$ then approximates $b^n$. The function $g$, with $\delta(\log u)^2<\log g(u)<u\log u$ for large $u$, bounds the witnesses.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/SingleFold/Power.lean

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Power.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SingleFold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.PowerEstimate
def input (ell u₀ b n c : ℕ) := (c+1)^ell*(n+1)*(b+1)+u₀
end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

def System (g : ℕ → ℕ) (ell u₀ b n c : ℕ) (w : Fin 9 → ℕ) : Prop :=
  2≤b ∧ w 0=input ell u₀ b n c ∧ w 1=g (w 0) ∧
  (w 2)^2+(w 3)^2=1+(b*w 0)^2*(w 3)^2 ∧
  (w 4)^2+(w 5)^2=1+(w 0)^2*(w 5)^2 ∧
  0<w 3 ∧ w 3<w 1 ∧ 0<w 5 ∧ w 5<w 1 ∧
  w 3=n+1+(b*w 0-1)*w 6 ∧ w 5=n+1+(w 0-1)*w 7 ∧
  w 3=c*w 5+w 8 ∧ w 8<w 5
noncomputable def px (a n : ℕ) : ℕ := if ha : 1<a then Pell.xn ha n else 0
noncomputable def py (a n : ℕ) : ℕ := if ha : 1<a then Pell.yn ha n else 0
variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
end SingleFold.PowerCompilation

end OAI


