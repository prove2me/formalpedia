-- Prove2me | Definitions.Def_BianchiIX_Algebra_Flow
-- name    : BianchiIX_Algebra_Flow
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T13:01:50.818802+00:00
-- url     : https://prove2.me/theorems/f670850c-8142-46a9-a2dd-f0e37ca65830
-- title:
--   Normalized vacuum Bianchi IX vector field
-- statement:
--   For real variables $p,s,a,b,c$, set
--   $$K=a^2+b^2+c^2-2(ab+bc+ca),\qquad S=p^2+s^2,\qquad C=S+K.$$
--   The shear components and wall rates are
--   $$P=Kp-2a^2+b^2+c^2+ab-2bc+ac,$$
--   $$Q=Ks+\sqrt{3}(-b^2+c^2+ab-ac),$$
--   $$r_1=-S+2p,\qquad r_2=-S-p+\sqrt{3}s,\qquad r_3=-S-p-\sqrt{3}s.$$
--   These functions define the normalized vacuum Bianchi IX vector field
--   $(P,Q,r_1a,r_2b,r_3c)$.
--
--   The constraint and rates give the algebraic quantities used in the conservation and growth estimates.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Algebra/Flow.lean

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Exact normalized vacuum Bianchi IX equations. -/

namespace BianchiIX

noncomputable section

def curvature (a b c : ℝ) : ℝ :=
  a ^ 2 + b ^ 2 + c ^ 2 - 2 * (a * b + b * c + c * a)

def shearSq (p s : ℝ) : ℝ := p ^ 2 + s ^ 2

def constraint (p s a b c : ℝ) : ℝ := shearSq p s + curvature a b c

def shearPlus (p a b c : ℝ) : ℝ :=
  curvature a b c * p - 2 * a ^ 2 + b ^ 2 + c ^ 2 + a * b - 2 * b * c + a * c

def shearMinus (s a b c : ℝ) : ℝ :=
  curvature a b c * s + Real.sqrt 3 * (-b ^ 2 + c ^ 2 + a * b - a * c)

def rateOne (p s : ℝ) : ℝ := -shearSq p s + 2 * p
def rateTwo (p s : ℝ) : ℝ := -shearSq p s - p + Real.sqrt 3 * s
def rateThree (p s : ℝ) : ℝ := -shearSq p s - p - Real.sqrt 3 * s



















end

end BianchiIX


