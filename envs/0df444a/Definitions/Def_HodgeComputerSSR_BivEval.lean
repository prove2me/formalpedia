-- Prove2me | Definitions.Def_HodgeComputerSSR_BivEval
-- name    : HodgeComputerSSR_BivEval
-- status  : Definition
-- author  : @benediamond
-- created : 2026-11-24T09:49:12.849371+00:00
-- url     : https://prove2.me/theorems/0cd29f23-7e86-4c8c-98be-c19be124b76b
-- title:
--   $K_5$ bivariate evaluator `evalBivK5`, `L_K`, and `bivFilterX0`/`bivFilterX1`
-- statement:
--   Defines the $K_5$ evaluation map `evalBivK5` for sparse bivariate polynomial ASTs, the linear factor $L_K = 77 S - 210 Q + 45$, and the $x$-degree splitting filters `bivFilterX0` and `bivFilterX1`.
-- source:
--   https://github.com/hodge-computer/sextics/blob/79defa555452e16e3125da280ac2c0103a85a72d/data/symmetric-sextic-residual/LocalResidueU0.lean#L1-L80

import Definitions.Def_HodgeComputerFormal_PolyEncoding
import Definitions.Def_HodgeComputerSSR_K5Field

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace SymmetricSexticResidual.LocalResidueU0
open SymmetricSexticResidual.K5Field
open Lean.Grind.CommRing PolynomialEncoding.SignedExpressions PolynomialEncoding.BivariateExpressions

def vK5 : ℕ → K5
  | 0 => S_K
  | 1 => Q_K
  | 2 => T_K
  | _ => 0

def evalBivK5 (p : Biv) : K5 := denote vK5 x_K y_K p


def L_K : K5 := 77 * S_K - 210 * Q_K + 45

lemma evalBivK5_scale (e : Expr) (i j : ℕ) (p : Biv) :
    evalBivK5 (scale e i j p) = ringEval vK5 e * x_K ^ i * y_K ^ j * evalBivK5 p := by
  simpa [evalBivK5] using scale_denote vK5 x_K y_K e i j p

def bivFilterX0 : Biv → Biv
  | .nil => .nil
  | .cons a i j p => if i = 0 then .cons a i j (bivFilterX0 p) else bivFilterX0 p

def bivFilterX1 : Biv → Biv
  | .nil => .nil
  | .cons a i j p => if i = 0 then bivFilterX1 p else .cons a i j (bivFilterX1 p)

lemma evalBivK5_bivFilter_add (p : Biv) :
    evalBivK5 p = evalBivK5 (bivFilterX0 p) + evalBivK5 (bivFilterX1 p) := by
  induction p with
  | nil => simp [bivFilterX0, bivFilterX1, evalBivK5, denote]
  | cons a i j p ih =>
    by_cases hi : i = 0
    · simp only [bivFilterX0, bivFilterX1, hi, ↓reduceIte, evalBivK5, denote] at ih ⊢; rw [ih]; ring
    · simp only [bivFilterX0, bivFilterX1, hi, ↓reduceIte, evalBivK5, denote] at ih ⊢; rw [ih]; ring

end SymmetricSexticResidual.LocalResidueU0


