-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussDensity
-- name    : BianchiIX_Statistics_GaussDensity
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T16:36:46.472196+00:00
-- url     : https://prove2.me/theorems/284562c9-7be6-4ad6-8d08-780b983417ff
-- title:
--   Length of a continued-fraction cylinder
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   Write $C_n=G_n((0,1))$ and
--   $$\ell_n=\frac1{q_n(q_n+q_{n-1})}.$$
--   Let $\lambda$ denote Lebesgue measure on $\mathbb R$.
--
--   The quantity $\ell_n$ is the exact length of the prefix cylinder $C_n$ and
--   normalizes the derivative density of its inverse branch.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDensity.lean

import Definitions.Def_BianchiIX_Statistics_GaussDistortion
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Group.MeasurableEquiv
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! Exact cylinder length and the uniform density comparison in Section 3.4. -/

namespace BianchiIX

noncomputable section

open Set MeasureTheory
open scoped ENNReal

def gaussPrefixLength (a : ℕ → ℕ+) (n : ℕ) : ℝ :=
  1 / ((gaussDenoms a n).1 * ((gaussDenoms a n).1 + (gaussDenoms a n).2))















end

end BianchiIX


