-- Prove2me | Definitions.Def_BianchiIX_Statistics_StoppedMass
-- name    : BianchiIX_Statistics_StoppedMass
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T16:57:40.689853+00:00
-- url     : https://prove2.me/theorems/bcbf2104-e5bb-44fa-9fd8-d1e3246271b1
-- title:
--   Surviving sets, first stopping sets, and image layers
-- statement:
--   For a sequence of sets $K_n$ in a space $X$, define
--   $$K_\infty=\bigcap_{n\geq0}K_n,\qquad F_n=K_n\setminus K_{n+1}.$$
--   For real maps $H_i$ and sets $A_i\subset\mathbb R$, put
--   $$\mathcal S(H,A)=\bigcup_i H_i(A_i).$$
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/StoppedMass.lean

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

/-! Countable stopping losses with no normalization by the surviving terminal domain. -/

namespace BianchiIX

noncomputable section

open Set MeasureTheory
open scoped ENNReal







def stoppedLayer {ι : Type*} (H : ι → ℝ → ℝ) (A : ι → Set ℝ) : Set ℝ :=
  ⋃ i, H i '' A i















def survivingSet {X : Type*} (K : ℕ → Set X) : Set X := ⋂ m, K m

def firstStoppedSet {X : Type*} (K : ℕ → Set X) (m : ℕ) : Set X := K m \ K (m + 1)













end

end BianchiIX


