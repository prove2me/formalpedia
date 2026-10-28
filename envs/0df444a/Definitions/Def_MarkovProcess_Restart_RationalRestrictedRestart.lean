-- Prove2me | Definitions.Def_MarkovProcess_Restart_RationalRestrictedRestart
-- name    : MarkovProcess_Restart_RationalRestrictedRestart
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:51:00.584059+00:00
-- url     : https://prove2.me/theorems/54e792d6-7909-4457-84bc-d04041eb3dcc
-- title:
--   MarkovProcess definitions: Restart.RationalRestrictedRestart
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.Restart.RationalRestrictedRestart`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/Restart/RationalRestrictedRestart.lean#L1-L94

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_Continuity_DenseTimeContinuousExtension
import Definitions.Def_MarkovProcess_Path_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Path_DenseFiltration
import Definitions.Def_MarkovProcess_Time_CountableDenseTime
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Encodable
import Mathlib.Logic.Denumerable
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.Probability.Kernel.Composition.CompNotation
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.CompactOpen

/-!
# Restricted restart at rational times

This file turns a full joint-law factorization of the rational past and shifted future into the
event-restricted restart identity on the canonical continuous-path filtration.  The joint-law
factorization remains an explicit input; proving it from the finite-dimensional Markov laws is the
next process-construction step.
-/

open MeasureTheory ProbabilityTheory

namespace MarkovProcess
namespace ContinuousPath

noncomputable section

variable {alpha : Type*} [MetricSpace alpha]
  [MeasurableSpace alpha] [BorelSpace alpha]

/-- Evaluation of a rational past at its terminal coordinate. -/
def densePastTerminal (S : DenseTime) (history : Set.Iic S → alpha) : alpha :=
  history ⟨S, Set.mem_Iic.mpr le_rfl⟩

omit [MetricSpace alpha] [BorelSpace alpha] in
/-- Terminal-coordinate evaluation on rational pasts is measurable. -/
theorem measurable_densePastTerminal (S : DenseTime) :
    Measurable (densePastTerminal (alpha := alpha) S) :=
  measurable_pi_apply (⟨S, Set.mem_Iic.mpr le_rfl⟩ : Set.Iic S)





end
end ContinuousPath
end MarkovProcess


