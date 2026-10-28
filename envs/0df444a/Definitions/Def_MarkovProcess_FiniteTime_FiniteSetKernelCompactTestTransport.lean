-- Prove2me | Definitions.Def_MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
-- name    : MarkovProcess_FiniteTime_FiniteSetKernelCompactTestTransport
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-28T12:56:38.53267+00:00
-- url     : https://prove2.me/theorems/6cdd862a-0028-40ab-acc9-01b260f93ab9
-- title:
--   MarkovProcess definitions: FiniteTime.FiniteSetKernelCompactTestTransport
-- statement:
--   Scott Armstrong’s MarkovProcess library, module `MarkovProcess.FiniteTime.FiniteSetKernelCompactTestTransport`. This source-preserving bundle supplies the non-theorem declarations and definition-embedded lemmas used in the main Markov process formalisation.
-- source:
--   https://github.com/scottnarmstrong/MarkovProcess/blob/1f8060caa137731fa08029592019eeaf9d997fe5/MarkovProcess/FiniteTime/FiniteSetKernelCompactTestTransport.lean#L1-L142

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductCoordinateNormalForm
import Definitions.Def_MarkovProcess_FiniteTime_FiniteProductStoneWeierstrass
import Definitions.Def_MarkovProcess_FiniteTime_Kernel
import Definitions.Def_MarkovProcess_FiniteTime_ProjectiveFamily
import Definitions.Def_MarkovProcess_Kernel_Basic_SourceClosedV3
import Definitions.Def_MarkovProcess_Kernel_KernelSemigroup_SourceClosedV3
import Definitions.Def_MarkovProcess_Time_FiniteOrderedTimes
import Mathlib.Algebra.Order.Sub.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.MeasureTheory.Integral.CompactlySupported
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Order.Fin.Basic
import Mathlib.Probability.Kernel.Composition.Comp
import Mathlib.Probability.Kernel.Composition.CompProd
import Mathlib.Probability.Kernel.Composition.KernelLemmas
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.UrysohnsLemma

/-!
# Compact-test transport for finite-set kernels

This file identifies the increasing-coordinate representation of a finite set with its ordinary
function space by a homeomorphism. It transports compactly supported tests across that
homeomorphism and rewrites their finite-set-kernel integrals as finite-time-kernel integrals.

Strong measurability of a compactly supported test is obtained privately from uniform coordinate-
polynomial approximations. This avoids adding an `OpensMeasurableSpace` assumption on the finite
product. These declarations are finite-dimensional infrastructure; no statement about path space
is proved here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal CompactlySupported

namespace MarkovProcess.SubMarkovKernelSemigroup





/-- The increasing-coordinate representation of paths on a finite time set, as a homeomorphism. -/
noncomputable def orderedPathToFiniteSetHomeomorph
    {alpha : Type*} [TopologicalSpace alpha] (I : Finset NNReal) :
    (Fin I.card → alpha) ≃ₜ (I → alpha) :=
  Homeomorph.piCongrLeft (Y := fun _ : I ↦ alpha) (I.orderIsoOfFin rfl).toEquiv



/-- Pull a compactly supported test on finite-set coordinates back to increasing coordinates. -/
noncomputable def pullbackFiniteSetCompactTest
    {alpha : Type*} [TopologicalSpace alpha] [T2Space alpha]
    (I : Finset NNReal) (f : C_c(I → alpha, ℝ)) : C_c(Fin I.card → alpha, ℝ) :=
  f.comp (orderedPathToFiniteSetHomeomorph I).toCocompactMap







end MarkovProcess.SubMarkovKernelSemigroup


