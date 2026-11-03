-- Prove2me | Definitions.Def_LeanLevy_Probability_IndependenceGrouping
-- name    : LeanLevy_Probability_IndependenceGrouping
-- status  : Definition
-- author  : @WillR
-- created : 2026-10-30T21:59:07.462005+00:00
-- url     : https://prove2.me/theorems/5ef167ac-fad0-47ec-b8cb-11ed9440d670
-- title:
--   LeanLevy source module: Probability.IndependenceGrouping
-- statement:
--   Source-faithful definition and structural-lemma bundle for `LeanLevy.Probability.IndependenceGrouping`. It preserves the original Lean declarations, namespaces, assumptions and imported definitions. The upstream source is credited below. This is a draft pending Prove2Me compilation.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Probability/IndependenceGrouping.lean

/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: LeanLevy Contributors
-/
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.PiSystem

/-!
# Grouping mutually independent families along disjoint index sets

Mathlib's `indepSets_piiUnionInter_of_disjoint` and `iIndepFun.indepFun_finset` express that
grouping an independent family into **two** blocks indexed by disjoint index sets preserves
independence. This file generalizes the underlying mechanism from binary to finite mutual grouping:
starting from a mutually independent family indexed by `κ` and a family of pairwise-disjoint index
sets `S : ι → Set κ`, the blocks obtained by gathering the members over each `S i` are again
mutually independent.

## Main results

* `iIndepSets.piiUnionInter_of_pairwiseDisjoint`: mutual independence of π-systems is preserved by
  grouping into the finite-intersection systems `piiUnionInter π (S i)`.
* `iIndep.biSup_of_pairwiseDisjoint`: mutual independence of σ-algebras is preserved by taking the
  suprema `⨆ k ∈ S i, m k`.
* `iIndepFun.setRestrict_of_pairwiseDisjoint`: the blocks of a mutually independent family of random
  variables, restricted to each `S i`, are mutually independent.

Each statement upgrades the corresponding mathlib binary grouping lemma to an arbitrary finite family
of blocks indexed by pairwise-disjoint index sets.
-/

open MeasureTheory MeasurableSpace Set

namespace ProbabilityTheory

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}







end ProbabilityTheory


