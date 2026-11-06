-- Prove2me | Definitions.Def_BlockBochner_Nspace
-- name    : BlockBochner_Nspace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:46.644659+00:00
-- url     : https://prove2.me/theorems/b753ead0-9a2c-4b49-b2bf-4aa9c4ce1f5c
-- title:
--   $N_\nu=\{(g_i):g_i\in\operatorname{ran}L^\nu_i,\ \sum_ig_i=0\}$
-- statement:
--   $N_\nu$ is the subspace of $\bigoplus_{i\in R}L^2_0(\nu)$ of tuples with $g_i\in\operatorname{ran}L^\nu_i$ for all $i$ and $\sum_ig_i=0$.
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228, Sec. 2.2, p.17

import Mathlib
import Definitions.Def_BlockBochner_siteLap
import Definitions.Def_BlockBochner_L20

open MeasureTheory

namespace BlockBochner

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- **`N_ν = {(g_i)_{i∈R} : g_i ∈ ran L^ν_i, Σ_i g_i = 0}`.** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Sec. 2.2, p.17.

**Formalization Note** A subspace of `⊕_{i∈R} L²₀(ν)` (`PiLp 2`); `L^ν_i = siteLap ν i`. -/
noncomputable def Nspace (ν : Measure (∀ i, X i)) : Submodule ℝ (PiLp 2 (fun _ : ι => L20 ν)) where
  carrier := {g | (∀ i, (g i : Lp ℝ 2 ν) ∈ LinearMap.range (siteLap ν i).toLinearMap) ∧ ∑ i, g i = 0}
  add_mem' := by
    intro a b ha hb
    refine ⟨fun i => ?_, ?_⟩
    · simpa using Submodule.add_mem _ (ha.1 i) (hb.1 i)
    · simp [Finset.sum_add_distrib, ha.2, hb.2]
  zero_mem' := ⟨fun i => by simp, by simp⟩
  smul_mem' := by
    intro c a ha
    refine ⟨fun i => ?_, ?_⟩
    · simpa using Submodule.smul_mem _ c (ha.1 i)
    · simp [← Finset.smul_sum, ha.2]

end BlockBochner


