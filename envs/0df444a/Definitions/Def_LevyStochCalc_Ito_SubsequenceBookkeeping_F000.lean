-- Prove2me | Definitions.Def_LevyStochCalc_Ito_SubsequenceBookkeeping_F000
-- name    : LevyStochCalc_Ito_SubsequenceBookkeeping_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-21T08:46:24.575182+00:00
-- url     : https://prove2.me/theorems/edff1d8c-0796-45cb-91b1-78e8715727f8
-- title:
--   Source declarations: LevyStochCalc.Ito.SubsequenceBookkeeping
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.SubsequenceBookkeeping. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormulaLimit_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F000
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F001
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F002
import Definitions.Def_LevyStochCalc_Ito_StochasticIntegralLimit_F004

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Subsequence bookkeeping for the truncation limits

The limit statements feeding the small-jump limit of the Itô–Lévy formula deliver almost-sure
convergence along a subsequence, in one of two shapes: along an index map `ms : ℕ → ℕ` dominating
the identity, or along a strictly monotone one. Each successive statement is applied to the
family already reindexed by the previous subsequences, so the assembly reads every term along
one composite index map `ms ∘ k₂ ∘ k₃`. This file collects the bookkeeping: index maps
dominating the identity tend to infinity and compose, a limit at infinity survives reindexing —
pointwise and almost surely — the eventual exclusion of the marks by an antitone family with null
intersection is read along the composite map, and three subsequence statements are merged into
one.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.tendsto_atTop_of_le` — an index map dominating the identity
  tends to infinity.
* `LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_le`,
  `LevyStochCalc.Ito.JumpFormula.Tendsto.comp_of_strictMono` — a limit at infinity is preserved
  along an index map dominating the identity, or a strictly monotone one.
* `LevyStochCalc.Ito.JumpFormula.le_comp_of_le`, `LevyStochCalc.Ito.JumpFormula.le_comp₃_of_le`,
  `LevyStochCalc.Ito.JumpFormula.strictMono_comp_and_le` — composites of index maps dominating
  the identity dominate the identity; composites of strictly monotone maps are strictly monotone.
* `LevyStochCalc.Ito.JumpFormula.ae_tendsto_comp_of_le`,
  `LevyStochCalc.Ito.JumpFormula.ae_tendsto_comp_of_strictMono`,
  `LevyStochCalc.Ito.JumpFormula.ae_tendsto_comp_comp_of_le`,
  `LevyStochCalc.Ito.JumpFormula.ae_tendsto_comp_comp_of_strictMono` — almost-sure convergence
  is preserved under reindexing, also when the original limit is itself along a subsequence.
* `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp'` — almost every mark eventually lies
  outside an antitone family of mark sets with null intersection read along the composite of
  three index maps dominating the identity.
* `LevyStochCalc.Ito.JumpFormula.ae_tendsto_comp₃`,
  `LevyStochCalc.Ito.JumpFormula.exists_strictMono_ae_tendsto₃`,
  `LevyStochCalc.Ito.JumpFormula.exists_ae_tendsto₃` — three almost-sure limits, the first
  along an index map `ms`, the second along `ms ∘ k₂` and the third along `ms ∘ k₂ ∘ k₃`, hold
  together along the composite map; with the subsequences given explicitly, produced from `ms`
  by two subsequence statements, or fully existential.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section IndexMaps

/-- An index map dominating the identity tends to infinity. -/
theorem tendsto_atTop_of_le {ms : ℕ → ℕ} (hms : ∀ k, k ≤ ms k) : Tendsto ms atTop atTop :=
  tendsto_atTop_mono hms tendsto_id
/-- A limit at infinity is preserved along an index map dominating the identity. -/
theorem Tendsto.comp_of_le {α : Type*} {l : Filter α} {u : ℕ → α} (hu : Tendsto u atTop l)
    {ms : ℕ → ℕ} (hms : ∀ k, k ≤ ms k) : Tendsto (fun k => u (ms k)) atTop l :=
  hu.comp (tendsto_atTop_of_le hms)
/-- A limit at infinity is preserved along a strictly monotone index map. -/
theorem Tendsto.comp_of_strictMono {α : Type*} {l : Filter α} {u : ℕ → α}
    (hu : Tendsto u atTop l) {k : ℕ → ℕ} (hk : StrictMono k) :
    Tendsto (fun i => u (k i)) atTop l :=
  hu.comp hk.tendsto_atTop
/-- The composite of two index maps dominating the identity dominates the identity. -/
theorem le_comp_of_le {ms k : ℕ → ℕ} (hms : ∀ i, i ≤ ms i) (hk : ∀ i, i ≤ k i) :
    ∀ i, i ≤ ms (k i) :=
  fun i => (hk i).trans (hms (k i))
/-- The composite of three index maps dominating the identity dominates the identity. -/
theorem le_comp₃_of_le {ms k₂ k₃ : ℕ → ℕ} (hms : ∀ i, i ≤ ms i) (hk₂ : ∀ i, i ≤ k₂ i)
    (hk₃ : ∀ i, i ≤ k₃ i) : ∀ i, i ≤ ms (k₂ (k₃ i)) :=
  le_comp_of_le (ms := ms) (k := fun i => k₂ (k₃ i)) hms (le_comp_of_le hk₂ hk₃)
/-- The composite of two strictly monotone index maps is strictly monotone and dominates the
identity. -/
theorem strictMono_comp_and_le {k₂ k₃ : ℕ → ℕ} (hk₂ : StrictMono k₂) (hk₃ : StrictMono k₃) :
    StrictMono (fun i => k₂ (k₃ i)) ∧ ∀ i, i ≤ k₂ (k₃ i) :=
  ⟨hk₂.comp hk₃, (hk₂.comp hk₃).id_le⟩
end IndexMaps

section AlmostSure

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {α : Type v} [TopologicalSpace α]

/-- Almost-sure convergence is preserved along an index map dominating the identity. -/
theorem ae_tendsto_comp_of_le {u : ℕ → Ω → α} {v : Ω → α}
    (h : ∀ᵐ ω ∂P, Tendsto (fun k => u k ω) atTop (𝓝 (v ω))) {ms : ℕ → ℕ}
    (hms : ∀ k, k ≤ ms k) :
    ∀ᵐ ω ∂P, Tendsto (fun k => u (ms k) ω) atTop (𝓝 (v ω)) := by
  filter_upwards [h] with ω hω
  exact Tendsto.comp_of_le hω hms
/-- Almost-sure convergence is preserved along a strictly monotone index map. -/
theorem ae_tendsto_comp_of_strictMono {u : ℕ → Ω → α} {v : Ω → α}
    (h : ∀ᵐ ω ∂P, Tendsto (fun k => u k ω) atTop (𝓝 (v ω))) {k : ℕ → ℕ}
    (hk : StrictMono k) :
    ∀ᵐ ω ∂P, Tendsto (fun i => u (k i) ω) atTop (𝓝 (v ω)) :=
  ae_tendsto_comp_of_le h hk.id_le
/-- Almost-sure convergence along an index map is preserved along a further reindexing by an
index map dominating the identity. -/
theorem ae_tendsto_comp_comp_of_le {u : ℕ → Ω → α} {v : Ω → α} {ms : ℕ → ℕ}
    (h : ∀ᵐ ω ∂P, Tendsto (fun k => u (ms k) ω) atTop (𝓝 (v ω))) {k : ℕ → ℕ}
    (hk : ∀ i, i ≤ k i) :
    ∀ᵐ ω ∂P, Tendsto (fun i => u (ms (k i)) ω) atTop (𝓝 (v ω)) :=
  ae_tendsto_comp_of_le (u := fun k => u (ms k)) h hk
/-- Almost-sure convergence along an index map is preserved along a further strictly monotone
reindexing. -/
theorem ae_tendsto_comp_comp_of_strictMono {u : ℕ → Ω → α} {v : Ω → α} {ms : ℕ → ℕ}
    (h : ∀ᵐ ω ∂P, Tendsto (fun k => u (ms k) ω) atTop (𝓝 (v ω))) {k : ℕ → ℕ}
    (hk : StrictMono k) :
    ∀ᵐ ω ∂P, Tendsto (fun i => u (ms (k i)) ω) atTop (𝓝 (v ω)) :=
  ae_tendsto_comp_comp_of_le h hk.id_le
end AlmostSure

section MarkSets

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-- Reading an antitone family of mark sets with `ν`-null intersection along the composite of
three index maps dominating the identity keeps almost every mark eventually outside the
family. -/
theorem ae_eventually_notMem_comp' {A : ℕ → Set E} (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {ms k₂ k₃ : ℕ → ℕ} (hms : ∀ i, i ≤ ms i)
    (hk₂ : ∀ i, i ≤ k₂ i) (hk₃ : ∀ i, i ≤ k₃ i) :
    ∀ᵐ e ∂ν, ∀ᶠ i in atTop, e ∉ A (ms (k₂ (k₃ i))) :=
  ae_eventually_notMem_comp hanti hnull (ms := fun i => ms (k₂ (k₃ i)))
    (le_comp₃_of_le hms hk₂ hk₃)
end MarkSets

section Packaging

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- Three almost-sure limits, the first along an index map `ms` dominating the identity, the
second along `ms ∘ k₂` and the third along `ms ∘ k₂ ∘ k₃` with `k₂`, `k₃` dominating the
identity, hold together along `ms ∘ k₂ ∘ k₃`. -/
theorem ae_tendsto_comp₃ {u₁ u₂ u₃ : ℕ → Ω → ℝ} {v₁ v₂ v₃ : Ω → ℝ} {ms k₂ k₃ : ℕ → ℕ}
    (hms : ∀ i, i ≤ ms i) (hk₂ : ∀ i, i ≤ k₂ i) (hk₃ : ∀ i, i ≤ k₃ i)
    (h₁ : ∀ᵐ ω ∂P, Tendsto (fun i => u₁ (ms i) ω) atTop (𝓝 (v₁ ω)))
    (h₂ : ∀ᵐ ω ∂P, Tendsto (fun i => u₂ (ms (k₂ i)) ω) atTop (𝓝 (v₂ ω)))
    (h₃ : ∀ᵐ ω ∂P, Tendsto (fun i => u₃ (ms (k₂ (k₃ i))) ω) atTop (𝓝 (v₃ ω))) :
    (∀ i, i ≤ ms (k₂ (k₃ i))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun i => u₁ (ms (k₂ (k₃ i))) ω) atTop (𝓝 (v₁ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun i => u₂ (ms (k₂ (k₃ i))) ω) atTop (𝓝 (v₂ ω))) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₃ (ms (k₂ (k₃ i))) ω) atTop (𝓝 (v₃ ω)) :=
  ⟨le_comp₃_of_le hms hk₂ hk₃,
    ae_tendsto_comp_comp_of_le (ms := ms) (k := fun i => k₂ (k₃ i)) h₁ (le_comp_of_le hk₂ hk₃),
    ae_tendsto_comp_comp_of_le (ms := fun i => ms (k₂ i)) (k := k₃) h₂ hk₃, h₃⟩
/-- Given an almost-sure limit along an index map `ms` dominating the identity, and two further
sequences each of which converges almost surely along a strictly monotone reindexing of any
family read along an index map dominating the identity, there is one strictly monotone `k` such
that all three converge almost surely along `ms ∘ k`. -/
theorem exists_strictMono_ae_tendsto₃ {u₁ u₂ u₃ : ℕ → Ω → ℝ} {v₁ v₂ v₃ : Ω → ℝ} {ms : ℕ → ℕ}
    (hms : ∀ i, i ≤ ms i)
    (h₁ : ∀ᵐ ω ∂P, Tendsto (fun i => u₁ (ms i) ω) atTop (𝓝 (v₁ ω)))
    (h₂ : ∀ ms' : ℕ → ℕ, (∀ i, i ≤ ms' i) → ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₂ (ms' (k i)) ω) atTop (𝓝 (v₂ ω)))
    (h₃ : ∀ ms' : ℕ → ℕ, (∀ i, i ≤ ms' i) → ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₃ (ms' (k i)) ω) atTop (𝓝 (v₃ ω))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i, i ≤ k i) ∧
      (∀ᵐ ω ∂P, Tendsto (fun i => u₁ (ms (k i)) ω) atTop (𝓝 (v₁ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun i => u₂ (ms (k i)) ω) atTop (𝓝 (v₂ ω))) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₃ (ms (k i)) ω) atTop (𝓝 (v₃ ω)) := by
  obtain ⟨k₂, hk₂mono, hk₂, h₂'⟩ := h₂ ms hms
  obtain ⟨k₃, hk₃mono, hk₃, h₃'⟩ :=
    h₃ (fun i => ms (k₂ i)) (le_comp_of_le (ms := ms) (k := k₂) hms hk₂)
  obtain ⟨_, h₁'', h₂'', h₃''⟩ := ae_tendsto_comp₃ hms hk₂ hk₃ h₁ h₂' h₃'
  exact ⟨fun i => k₂ (k₃ i), hk₂mono.comp hk₃mono, (hk₂mono.comp hk₃mono).id_le,
    h₁'', h₂'', h₃''⟩
/-- Given a sequence converging almost surely along some index map dominating the identity, and
two further sequences each of which converges almost surely along a strictly monotone reindexing
of any family read along an index map dominating the identity, there is one index map `φ`
dominating the identity along which all three converge almost surely. -/
theorem exists_ae_tendsto₃ {u₁ u₂ u₃ : ℕ → Ω → ℝ} {v₁ v₂ v₃ : Ω → ℝ}
    (h₁ : ∃ ms : ℕ → ℕ, (∀ i, i ≤ ms i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₁ (ms i) ω) atTop (𝓝 (v₁ ω)))
    (h₂ : ∀ ms' : ℕ → ℕ, (∀ i, i ≤ ms' i) → ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₂ (ms' (k i)) ω) atTop (𝓝 (v₂ ω)))
    (h₃ : ∀ ms' : ℕ → ℕ, (∀ i, i ≤ ms' i) → ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₃ (ms' (k i)) ω) atTop (𝓝 (v₃ ω))) :
    ∃ φ : ℕ → ℕ, (∀ i, i ≤ φ i) ∧
      (∀ᵐ ω ∂P, Tendsto (fun i => u₁ (φ i) ω) atTop (𝓝 (v₁ ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun i => u₂ (φ i) ω) atTop (𝓝 (v₂ ω))) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u₃ (φ i) ω) atTop (𝓝 (v₃ ω)) := by
  obtain ⟨ms, hms, h₁'⟩ := h₁
  obtain ⟨k, _, hk, h₁'', h₂'', h₃''⟩ := exists_strictMono_ae_tendsto₃ hms h₁' h₂ h₃
  exact ⟨fun i => ms (k i), le_comp_of_le hms hk, h₁'', h₂'', h₃''⟩
end Packaging

end LevyStochCalc.Ito.JumpFormula


