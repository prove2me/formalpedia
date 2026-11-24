-- Prove2me | Definitions.Def_ValiantBorder_localCuts
-- name    : ValiantBorder_localCuts
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T01:02:27.744489+00:00
-- url     : https://prove2.me/theorems/dfb26777-9fab-434e-9957-1ce1fcfe6c3b
-- title:
--   Local cut programs and their quantitative bounds
-- statement:
--   A single-cut program expands a long run into a weighted sum of products of shorter runs. The local-cut condition specifies a range of reduction factors together with compatible bounds on the program, work and output instance sizes.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L72-L113).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Paper/Cuts.lean#L72-L113.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_scaleCuts
/-! Based on Claude (Anthropic), *VP ≠ VNP over every field*, Theorems onecut and cut,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp .
This arrangement refactors the single-cut hypothesis from its quantitative amplification.
The upstream Lean source is copyright 2026 Anthropic, PBC and released under Apache 2.0,
https://www.apache.org/licenses/LICENSE-2.0. -/
namespace NS1
variable {A : Type} [CommRing A]
/-- Weighted sums over a list of pairs (weight, value). -/
def wsum (Q : List (A × Tree)) (φ : Tree → A) : A := (Q.map fun q => q.1 * φ q.2).sum

/-- The formula computes the weighted list `Q` at `x`. -/
def Does (θ : List Bool → A) (F : Fm) (x : Tree) (Q : List (A × Tree)) (c : ℕ) : Prop :=
  ∃ l, Ev θ F x l ∧ (∀ r ∈ l, r.bill = [] ∧ r.cost ≤ c ∧ ∃ q ∈ Q, q.2 = r.out) ∧
    ∀ φ : Tree → A, (l.map fun r => r.th * φ r.out).sum = wsum Q φ

/-- The product of the plain sums of a list of instances. -/
noncomputable def pvs (θ : List Bool → A) (o : Tree) : A := (o.toList.map (pv θ)).prod

/-- A program `G` that cuts plain sums of `τ` steps on instances of size `s` into at most `P` pieces of `τ'` steps on
instances of size `s'`, in `t` steps. -/
def CutD (θ : List Bool → A) (τ s τ' s' P t : ℕ) (G : Tree) : Prop :=
  ∀ z, z.size ≤ s → ∃ Q, Does θ (Fm.ofTree G) z Q t ∧
    (∀ q ∈ Q, q.2.toList.length ≤ P ∧ ∀ y ∈ q.2.toList, y.size ≤ s') ∧
    (Plain θ τ z → (∀ q ∈ Q, ∀ y ∈ q.2.toList, Plain θ τ' y) ∧ pv θ z = wsum Q (pvs θ))

/-- A single program cuts by any admissible local factor `k`, with a fixed polylogarithmic loss. -/
def LocalCuts (θ : List Bool → A) : Prop :=
  ∃ a₀ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∀ τ s k, v ^ a₀ ≤ τ → 4 * lg τ ≤ lg v ^ 2 → s ≤ τ → 2 ≤ k → k ≤ v ^ 64 →
    ∃ G : Tree, G.size ≤ v ^ a₀ ∧ CutD θ τ s (τ * lg v ^ C / k) ((s / k + τ / v ^ 256) * lg v ^ C)
      (k * lg v ^ C) ((s + τ * k / v ^ 256) * lg v ^ C) G
end NS1


