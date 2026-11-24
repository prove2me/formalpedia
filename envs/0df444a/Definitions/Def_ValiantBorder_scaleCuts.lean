-- Prove2me | Definitions.Def_ValiantBorder_scaleCuts
-- name    : ValiantBorder_scaleCuts
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:33:17.848286+00:00
-- url     : https://prove2.me/theorems/2c72a2f0-9769-458f-8568-3e83d993294e
-- title:
--   Scale cuts for weighted sum programs
-- statement:
--   A cut program replaces a long plain sum by a sum of products of shorter plain sums, subject to bounds on the input length, running time, and sizes of the resulting instances. The scale-cut property requires such programs for the parameter ranges in the contracting-field argument.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/NS1/Accel.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/NS1/Accel.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Definitions.Def_ValiantBorder_approxAccelerator
/-! Source: Claude (Anthropic), *VP ≠ VNP over every field* (2026),
`anthropics/formal-math` commit 11b6c7e3c927df2658f513b6b68ea7f8929c62c5.
Adapted with attribution under the Apache-2.0 license. -/
namespace NS1
variable {A : Type} [CommRing A]
/-- A program `G` that cuts plain sums of `τ` steps on instances of size `s` into pieces of `v ^ H` steps. Its values
are lists of instances. -/
structure CutProg (θ : List Bool → A) (H v τ s : ℕ) (G : Tree) : Prop where
  size : G.size ≤ v ^ H
  list : ∀ z, z.size ≤ s → Hl θ (Fm.ofTree G) z ∧ ∀ r ∈ evl θ (Fm.ofTree G) z, r.bill = [] ∧ r.cost * v ^ 24 ≤ τ ∧
    r.out.toList.length * v ^ H ≤ τ * v ^ 2 ∧ ∀ y ∈ r.out.toList, y.size ≤ v ^ (H - 32)
  val : ∀ z, z.size ≤ s → Plain θ τ z →
    (∀ r ∈ evl θ (Fm.ofTree G) z, ∀ y ∈ r.out.toList, Plain θ (v ^ H) y) ∧
    pv θ z = ((evl θ (Fm.ofTree G) z).map fun r => r.th * (r.out.toList.map (pv θ)).prod).sum

/-- **Theorem C (the cut, at all scales)**, as a property of the ring and its constants. -/
def CutHyp (θ : List Bool → A) (H C₀ v₀ : ℕ) : Prop :=
  ∀ v, v₀ ≤ v → ∀ α τ s, lg v ^ (C₀ * α) ≤ v → v ^ H ≤ τ → τ ≤ v ^ (H * α) → s * v ^ 48 ≤ τ →
    ∃ G, CutProg θ H v τ s G

end NS1


