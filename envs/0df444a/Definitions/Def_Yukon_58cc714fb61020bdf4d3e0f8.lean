-- Prove2me | Definitions.Def_Yukon_58cc714fb61020bdf4d3e0f8
-- name    : Yukon_58cc714fb61020bdf4d3e0f8
-- status  : Definition
-- author  : @yukon
-- created : 2026-09-30T16:01:26.557518+00:00
-- url     : https://prove2.me/theorems/cc191328-5bdf-44ac-a9dc-643e5b9cd776
-- title:
--   YukonModule.ArkLib.Data.Probability.Notation.part0
-- statement:
--   Source module ArkLib.Data.Probability.Notation. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Probability/Notation.lean
-- source:
--   https://github.com/Verified-zkEVM/ArkLib/blob/e65197892890b8fd9b0dc05b8980273cf1d595cc/ArkLib/Data/Probability/Notation.lean
--
--   yukon-proof-operation:58cc714fb61020bdf4d3e0f89b658104b0dd806afd5597d41e5c6fc58ce36aa5
--   [yukon-proof-receipt:eyJ2IjoxLCJtYXJrZXIiOiJ5dWtvbi1wcm9vZi1vcGVyYXRpb246NThjYzcxNGZiNjEwMjBiZGY0ZDNlMGY4OWI2NTgxMDRiMGRkODA2YWZkNTU5N2Q0MWU1YzZmYzU4Y2UzNmFhNSIsImhhc2giOiI5ZDhmZjE4MDc5NWY2NjEzZDg4Y2EyY2M2MWEzMmYyZWI4OWZlZTMwZTRkYzQyN2Q3OTJlZmEyMGM5YjJhYjQ2Iiwia2luZCI6ImRlZmluaXRpb24iLCJ0YXJnZXQiOiJZdWtvbl81OGNjNzE0ZmI2MTAyMGJkZjRkM2UwZjgiLCJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJ0YWciOiJiZXR0ZXItY29kZXMifQ]

/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, František Silváši
-/

import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform


import Init
set_option backward.isDefEq.respectTransparency.types false
/-!
  # Notation for probability sampling statements

  The goal is to be able to write readable statements like:
  ```
  Pr_{ let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ F × F }[ z = (x, y) ]
  ```
  which should parse as:
  ```
  (do let x ← PMF.uniformOfFintype F
      let y ← PMF.uniformOfFintype F
      let z ← PMF.uniformOfFintype (F × F)
      return z = (x, y)).val True
  ```
  The `.val True` is used to extract the probability of the condition holding.

  In general the `do` notation is more restrictive than `PMF.bind`, as the latter allows for
  changing universe levels. This should not be an issue in general if we always work over `Type`.

  We should also allow for non-uniform distributions, e.g.
  `Pr_{ let e ← discreteGaussian (ZMod p) }[ e = 0 ]`.
-/

open scoped ProbabilityTheory NNReal ENNReal

open Lean Elab Parser Term Meta PMF

namespace ProbabilityTheory

/-- Notation for uniform sampling from a finite, non-empty type. Just converts to
  `PMF.uniformOfFintype`. -/
scoped notation "$ᵖ" => PMF.uniformOfFintype

/-
Syntax for probability expressions: `Pr_{...}[...]`

Expands `Pr_{e₁; e₂; ...; eₙ}[cond]` to `(do e₁; e₂; ...; eₙ; return cond).val True`.

The do-notation uses the `Bind` typeclass, which requires all sampled types to live in the same
universe. In practice this is not a restriction since all our probability distributions sample from
`Type` (finite fields, finite sets, etc.) and conditions are in `Prop`.

If you somehow need universe polymorphism (sampling from `Type u` and returning something in
`Type v`), you'd need to manually use `PMF.bind` instead of this notation. But this never happens
in cryptographic applications.

# Examples
```
Pr_{ let x ←$ᵖ F; let y ←$ᵖ F }[x = y]
```
expands to
```
(do let x ← PMF.uniformOfFintype F; let y ← PMF.uniformOfFintype F; return x = y).val True
```
-/
/-- Unfold a single-sample event as an indicator-weighted `tsum` over the `PMF`. -/
lemma Pr_eq_tsum_indicator {α : Type} (p : PMF α) (P : α → Prop)
    [DecidablePred P] :
    (((do { let a ← p; return (P a) }) True) : ENNReal) =
      ∑' a, p a * (if P a then (1 : ENNReal) else 0) := by
  simp only [Bind.bind, Pure.pure, PMF.bind, PMF.pure, DFunLike.coe,
    eq_iff_iff, true_iff]

/-- Uniform probability is invariant under an equivalence of finite sample spaces. -/
lemma Pr_uniform_equiv {α β : Type} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) (P : β → Prop) :
    (((do { let a ← $ᵖ α; return (P (e a)) }) True) : ENNReal) = (((do { let b ← $ᵖ β; return (P b) }) True) : ENNReal) := by
  classical
  have hmap : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
    ext b
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply,
      Fintype.card_congr e, tsum_fintype]
    have hs :
        Finset.univ.sum (fun a : α =>
            if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0) =
          Finset.univ.sum (fun b' : β =>
            if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) := by
      simpa using
        (Fintype.sum_equiv e
          (fun a : α => if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0)
          (fun b' : β => if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0)
          (by intro a; rfl))
    exact hs.trans (by simp)
  change
    (PMF.uniformOfFintype α).map (P ∘ e) True =
      (PMF.uniformOfFintype β).map P True
  have hcomp :
      (PMF.uniformOfFintype α).map (P ∘ e) =
        ((PMF.uniformOfFintype α).map e).map P := by
    simpa [Function.comp] using
      (PMF.map_comp (p := PMF.uniformOfFintype α) (f := e) (g := P)).symm
  exact congrArg (fun q : PMF Prop => q True) (hcomp.trans (by rw [hmap]))

end ProbabilityTheory

example {F} [Fintype F] [Nonempty F] :
  (((do { let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ (F × F); return (z = (x, y)) }) True) : ENNReal) =
  (do let x ← PMF.uniformOfFintype F
      let y ← PMF.uniformOfFintype F
      let z ← PMF.uniformOfFintype (F × F)
      return (z = (x, y))).val True := rfl

section

variable {F : Type} [Nonempty F] [Fintype F]

example :
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y) : PMF Prop).1 True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  classical
  simp [Bind.bind, Pure.pure, PMF.bind]
  simp [DFunLike.coe]
  ring_nf
  rw [mul_comm (_ ^ 2) _, mul_assoc, ENNReal.mul_inv_cancel, mul_one, ENNReal.inv_pow]
  <;> aesop

example :
  (((do { let x ←$ᵖ F; let y ←$ᵖ F; let z ←$ᵖ (F × F); return ( z = (x, y) ) }) True) : ENNReal) =
  ((1 : ℝ≥0∞) / Fintype.card (F × F)) ↔
  (do
    let x ← $ᵖ F
    let y ← $ᵖ F
    let z ← $ᵖ (F × F)
    return z = (x, y)).val True = ((1 : ℝ≥0∞) / Fintype.card (F × F)) := by
  rfl

end


