-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:37.398064+00:00
-- url     : https://prove2.me/theorems/44b88a58-5db6-4b34-a51e-f9e1e38143d3
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds — Independent computation bounds and encoded-output growth
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Time, workspace and encoded output are separate obligations. These rules package or forget the
--   actual realizing machine; they do not normalize it or import a higher construction calculus.
--   `computableInO_iff_computableInBigO_and_length_le` separates the charged convenience
--   predicate into uncharged machine bounds and the existing pointwise output-length relation.
--
--   **Contents.** The module is published as a whole: 14 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/Bounds.lean

/-
Copyright (c) 2026 Samuel Schlesinger, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigOLe
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Polynomial
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Independent computation bounds and encoded-output growth

Time, workspace and encoded output are separate obligations. These rules package or forget the
actual realizing machine; they do not normalize it or import a higher construction calculus.
`computableInO_iff_computableInBigO_and_length_le` separates the charged convenience
predicate into uncharged machine bounds and the existing pointwise output-length relation.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

open Cslib

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {T S : α → ℕ}

/-- Forget the encoded-output charge, retaining the same realizing machine. -/
theorem computableInBigO (h : ComputableInO f encIn encOut T S) :
    ComputableInBigO f encIn encOut T S :=
  let ⟨c, hc, _⟩ := h
  ⟨c, hc⟩

/-- The encoded value is within the certificate's existing workspace charge. -/
theorem length_le (h : ComputableInO f encIn encOut T S) :
    ∃ c, ∀ a, (encOut (f a)).length ≤ c * (S a + 1) :=
  let ⟨c, _, hl⟩ := h
  ⟨c, hl⟩

/-- Exact plain machine bounds and an explicit output charge supply asymptotic bounds. -/
theorem of_bounds {t s : α → ℕ}
    (hf : ComputableInTimeAndSpace f encIn encOut t s) (k : ℕ)
    (ht : ∀ a, t a ≤ k * (T a + 1)) (hs : ∀ a, s a ≤ k * (S a + 1))
    (hl : ∀ a, (encOut (f a)).length ≤ k * (S a + 1)) :
    ComputableInO f encIn encOut T S :=
  ⟨k, hf.mono ht hs, hl⟩

/-- Weaken both bounds by independent pointwise estimates and a common constant. -/
theorem mono {T' S' : α → ℕ} (h : ComputableInO f encIn encOut T S) (k : ℕ)
    (hT : ∀ a, T a ≤ k * (T' a + 1)) (hS : ∀ a, S a ≤ k * (S' a + 1)) :
    ComputableInO f encIn encOut T' S' :=
  let ⟨c, hc, hl⟩ := h
  of_bounds hc (c * (k + 1)) (fun a => by nlinarith [hT a])
    (fun a => by nlinarith [hS a]) (fun a => by nlinarith [hS a, hl a])

/-- Weaken only the time bound up to a constant, keeping the space bound. -/
theorem mono_time {T' : α → ℕ} (h : ComputableInO f encIn encOut T S) (k : ℕ)
    (hT : ∀ a, T a ≤ k * (T' a + 1)) : ComputableInO f encIn encOut T' S :=
  h.mono (k + 1) (fun a => (hT a).trans (Nat.mul_le_mul_right _ (Nat.le_succ k)))
    fun _ => (Nat.le_succ _).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos k))

/-- Pointwise larger bounds retain the same encoded-output charge. -/
theorem mono_le {T' S' : α → ℕ} (h : ComputableInO f encIn encOut T S)
    (hT : ∀ a, T a ≤ T' a) (hS : ∀ a, S a ≤ S' a) :
    ComputableInO f encIn encOut T' S' :=
  h.mono 1 (fun a => by have := hT a; omega) (fun a => by have := hS a; omega)

/-- Weaken independent time and charged workspace bounds up to constants. -/
theorem weaken {T' S' : α → ℕ} (h : ComputableInO f encIn encOut T S)
    (hT : T ≼ T') (hS : S ≼ S') : ComputableInO f encIn encOut T' S' :=
  let ⟨k₁, h₁⟩ := hT
  let ⟨k₂, h₂⟩ := hS
  h.mono (k₁ + k₂) (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    (fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _)))

/-- An equal encoded output reuses the same machine and both resource budgets. -/
theorem of_enc_eq {γ : Type*} {encC : γ ↪ List Bool} {g : α → γ}
    (h : ComputableInO f encIn encOut T S) (hg : ∀ a, encC (g a) = encOut (f a)) :
    ComputableInO g encIn encC T S := by
  obtain ⟨c, ⟨k, State, hfinite, tm, htm⟩, hl⟩ := h
  exact ⟨c, ⟨k, State, hfinite, tm, fun a => hg a ▸ htm a⟩,
    fun a => by rw [hg a]; exact hl a⟩

/-- Pull back along an input map preserving the complete encoded word. No algorithm for the
semantic map is assumed: the realizing machine receives exactly the same word. -/
theorem of_encIn_eq {δ : Type*} {encD : δ ↪ List Bool}
    (h : ComputableInO f encIn encOut T S) (g : δ → α)
    (hg : ∀ a, encIn (g a) = encD a) :
    ComputableInO (f ∘ g) encD encOut (T ∘ g) (S ∘ g) := by
  obtain ⟨c, ⟨k, State, hfinite, tm, htm⟩, hl⟩ := h
  exact ⟨c, ⟨k, State, hfinite, tm, fun a => hg a ▸ htm (g a)⟩, fun a => hl (g a)⟩

/-- Polynomial bounds on both resource functions give a plain polynomial-time certificate. -/
theorem computableInPolyTime (h : ComputableInO f encIn encOut T S)
    (hT : PolyBounded (fun a => (encIn a).length) T)
    (hS : PolyBounded (fun a => (encIn a).length) S) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨c, h, _⟩ := h
  obtain ⟨ct, dt, ht⟩ := hT.exists_le
  obtain ⟨cs, ds, hs⟩ := hS.exists_le
  refine ⟨fun n => c * (ct * (n + 1) ^ dt + 1),
    fun n => c * (cs * (n + 1) ^ ds + 1), by fun_prop, by fun_prop, h.mono ?_ ?_⟩
  · exact fun a => Nat.mul_le_mul_left _ (Nat.add_le_add_right (ht a) 1)
  · exact fun a => Nat.mul_le_mul_left _ (Nat.add_le_add_right (hs a) 1)

end Turing.MultiTapeTM.ComputableInO

namespace Turing.MultiTapeTM

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {T S T' S' t s : α → ℕ}

/-- Add an independently proved output-length bound to an uncharged machine certificate. -/
public theorem ComputableInBigO.with_output_bound (h : ComputableInBigO f encIn encOut T S)
    (hl : (fun a => (encOut (f a)).length) ≼ S) : ComputableInO f encIn encOut T S := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨d, hd⟩ := hl
  refine ⟨c + d, hc.mono (fun a => Nat.mul_le_mul_right _ (Nat.le_add_right c d))
    (fun a => Nat.mul_le_mul_right _ (Nat.le_add_right c d)), ?_⟩
  exact fun a => (hd a).trans (Nat.mul_le_mul_right _ (Nat.le_add_left d c))

/-- Charged computability is exactly uncharged computation and a separate output-growth bound.
The two existential constants can be enlarged to a common constant without changing machines. -/
public theorem computableInO_iff_computableInBigO_and_length_le :
    ComputableInO f encIn encOut T S ↔ ComputableInBigO f encIn encOut T S ∧
      (fun a => (encOut (f a)).length) ≼ S :=
  ⟨fun h => ⟨h.computableInBigO, h.length_le⟩, fun ⟨h, hl⟩ => h.with_output_bound hl⟩

/-- Bounds up to constant factors. -/
public theorem ComputableInBigO.of_bounds (h : ComputableInTimeAndSpace f encIn encOut t s)
    (ht : t ≼ T) (hs : s ≼ S) : ComputableInBigO f encIn encOut T S :=
  let ⟨k₁, h₁⟩ := ht
  let ⟨k₂, h₂⟩ := hs
  ⟨k₁ + k₂, h.mono (fun a => (h₁ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
    fun a => (h₂ a).trans (Nat.mul_le_mul_right _ (Nat.le_add_left _ _))⟩

/-- Weakening the bounds, up to constant factors. -/
public theorem ComputableInBigO.weaken (h : ComputableInBigO f encIn encOut T S)
    (hT : T ≼ T') (hS : S ≼ S') : ComputableInBigO f encIn encOut T' S' :=
  let ⟨c, hc⟩ := h
  .of_bounds hc ((BigOLe.const_mul c (u := fun a => T a + 1)
    (.of_le_linear 1 1 fun _ => by omega)).trans hT)
    ((BigOLe.const_mul c (u := fun a => S a + 1) (.of_le_linear 1 1 fun _ => by omega)).trans hS)

end Turing.MultiTapeTM


