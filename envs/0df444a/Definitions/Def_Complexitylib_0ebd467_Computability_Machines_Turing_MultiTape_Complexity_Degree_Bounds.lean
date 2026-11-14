-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:36:38.414348+00:00
-- url     : https://prove2.me/theorems/6f327cfc-5f18-46f4-8fdf-49438299d167
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds — Direct degree weakening and polynomial-time consequences
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The original three plain rules are moved unchanged from the degree-calculus module to keep
--   ordinary clients independent of its legacy construction calculus.
--
--   Charged `ComputableInO` bounds also give degree certificates: a lower workspace degree bounds
--   encoded output at that lower degree, even when the time bound has a higher degree.
--
--   **Contents.** The module is published as a whole: 7 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/Degree/Bounds.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Direct degree weakening and polynomial-time consequences

The original three plain rules are moved unchanged from the degree-calculus module to keep
ordinary clients independent of its legacy construction calculus.

Charged `ComputableInO` bounds also give degree certificates: a lower workspace degree bounds
encoded output at that lower degree, even when the time bound has a higher degree.
-/

@[expose] public section
namespace Turing.MultiTapeTM

namespace ComputableInDegree

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {d e d' e' : ℕ}

/-- Increasing either degree retains the same realizing machine. -/
public theorem mono (h : ComputableInDegree f encIn encOut d e)
    (hd : d ≤ d' := by first | decide | omega) (he : e ≤ e' := by first | decide | omega) :
    ComputableInDegree f encIn encOut d' e' :=
  let ⟨⟨t, s, ht, hs, hf⟩, hl⟩ := h
  ⟨⟨t, s, ht.mono_deg hd, hs.mono_deg hd, hf⟩, hl.mono_deg he⟩

/-- Exact time and workspace bounds of degree `d` also bound the output length in degree `d`. -/
public theorem of_bounds {t s : α → ℕ}
    (ht : DegreeBounded (fun a => (encIn a).length) t d)
    (hs : DegreeBounded (fun a => (encIn a).length) s d)
    (hf : ComputableInTimeAndSpace f encIn encOut t s) :
    ComputableInDegree f encIn encOut d d :=
  ⟨⟨t, s, ht, hs, hf⟩, ht.mono hf.length_le⟩

/-- Degree one is exactly one uniform machine with common linear time/workspace bounds.
Independent constants can be enlarged to a common constant. The same machine's runtime bounds
its output; output length is not charged to workspace. -/
theorem one_one_iff : ComputableInDegree f encIn encOut 1 1 ↔
    ∃ c, ComputableInTimeAndSpace f encIn encOut
      (fun a => c * ((encIn a).length + 1)) (fun a => c * ((encIn a).length + 1)) := by
  constructor
  · rintro ⟨⟨t, s, ⟨ct, ht⟩, ⟨cs, hs⟩, hm⟩, _⟩
    refine ⟨ct + cs, hm.mono (fun a => ?_) (fun a => ?_)⟩
    · simpa only [pow_one] using (ht a).trans
        (Nat.mul_le_mul_right _ (Nat.le_add_right ct cs))
    · simpa only [pow_one] using (hs a).trans
        (Nat.mul_le_mul_right _ (Nat.le_add_left cs ct))
  · rintro ⟨c, hm⟩
    exact of_bounds ⟨c, fun _ => by simp⟩ ⟨c, fun _ => by simp⟩ hm

/-- Fixed time and workspace degrees give plain polynomial-time computability, including degree
zero. Encoded output is bounded separately and is not charged to workspace. -/
public theorem computableInPolyTime (h : ComputableInDegree f encIn encOut d e) :
    ComputableInPolyTime f encIn encOut := by
  obtain ⟨⟨_, _, ht, hs, h⟩, _⟩ := h
  obtain ⟨T, hT, ht⟩ := ht.polyBounded
  obtain ⟨S, hS, hs⟩ := hs.polyBounded
  exact ⟨T, S, hT, hS, h.mono ht hs⟩

/-- The realizing machine's own clock bounds its output, independently of the supplied output
 degree. Both asymptotic resource exponents remain `d`, including zero. -/
theorem inO (h : ComputableInDegree f encIn encOut d e) :
    ComputableInO f encIn encOut (fun a => ((encIn a).length + 1) ^ d)
      (fun a => ((encIn a).length + 1) ^ d) := by
  obtain ⟨⟨_, _, ⟨ct, ht⟩, ⟨cs, hs⟩, hf⟩, _⟩ := h
  exact .of_bounds hf (ct + cs)
    (fun a => (ht a).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _)))
    (fun a => (hs a).trans (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.le_succ _)))
    (fun a => (hf.length_le a).trans
      ((ht a).trans (Nat.mul_le_mul (Nat.le_add_right _ _) (Nat.le_succ _))))

/-- Cost degree one gives linear charged resource bounds, without restricting the output degree. -/
theorem inO_one (h : ComputableInDegree f encIn encOut 1 e) :
    ComputableInO f encIn encOut (fun a => (encIn a).length) (fun a => (encIn a).length) :=
  h.inO.mono 1 (fun _ => by simp) (fun _ => by simp)

end ComputableInDegree

/-- Charged workspace of degree `e` bounds the encoded output at that same degree. When
`e ≤ d`, independent degree bounds on time and workspace give cost degree `d` and output
degree `e`, retaining the realizing machine and its original resource bounds. -/
theorem ComputableInO.computableInDegree
    {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
    {T S : α → ℕ} {d e : ℕ} (h : ComputableInO f encIn encOut T S)
    (hT : DegreeBounded (fun a => (encIn a).length) T d)
    (hS : DegreeBounded (fun a => (encIn a).length) S e) (hed : e ≤ d) :
    ComputableInDegree f encIn encOut d e := by
  obtain ⟨c, hc, hl⟩ := h
  have ht := (hT.add_const 1).smul c
  have hs := (hS.add_const 1).smul c
  exact ⟨⟨_, _, ht, hs.mono_deg hed, hc⟩, hs.mono hl⟩

end Turing.MultiTapeTM


