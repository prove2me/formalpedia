-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_ZipTransducer
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_ZipTransducer
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:25.14382+00:00
-- url     : https://prove2.me/theorems/a65cf16f-381a-4d9b-94ec-2388411eb3d7
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer — Zip transducers
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A zip transducer (`Turing.MultiTapeTM.ZipTransducer`) reads two binary words in lockstep, least
--   significant digit first, padding the shorter word with `none`. In state `q`, on the pair `(x, y)`
--   of next digits, it moves to state `(τ.step q (x, y)).1` and emits `(τ.step q (x, y)).2`; when both
--   words are exhausted it emits `τ.final q`. Every emitted word has length at most two.
--
--   On a pair `(a, b)` encoded as `frame (enc₁ a) ++ enc₂ b`, the machine `τ.toTM` copies `enc₁ a` to
--   its work tape and then reads both words simultaneously. Every two-operand function whose encoded
--   value is the output of a zip transducer on the encoded operands is therefore computable in time
--   linear in the encoded pair and in work space linear in the first operand.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ZipTransducer.computableInTimeAndSpace`: a function computed by a zip
--     transducer with finitely many states on the encoded components of a pair is computable within
--     `3 * (encPair enc₁ enc₂ p).length + 1` steps and `(enc₁ p.1).length + 2` work-tape cells.
--   * `Turing.MultiTapeTM.ZipTransducer.computableInTimeAndSpace_run`: the same on raw words.
--   * `Turing.MultiTapeTM.ZipTransducer.computableInDegree`: its degree-1/1 certificate.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_ZipTransducer`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/ZipTransducer.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelZipTransducer
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Pair
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_List
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.ZipTransducer` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Zip transducers

A zip transducer (`Turing.MultiTapeTM.ZipTransducer`) reads two binary words in lockstep, least
significant digit first, padding the shorter word with `none`. In state `q`, on the pair `(x, y)`
of next digits, it moves to state `(τ.step q (x, y)).1` and emits `(τ.step q (x, y)).2`; when both
words are exhausted it emits `τ.final q`. Every emitted word has length at most two.

On a pair `(a, b)` encoded as `frame (enc₁ a) ++ enc₂ b`, the machine `τ.toTM` copies `enc₁ a` to
its work tape and then reads both words simultaneously. Every two-operand function whose encoded
value is the output of a zip transducer on the encoded operands is therefore computable in time
linear in the encoded pair and in work space linear in the first operand.

## Main results

* `Turing.MultiTapeTM.ZipTransducer.computableInTimeAndSpace`: a function computed by a zip
  transducer with finitely many states on the encoded components of a pair is computable within
  `3 * (encPair enc₁ enc₂ p).length + 1` steps and `(enc₁ p.1).length + 2` work-tape cells.
* `Turing.MultiTapeTM.ZipTransducer.computableInTimeAndSpace_run`: the same on raw words.
* `Turing.MultiTapeTM.ZipTransducer.computableInDegree`: its degree-1/1 certificate.
-/

namespace Turing.MultiTapeTM

namespace ZipTransducer

universe u

variable {Q : Type} [Finite Q] (τ : ZipTransducer Q) {α β γ : Type u}
  {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool} {encOut : γ ↪ List Bool} {f : α × β → γ}

/-- **Two-operand functions computed by a zip transducer.** If the encoded value of `f p` is what
`τ` emits on the encoded components of `p`, then `f` is computable within
`3 * (encPair enc₁ enc₂ p).length + 1` steps and `(enc₁ p.1).length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace
    (hf : ∀ p, encOut (f p) = τ.run τ.q₀ (enc₁ p.1) (enc₂ p.2)) :
    ComputableInTimeAndSpace f (encPair enc₁ enc₂) encOut
      (fun p => 3 * (encPair enc₁ enc₂ p).length + 1) (fun p => (enc₁ p.1).length + 2) :=
  ⟨1, State Q, inferInstance, τ.toTM, fun p => by
    rw [hf p, encPair_apply]
    exact τ.computesInTimeAndSpace_toTM (enc₁ p.1) (enc₂ p.2)⟩

/-- `τ` on raw words: on `frame u ++ v` it emits `τ.run τ.q₀ u v` within
`3 * (frame u ++ v).length + 1` steps and `u.length + 2` work-tape cells. -/
public theorem computableInTimeAndSpace_run :
    ComputableInTimeAndSpace (fun p : List Bool × List Bool => τ.run τ.q₀ p.1 p.2)
      (encPair encBits encBits) encBits
      (fun p => 3 * (encPair encBits encBits p).length + 1) (fun p => p.1.length + 2) :=
  τ.computableInTimeAndSpace fun _ => rfl

/-- A function computed by a zip transducer has cost and output degree one. -/
public theorem computableInDegree
    (hf : ∀ p, encOut (f p) = τ.run τ.q₀ (enc₁ p.1) (enc₂ p.2)) :
    ComputableInDegree f (encPair enc₁ enc₂) encOut 1 1 :=
  ComputableInDegree.of_bounds ⟨3, fun _ => by simp only [pow_one]; omega⟩
    ⟨3, fun p => by
      have := length_le_encPair_left enc₁ enc₂ p
      simp only [pow_one]
      omega⟩ (τ.computableInTimeAndSpace hf)

end ZipTransducer

end Turing.MultiTapeTM


