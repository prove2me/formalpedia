-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:34:45.373308+00:00
-- url     : https://prove2.me/theorems/7e3251ba-c963-4c65-a285-2c221bb83e84
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds — Computability within resource bounds up to constant factors
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Upstream `Turing.MultiTapeTM.ComputableInTimeAndSpace f encIn encOut t s` asks for a machine with a
--   binary alphabet and finitely many states that computes `f` within time `t a` and work space `s a`
--   on every input `a`. This file names the bounds that hold up to constant factors. Time and space
--   are independent bounds: a space bound is never derived from a time bound.
--
--   * `Turing.MultiTapeTM.ComputableInO f encIn encOut T S`: time `O(T a)` and space `O(S a)`.
--   * `Turing.MultiTapeTM.ComputableInSpace f encIn encOut S`: space `O(S a)`, in some time.
--   * `Turing.MultiTapeTM.ComputableInPolySpace f encIn encOut`: space polynomial in the length of the
--     encoded input, in some time.
--
--   The bounds `T` and `S` are any functions of the input, not only of the length of its encoding, so
--   that they can be stated in several measures of the input.
--
--   The three space-charged notions above also bound the length of the encoded value `encOut (f a)`
--   by its space bound, so the
--   value is charged to the space bound although the machine writes it on its output tape. For
--   `ComputableInO` and `ComputableInSpace` this departs from the usual convention, in which a space
--   bound counts only the work tapes and the output of a transducer may be much longer than the bound
--   [Arora and Barak, Chapter 4][AroraBarak09] [Papadimitriou, Section 2.5][Papadimitriou94]. It also
--   departs from the library's `Turing.MultiTapeTM.ComputableInLogSpace`, which charges neither the
--   input nor the output. At sublinear bounds these notions are therefore strictly stronger than
--   transducer space. For instance, the identity on words is computable in logarithmic space, but not
--   within space `O(log n)` in the sense of `ComputableInSpace`, since its value is as long as its
--   input. Transducer space, as in log-space reductions, is `Turing.MultiTapeTM.ComputableInLogSpace`,
--   or upstream `ComputableInTimeAndSpace` with an explicit space bound.
--
--   `ComputableInDegree` separately bounds time and workspace in degree `d` and encoded output in
--   degree `e`; both degrees may be zero, with one realizing machine for all inputs. It does not
--   charge output length to workspace.
--
--   The space-charge condition accounts for values kept on work tapes by the machine combinators.
--   It costs nothing for decision problems, whose values are single bits. For polynomial space it is
--   the usual requirement that the value have polynomial length.
--
--   `Turing.MultiTapeTM.ComputableTidilyInO` and `Turing.MultiTapeTM.ComputableTidilyInSpace`
--   ask for a machine that also clears its work tapes and rewinds its heads before halting.
--   Their plain counterparts agree with them with the same bounds
--   (`Turing.MultiTapeTM.computableInO_iff_computableTidilyInO`,
--   `Turing.MultiTapeTM.ComputableInSpace.tidy` and `Turing.MultiTapeTM.ComputableInSpace.of_tidy`).
--   Polynomial space uses only the plain predicate `Turing.MultiTapeTM.ComputableInPolySpace`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.ComputableInO`: computability within time and space bounds up to constants.
--   * `Turing.MultiTapeTM.ComputableInDegree`: independent time/workspace and encoded-output degrees
--     with a single realizing machine; degrees `1 1` give linear time and workspace.
--   * `Turing.MultiTapeTM.ComputableInBigO`: independent uncharged time/workspace bounds up to
--     constants; unlike `ComputableInO`, the workspace bound does not charge encoded output.
--   * `Turing.MultiTapeTM.ComputableInSpace`: computability within a space bound up to constants.
--   * `Turing.MultiTapeTM.ComputableInPolySpace`: computability within polynomial space.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 4][AroraBarak09]
--   * [C. H. Papadimitriou, *Computational Complexity*, Section 2.5][Papadimitriou94]
--
--   **Contents.** The module is published as a whole: 5 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/ResourceBounds.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Nat_PolynomialBound
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds_Degree

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Computability within resource bounds up to constant factors

Upstream `Turing.MultiTapeTM.ComputableInTimeAndSpace f encIn encOut t s` asks for a machine with a
binary alphabet and finitely many states that computes `f` within time `t a` and work space `s a`
on every input `a`. This file names the bounds that hold up to constant factors. Time and space
are independent bounds: a space bound is never derived from a time bound.

* `Turing.MultiTapeTM.ComputableInO f encIn encOut T S`: time `O(T a)` and space `O(S a)`.
* `Turing.MultiTapeTM.ComputableInSpace f encIn encOut S`: space `O(S a)`, in some time.
* `Turing.MultiTapeTM.ComputableInPolySpace f encIn encOut`: space polynomial in the length of the
  encoded input, in some time.

The bounds `T` and `S` are any functions of the input, not only of the length of its encoding, so
that they can be stated in several measures of the input.

The three space-charged notions above also bound the length of the encoded value `encOut (f a)`
by its space bound, so the
value is charged to the space bound although the machine writes it on its output tape. For
`ComputableInO` and `ComputableInSpace` this departs from the usual convention, in which a space
bound counts only the work tapes and the output of a transducer may be much longer than the bound
[Arora and Barak, Chapter 4][AroraBarak09] [Papadimitriou, Section 2.5][Papadimitriou94]. It also
departs from the library's `Turing.MultiTapeTM.ComputableInLogSpace`, which charges neither the
input nor the output. At sublinear bounds these notions are therefore strictly stronger than
transducer space. For instance, the identity on words is computable in logarithmic space, but not
within space `O(log n)` in the sense of `ComputableInSpace`, since its value is as long as its
input. Transducer space, as in log-space reductions, is `Turing.MultiTapeTM.ComputableInLogSpace`,
or upstream `ComputableInTimeAndSpace` with an explicit space bound.

`ComputableInDegree` separately bounds time and workspace in degree `d` and encoded output in
degree `e`; both degrees may be zero, with one realizing machine for all inputs. It does not
charge output length to workspace.

The space-charge condition accounts for values kept on work tapes by the machine combinators.
It costs nothing for decision problems, whose values are single bits. For polynomial space it is
the usual requirement that the value have polynomial length.

`Turing.MultiTapeTM.ComputableTidilyInO` and `Turing.MultiTapeTM.ComputableTidilyInSpace`
ask for a machine that also clears its work tapes and rewinds its heads before halting.
Their plain counterparts agree with them with the same bounds
(`Turing.MultiTapeTM.computableInO_iff_computableTidilyInO`,
`Turing.MultiTapeTM.ComputableInSpace.tidy` and `Turing.MultiTapeTM.ComputableInSpace.of_tidy`).
Polynomial space uses only the plain predicate `Turing.MultiTapeTM.ComputableInPolySpace`.

## Main definitions

* `Turing.MultiTapeTM.ComputableInO`: computability within time and space bounds up to constants.
* `Turing.MultiTapeTM.ComputableInDegree`: independent time/workspace and encoded-output degrees
  with a single realizing machine; degrees `1 1` give linear time and workspace.
* `Turing.MultiTapeTM.ComputableInBigO`: independent uncharged time/workspace bounds up to
  constants; unlike `ComputableInO`, the workspace bound does not charge encoded output.
* `Turing.MultiTapeTM.ComputableInSpace`: computability within a space bound up to constants.
* `Turing.MultiTapeTM.ComputableInPolySpace`: computability within polynomial space.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 4][AroraBarak09]
* [C. H. Papadimitriou, *Computational Complexity*, Section 2.5][Papadimitriou94]
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {α β : Type*}

/-- `f` is computable within time `O(T a)` and space `O(S a)` on the input `a`, and its encoded
value has length `O(S a)`: for a constant `c`, some machine computes `f` within time `c (T a + 1)`
and space `c (S a + 1)`, and `encOut (f a)` has length at most `c (S a + 1)`.

Unlike the textbook convention and `Turing.MultiTapeTM.ComputableInLogSpace`, the value is charged
to the space bound, as in `Turing.MultiTapeTM.ComputableTidilyInO`; see the module documentation.
-/
def ComputableInO (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (T S : α → ℕ) :
    Prop :=
  ∃ c, ComputableInTimeAndSpace f encIn encOut (fun a => c * (T a + 1)) (fun a => c * (S a + 1)) ∧
    ∀ a, (encOut (f a)).length ≤ c * (S a + 1)

/-- `f` is computable within space `O(S a)` on the input `a`, in some time, and its encoded value
has length `O(S a)`: for a constant `c`, some machine computes `f` within some time and space
`c (S a + 1)`, and `encOut (f a)` has length at most `c (S a + 1)`.

Unlike the textbook convention and `Turing.MultiTapeTM.ComputableInLogSpace`, the value is charged
to the space bound, as in `Turing.MultiTapeTM.ComputableTidilyInSpace`. At sublinear bounds this
notion is strictly stronger than transducer space: with the bound
`fun a => Nat.log2 (encIn a).length` it implies `Turing.MultiTapeTM.ComputableInLogSpace`, but
not conversely. See the module documentation.
-/
def ComputableInSpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) (S : α → ℕ) :
    Prop :=
  ∃ (t : α → ℕ) (c : ℕ), ComputableInTimeAndSpace f encIn encOut t (fun a => c * (S a + 1)) ∧
    ∀ a, (encOut (f a)).length ≤ c * (S a + 1)

/-- `f` is computable within polynomial space, in some time, and its encoded value has polynomial
length: for a polynomially bounded `s`, some machine computes `f` within some time and space
`s n` on encoded inputs of length `n`, and `encOut (f a)` has length at most `s n`. -/
def ComputableInPolySpace (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool) : Prop :=
  ∃ (t : α → ℕ) (s : ℕ → ℕ), Cslib.PolynomiallyBounded s ∧
    ComputableInTimeAndSpace f encIn encOut t (fun a => s (encIn a).length) ∧
    ∀ a, (encOut (f a)).length ≤ s (encIn a).length

/-- `f` is computable within time `O(T a)` and space `O(S a)` on the input `a`. -/
def ComputableInBigO {α β : Type*} (f : α → β) (encIn : α ↪ List Bool)
    (encOut : β ↪ List Bool) (T S : α → ℕ) : Prop :=
  ∃ c, ComputableInTimeAndSpace f encIn encOut (fun a => c * (T a + 1)) fun a => c * (S a + 1)

/-- Polynomial time and work space of degree `d`, and encoded output growth of degree `e`.
The realization is one machine for all inputs. Both degrees may be zero. -/
def ComputableInDegree (f : α → β) (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (d e : ℕ) : Prop :=
  (∃ t s, DegreeBounded (fun a => (encIn a).length) t d ∧
    DegreeBounded (fun a => (encIn a).length) s d ∧
    ComputableInTimeAndSpace f encIn encOut t s) ∧
  DegreeBounded (fun a => (encIn a).length) (fun a => (encOut (f a)).length) e

end Turing.MultiTapeTM


