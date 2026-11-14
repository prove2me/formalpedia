-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:46:23.599403+00:00
-- url     : https://prove2.me/theorems/00a04d19-a5e5-47ab-a157-6c2c270c7286
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain — Polynomial time on plain machines
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `Turing.MultiTapeTM.ComputableTidilyInPolyTime` asks for a *tidy* machine, which clears its work
--   tapes and rewinds its heads before halting, within polynomially bounded time and space. Neither
--   requirement changes the class. A machine that halts within `t` steps visits at most `k t + k`
--   work-tape cells, where `k` is its number of work tapes
--   (`Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`), and the tidy normal form makes any
--   machine tidy at a linear cost in time and space
--   (`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`). So a function
--   is tidily computable in polynomial time exactly when some machine computes it in the sense of
--   upstream `Turing.MultiTapeTM.ComputableInTimeAndSpace`, within polynomially bounded time and space
--   (`Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`), and
--   a polynomial time bound alone already suffices
--   (`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime`)
--   [Arora and Barak, Chapter 1][AroraBarak09].
--
--   Passing from tidy to plain computations is lossless: a tidy machine is a machine, with the same
--   bounds. Passing from plain to tidy computations changes the bounds by linear functions whose
--   coefficients depend on the machine.
--
--   The plain notion, `Turing.MultiTapeTM.ComputableInPolyTime`, is the one for definitions and public
--   statements; the tidy notion is a proof device. Proofs switch between them with
--   `Turing.MultiTapeTM.ComputableInPolyTime.tidy` and
--   `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy`.
--   The core closure rules of the plain notion use direct machine constructions and are registered with
--   `fun_prop`, together with the transition from tidy to plain computability. `fun_prop` decomposes a
--   plain goal with the plain closure rules and proves the remaining atoms from plain hypotheses or,
--   through the transition, from tidy certificates. Ordinary plain rules for captured scans and list
--   operations are supplied by `PolyTime.List` and `PolyTime.BitString`. If a routine has only a tidy
--   construction certificate, its proof can switch explicitly with `.of_tidy`.
--
--   ### Mixing plain hypotheses with tidy certificates
--
--   There is deliberately no `fun_prop` transition from plain to tidy: registering it together with
--   the reverse transition would create a search cycle. In particular, a tidy goal such as
--   `ComputableTidilyInPolyTime (fun a => [f a]) enc (encList encIntBin)` cannot use a plain certificate
--   for `f` directly. This occurs when constructing singleton target lists in
--   `Complexity/Computability/Complexity/Classes/WPP/Robustness.lean`
--   and `Complexity/Computability/Complexity/Classes/WPP/TwoSided.lean`. Unbounded `fun_prop` can
--   exhaust its heartbeat budget while looking for
--   another certificate. Restate the needed hypothesis with `have hf := hf.tidy` before `fun_prop`,
--   or use `polytime` from `Complexity.Tactic.PolyTime`, which prepares plain hypotheses for tidy
--   search. When trying composition speculatively, use
--   `fun_prop (config := { maxSteps := 32 })` to bound that attempt, then supply a certificate or
--   switch tactics. This is a search budget, not a guarantee that every unsuccessful search is cheap.
--
--   `selectVerifier`, `andVerifier` and `orVerifier` have plain `fun_prop` rules in
--   `Complexity/Computability/Complexity/Classes/SharpP/Combinators.lean`, so plain verifier hypotheses
--   need no manual `.tidy` conversion
--   for a plain goal. Their tidy rules remain available for proofs using the tidy calculus.
--
--   For a tidy certificate covering a whole composite whose intermediate encoding is difficult to
--   infer, prefer `polytime`, or convert the hypotheses with `.tidy` and use
--   `.of_tidy (by fun_prop)`. Two representative cases are the binary threshold
--   `fun a => 3 * (k a * 2 ^ q.eval (enc a).length)` in `inter_mem_SBP_of_mem_BPP` (where `k` uses
--   `encNat`, while the exponent uses `encUnary`), and the input-dependent `sharpTest` verifier in
--   `Complexity/Computability/Complexity/Classes/Toda.lean`. `polytime` proves both directly from plain
--   hypotheses. The mixed-encoding
--   examples and the bounded singleton failure are checked in ComplexityTests/PolyTimeMixes.lean.
--
--   Upstream `Turing.MultiTapeTM.DecidableInTimeAndSpace` decides a problem through its Boolean
--   indicator. `Turing.MultiTapeTM.decidableInTimeAndSpace_iff` restates it for any Boolean function
--   deciding membership, the form used by the classes in `Cslib.Complexity`.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`,
--     `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_space_linear`: time bounds space.
--   * `Turing.MultiTapeTM.ComputesInTimeAndSpace.length_output_le`,
--     `Turing.MultiTapeTM.ComputableInTimeAndSpace.length_le`: time bounds the output.
--   * `Turing.MultiTapeTM.decidableInTimeAndSpace_iff`: decidability through any Boolean decider.
--   * `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime`: a polynomial time
--     bound for any machine, with any space bound, gives tidy polynomial time.
--   * `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength`: tidy
--     polynomial time gives a machine within polynomially bounded time and space.
--   * `Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`: the
--     two notions agree.
--   * `Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime`: the same statement for
--     `Turing.MultiTapeTM.ComputableInPolyTime`, with the shortcuts
--     `Turing.MultiTapeTM.ComputableInPolyTime.tidy`, `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy`
--     and `Turing.MultiTapeTM.ComputableTidilyInPolyTime.computableInPolyTime`.
--   * `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInPolyTime`: a polynomial time bound for
--     any machine, with any space bound, gives polynomial time.
--   * `Turing.MultiTapeTM.ComputableInPolyTime.comp`, `.trans`, `.pair`, `.ite'`, `.fst'`, `.snd'`:
--     closure rules.
--
--   ### References
--
--   * [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
--
--   **Contents.** The module is published as a whole: 13 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Plain`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Plain.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (after crei/tidy-universal lands)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_ResourceFacts
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_PolyTimePrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_PolyTime
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TidyNormalForm
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Polynomial time on plain machines

`Turing.MultiTapeTM.ComputableTidilyInPolyTime` asks for a *tidy* machine, which clears its work
tapes and rewinds its heads before halting, within polynomially bounded time and space. Neither
requirement changes the class. A machine that halts within `t` steps visits at most `k t + k`
work-tape cells, where `k` is its number of work tapes
(`Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`), and the tidy normal form makes any
machine tidy at a linear cost in time and space
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_computableTidilyInTimeAndSpace`). So a function
is tidily computable in polynomial time exactly when some machine computes it in the sense of
upstream `Turing.MultiTapeTM.ComputableInTimeAndSpace`, within polynomially bounded time and space
(`Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`), and
a polynomial time bound alone already suffices
(`Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime`)
[Arora and Barak, Chapter 1][AroraBarak09].

Passing from tidy to plain computations is lossless: a tidy machine is a machine, with the same
bounds. Passing from plain to tidy computations changes the bounds by linear functions whose
coefficients depend on the machine.

The plain notion, `Turing.MultiTapeTM.ComputableInPolyTime`, is the one for definitions and public
statements; the tidy notion is a proof device. Proofs switch between them with
`Turing.MultiTapeTM.ComputableInPolyTime.tidy` and
`Turing.MultiTapeTM.ComputableInPolyTime.of_tidy`.
The core closure rules of the plain notion use direct machine constructions and are registered with
`fun_prop`, together with the transition from tidy to plain computability. `fun_prop` decomposes a
plain goal with the plain closure rules and proves the remaining atoms from plain hypotheses or,
through the transition, from tidy certificates. Ordinary plain rules for captured scans and list
operations are supplied by `PolyTime.List` and `PolyTime.BitString`. If a routine has only a tidy
construction certificate, its proof can switch explicitly with `.of_tidy`.

## Mixing plain hypotheses with tidy certificates

There is deliberately no `fun_prop` transition from plain to tidy: registering it together with
the reverse transition would create a search cycle. In particular, a tidy goal such as
`ComputableTidilyInPolyTime (fun a => [f a]) enc (encList encIntBin)` cannot use a plain certificate
for `f` directly. This occurs when constructing singleton target lists in
`Complexity/Computability/Complexity/Classes/WPP/Robustness.lean`
and `Complexity/Computability/Complexity/Classes/WPP/TwoSided.lean`. Unbounded `fun_prop` can
exhaust its heartbeat budget while looking for
another certificate. Restate the needed hypothesis with `have hf := hf.tidy` before `fun_prop`,
or use `polytime` from `Complexity.Tactic.PolyTime`, which prepares plain hypotheses for tidy
search. When trying composition speculatively, use
`fun_prop (config := { maxSteps := 32 })` to bound that attempt, then supply a certificate or
switch tactics. This is a search budget, not a guarantee that every unsuccessful search is cheap.

`selectVerifier`, `andVerifier` and `orVerifier` have plain `fun_prop` rules in
`Complexity/Computability/Complexity/Classes/SharpP/Combinators.lean`, so plain verifier hypotheses
need no manual `.tidy` conversion
for a plain goal. Their tidy rules remain available for proofs using the tidy calculus.

For a tidy certificate covering a whole composite whose intermediate encoding is difficult to
infer, prefer `polytime`, or convert the hypotheses with `.tidy` and use
`.of_tidy (by fun_prop)`. Two representative cases are the binary threshold
`fun a => 3 * (k a * 2 ^ q.eval (enc a).length)` in `inter_mem_SBP_of_mem_BPP` (where `k` uses
`encNat`, while the exponent uses `encUnary`), and the input-dependent `sharpTest` verifier in
`Complexity/Computability/Complexity/Classes/Toda.lean`. `polytime` proves both directly from plain
hypotheses. The mixed-encoding
examples and the bounded singleton failure are checked in ComplexityTests/PolyTimeMixes.lean.

Upstream `Turing.MultiTapeTM.DecidableInTimeAndSpace` decides a problem through its Boolean
indicator. `Turing.MultiTapeTM.decidableInTimeAndSpace_iff` restates it for any Boolean function
deciding membership, the form used by the classes in `Cslib.Complexity`.

## Main results

* `Turing.MultiTapeTM.ComputesInTimeAndSpace.space_linear`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_space_linear`: time bounds space.
* `Turing.MultiTapeTM.ComputesInTimeAndSpace.length_output_le`,
  `Turing.MultiTapeTM.ComputableInTimeAndSpace.length_le`: time bounds the output.
* `Turing.MultiTapeTM.decidableInTimeAndSpace_iff`: decidability through any Boolean decider.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableTidilyInPolyTime`: a polynomial time
  bound for any machine, with any space bound, gives tidy polynomial time.
* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength`: tidy
  polynomial time gives a machine within polynomially bounded time and space.
* `Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`: the
  two notions agree.
* `Turing.MultiTapeTM.computableInPolyTime_iff_computableTidilyInPolyTime`: the same statement for
  `Turing.MultiTapeTM.ComputableInPolyTime`, with the shortcuts
  `Turing.MultiTapeTM.ComputableInPolyTime.tidy`, `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy`
  and `Turing.MultiTapeTM.ComputableTidilyInPolyTime.computableInPolyTime`.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.computableInPolyTime`: a polynomial time bound for
  any machine, with any space bound, gives polynomial time.
* `Turing.MultiTapeTM.ComputableInPolyTime.comp`, `.trans`, `.pair`, `.ite'`, `.fst'`, `.snd'`:
  closure rules.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Turing.MultiTapeTM

open Cslib

-- upstream: candidate (addition to `Machines/Turing/MultiTape/Deterministic.lean`)

/-! ### Time bounds space -/

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- The indicator of `A` is the Boolean function that is `true` exactly on `A`. -/
theorem indicator_eq_iff {A : Set α} {g : α → Bool} :
    indicator A = g ↔ ∀ a, a ∈ A ↔ g a = true := by
  refine ⟨fun h a => ?_, fun h => funext fun a => ?_⟩
  · subst h
    by_cases ha : a ∈ A <;> simp [indicator, ha]
  · rcases hg : g a <;> simp [indicator, h a, hg]

-- upstream: candidate (after crei/tidy-universal lands)

/-! ### Decidability through a Boolean decider -/

/-- A problem is decidable within given bounds exactly when some Boolean function deciding
membership is computable within them, with answers encoded by `encBool`. -/
theorem decidableInTimeAndSpace_iff {A : Set α} {enc : α ↪ List Bool} {t s : α → ℕ} :
    DecidableInTimeAndSpace A enc t s ↔
      ∃ g : α → Bool, ComputableInTimeAndSpace g enc encBool t s ∧ ∀ a, a ∈ A ↔ g a = true := by
  refine ⟨fun h => ⟨indicator A, h, indicator_eq_iff.mp rfl⟩, fun ⟨g, hg, hA⟩ => ?_⟩
  rw [DecidableInTimeAndSpace, indicator_eq_iff.mpr hA]
  exact hg

/-! ### Tidy and plain polynomial time -/

/-- **Plain polynomial time is tidy polynomial time.** A function computable by some machine
within a time bound polynomial in the length of the encoded input, with any space bound, is
tidily computable in polynomial time. -/
theorem ComputableInTimeAndSpace.computableTidilyInPolyTime {t : ℕ → ℕ} {s : α → ℕ}
    (ht : PolynomiallyBounded t)
    (h : ComputableInTimeAndSpace f encIn encOut (fun a => t (encIn a).length) s) :
    ComputableTidilyInPolyTime f encIn encOut := by
  obtain ⟨c, h⟩ := h.exists_space_linear
  obtain ⟨d, h⟩ := h.exists_computableTidilyInTimeAndSpace
  exact ⟨_, _,
    PolyBounded.of_polynomiallyBounded (fun a => (encIn a).length)
      (bound := fun n => 2 * t n + 3 * (c * t n + c) + d) (by fun_prop),
    PolyBounded.of_polynomiallyBounded (fun a => (encIn a).length)
      (bound := fun n => d * (c * t n + c + 1)) (by fun_prop), h⟩

/-- Tidy polynomial time gives a machine computing the function within polynomially bounded time
and space. The machine and its bounds are those of the tidy computation. -/
theorem ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength
    (h : ComputableTidilyInPolyTime f encIn encOut) :
    ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧ PolynomiallyBounded s ∧
      ComputableInTimeAndSpaceOfLength f encIn encOut t s :=
  let ⟨_, _, ⟨t, ht, htb⟩, ⟨s, hs, hsb⟩, h⟩ := h
  ⟨t, s, ht, hs, (h.mono htb hsb).computableInTimeAndSpace⟩

/-- **Tidy polynomial time is plain polynomial time:** `f` is tidily computable in polynomial time
exactly when some machine with a binary alphabet and finitely many states computes it within time
and space bounded by polynomially bounded functions of the length of the encoded input. -/
theorem computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength :
    ComputableTidilyInPolyTime f encIn encOut ↔ ∃ t s : ℕ → ℕ, PolynomiallyBounded t ∧
      PolynomiallyBounded s ∧ ComputableInTimeAndSpaceOfLength f encIn encOut t s :=
  ⟨ComputableTidilyInPolyTime.exists_computableInTimeAndSpaceOfLength,
    fun ⟨_, _, ht, _, h⟩ => h.computableTidilyInPolyTime ht⟩

/-! ### Bridges to `ComputableInPolyTime` -/

/-- **Plain and tidy polynomial time agree.** `Turing.MultiTapeTM.ComputableInPolyTime` unfolds to
the right-hand side of
`Turing.MultiTapeTM.computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength`. -/
theorem computableInPolyTime_iff_computableTidilyInPolyTime :
    ComputableInPolyTime f encIn encOut ↔ ComputableTidilyInPolyTime f encIn encOut :=
  computableTidilyInPolyTime_iff_exists_computableInTimeAndSpaceOfLength.symm

/-- A function computable in polynomial time is tidily computable in polynomial time. The tidy
machine runs within time and space linear in the plain time bound. -/
theorem ComputableInPolyTime.tidy (h : ComputableInPolyTime f encIn encOut) :
    ComputableTidilyInPolyTime f encIn encOut :=
  computableInPolyTime_iff_computableTidilyInPolyTime.mp h

/-- A function tidily computable in polynomial time is computable in polynomial time, by the same
machine within the same bounds. -/
theorem ComputableInPolyTime.of_tidy (h : ComputableTidilyInPolyTime f encIn encOut) :
    ComputableInPolyTime f encIn encOut :=
  h.exists_computableInTimeAndSpaceOfLength

/-- `Turing.MultiTapeTM.ComputableInPolyTime.of_tidy` for dot notation on a tidy hypothesis. As a
`fun_prop` transition rule, it proves the atoms of a plain goal from tidy certificates. -/
@[fun_prop]
theorem ComputableTidilyInPolyTime.computableInPolyTime
    (h : ComputableTidilyInPolyTime f encIn encOut) : ComputableInPolyTime f encIn encOut :=
  .of_tidy h

end Turing.MultiTapeTM

/-! ### Closure of `ComputableInPolyTime`

The direct core supplies both composition directions (`comp` and `trans`) and ordinary pair
projections. This facade retains legacy-client projection registrations and additional captured
closure rules during migration. Proof-local tidy bridges remain available explicitly; their
presence here does not make the direct core depend on a higher tidy calculus. -/

namespace Turing.MultiTapeTM.ComputableInPolyTime

universe u

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

-- Preserve existing legacy-client registration while the direct core remains usable alone.
attribute [fun_prop] fst' snd'

/-- Project a first component and convert its encoding. Certifying the pair-valued function first
determines the source encoding before automation searches for the conversion certificate. -/
@[fun_prop]
theorem fstWithEncoding {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {output : α ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encA output) :
    ComputableInPolyTime (fun p => (f p).1) encC output :=
  h.comp hf.fst'

/-- Project a second component and convert its encoding. The pair certificate fixes the source
encoding; the conversion certificate supplies the efficient change of representation. -/
@[fun_prop]
theorem sndWithEncoding {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {output : β ↪ List Bool} {f : γ → α × β}
    (hf : ComputableInPolyTime f encC (encPair encA encB))
    (h : ComputableInPolyTime (fun a => a) encB output) :
    ComputableInPolyTime (fun p => (f p).2) encC output :=
  h.comp hf.snd'

/-- A case distinction between functions computable in polynomial time on all inputs. -/
@[fun_prop]
theorem ite' {encC : Bool ↪ List Bool} {c : α → Bool} {f g : α → β}
    (hc : ComputableInPolyTime c encIn encC) (hf : ComputableInPolyTime f encIn encMid)
    (hg : ComputableInPolyTime g encIn encMid) :
    ComputableInPolyTime (fun x => if c x then f x else g x) encIn encMid :=
  ComputableInPolyTime.ite hc hf hg

/-- Return the encoded word of an already computed value. The source and result encodings of
that value remain fixed; this reads the representation already produced by its certificate. -/
@[fun_prop]
theorem encoding_comp {δ : Type*} {ε : Type*} {input : δ ↪ List Bool}
    {output : ε ↪ List Bool} {f : δ → ε} (hf : ComputableInPolyTime f input output) :
    ComputableInPolyTime (fun a => output (f a)) input encBits :=
  (ComputableInPolyTime.of_eq (fun _ => rfl) :
    ComputableInPolyTime output output encBits).comp hf

end Turing.MultiTapeTM.ComputableInPolyTime


