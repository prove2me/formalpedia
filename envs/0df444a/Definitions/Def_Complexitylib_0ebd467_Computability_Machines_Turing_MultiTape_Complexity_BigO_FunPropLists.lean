-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunPropLists
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunPropLists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:59:12.16171+00:00
-- url     : https://prove2.me/theorems/313f5d41-dc9c-45c5-a160-3f69d2bac7da
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists — `fun_prop` rules for list, option, number and test operations
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   These rules assemble `Turing.MultiTapeTM.ComputableInO` certificates with explicit time and
--   charged-space bounds. `fun_prop` composes the primitives through
--   `Turing.MultiTapeTM.ComputableInO.comp'`; `Turing.MultiTapeTM.ComputableInO.mono` then compares
--   the assembled bounds with the client's target bounds.
--
--   The list, option and unary-number primitives are linear in their encoded arguments. The
--   registered binary `natSucc` and `natPred` certificates instead have quadratic time and linear
--   charged space. General equality `eq'` adds its explicit product-of-lengths time charge and
--   encoded-pair space charge; clients enable it locally. Tests against a fixed value of a finite
--   type and binary zero retain the tested computation's bounds, whereas `isEmpty'` adds the
--   computed list's encoded length to both time and space. A test takes that computation as a
--   premise, since its Boolean result does not determine the tested value's encoding.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputableInO.take'`, `.drop'`: prefixes and suffixes, with a unary count.
--   * `Turing.MultiTapeTM.ComputableInO.not'`, `.and'`, `.or'`: Boolean connectives.
--   * `Turing.MultiTapeTM.ComputableInO.decideEq'`, `.natIsZero'`: tests against a constant.
--   * `Turing.MultiTapeTM.ComputableInO.eq'`: equality of computed values, enabled locally by a client.
--   * `Turing.MultiTapeTM.ComputableInO.iteDecide`: case distinction on a decidable proposition.
--
--   **Contents.** The module is published as a whole: 19 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunPropLists`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Complexity/BigO/FunPropLists.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_BigO_FunProp
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_TakeDropUnary
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeUnaryPrimitives

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunPropLists` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# `fun_prop` rules for list, option, number and test operations

These rules assemble `Turing.MultiTapeTM.ComputableInO` certificates with explicit time and
charged-space bounds. `fun_prop` composes the primitives through
`Turing.MultiTapeTM.ComputableInO.comp'`; `Turing.MultiTapeTM.ComputableInO.mono` then compares
the assembled bounds with the client's target bounds.

The list, option and unary-number primitives are linear in their encoded arguments. The
registered binary `natSucc` and `natPred` certificates instead have quadratic time and linear
charged space. General equality `eq'` adds its explicit product-of-lengths time charge and
encoded-pair space charge; clients enable it locally. Tests against a fixed value of a finite
type and binary zero retain the tested computation's bounds, whereas `isEmpty'` adds the
computed list's encoded length to both time and space. A test takes that computation as a
premise, since its Boolean result does not determine the tested value's encoding.

## Main results

* `Turing.MultiTapeTM.ComputableInO.take'`, `.drop'`: prefixes and suffixes, with a unary count.
* `Turing.MultiTapeTM.ComputableInO.not'`, `.and'`, `.or'`: Boolean connectives.
* `Turing.MultiTapeTM.ComputableInO.decideEq'`, `.natIsZero'`: tests against a constant.
* `Turing.MultiTapeTM.ComputableInO.eq'`: equality of computed values, enabled locally by a client.
* `Turing.MultiTapeTM.ComputableInO.iteDecide`: case distinction on a decidable proposition.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInO

variable {α γ : Type} {enc : α ↪ List Bool} {encIn : γ ↪ List Bool}
  {T S T₁ S₁ T₂ S₂ T₃ S₃ : γ → ℕ}

-- The linear primitives as `fun_prop` rules (written out; the source generates them with a local macro).
@[fun_prop] theorem cons' : ComputableInO (fun p : α × List α => p.1 :: p.2) (encPair enc (encList enc)) (encList enc)
    (fun a => ((encPair enc (encList enc)) a).length) fun a => ((encPair enc (encList enc)) a).length := ComputableInDegree.inO_one (ComputableInDegree.cons enc)

@[fun_prop] theorem snoc' : ComputableInO (fun p : List α × α => p.1 ++ [p.2]) (encPair (encList enc) enc) (encList enc)
    (fun a => ((encPair (encList enc) enc) a).length) fun a => ((encPair (encList enc) enc) a).length := ComputableInDegree.inO_one (ComputableInDegree.snoc enc)

@[fun_prop] theorem append' : ComputableInO (fun p : List α × List α => p.1 ++ p.2) (encPair (encList enc) (encList enc)) (encList enc)
    (fun a => ((encPair (encList enc) (encList enc)) a).length) fun a => ((encPair (encList enc) (encList enc)) a).length := ComputableInDegree.inO_one (ComputableInDegree.listAppend enc)

@[fun_prop] theorem tail' : ComputableInO (fun l : List α => l.tail) (encList enc) (encList enc)
    (fun a => ((encList enc) a).length) fun a => ((encList enc) a).length := ComputableInDegree.inO_one (ComputableInDegree.listTail enc)

/-- Whether a computed list is empty. The list is a premise since a Boolean does not determine its
encoding. -/
@[fun_prop]
theorem isEmpty' {l : γ → List α} (hl : ComputableInO l encIn (encList enc) T₁ S₁) :
    ComputableInO (fun x => (l x).isEmpty) encIn encBool
      (fun x => T₁ x + (encList enc (l x)).length) fun x => S₁ x + (encList enc (l x)).length :=
  ComputableInO.comp' (ComputableInDegree.listIsEmpty enc).inO_one hl

@[fun_prop]
theorem headD' (d : α) : ComputableInO (fun l : List α => l.headD d) (encList enc) enc
    (fun l => (encList enc l).length) fun l => (encList enc l).length :=
  (ComputableInDegree.listHeadD enc d).inO_one

@[fun_prop]
theorem some' : ComputableInO (fun a : α => some a) enc (encOption enc)
    (fun a => (enc a).length) fun a => (enc a).length :=
  (ComputableInDegree.optionSome (enc₁ := enc) (enc := encOption enc)).inO_one

@[fun_prop]
theorem unarySucc' : ComputableInO (fun n : ℕ => n + 1) encUnary encUnary
    (fun n => (encUnary n).length) fun n => (encUnary n).length :=
  ComputableInDegree.unary_succ.inO_one

@[fun_prop]
theorem unaryPred' : ComputableInO (fun n : ℕ => n - 1) encUnary encUnary
    (fun n => (encUnary n).length) fun n => (encUnary n).length :=
  ComputableInDegree.unary_pred.inO_one

/-- The first `n x` elements of `l x`, with the count in unary. -/
@[fun_prop]
theorem take' {l : γ → List α} {n : γ → ℕ} (hl : ComputableInO l encIn (encList enc) T₁ S₁)
    (hn : ComputableInO n encIn encUnary T₂ S₂) :
    ComputableInO (fun x => (l x).take (n x)) encIn (encList enc)
      (fun x => T₁ x + T₂ x + (encPair (encList enc) encUnary (l x, n x)).length)
      fun x => S₁ x + S₂ x + (encPair (encList enc) encUnary (l x, n x)).length :=
  ComputableInO.comp' (f := fun p : List α × ℕ => p.1.take p.2)
    (ComputableInDegree.takeUnary enc).inO_one (hl.prod hn)

/-- All but the first `n x` elements of `l x`, with the count in unary. -/
@[fun_prop]
theorem drop' {l : γ → List α} {n : γ → ℕ} (hl : ComputableInO l encIn (encList enc) T₁ S₁)
    (hn : ComputableInO n encIn encUnary T₂ S₂) :
    ComputableInO (fun x => (l x).drop (n x)) encIn (encList enc)
      (fun x => T₁ x + T₂ x + (encPair (encList enc) encUnary (l x, n x)).length)
      fun x => S₁ x + S₂ x + (encPair (encList enc) encUnary (l x, n x)).length :=
  ComputableInO.comp' (f := fun p : List α × ℕ => p.1.drop p.2)
    (ComputableInDegree.dropUnary enc).inO_one (hl.prod hn)

attribute [fun_prop] natSucc natPred

/-- The negation of a computed Boolean. -/
@[fun_prop]
theorem not' {b : γ → Bool} (hb : ComputableInO b encIn encBool T S) :
    ComputableInO (fun x => !b x) encIn encBool T S :=
  (ComputableInDegree.of_finite (encIn := encBool) (encMid := encBool) not).inO_one.comp_linear hb

/-- The conjunction of two computed Booleans. -/
@[fun_prop]
theorem and' {a b : γ → Bool} (ha : ComputableInO a encIn encBool T₁ S₁)
    (hb : ComputableInO b encIn encBool T₂ S₂) :
    ComputableInO (fun x => a x && b x) encIn encBool (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 && q.2).inO_one.comp_linear (ha.prod hb)

/-- The disjunction of two computed Booleans. -/
@[fun_prop]
theorem or' {a b : γ → Bool} (ha : ComputableInO a encIn encBool T₁ S₁)
    (hb : ComputableInO b encIn encBool T₂ S₂) :
    ComputableInO (fun x => a x || b x) encIn encBool (fun x => T₁ x + T₂ x)
      fun x => S₁ x + S₂ x :=
  (ComputableInDegree.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
    fun q : Bool × Bool => q.1 || q.2).inO_one.comp_linear (ha.prod hb)

/-- Whether two computed values agree. This is not a global `fun_prop` rule, since it would also
apply to tests against a constant, which have cheaper rules; a client enables it locally. -/
theorem eq' [DecidableEq α] {a b : γ → α} (ha : ComputableInO a encIn enc T₁ S₁)
    (hb : ComputableInO b encIn enc T₂ S₂) :
    ComputableInO (fun x => decide (a x = b x)) encIn encBool
      (fun x => T₁ x + T₂ x +
        ((enc (a x)).length + 1) * ((enc (a x)).length + (enc (b x)).length + 1))
      fun x => S₁ x + S₂ x + (encPair enc enc (a x, b x)).length :=
  (eq enc).comp' (ha.prod hb)

/-- Whether a computed option is empty, within the bounds of the option. -/
@[fun_prop]
theorem optionIsNone {o : γ → Option α} (h : ComputableInO o encIn (encOption enc) T S) :
    ComputableInO (fun x => (o x).isNone) encIn encBool T S :=
  (not' h.optionIsSome).of_enc_eq fun x => by cases o x <;> rfl

/-- Whether a computed value of a finite type equals a fixed value. -/
@[fun_prop]
theorem decideEq' [Finite α] [DecidableEq α] (c : α) {v : γ → α}
    (hv : ComputableInO v encIn enc T S) :
    ComputableInO (fun x => decide (v x = c)) encIn encBool T S :=
  (ComputableInDegree.of_finite (encIn := enc) (encMid := encBool)
    fun a => decide (a = c)).inO_one.comp_linear hv

/-- Whether a computed binary number is zero. -/
@[fun_prop]
theorem natIsZero' {n : γ → ℕ} (hn : ComputableInO n encIn encNat T S) :
    ComputableInO (fun x => decide (n x = 0)) encIn encBool T S :=
  natIsZero.comp_linear hn

/-- Case distinction on a decidable proposition, through its computed `decide`. -/
@[fun_prop]
theorem iteDecide {β : Type} {encOut : β ↪ List Bool} {c : γ → Prop} [DecidablePred c]
    {f g : γ → β} (hc : ComputableInO (fun x => decide (c x)) encIn encBool T₁ S₁)
    (hf : ComputableInO f encIn encOut T₂ S₂) (hg : ComputableInO g encIn encOut T₃ S₃) :
    ComputableInO (fun x => if c x then f x else g x) encIn encOut
      (fun x => T₁ x + if decide (c x) then T₂ x else T₃ x)
      fun x => S₁ x + if decide (c x) then S₂ x else S₃ x :=
  (hc.ite hf hg).of_enc_eq fun x => by simp only [decide_eq_true_eq]

-- Registered again so that a Boolean condition is tried here before `iteDecide`.
attribute [fun_prop] ite

end Turing.MultiTapeTM.ComputableInO


