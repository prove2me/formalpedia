-- Prove2me | Definitions.Def_CookPvsNP_comp_machine
-- name    : CookPvsNP_comp_machine
-- status  : Definition
-- author  : @Sneed
-- created : 2026-09-30T17:50:15.574531+00:00
-- url     : https://prove2.me/theorems/9c26b5f3-2f9d-4c5d-9194-692cbc786b4a
-- title:
--   Composite Cook one-tape transducer with two-track work alphabet
-- statement:
--   A concrete finite-alphabet one-tape machine construction for sequentially composing two Cook-style polynomial-time transducers. The combined tape stores the first and second machine alphabets on separate tracks, uses movable boundary markers to preserve the finite-list tape semantics, translates the intermediate output between the two symbol embeddings, and cleans the final tape into the requested output encoding.
-- source:
--   Cook, The P versus NP problem, Clay Mathematics Institute (2000), Definition 3; standard sequential simulation of one-tape deterministic transducers.

import Definitions.Def_CookPvsNP_defs

set_option autoImplicit false

namespace CookPvsNP

structure CompCell (Γ₁ Γ₂ : Type) where
  one : Option Γ₁
  two : Option Γ₂
  setupOrigin : Bool
  leftB : Bool
  rightB : Bool
  secondOrigin : Bool
  finalOrigin : Bool
deriving DecidableEq

noncomputable instance instFintypeCompCell {Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂] :
    Fintype (CompCell Γ₁ Γ₂) :=
  Fintype.ofInjective
    (fun c : CompCell Γ₁ Γ₂ =>
      (c.one, c.two, c.setupOrigin, c.leftB, c.rightB, c.secondOrigin, c.finalOrigin))
    (by
      intro a b h
      cases a
      cases b
      simp_all)

def CompCell.blank {Γ₁ Γ₂ : Type} : CompCell Γ₁ Γ₂ :=
  ⟨none, none, false, false, false, false, false⟩

def CompCell.unpack {Γ₁ Γ₂ : Type} : Option (CompCell Γ₁ Γ₂) → CompCell Γ₁ Γ₂
  | none => .blank
  | some c => c

def CompCell.pack {Γ₁ Γ₂ : Type} (c : CompCell Γ₁ Γ₂) : Option (CompCell Γ₁ Γ₂) :=
  if c.one = none ∧ c.two = none ∧ !c.setupOrigin ∧ !c.leftB ∧ !c.rightB ∧
      !c.secondOrigin ∧ !c.finalOrigin then none else some c

def compInputEmbedding {Sym₁ Γ₁ Γ₂ : Type} (ι : Sym₁ ↪ Γ₁) :
    Sym₁ ↪ CompCell Γ₁ Γ₂ where
  toFun x := ⟨some (ι x), none, false, false, false, false, false⟩
  inj' := by
    intro a b h
    apply ι.injective
    exact Option.some.inj (congrArg CompCell.one h)

def compOutputEmbedding {Sym₃ Γ₁ Γ₂ : Type} (ι : Sym₃ ↪ Γ₂) :
    Sym₃ ↪ CompCell Γ₁ Γ₂ where
  toFun x := ⟨none, some (ι x), false, false, false, false, false⟩
  inj' := by
    intro a b h
    apply ι.injective
    exact Option.some.inj (congrArg CompCell.two h)

noncomputable def translateCell {Sym₂ Γ₁ Γ₂ : Type}
    (ι₁ : Sym₂ ↪ Γ₁) (ι₂ : Sym₂ ↪ Γ₂) (a : Γ₁) : Option Γ₂ := by
  classical
  exact if h : ∃ s : Sym₂, ι₁ s = a then some (ι₂ (Classical.choose h)) else none

inductive CompQ (Q₁ Q₂ : Type)
  | setupStart
  | setupScan
  | setupReturn
  | setupBounce
  | sim₁ (q : Q₁)
  | sim₁R (q : Q₁)
  | sim₁RBack (q : Q₁) (expand : Bool)
  | sim₁L (q : Q₁)
  | sim₁LBack (q : Q₁)
  | convPlaceLeft
  | convCopy (first : Bool)
  | convEmptyRight
  | convSeekOldRight
  | convReturn
  | convBounce
  | sim₂ (q : Q₂)
  | sim₂R (q : Q₂)
  | sim₂RBack (q : Q₂) (expand : Bool)
  | sim₂L (q : Q₂)
  | sim₂LBack (q : Q₂) (expand : Bool)
  | finalClean (ended : Bool)
  | finalReturn
  | finalBounce
  | haltAccept
  | haltReject
deriving DecidableEq, Fintype

noncomputable def compTM
    {Sym₂ Γ₁ Γ₂ : Type} [Fintype Γ₁] [Fintype Γ₂]
    (ι₂₁ : Sym₂ ↪ Γ₁) (ι₂₂ : Sym₂ ↪ Γ₂)
    (M₁ : TM Γ₁) (M₂ : TM Γ₂) : TM (CompCell Γ₁ Γ₂) where
  Q := CompQ M₁.Q M₂.Q
  q₀ := .setupStart
  qaccept := .haltAccept
  qreject := .haltReject
  accept_ne_reject := by intro h; cases h
  δ := fun q s =>
    let c := CompCell.unpack s
    let keep := CompCell.pack c
    match q with
    | .setupStart =>
        (.setupScan, CompCell.pack { c with setupOrigin := true }, .right)
    | .setupScan =>
        match s with
        | none =>
            (.setupReturn, CompCell.pack { c with rightB := true }, .left)
        | some _ => (.setupScan, keep, .right)
    | .setupReturn =>
        if c.setupOrigin then
          (.setupBounce, CompCell.pack { c with setupOrigin := false }, .right)
        else
          (.setupReturn, keep, .left)
    | .setupBounce =>
        (.sim₁ M₁.q₀, keep, .left)
    | .sim₁ q₁ =>
        if q₁ = M₁.qaccept ∨ q₁ = M₁.qreject then
          (.convPlaceLeft, CompCell.pack { c with secondOrigin := true }, .left)
        else
          match M₁.δ q₁ c.one with
          | (q', w, .right) =>
              (.sim₁R q', CompCell.pack { c with one := w }, .right)
          | (q', w, .left) =>
              (.sim₁L q', CompCell.pack { c with one := w }, .left)
    | .sim₁R q₁ =>
        if c.rightB then
          (.sim₁RBack q₁ true, CompCell.pack { c with rightB := false }, .right)
        else
          (.sim₁RBack q₁ false, keep, .left)
    | .sim₁RBack q₁ expand =>
        if expand then
          (.sim₁ q₁, CompCell.pack { c with rightB := true }, .left)
        else
          (.sim₁ q₁, keep, .right)
    | .sim₁L q₁ =>
        (.sim₁LBack q₁, keep, .right)
    | .sim₁LBack q₁ =>
        (.sim₁ q₁, keep, .left)
    | .convPlaceLeft =>
        (.convCopy true, CompCell.pack { c with leftB := true }, .right)
    | .convCopy first =>
        match c.one with
        | some a =>
            (.convCopy false,
              CompCell.pack { c with two := translateCell ι₂₁ ι₂₂ a },
              .right)
        | none =>
            if first then
              (.convEmptyRight, keep, .right)
            else if c.rightB then
              (.convReturn, keep, .left)
            else
              (.convSeekOldRight, CompCell.pack { c with rightB := true }, .right)
    | .convEmptyRight =>
        if c.rightB then
          (.convReturn, keep, .left)
        else
          (.convSeekOldRight, CompCell.pack { c with rightB := true }, .right)
    | .convSeekOldRight =>
        if c.rightB then
          (.convReturn, CompCell.pack { c with rightB := false }, .left)
        else
          (.convSeekOldRight, CompCell.pack { c with one := none, two := none }, .right)
    | .convReturn =>
        if c.secondOrigin then
          (.convBounce, CompCell.pack { c with secondOrigin := false }, .right)
        else
          (.convReturn, keep, .left)
    | .convBounce =>
        (.sim₂ M₂.q₀, keep, .left)
    | .sim₂ q₂ =>
        if q₂ = M₂.qaccept ∨ q₂ = M₂.qreject then
          let ended := c.two.isNone
          let c' : CompCell Γ₁ Γ₂ :=
            { c with
              one := none
              setupOrigin := false
              secondOrigin := false
              finalOrigin := true }
          (.finalClean ended, CompCell.pack c', .right)
        else
          match M₂.δ q₂ c.two with
          | (q', w, .right) =>
              (.sim₂R q', CompCell.pack { c with two := w }, .right)
          | (q', w, .left) =>
              (.sim₂L q', CompCell.pack { c with two := w }, .left)
    | .sim₂R q₂ =>
        if c.rightB then
          (.sim₂RBack q₂ true, CompCell.pack { c with rightB := false }, .right)
        else
          (.sim₂RBack q₂ false, keep, .left)
    | .sim₂RBack q₂ expand =>
        if expand then
          (.sim₂ q₂, CompCell.pack { c with rightB := true }, .left)
        else
          (.sim₂ q₂, keep, .right)
    | .sim₂L q₂ =>
        if c.leftB then
          (.sim₂LBack q₂ true, CompCell.pack { c with leftB := false }, .left)
        else
          (.sim₂LBack q₂ false, keep, .right)
    | .sim₂LBack q₂ expand =>
        if expand then
          (.sim₂ q₂, CompCell.pack { c with leftB := true }, .right)
        else
          (.sim₂ q₂, keep, .left)
    | .finalClean ended =>
        if c.rightB then
          (.finalReturn, none, .left)
        else if ended then
          (.finalClean true, none, .right)
        else
          match c.two with
          | none => (.finalClean true, none, .right)
          | some _ =>
              (.finalClean false,
                CompCell.pack { c with
                  one := none
                  setupOrigin := false
                  leftB := false
                  rightB := false
                  secondOrigin := false
                  finalOrigin := false },
                .right)
    | .finalReturn =>
        if c.finalOrigin then
          (.finalBounce, CompCell.pack { c with finalOrigin := false }, .right)
        else
          (.finalReturn, keep, .left)
    | .finalBounce =>
        (.haltAccept, keep, .left)
    | .haltAccept => (.haltAccept, keep, .right)
    | .haltReject => (.haltReject, keep, .right)

end CookPvsNP


