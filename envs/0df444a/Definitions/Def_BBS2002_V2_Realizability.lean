-- Prove2me | Definitions.Def_BBS2002_V2_Realizability
-- name    : BBS2002_V2_Realizability
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-01T18:39:56.545103+00:00
-- url     : https://prove2.me/theorems/2b406e5b-e279-4ead-be27-57f9df8682d4
-- title:
--   Capture-avoiding modified realizability and indexed realizers
-- statement:
--   Section 4's modified realizability translation with explicit capture avoidance. A realizer at the omitted type is the symbol epsilon, represented by a singleton; at a program type it is a term, with a separate typing predicate. The translation of X applies the comprehension term to the supplied realizer. Atomic formulas are unchanged. Universal and implication clauses use fresh bound variables, preserving free parameters of both the comprehension term and realizer. Universal clauses rename the original bound variable before recursing. The module also gives the source assumption's indexed realizer and a comprehension-independent naming convention: the dummy is typed and closed; assumption identifiers do not coincide with object-variable identifiers written in the proof; equal assumption identifiers carry equal formulas. This module reuses the original syntax and structural extraction, and supersedes the original mrFormula and AdmissibleForExtraction for the V2 extraction targets.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, Refined program extraction from classical proofs, Annals of Pure and Applied Logic 114 (2002), pp. 3–25, https://doi.org/10.1016/S0168-0072(01)00073-2; page references below use the author's preprint pagination. Section 4, preprint pp. 11–12, type assignment, extraction, and modified realizability.

import Definitions.Def_BBS2002_Extraction

/-!
# Capture-avoiding modified realizability

Berger, Buchholz, and Schwichtenberg, *Refined program extraction from classical proofs*,
Section 4, preprint pp. 11–12. Object-language bound variables are renamed when translating
formulas, so that the parameters of the comprehension term and the realizer remain free.
The indexed `Realizer` type represents exactly the source alternatives: epsilon for `*`, and
a term when the assigned type is computationally relevant. There is no fallback at `X`.
-/

namespace BBS2002.V2

/-- The source's epsilon when the assigned type is `*`, and a term otherwise. -/
def Realizer : Option Ty → Type
  | none => Unit
  | some _ => Term

namespace Realizer

/-- The option representation used by structural proof extraction. -/
def toOption {τ : Option Ty} : Realizer τ → Option Term :=
  match τ with
  | none => fun _ ↦ none
  | some _ => fun t ↦ some t

/-- Typing of a realizer; epsilon has no typing obligation. -/
def Typed {τ : Option Ty} : Realizer τ → Prop :=
  match τ with
  | none => fun _ ↦ True
  | some ρ => fun t ↦ HasType t ρ

/-- Transport a realizer along equality of assigned types. -/
def cast {τ σ : Option Ty} (h : τ = σ) (r : Realizer τ) : Realizer σ := h ▸ r

/-- Convert an option from extraction only when its shape agrees with the assigned type. -/
def ofOption {τ : Option Ty} (r : Option Term) (h : r.isSome = τ.isSome) : Realizer τ := by
  cases τ with
  | none =>
      cases r with
      | none => exact ()
      | some _ => cases h
  | some ρ =>
      cases r with
      | none => cases h
      | some t => exact t

@[simp] theorem toOption_ofOption {τ : Option Ty} (r : Option Term)
    (h : r.isSome = τ.isSome) : (ofOption r h).toOption = r := by
  cases τ <;> cases r
  · rfl
  · cases h
  · cases h
  · rfl

@[simp] theorem toOption_cast {τ σ : Option Ty} (h : τ = σ) (r : Realizer τ) :
    (cast h r).toOption = r.toOption := by
  cases h
  rfl

end Realizer

/-- Renaming object variables does not change computational type. -/
theorem tau_renameFreeVarFormula (ν : Ty) (A : Formula) (x y : Var) :
    tau ν (renameFreeVarFormula A x y) = tau ν A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp A B ihA ihB => simp only [renameFreeVarFormula, tau, ihA, ihB]
  | all v A ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp only [tau, ih]

/-- A fresh variable above both formulas, the comprehension term, and the current realizer. -/
def freshVar {ν : Ty} (comp : CompTerm ν) (r : Option Term)
    (A B : Formula) (ρ : Ty) : Var :=
  ⟨freshMrVarId comp r A B, ρ⟩

/-- Capture-avoiding modified realizability, with the source's realizer-shape convention
enforced by the index of `r`. All newly emitted quantifiers use fresh names. -/
def mrFormula (ν : Ty) (comp : CompTerm ν) (A : Formula)
    (r : Realizer (tau ν A)) : Formula :=
  match A with
  | .varX => comp.apply r
  | .bot => .bot
  | .atom t => .atom t
  | .all x A =>
      let y := freshVar comp r.toOption (.all x A) .bot x.ty
      let A' := renameFreeVarFormula A x y
      match hA : tau ν A with
      | none =>
          let ar : Realizer (tau ν A') :=
            Realizer.cast ((tau_renameFreeVarFormula ν A x y).trans hA).symm ()
          .all y (mrFormula ν comp A' ar)
      | some ρ =>
          let t : Term := Realizer.cast (σ := some (.arr x.ty ρ))
            (by simp only [tau, hA]) r
          let ar : Realizer (tau ν A') :=
            Realizer.cast ((tau_renameFreeVarFormula ν A x y).trans hA).symm
              (.app t (.var y))
          .all y (mrFormula ν comp A' ar)
  | .imp A B =>
      match hA : tau ν A, hB : tau ν B with
      | none, none =>
          .imp (mrFormula ν comp A (Realizer.cast hA.symm ()))
            (mrFormula ν comp B (Realizer.cast hB.symm ()))
      | none, some _ =>
          let rb : Realizer (tau ν B) := Realizer.cast (by simp only [tau, hA]) r
          .imp (mrFormula ν comp A (Realizer.cast hA.symm ())) (mrFormula ν comp B rb)
      | some ρ, none =>
          let y := freshVar comp none A B ρ
          let ar : Realizer (tau ν A) := Realizer.cast hA.symm (.var y)
          .all y (.imp (mrFormula ν comp A ar)
            (mrFormula ν comp B (Realizer.cast hB.symm ())))
      | some ρ, some σ =>
          let t : Term := Realizer.cast (σ := some (.arr ρ σ))
            (by simp only [tau, hA, hB]) r
          let y := freshVar comp (some t) A B ρ
          let ar : Realizer (tau ν A) := Realizer.cast hA.symm (.var y)
          let br : Realizer (tau ν B) := Realizer.cast hB.symm (.app t (.var y))
          .all y (.imp (mrFormula ν comp A ar) (mrFormula ν comp B br))
termination_by formulaSize A
decreasing_by
  all_goals simp_wf
  all_goals simp [formulaSize, renameFreeVarFormula_size]
  all_goals omega

/-- Indexed realizer variable associated with a source assumption variable. -/
def assumpRealizer (ν : Ty) (u : AssumpVar) : Realizer (tau ν u.formula) :=
  match tau ν u.formula with
  | none => ()
  | some ρ => .var ⟨u.id, ρ⟩

@[simp] theorem assumpRealizer_toOption (ν : Ty) (u : AssumpVar) :
    (assumpRealizer ν u).toOption = assumpRealizerTerm ν u := by
  unfold assumpRealizer assumpRealizerTerm assumpRealizerVar
  cases tau ν u.formula <;> rfl

theorem assumpRealizer_typed (ν : Ty) (u : AssumpVar) :
    (assumpRealizer ν u).Typed := by
  unfold assumpRealizer
  cases tau ν u.formula with
  | none => exact True.intro
  | some ρ => exact HasType.var ⟨u.id, ρ⟩

/-- Naming and dummy-term conventions for structural extraction. Assumption labels are
consistent, and their realizer variables do not collide with object variables written in the
proof. The comprehension term is arbitrary: its free parameters need no global separation
from source parameters, since realizability itself avoids capture. -/
def AdmissibleForExtraction (ν : Ty) (dummy : Term) (M : ProofTerm) : Prop :=
  HasType dummy ν ∧
  IsClosedTerm dummy ∧
  (∀ u ∈ allAssumpVars M, ∀ x ∈ allVarsProof M, u.id ≠ x.id) ∧
  (∀ u₁ ∈ allAssumpVars M, ∀ u₂ ∈ allAssumpVars M,
    u₁.id = u₂.id → u₁.formula = u₂.formula)

end BBS2002.V2


