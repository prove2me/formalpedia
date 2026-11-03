-- Prove2me | Definitions.Def_NishtAbel2024V2_Inference
-- name    : NishtAbel2024V2_Inference
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-02T21:44:13.659829+00:00
-- url     : https://prove2.me/theorems/ebf8d60e-4f75-4946-abd8-8cba410aac0a
-- title:
--   Repaired V2 Chapter 6: Polarized Signature Encoding, Guarded Comparison, Safe Term Inference, and Checked Constraint Solving
-- statement:
--   Repaired V2 formalization of Chapter 6 (pp. 41–60) and Appendix A (pp. I–V) of Nisht & Abel (2024): includes `CompareFresh` and `CompareKinded` on `CompareTypes.lam`, kinding-aware fixpoint occurrence relations (`InferUse`, `CheckUse`), occurrence-transporting `GuardedCompareTypes`, no-incoming-edge guarded term inference/checking (`SafeInferTerm`, `SafeCheckTerm`, `NoDistinctIncoming`, `NoOutsideIncoming`), the fuel-bounded `CheckedConstraintSolver`, and `PostcheckedAlgorithm2Accepts`.
-- source:
--   Kanstantsin Nisht, "Type-Based Termination Checking in Agda", Master's Thesis in Computer Science and Engineering, Chalmers University of Technology and University of Gothenburg (supervised by Andreas Abel), 2024; extended abstract by Kanstantsin Nisht and Andreas Abel, TYPES 2024. Repaired V2 formalization.

import Mathlib
import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Semantics

/-!
# Chapter 6 & Appendix A of Nisht & Abel (2024): Size Inference, Constraint Solving, and Termination Checking

This module formalizes the type-based termination inference pipeline of Chapter 6 (pp. 41–60)
and the unannotated source calculus System `F_ω^c` of Appendix A (pp. I–V) of
Kanstantsin Nisht and Andreas Abel, *"Type-Based Termination Checking in Agda"* (2024):

1. **Appendix A (pp. I–V): Unannotated System `F_ω^c`**:
   - Kind checking `Δ ⊢_{F_ω} A ⇒ ι` and `Δ ⊢_{F_ω} A ⇐ ι` (`FwKindInfer`, `FwKindCheck`)
   - Pattern and copattern-spine typing `Δ; Γ ⊢^{Δ'}_{F_ω} p ⇐ A` and
     `Δ; Γ | A ⊢^{Δ'}_{F_ω} q⃗ ⇒ C` (`FwPatTyping`, `FwSpineTyping`)
2. **Section 6.1 (pp. 41–44): Function Signature Encoding**:
   - Polarized type encoding `π; Δ ⊢_{SCT}^{π*} A ⇒ Ψ; A'` (`EncodeType`)
   - Fixpoint kind tag `FixKind` (`μ` vs. `ν`) and polarized size-variable occurrence
     `Δ ⊢ i ∈_π F` (`SizeOccursFixPol`, `SizeOccursPol`)
3. **Section 6.2 (pp. 44–47): Pattern & Copattern-Spine Rigid Variable Gathering**:
   - Pattern rigid-variable gathering `Δ₀ ⊢_{SCT} p : A ⇒ Γ; Δ; Ψ; p'` (`InferPat`)
   - Copattern-spine rigid-variable gathering `Δ₀ ⊢_{SCT} q⃗ : A ⇒ C; Γ; Δ; Ψ; q⃗'` (`InferSpine`)
4. **Section 6.3 (pp. 48–56): Call-Site Inference, Checking, and Type Comparison**:
   - Flexible variable context `Φ` (`FlexVars`), size constraints `C` (`SizeConstraint`),
     and non-recursive constructor size variables `T`
   - Call-site inference `Φ; Γ; Δ ⊢_{SCT} t ⇒ A; Φ'; C; T; t'` (`InferTerm`)
   - Call-site checking `Φ; Γ; Δ | A ⊢_{SCT} t ⇒ Φ'; C; T; t'` (`CheckTerm`)
   - Context trivialization `Φ ⊢_↓ Ψ₁ ⇒ Ψ₂` (`TrivializeCtx`) and clause checking
     `Φ; Γ; Δ | C ⊢_{SCT} D ⇒ Φ'; C_out; T; D'` (`CheckClauseInfer`, `CheckClausesInfer`)
   - Polarized type comparison `Φ; Δ; ι ⊢_{SCT} A ≤^π B ⇒ C` (`CompareTypes`)
5. **Sections 6.4–6.5 (pp. 56–60): Constraint Solving (Algorithm 1) & Termination Checker (Algorithm 2)**:
   - Flexible substitution `φ`, functorial term application `φ(t)`, and coherence `Ψ; C ⊢ φ`
     (`CoherentSubst`)
   - Closest next bound `Ψ ⊢ R a ⇒ b` (`ClosestNextBound`, `closestNextBound`) and least upper
     bound `Ψ ⊢ LUB(b₁, ..., bₘ) ⇒ c` (`IsLubSize`, `lubSizes`)
   - **Algorithm 1** (`solveConstraintGraph` computing `φ*`)
   - Recursive-call invocation graph conformance (`LocalCallsConform`, `buildCallGraph`) and
     **Algorithm 2** (`Algorithm2Accepts`)
-/

namespace NishtAbel2024V2

/-! ## Appendix A: Unannotated Source Calculus System `F_ω^c` (pp. I–V) -/

/-- Simple functor kind `◦* → *` in System `F_ω^c` (Appendix A, p. II). -/
def fwFunctorSKind : SKind :=
  .arr .mixed .star .star

mutual

/-- Check whether a `TypeExpr` belongs to the unannotated System `F_ω^c` fragment
(i.e. contains no size atoms `.size`, no bounded size quantifiers `.lt`, and all fixpoints
`μ` and `ν` carry the unannotated size `.infty`). -/
def TypeExpr.isUnannotated : TypeExpr → Prop
  | .atom (.size _) => False
  | .atom (.all (.lt _)) => False
  | .atom (.ex (.lt _)) => False
  | .atom _ => True
  | .lam _ _ body => body.isUnannotated
  | .app F G => F.isUnannotated ∧ G.isUnannotated
  | .mu a S => a = .infty ∧ isUnannotatedBranches S
  | .nu a R => a = .infty ∧ isUnannotatedBranches R

/-- Helper: check whether all branches/fields in a list are unannotated. -/
def isUnannotatedBranches : List (Nat × TypeExpr) → Prop
  | [] => True
  | (_, F) :: rest => F.isUnannotated ∧ isUnannotatedBranches rest

end

mutual

/-- Unannotated kind inference `Δ ⊢_{F_ω} F ⇒ ι` in System `F_ω^c` (Appendix A, Section A.1.2, p. II). -/
inductive FwKindInfer : KindingCtx → TypeExpr → SKind → Prop where
  | unit (Δ : KindingCtx) :
      FwKindInfer Δ (.atom .unit) .star
  | prod (Δ : KindingCtx) :
      FwKindInfer Δ (.atom .prod) (.arr .pos .star (.arr .pos .star .star))
  | arr (Δ : KindingCtx) :
      FwKindInfer Δ (.atom .arr) (.arr .neg .star (.arr .pos .star .star))
  | var {Δ : KindingCtx} {X : TyVar} {π : Polarity} {ι : SKind} :
      TyDecl.mk X π (Kind.ofSKind ι) ∈ Δ.types →
      Polarity.le π .pos = true →
      FwKindInfer Δ (.atom (.var X)) ι
  | app {Δ : KindingCtx} {F G : TypeExpr} {π : Polarity} {ι ι' : SKind} :
      FwKindInfer Δ F (.arr π ι ι') →
      FwKindCheck (Δ.invScalePol π) G ι →
      FwKindInfer Δ (.app F G) ι'
  | all {Δ : KindingCtx} {ι : SKind} :
      FwKindInfer Δ (.atom (.all (Kind.ofSKind ι)))
        (.arr .pos (.arr .mixed ι .star) .star)
  | ex {Δ : KindingCtx} {ι : SKind} :
      FwKindInfer Δ (.atom (.ex (Kind.ofSKind ι)))
        (.arr .pos (.arr .mixed ι .star) .star)
  | mu {Δ : KindingCtx} {S : List (ConsName × TypeExpr)} :
      (∀ p ∈ S, FwKindCheck Δ p.2 fwFunctorSKind) →
      FwKindInfer Δ (.mu .infty S) .star
  | nu {Δ : KindingCtx} {R : List (ProjName × TypeExpr)} :
      (∀ p ∈ R, FwKindCheck Δ p.2 fwFunctorSKind) →
      FwKindInfer Δ (.nu .infty R) .star

/-- Unannotated kind checking `Δ ⊢_{F_ω} F ⇐ ι` in System `F_ω^c` (Appendix A, Section A.1.2, p. II). -/
inductive FwKindCheck : KindingCtx → TypeExpr → SKind → Prop where
  | infer {Δ : KindingCtx} {F : TypeExpr} {ι : SKind} :
      FwKindInfer Δ F ι →
      FwKindCheck Δ F ι
  | lam {Δ : KindingCtx} {X : TyVar} {ι ι' : SKind} {F : TypeExpr} {π : Polarity} :
      FwKindCheck (Δ.extType X π (Kind.ofSKind ι)) F ι' →
      FwKindCheck Δ (.lam X ι F) (.arr π ι ι')

end

/-- Unannotated pattern typing `Δ; Γ ⊢^{Δ'}_{F_ω} p ⇐ A` in System `F_ω^c`
(Appendix A, Section A.2, p. II). -/
inductive FwPatTyping : KindingCtx → List TyDecl → TermCtx → Pat → TypeExpr → Prop where
  | var (Δ : KindingCtx) (x : TermVar) {A : TypeExpr} :
      FwKindCheck Δ A .star →
      FwPatTyping Δ [] [(x, A)] (.var x) A
  | unit (Δ : KindingCtx) :
      FwPatTyping Δ [] [] .unit .unitTy
  | pair {Δ : KindingCtx} {Δ₁ Δ₂ : List TyDecl} {Γ₁ Γ₂ : TermCtx}
      {p₁ p₂ : Pat} {A₁ A₂ : TypeExpr} :
      FwPatTyping Δ Δ₁ Γ₁ p₁ A₁ →
      FwPatTyping (Δ.append ⟨[], Δ₁⟩) Δ₂ Γ₂ p₂ A₂ →
      FwPatTyping Δ (Δ₁ ++ Δ₂) (Γ₁ ++ Γ₂) (.pair p₁ p₂) (.prodTy A₁ A₂)
  | cons {Δ : KindingCtx} {Δ' : List TyDecl} {Γ : TermCtx} {c : ConsName} {p : Pat}
      {S : List (ConsName × TypeExpr)} {Sc : TypeExpr} :
      TypeExpr.lookupCons S c = some Sc →
      FwPatTyping Δ Δ' Γ p (Sc.normApp (.mu .infty S)) →
      FwPatTyping Δ Δ' Γ (.cons c p) (.mu .infty S)
  | tyPack {Δ : KindingCtx} {Δ' : List TyDecl} {Γ : TermCtx} {X : TyVar} {ι : SKind}
      {p : Pat} {F : TypeExpr} :
      X ∉ (Δ.types ++ Δ').map (·.var) →
      FwPatTyping (Δ.extType X .pos (Kind.ofSKind ι)) Δ' Γ p (F.normApp (.atom (.var X))) →
      FwPatTyping Δ (⟨X, .pos, Kind.ofSKind ι⟩ :: Δ') Γ (.tyPack X p) (.exTy (Kind.ofSKind ι) F)

/-- Unannotated copattern-spine typing `Δ; Γ | A ⊢^{Δ'}_{F_ω} q⃗ ⇒ C` in System `F_ω^c`
(Appendix A, Section A.2, p. III). -/
inductive FwSpineTyping :
    KindingCtx → List TyDecl → TermCtx → TypeExpr → PatSpine → TypeExpr → Prop where
  | nil (Δ : KindingCtx) (A : TypeExpr) :
      FwSpineTyping Δ [] [] A [] A
  | pat {Δ : KindingCtx} {Δ₁ Δ₂ : List TyDecl} {Γ₁ Γ₂ : TermCtx}
      {p : Pat} {qs : PatSpine} {A B C : TypeExpr} :
      FwPatTyping Δ Δ₁ Γ₁ p A →
      FwSpineTyping (Δ.append ⟨[], Δ₁⟩) Δ₂ Γ₂ B qs C →
      FwSpineTyping Δ (Δ₁ ++ Δ₂) (Γ₁ ++ Γ₂) (.arrTy A B) (.pat p :: qs) C
  | tyApp {Δ : KindingCtx} {Δ' : List TyDecl} {Γ : TermCtx} {X : TyVar} {ι : SKind}
      {F C : TypeExpr} {qs : PatSpine} :
      X ∉ (Δ.types ++ Δ').map (·.var) →
      FwSpineTyping (Δ.extType X .pos (Kind.ofSKind ι)) Δ' Γ
        (F.normApp (.atom (.var X))) qs C →
      FwSpineTyping Δ (⟨X, .pos, Kind.ofSKind ι⟩ :: Δ') Γ
        (.allTy (Kind.ofSKind ι) F) (.tyVar X :: qs) C
  | proj {Δ : KindingCtx} {Δ' : List TyDecl} {Γ : TermCtx} {d : ProjName}
      {R : List (ProjName × TypeExpr)} {Rd C : TypeExpr} {qs : PatSpine} :
      TypeExpr.lookupProj R d = some Rd →
      FwSpineTyping Δ Δ' Γ (Rd.normApp (.nu .infty R)) qs C →
      FwSpineTyping Δ Δ' Γ (.nu .infty R) (.proj d :: qs) C

/-! ## Section 6.1: Function Signature Encoding & Polarized Size Occurrences (pp. 41–44) -/

/-- Tag distinguishing inductive (`μ`) and coinductive (`ν`) fixpoint operators
(Section 6.1, Lemma 3, p. 43). -/
inductive FixKind where
  | mu : FixKind
  | nu : FixKind
  deriving DecidableEq, Repr

mutual

/-- Collect all size variables mentioned in a `TypeExpr`. -/
def TypeExpr.allSizeVars : TypeExpr → List SizeVar
  | .atom (.size a) => a.vars
  | .atom (.all (.lt a)) => a.vars
  | .atom (.ex (.lt a)) => a.vars
  | .atom _ => []
  | .lam _ _ body => body.allSizeVars
  | .app F G => F.allSizeVars ++ G.allSizeVars
  | .mu a S => a.vars ++ allSizeVarsBranches S
  | .nu a R => a.vars ++ allSizeVarsBranches R

/-- Helper: collect all size variables mentioned across a list of branches/fields. -/
def allSizeVarsBranches : List (Nat × TypeExpr) → List SizeVar
  | [] => []
  | (_, F) :: rest => F.allSizeVars ++ allSizeVarsBranches rest

end

/-- Polarized size-variable occurrence judgment `Δ ⊢ i ∈_π F` refined by fixpoint kind `fk ∈ {μ, ν}`
(Section 6.1, p. 43): records that size variable `i` occurs as the size annotation of a fixpoint
of kind `fk` with polarity `π` in `F`. -/
inductive SizeOccursFixPol : KindingCtx → FixKind → SizeVar → Polarity → TypeExpr → Prop where
  | mu_top {Δ : KindingCtx} {i : SizeVar} {n : Nat} {S : List (ConsName × TypeExpr)} :
      SizeOccursFixPol Δ .mu i .pos (.mu (.var i n) S)
  | nu_top {Δ : KindingCtx} {i : SizeVar} {n : Nat} {R : List (ProjName × TypeExpr)} :
      SizeOccursFixPol Δ .nu i .pos (.nu (.var i n) R)
  | mu_branch {Δ : KindingCtx} {fk : FixKind} {i : SizeVar} {π : Polarity}
      {a : SizeExp} {S : List (ConsName × TypeExpr)} {c : ConsName} {Sc : TypeExpr} :
      (c, Sc) ∈ S →
      SizeOccursFixPol Δ fk i π Sc →
      SizeOccursFixPol Δ fk i π (.mu a S)
  | nu_field {Δ : KindingCtx} {fk : FixKind} {i : SizeVar} {π : Polarity}
      {a : SizeExp} {R : List (ProjName × TypeExpr)} {d : ProjName} {Rd : TypeExpr} :
      (d, Rd) ∈ R →
      SizeOccursFixPol Δ fk i π Rd →
      SizeOccursFixPol Δ fk i π (.nu a R)
  | lam {Δ : KindingCtx} {fk : FixKind} {i : SizeVar} {π : Polarity}
      {X : TyVar} {ι : SKind} {F : TypeExpr} :
      SizeOccursFixPol (Δ.extType X .mixed (Kind.ofSKind ι)) fk i π F →
      SizeOccursFixPol Δ fk i π (.lam X ι F)
  | app_left {Δ : KindingCtx} {fk : FixKind} {i : SizeVar} {π π' : Polarity}
      {κ κ' : Kind} {F G : TypeExpr} :
      KindInfer Δ F (.arr π' κ κ') →
      SizeOccursFixPol Δ fk i π F →
      SizeOccursFixPol Δ fk i π (.app F G)
  | app_right {Δ : KindingCtx} {fk : FixKind} {i : SizeVar} {π π' : Polarity}
      {κ κ' : Kind} {F G : TypeExpr} :
      KindInfer Δ F (.arr π' κ κ') →
      SizeOccursFixPol (Δ.invScalePol π') fk i π G →
      SizeOccursFixPol Δ fk i (Polarity.comp π' π) (.app F G)

/-- Polarized size-variable occurrence `Δ ⊢ i ∈_π F` (Section 6.1, p. 43):
`i` occurs as index to some fixpoint operator (`μ` or `ν`) with polarity `π` in `F`. -/
def SizeOccursPol (Δ : KindingCtx) (i : SizeVar) (π : Polarity) (F : TypeExpr) : Prop :=
  ∃ fk : FixKind, SizeOccursFixPol Δ fk i π F

/-- Check whether a size variable `i` occurs anywhere in a type `F` (`i ∈ F.allSizeVars`). -/
def SizeOccursIn (i : SizeVar) (F : TypeExpr) : Prop :=
  i ∈ F.allSizeVars

mutual

/-- Polarized type signature encoding `π; Δ ⊢_{SCT}^{π*} A ⇒ Ψ; A'` (Section 6.1, pp. 42–43):
given target polarity `π*` (`π* = −` for top-level function signatures, `π* = ◦` for local type
annotations), current polarity `π`, kinding context `Δ`, and an unannotated type `A` of kind `κ`,
generates fresh unbounded size variables `Ψ` and a size-annotated type `A'`. -/
inductive EncodeType (πstar : Polarity) :
    Polarity → KindingCtx → TypeExpr → SizeCtx → TypeExpr → Prop where
  | unit (π : Polarity) (Δ : KindingCtx) :
      EncodeType πstar π Δ (.atom .unit) [] (.atom .unit)
  | prod (π : Polarity) (Δ : KindingCtx) :
      EncodeType πstar π Δ (.atom .prod) [] (.atom .prod)
  | arr (π : Polarity) (Δ : KindingCtx) :
      EncodeType πstar π Δ (.atom .arr) [] (.atom .arr)
  | var {π π' : Polarity} {Δ : KindingCtx} {X : TyVar} {ι : SKind} :
      TyDecl.mk X π' (Kind.ofSKind ι) ∈ Δ.types →
      Polarity.le π' .pos = true →
      EncodeType πstar π Δ (.atom (.var X)) [] (.atom (.var X))
  | all (π : Polarity) (Δ : KindingCtx) (ι : SKind) :
      EncodeType πstar π Δ (.atom (.all (Kind.ofSKind ι))) []
        (.atom (.all (Kind.ofSKind ι)))
  | ex (π : Polarity) (Δ : KindingCtx) (ι : SKind) :
      EncodeType πstar π Δ (.atom (.ex (Kind.ofSKind ι))) []
        (.atom (.ex (Kind.ofSKind ι)))
  | lam {π : Polarity} {Δ : KindingCtx} {X : TyVar} {ι : SKind}
      {F F' : TypeExpr} {Ψ : SizeCtx} :
      X ∉ Ψ.dom →
      EncodeType πstar π (Δ.extType X .mixed (Kind.ofSKind ι)) F Ψ F' →
      EncodeType πstar π Δ (.lam X ι F) Ψ (.lam X ι F')
  | app {π π' : Polarity} {Δ : KindingCtx} {F F' G G' : TypeExpr}
      {ι ι' : SKind} {Ψ₁ Ψ₂ : SizeCtx} :
      FwKindInfer Δ F (.arr π' ι ι') →
      KindInfer (Δ.extSizes Ψ₁) F' (.arr π' (Kind.ofSKind ι) (Kind.ofSKind ι')) →
      KindCheck ((Δ.extSizes Ψ₂).invScalePol π') G' (Kind.ofSKind ι) →
      EncodeType πstar π Δ F Ψ₁ F' →
      EncodeType πstar (Polarity.comp π' π) (Δ.invScalePol π') G Ψ₂ G' →
      List.Disjoint Ψ₁.dom Ψ₂.dom →
      List.Disjoint Ψ₁.dom G'.allSizeVars →
      List.Disjoint Ψ₂.dom F'.allSizeVars →
      EncodeType πstar π Δ (.app F G) (Ψ₁ ++ Ψ₂) (.app F' G')
  | mu_fresh {π : Polarity} {Δ : KindingCtx}
      {S S' : List (ConsName × TypeExpr)} {Ψ : SizeCtx} {i : SizeVar} :
      π = πstar →
      i ∉ Δ.sizes.dom →
      i ∉ Ψ.dom →
      i ∉ allSizeVarsBranches S' →
      EncodeBranches πstar π Δ S Ψ S' →
      EncodeType πstar π Δ (.mu .infty S) (⟨i, .mixed, .infty⟩ :: Ψ) (.mu (.var i 0) S')
  | mu_inf {π : Polarity} {Δ : KindingCtx}
      {S S' : List (ConsName × TypeExpr)} {Ψ : SizeCtx} :
      π ≠ πstar →
      EncodeBranches πstar π Δ S Ψ S' →
      EncodeType πstar π Δ (.mu .infty S) Ψ (.mu .infty S')
  | nu_fresh {π : Polarity} {Δ : KindingCtx}
      {R R' : List (ProjName × TypeExpr)} {Ψ : SizeCtx} {i : SizeVar} :
      π = Polarity.comp .neg πstar →
      i ∉ Δ.sizes.dom →
      i ∉ Ψ.dom →
      i ∉ allSizeVarsBranches R' →
      EncodeBranches πstar π Δ R Ψ R' →
      EncodeType πstar π Δ (.nu .infty R) (⟨i, .mixed, .infty⟩ :: Ψ) (.nu (.var i 0) R')
  | nu_inf {π : Polarity} {Δ : KindingCtx}
      {R R' : List (ProjName × TypeExpr)} {Ψ : SizeCtx} :
      π ≠ Polarity.comp .neg πstar →
      EncodeBranches πstar π Δ R Ψ R' →
      EncodeType πstar π Δ (.nu .infty R) Ψ (.nu .infty R')

/-- Helper judgment encoding datatype branches `S` or record fields `R` (Section 6.1, p. 42). -/
inductive EncodeBranches (πstar : Polarity) :
    Polarity → KindingCtx → List (Nat × TypeExpr) → SizeCtx → List (Nat × TypeExpr) → Prop where
  | nil (π : Polarity) (Δ : KindingCtx) :
      EncodeBranches πstar π Δ [] [] []
  | cons {π : Polarity} {Δ : KindingCtx} {nm : Nat} {F F' : TypeExpr}
      {rest rest' : List (Nat × TypeExpr)} {Ψ₁ Ψ₂ : SizeCtx} :
      EncodeType πstar π Δ F Ψ₁ F' →
      KindCheck (Δ.extSizes Ψ₁) F' functorKind →
      EncodeBranches πstar π Δ rest Ψ₂ rest' →
      List.Disjoint Ψ₁.dom Ψ₂.dom →
      List.Disjoint Ψ₁.dom (allSizeVarsBranches rest') →
      List.Disjoint Ψ₂.dom F'.allSizeVars →
      EncodeBranches πstar π Δ ((nm, F) :: rest) (Ψ₁ ++ Ψ₂) ((nm, F') :: rest')

end

/-! ## Section 6.2: Pattern and Copattern-Spine Rigid Variable Gathering (pp. 44–47) -/

/-- Rigid-variable gathering in a pattern `Δ₀ ⊢_{SCT} p : A ⇒ Γ; Δ; Ψ; p'`
(Section 6.2, p. 44). -/
inductive InferPat :
    KindingCtx → Pat → TypeExpr → TermCtx → List TyDecl → SizeCtx → Pat → Prop where
  | var (Δ₀ : KindingCtx) (x : TermVar) {A : TypeExpr} :
      KindCheck Δ₀ A .star →
      InferPat Δ₀ (.var x) A [(x, A)] [] [] (.var x)
  | unit (Δ₀ : KindingCtx) :
      InferPat Δ₀ .unit .unitTy [] [] [] .unit
  | pair {Δ₀ : KindingCtx} {p₁ p₂ p₁' p₂' : Pat} {A₁ A₂ : TypeExpr}
      {Γ₁ Γ₂ : TermCtx} {Δ₁ Δ₂ : List TyDecl} {Ψ₁ Ψ₂ : SizeCtx} :
      InferPat Δ₀ p₁ A₁ Γ₁ Δ₁ Ψ₁ p₁' →
      InferPat Δ₀ p₂ A₂ Γ₂ Δ₂ Ψ₂ p₂' →
      List.Disjoint Ψ₁.dom Ψ₂.dom →
      List.Disjoint Ψ₁.dom A₂.allSizeVars →
      InferPat Δ₀ (.pair p₁ p₂) (.prodTy A₁ A₂)
        (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂) (Ψ₁ ++ Ψ₂) (.pair p₁' p₂')
  | cons {Δ₀ : KindingCtx} {c : ConsName} {p p' : Pat} {a : SizeExp}
      {S : List (ConsName × TypeExpr)} {Sc : TypeExpr}
      {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx} (j : SizeVar) :
      TypeExpr.lookupCons S c = some Sc →
      j ∉ Δ₀.sizes.dom →
      j ∉ Ψ.dom →
      j ∉ a.vars →
      j ∉ allSizeVarsBranches S →
      InferPat (Δ₀.extType j .pos (.lt a.boundNorm))
        p (Sc.normApp (.mu (.var j 0) S)) Γ Δ Ψ p' →
      InferPat Δ₀ (.cons c p) (.mu a S)
        Γ (⟨j, .pos, .lt a.boundNorm⟩ :: Δ) (⟨j, .pos, a.boundNorm⟩ :: Ψ)
        (.cons c (.tyPack j p'))
  | tyPack {Δ₀ : KindingCtx} {X : TyVar} {ι : SKind} {p p' : Pat} {F : TypeExpr}
      {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx} :
      KindWf (Δ₀.sizes.invScalePol .mixed) (Kind.ofSKind ι) →
      InferPat (Δ₀.extType X .pos (Kind.ofSKind ι))
        p (F.normApp (.atom (.var X))) Γ Δ Ψ p' →
      InferPat Δ₀ (.tyPack X p) (.exTy (Kind.ofSKind ι) F)
        Γ (⟨X, .pos, Kind.ofSKind ι⟩ :: Δ) Ψ (.tyPack X p')

/-- Rigid-variable gathering in a copattern spine `Δ₀ ⊢_{SCT} q⃗ : A ⇒ C; Γ; Δ; Ψ; q⃗'`
(Section 6.2, p. 45). -/
inductive InferSpine :
    KindingCtx → PatSpine → TypeExpr → TypeExpr → TermCtx → List TyDecl → SizeCtx → PatSpine → Prop where
  | nil (Δ₀ : KindingCtx) (A : TypeExpr) :
      InferSpine Δ₀ [] A A [] [] [] []
  | pat {Δ₀ : KindingCtx} {p p' : Pat} {qs qs' : PatSpine} {A B C : TypeExpr}
      {Γ₁ Γ₂ : TermCtx} {Δ₁ Δ₂ : List TyDecl} {Ψ₁ Ψ₂ : SizeCtx} :
      InferPat Δ₀ p A Γ₁ Δ₁ Ψ₁ p' →
      InferSpine Δ₀ qs B C Γ₂ Δ₂ Ψ₂ qs' →
      List.Disjoint Ψ₁.dom Ψ₂.dom →
      List.Disjoint Ψ₁.dom B.allSizeVars →
      InferSpine Δ₀ (.pat p :: qs) (.arrTy A B) C
        (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂) (Ψ₁ ++ Ψ₂) (.pat p' :: qs')
  | proj {Δ₀ : KindingCtx} {d : ProjName} {qs qs' : PatSpine} {a : SizeExp}
      {R : List (ProjName × TypeExpr)} {Rd C : TypeExpr}
      {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx} (j : SizeVar) :
      TypeExpr.lookupProj R d = some Rd →
      j ∉ Δ₀.sizes.dom →
      j ∉ Ψ.dom →
      j ∉ a.vars →
      j ∉ allSizeVarsBranches R →
      InferSpine (Δ₀.extType j .pos (.lt a.boundNorm))
        qs (Rd.normApp (.nu (.var j 0) R)) C Γ Δ Ψ qs' →
      InferSpine Δ₀ (.proj d :: qs) (.nu a R) C
        Γ (⟨j, .pos, .lt a.boundNorm⟩ :: Δ) (⟨j, .pos, a.boundNorm⟩ :: Ψ)
        (.proj d :: .tyVar j :: qs')
  | tyApp {Δ₀ : KindingCtx} {X : TyVar} {ι : SKind} {qs qs' : PatSpine}
      {F C : TypeExpr} {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx} :
      KindWf (Δ₀.sizes.invScalePol .mixed) (Kind.ofSKind ι) →
      InferSpine (Δ₀.extType X .pos (Kind.ofSKind ι))
        qs (F.normApp (.atom (.var X))) C Γ Δ Ψ qs' →
      InferSpine Δ₀ (.tyVar X :: qs) (.allTy (Kind.ofSKind ι) F) C
        Γ (⟨X, .pos, Kind.ofSKind ι⟩ :: Δ) Ψ (.tyVar X :: qs')

/-- Classification of rigid-variable polarities in a pattern (Lemma 4, pp. 45–46):
for a size variable `i ∈ Ψ`, either:
1. `∃ (x, B) ∈ Γ` such that `μ^i` occurs positively in `B` (and nowhere negatively),
2. `∃ (x, B) ∈ Γ` such that `ν^i` occurs negatively in `B` (and nowhere positively), or
3. `i` does not occur in `B` for any `(x, B) ∈ Γ`. -/
def PatRigidVarClass (Δ : KindingCtx) (Γ : TermCtx) (i : SizeVar) : Prop :=
  ((∃ p ∈ Γ, SizeOccursFixPol Δ .mu i .pos p.2) ∧
    ¬ (∃ p ∈ Γ, SizeOccursFixPol Δ .nu i .neg p.2) ∧
    (∃ p ∈ Γ, SizeOccursIn i p.2)) ∨
  (¬ (∃ p ∈ Γ, SizeOccursFixPol Δ .mu i .pos p.2) ∧
    (∃ p ∈ Γ, SizeOccursFixPol Δ .nu i .neg p.2) ∧
    (∃ p ∈ Γ, SizeOccursIn i p.2)) ∨
  (¬ (∃ p ∈ Γ, SizeOccursFixPol Δ .mu i .pos p.2) ∧
    ¬ (∃ p ∈ Γ, SizeOccursFixPol Δ .nu i .neg p.2) ∧
    ¬ (∃ p ∈ Γ, SizeOccursIn i p.2))

/-- Classification of rigid-variable polarities in a copattern spine (Lemma 5, pp. 46–47):
for a size variable `i ∈ Ψ₁ ++ Ψ₂`, exactly one of the four statements holds:
1. `∃ (x, B) ∈ Γ` such that `μ^i` occurs positively in `B`
2. `μ^i` occurs negatively in `A''`
3. `(∃ (x, B) ∈ Γ, ν^i occurs negatively in B) ∨ (ν^i occurs positively in A'')`
4. `i` does not occur in `A''` and does not occur in `B` for any `(x, B) ∈ Γ`. -/
def SpineRigidVarClass (Δ : KindingCtx) (Γ : TermCtx) (A'' : TypeExpr) (i : SizeVar) : Prop :=
  let c1 := ∃ p ∈ Γ, SizeOccursFixPol Δ .mu i .pos p.2
  let c2 := SizeOccursFixPol Δ .mu i .neg A''
  let c3 := (∃ p ∈ Γ, SizeOccursFixPol Δ .nu i .neg p.2) ∨ SizeOccursFixPol Δ .nu i .pos A''
  let c4 := ¬ SizeOccursIn i A'' ∧ ¬ ∃ p ∈ Γ, SizeOccursIn i p.2
  (c1 ∧ ¬ c2 ∧ ¬ c3 ∧ ¬ c4) ∨
  (¬ c1 ∧ c2 ∧ ¬ c3 ∧ ¬ c4) ∨
  (¬ c1 ∧ ¬ c2 ∧ c3 ∧ ¬ c4) ∨
  (¬ c1 ∧ ¬ c2 ∧ ¬ c3 ∧ c4)

mutual

/-- Collect all inductive branch lists `S` occurring in `.mu a S` subterms of a `TypeExpr`. -/
def TypeExpr.allMuBranchLists : TypeExpr → List (List (ConsName × TypeExpr))
  | .atom _ => []
  | .lam _ _ body => body.allMuBranchLists
  | .app F G => F.allMuBranchLists ++ G.allMuBranchLists
  | .mu _ S => S :: allMuBranchListsInBranches S
  | .nu _ R => allMuBranchListsInBranches R

/-- Helper: collect inductive branch lists across a list of named branches/fields. -/
def allMuBranchListsInBranches : List (Nat × TypeExpr) → List (List (ConsName × TypeExpr))
  | [] => []
  | (_, F) :: rest => F.allMuBranchLists ++ allMuBranchListsInBranches rest

end

mutual

/-- Collect all coinductive field lists `R` occurring in `.nu a R` subterms of a `TypeExpr`. -/
def TypeExpr.allNuFieldLists : TypeExpr → List (List (ProjName × TypeExpr))
  | .atom _ => []
  | .lam _ _ body => body.allNuFieldLists
  | .app F G => F.allNuFieldLists ++ G.allNuFieldLists
  | .mu _ S => allNuFieldListsInBranches S
  | .nu _ R => R :: allNuFieldListsInBranches R

/-- Helper: collect coinductive field lists across a list of named branches/fields. -/
def allNuFieldListsInBranches : List (Nat × TypeExpr) → List (List (ProjName × TypeExpr))
  | [] => []
  | (_, F) :: rest => F.allNuFieldLists ++ allNuFieldListsInBranches rest

end

/-- Positive fixpoint-polarity separation on a domain/pattern type `A` in `Δ`:
every size variable `i` occurring in `A` occurs either at `(μ, +)` (and not `(ν, -)`)
or at `(ν, -)` (and not `(μ, +)`). -/
def PosFixpointPolClean (Δ : KindingCtx) (A : TypeExpr) : Prop :=
  ∀ i : SizeVar,
    SizeOccursIn i A →
    (SizeOccursFixPol Δ .mu i .pos A ∧ ¬ SizeOccursFixPol Δ .nu i .neg A) ∨
    (SizeOccursFixPol Δ .nu i .neg A ∧ ¬ SizeOccursFixPol Δ .mu i .pos A)

/-- Negative fixpoint-polarity separation on a signature/clause type `A` in `Δ`:
every size variable `i` occurring in `A` occurs either at `(μ, -)` (and not `(ν, +)`)
or at `(ν, +)` (and not `(μ, -)`). -/
def NegFixpointPolClean (Δ : KindingCtx) (A : TypeExpr) : Prop :=
  ∀ i : SizeVar,
    SizeOccursIn i A →
    (SizeOccursFixPol Δ .mu i .neg A ∧ ¬ SizeOccursFixPol Δ .nu i .pos A) ∨
    (SizeOccursFixPol Δ .nu i .pos A ∧ ¬ SizeOccursFixPol Δ .mu i .neg A)

/-- Strict positivity and polarity hygiene of a size-annotated pattern type `A₀` in context `Δ₀`
(Section 6.2, Lemma 4, pp. 45–46):
1. `PosFixpointPolClean Δ₀ A₀` holds;
2. For every inductive branch list `S ∈ A₀.allMuBranchLists`, every constructor `(c, Sc)` in `S`,
   and every fresh size variable `j`, the unrolled constructor domain `B = Sc.normApp (.mu (.var j 0) S)`
   satisfies `PosFixpointPolClean`, and if `j` occurs in `B`, `j` occurs at `(μ, +)` and not `(ν, -)`. -/
def PositiveFixpointHygiene (Δ₀ : KindingCtx) (A₀ : TypeExpr) : Prop :=
  PosFixpointPolClean Δ₀ A₀ ∧
  ∀ S ∈ A₀.allMuBranchLists, ∀ (c : ConsName) (Sc : TypeExpr) (j : SizeVar),
    TypeExpr.lookupCons S c = some Sc →
    j ∉ Δ₀.sizes.dom →
    j ∉ allSizeVarsBranches S →
    let Δj := Δ₀.extType j .pos (.lt .infty)
    let B := Sc.normApp (.mu (.var j 0) S)
    PosFixpointPolClean Δj B ∧
    (SizeOccursIn j B →
      SizeOccursFixPol Δj .mu j .pos B ∧ ¬ SizeOccursFixPol Δj .nu j .neg B)

/-- Polarity and fixpoint-functor hygiene of a size-annotated signature/spine type `A₀` in context
`Δ₀` (Section 6.2, Lemma 5, pp. 46–47):
1. `NegFixpointPolClean Δ₀ A₀` holds;
2. Every inductive branch list `S ∈ A₀.allMuBranchLists` has positive constructor functors;
3. Every coinductive field list `R ∈ A₀.allNuFieldLists` has positive destructor functors. -/
def SignatureFixpointHygiene (Δ₀ : KindingCtx) (A₀ : TypeExpr) : Prop :=
  NegFixpointPolClean Δ₀ A₀ ∧
  (∀ S ∈ A₀.allMuBranchLists, ∀ (c : ConsName) (Sc : TypeExpr) (j : SizeVar),
    TypeExpr.lookupCons S c = some Sc →
    j ∉ Δ₀.sizes.dom →
    j ∉ allSizeVarsBranches S →
    let Δj := Δ₀.extType j .pos (.lt .infty)
    let B := Sc.normApp (.mu (.var j 0) S)
    PosFixpointPolClean Δj B ∧
    (SizeOccursIn j B →
      SizeOccursFixPol Δj .mu j .pos B ∧ ¬ SizeOccursFixPol Δj .nu j .neg B)) ∧
  (∀ R ∈ A₀.allNuFieldLists, ∀ (d : ProjName) (Rd : TypeExpr) (j : SizeVar),
    TypeExpr.lookupProj R d = some Rd →
    j ∉ Δ₀.sizes.dom →
    j ∉ allSizeVarsBranches R →
    let Δj := Δ₀.extType j .pos (.lt .infty)
    let B := Rd.normApp (.nu (.var j 0) R)
    NegFixpointPolClean Δj B ∧
    (SizeOccursIn j B →
      SizeOccursFixPol Δj .nu j .pos B ∧ ¬ SizeOccursFixPol Δj .mu j .neg B))

/-! ## Section 6.3: Call-Site Inference, Checking, and Type Comparison (pp. 48–56) -/

/-- Polarized size variable context `Φ ⊂ SizeVar × Polarity` tracking flexible (and rigid)
size variables together with their fixpoint polarities (`+` for `μ`, `−` for `ν`, `◦` for mixed)
(Section 6.3, p. 48). -/
abbrev FlexVars := List (SizeVar × Polarity)

namespace FlexVars

/-- Domain of size variables in `Φ`. -/
def dom (Φ : FlexVars) : List SizeVar :=
  Φ.map (·.1)

/-- Lookup the polarity `π` associated with a size variable `i` in `Φ`. -/
def lookupPol (Φ : FlexVars) (i : SizeVar) : Option Polarity :=
  (Φ.find? (fun p => p.1 == i)).map (·.2)

/-- Lookup the polarity of a size expression `a` in `Φ ∪ {(∞, defaultInfPol)}`
(Section 6.3.3, p. 51). -/
def lookupSizePol (Φ : FlexVars) (defaultInfPol : Polarity) (a : SizeExp) : Option Polarity :=
  match a with
  | .inf _ => some defaultInfPol
  | .meet ⟨⟨i, 0⟩, []⟩ => Φ.lookupPol i
  | _ => none

end FlexVars

/-- Information-order join `max(π₁, π₂)` on `{◦, +, −}` used in fixpoint size comparison
(Section 6.3.3, p. 51 & Theorem 10 proof, p. 52: `max(π₁, +) = +` for `π₁ ∈ {◦, +}`, and
`max(π₁, −) = −` for `π₁ ∈ {◦, −}`). -/
def Polarity.infoMax : Polarity → Polarity → Polarity
  | .mixed, π => π
  | π, .mixed => π
  | .pos, .pos => .pos
  | .neg, .neg => .neg
  | _, _ => .top

/-- A size constraint `(lhs R rhs) ∈ C` where `R ∈ {<, ≤}` (Section 6.3, p. 48). -/
structure SizeConstraint where
  lhs : SizeExp
  rel : EdgeRel
  rhs : SizeExp
  deriving DecidableEq, Repr

namespace SizeConstraint

/-- Generate the constraint(s) corresponding to polarized comparison `a ≤^π b`
(Section 4.1.3, p. 22 & Section 6.3.3, p. 51):
- `a ≤^+ b` produces `[a ≤ b]`
- `a ≤^− b` produces `[b ≤ a]`
- `a ≤^◦ b` produces `[a ≤ b, b ≤ a]`
- `a ≤^⊤ b` produces `[]`. -/
def ofPol (π : Polarity) (a b : SizeExp) : List SizeConstraint :=
  match π with
  | .pos => [⟨a, .le, b⟩]
  | .neg => [⟨b, .le, a⟩]
  | .mixed => [⟨a, .le, b⟩, ⟨b, .le, a⟩]
  | .top => []

/-- Check whether size variable `i` appears on the LHS or RHS of a constraint `c`. -/
def mentions (c : SizeConstraint) (i : SizeVar) : Bool :=
  c.lhs.vars.contains i || c.rhs.vars.contains i

end SizeConstraint

/-- Comparison inputs must be kindable at a refined kind with the expected
simple-kind shape. This is an explicit formalization of the source's stated
input-domain assumption for comparing size-annotated types. -/
def CompareKinded (Δ : KindingCtx) (ι : SKind) (F : TypeExpr) : Prop :=
  ∃ κ : Kind, simpleKindShape ι = refinedKindShape κ ∧ KindCheck Δ F κ

/-- Size-variable names appearing in kind bounds, including nested arrows. -/
def comparisonKindNames : Kind → List Nat
  | .star => []
  | .lt a => a.vars
  | .arr _ a b => comparisonKindNames a ++ comparisonKindNames b

mutual

/-- Conservative name support, including lambda binders as well as type and
size-variable occurrences. Used to pick a fresh extensional comparison variable. -/
def comparisonTypeNames : TypeExpr → List Nat
  | .atom (.var x) => [x]
  | .atom (.size a) => a.vars
  | .atom (.all κ) | .atom (.ex κ) => comparisonKindNames κ
  | .atom _ => []
  | .lam x _ body => x :: comparisonTypeNames body
  | .app f g => comparisonTypeNames f ++ comparisonTypeNames g
  | .mu a branches | .nu a branches => a.vars ++ comparisonBranchNames branches

def comparisonBranchNames : List (Nat × TypeExpr) → List Nat
  | [] => []
  | (_, f) :: rest => comparisonTypeNames f ++ comparisonBranchNames rest

end

/-- Freshness includes both operands, the flexible size variables, and every
declared type/size variable and kind-bound name in the surrounding context. -/
def CompareFresh (X : TyVar) (Δ : KindingCtx) (Φ : FlexVars) (F F' : TypeExpr) : Prop :=
  X ∉ comparisonTypeNames F ∧ X ∉ comparisonTypeNames F' ∧
  X ∉ Φ.dom ∧ X ∉ Δ.sizes.dom ∧
  (∀ d ∈ Δ.sizes, X ∉ d.bound.vars) ∧
  X ∉ (Δ.types.map TyDecl.var) ∧
  (∀ d ∈ Δ.types, X ∉ comparisonKindNames d.kind)

mutual

/-- Polarized type comparison `Φ; Δ; ι ⊢_{SCT} A ≤^π B ⇒ C` generating size constraints `C`
(Section 6.3.3, pp. 50–52). -/
inductive CompareTypes (Φ : FlexVars) :
    KindingCtx → SKind → Polarity → TypeExpr → TypeExpr → List SizeConstraint → Prop where
  | atom (Δ : KindingCtx) (ι : SKind) (π : Polarity) (K : TyAtom) :
      CompareTypes Φ Δ ι π (.atom K) (.atom K) []
  | app {Δ : KindingCtx} {π₁ π : Polarity} {ι₁ ι₂ : SKind}
      {F F' G G' : TypeExpr} {C₁ C₂ : List SizeConstraint} :
      KindInfer Δ F' (.arr π₁ (Kind.ofSKind ι₁) (Kind.ofSKind ι₂)) →
      CompareTypes Φ Δ (.arr π₁ ι₁ ι₂) π F F' C₁ →
      CompareTypes Φ (Δ.invScalePol π₁) ι₁ (Polarity.comp π₁ π) G G' C₂ →
      CompareTypes Φ Δ ι₂ π (.app F G) (.app F' G') (C₁ ++ C₂)
  | lam {Δ : KindingCtx} {π₁ π : Polarity} {ι₁ ι₂ : SKind}
      {F F' : TypeExpr} {X : TyVar} {C : List SizeConstraint} :
      CompareFresh X Δ Φ F F' →
      CompareKinded Δ (.arr π₁ ι₁ ι₂) F →
      CompareKinded Δ (.arr π₁ ι₁ ι₂) F' →
      CompareTypes Φ (Δ.extType X π₁ (Kind.ofSKind ι₁)) ι₂ π
        (F.normApp (.atom (.var X))) (F'.normApp (.atom (.var X))) C →
      CompareTypes Φ Δ (.arr π₁ ι₁ ι₂) π F F' C
  | mu {Δ : KindingCtx} {π π₁ π₂ : Polarity} {a b : SizeExp}
      {S S' : List (ConsName × TypeExpr)} {C : List SizeConstraint} :
      Φ.lookupSizePol .pos a = some π₁ →
      Φ.lookupSizePol .pos b = some π₂ →
      CompareBranches Φ Δ π S S' C →
      CompareTypes Φ Δ .star π (.mu a S) (.mu b S')
        (SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax π₁ π₂) π) a b ++ C)
  | nu {Δ : KindingCtx} {π π₁ π₂ : Polarity} {a b : SizeExp}
      {R R' : List (ProjName × TypeExpr)} {C : List SizeConstraint} :
      Φ.lookupSizePol .neg a = some π₁ →
      Φ.lookupSizePol .neg b = some π₂ →
      CompareBranches Φ Δ π R R' C →
      CompareTypes Φ Δ .star π (.nu a R) (.nu b R')
        (SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax π₁ π₂) π) a b ++ C)

/-- Helper judgment comparing datatype branches `S ≤^π S'` or record fields `R ≤^π R'`
(Section 6.3.3, p. 51). -/
inductive CompareBranches (Φ : FlexVars) :
    KindingCtx → Polarity → List (Nat × TypeExpr) → List (Nat × TypeExpr) → List SizeConstraint → Prop where
  | nil (Δ : KindingCtx) (π : Polarity) :
      CompareBranches Φ Δ π [] [] []
  | cons {Δ : KindingCtx} {π : Polarity} {nm : Nat} {F F' : TypeExpr}
      {rest rest' : List (Nat × TypeExpr)} {C₁ C₂ : List SizeConstraint} :
      CompareTypes Φ Δ fwFunctorSKind π F F' C₁ →
      CompareBranches Φ Δ π rest rest' C₂ →
      CompareBranches Φ Δ π ((nm, F) :: rest) ((nm, F') :: rest') (C₁ ++ C₂)

end

/-- Well-formed polarity assignment in `Φ` (Section 6.3.4, Theorem 10, pp. 51–52):
variables generated for least fixpoints (`μ`) have polarity `+` or `◦`, and variables
generated for greatest fixpoints (`ν`) have polarity `−` or `◦`. -/
def FlexPolHygiene (Φ : FlexVars) (Δ : KindingCtx) (A C : TypeExpr) : Prop :=
  (∀ i π₁, Φ.lookupSizePol .pos (.var i 0) = some π₁ →
    (SizeOccursFixPol Δ .mu i .pos A ∨ SizeOccursFixPol Δ .mu i .neg A ∨
     SizeOccursFixPol Δ .mu i .pos C ∨ SizeOccursFixPol Δ .mu i .neg C) →
    π₁ = .pos ∨ π₁ = .mixed) ∧
  (∀ i π₁, Φ.lookupSizePol .neg (.var i 0) = some π₁ →
    (SizeOccursFixPol Δ .nu i .pos A ∨ SizeOccursFixPol Δ .nu i .neg A ∨
     SizeOccursFixPol Δ .nu i .pos C ∨ SizeOccursFixPol Δ .nu i .neg C) →
    π₁ = .neg ∨ π₁ = .mixed)

/-- Context trivialization `Φ ⊢_↓ Ψ₁ ⇒ Ψ₂` (Section 6.3.2, p. 50):
replaces any bound `< i` in `Ψ₁` whose variable `i` belongs to `Φ` with `< ∞`, so that
the resulting context `Ψ₂` satisfies the consistent extension check `Δ ⊢ ∃Δ'`. -/
def trivializeCtx (Φ : FlexVars) (Ψ₁ : SizeCtx) : SizeCtx :=
  Ψ₁.map fun d =>
    match d.bound with
    | .meet ⟨⟨a, 0⟩, []⟩ =>
        if Φ.dom.contains a then { d with bound := .infty } else d
    | _ => d

/-- Relational form of context trivialization `Φ ⊢_↓ Ψ₁ ⇒ Ψ₂` (Section 6.3.2, p. 50). -/
def TrivializeCtx (Φ : FlexVars) (Ψ₁ Ψ₂ : SizeCtx) : Prop :=
  Ψ₂ = trivializeCtx Φ Ψ₁

mutual

/-- Call-site inference judgment `Φ; Γ; Δ ⊢_{SCT} t ⇒ A; Φ'; C; T; t'`
(Section 6.3.1, pp. 48–50). -/
inductive InferTerm (sig : GlobalSig) (Ξ : MutualBlock) :
    FlexVars → TermCtx → KindingCtx → Term →
    TypeExpr → FlexVars → List SizeConstraint → List SizeVar → Term → Prop where
  | var {Φ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx} {x : TermVar} {A : TypeExpr} :
      (x, A) ∈ Γ →
      InferTerm sig Ξ Φ Γ Δ (.var x) A Φ [] [] (.var x)
  | appTerm {Φ Φ₁ Φ₂ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {r r' s s' : Term} {A B : TypeExpr}
      {C₁ C₂ : List SizeConstraint} {T₁ T₂ : List SizeVar} :
      InferTerm sig Ξ Φ Γ Δ r (.arrTy A B) Φ₁ C₁ T₁ r' →
      CheckTerm sig Ξ Φ₁ Γ Δ A s Φ₂ C₂ T₂ s' →
      InferTerm sig Ξ Φ Γ Δ (.app r (.term s)) B Φ₂ (C₁ ++ C₂) (T₁ ++ T₂) (.app r' (.term s'))
  | proj {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {r r' : Term} {a : SizeExp} {R : List (ProjName × TypeExpr)}
      {d : ProjName} {Rd : TypeExpr}
      {C : List SizeConstraint} {T T' : List SizeVar} (j : SizeVar) :
      InferTerm sig Ξ Φ Γ Δ r (.nu a R) Φ' C T r' →
      TypeExpr.lookupProj R d = some Rd →
      j ∉ Φ'.dom →
      j ∉ Δ.sizes.dom →
      T' = (if j ∈ (Rd.normApp (.nu (.var j 0) R)).allSizeVars then T else j :: T) →
      InferTerm sig Ξ Φ Γ Δ (.app r (.proj d none))
        (Rd.normApp (.nu (.var j 0) R))
        ((j, .neg) :: Φ') (⟨.var j 0, .lt, a⟩ :: C) T'
        (.app r' (.proj d (some (.var j 0))))
  | appTy {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {r r' : Term} {G G' F : TypeExpr} {ι : SKind} {Ψ : SizeCtx}
      {C : List SizeConstraint} {T : List SizeVar} :
      EncodeType .mixed .mixed Δ G Ψ G' →
      List.Disjoint Ψ.dom Φ'.dom →
      InferTerm sig Ξ Φ Γ Δ r (.allTy (Kind.ofSKind ι) F) Φ' C T r' →
      InferTerm sig Ξ Φ Γ Δ (.app r (.tyArg G))
        (F.normApp G')
        (Ψ.map (fun d => (d.var, .mixed)) ++ Φ') C T
        (.app r' (.tyArg G'))
  | ascr {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {t t' : Term} {A A' : TypeExpr} {Ψ : SizeCtx}
      {C : List SizeConstraint} {T : List SizeVar} :
      EncodeType .mixed .mixed Δ A Ψ A' →
      List.Disjoint Ψ.dom Φ'.dom →
      CheckTerm sig Ξ Φ Γ Δ A' t Φ' C T t' →
      InferTerm sig Ξ Φ Γ Δ (.ascr t A) A'
        (Ψ.map (fun d => (d.var, .mixed)) ++ Φ') C T
        (.ascr t' A')
  | funCall {Φ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {decl : FunDecl} {flexVars : List (SizeVar × Polarity)} {as : List SizeExp} :
      decl ∈ sig ++ Ξ →
      flexVars.length = decl.sizeParams.length →
      flexVars.Nodup →
      List.Disjoint (flexVars.map (·.1)) Φ.dom →
      List.Disjoint (flexVars.map (·.1)) Δ.sizes.dom →
      (∀ p ∈ decl.sizeParams.zip flexVars,
        (SizeOccursFixPol (Δ.extSizes decl.sizeParams) .mu p.1.var .neg decl.ty → p.2.2 = .pos) ∧
        (SizeOccursFixPol (Δ.extSizes decl.sizeParams) .nu p.1.var .pos decl.ty → p.2.2 = .neg) ∧
        (p.2.2 = .pos ∨ p.2.2 = .neg ∨ p.2.2 = .mixed)) →
      as = flexVars.map (fun p => SizeExp.var p.1 0) →
      InferTerm sig Ξ Φ Γ Δ (.funRef decl.name [])
        (decl.ty.substSizes (decl.sizeParams.dom.zip as))
        (flexVars ++ Φ) [] []
        (.funRef decl.name as)

/-- Call-site checking judgment `Φ; Γ; Δ | A ⊢_{SCT} t ⇒ Φ'; C; T; t'`
(Section 6.3.2, pp. 50–51). -/
inductive CheckTerm (sig : GlobalSig) (Ξ : MutualBlock) :
    FlexVars → TermCtx → KindingCtx → TypeExpr → Term →
    FlexVars → List SizeConstraint → List SizeVar → Term → Prop where
  | unit (Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) :
      CheckTerm sig Ξ Φ Γ Δ .unitTy .unit Φ [] [] .unit
  | pair {Φ Φ₁ Φ₂ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {A₁ A₂ : TypeExpr} {t₁ t₁' t₂ t₂' : Term}
      {C₁ C₂ : List SizeConstraint} {T₁ T₂ : List SizeVar} :
      CheckTerm sig Ξ Φ Γ Δ A₁ t₁ Φ₁ C₁ T₁ t₁' →
      CheckTerm sig Ξ Φ₁ Γ Δ A₂ t₂ Φ₂ C₂ T₂ t₂' →
      CheckTerm sig Ξ Φ Γ Δ (.prodTy A₁ A₂) (.pair t₁ t₂)
        Φ₂ (C₁ ++ C₂) (T₁ ++ T₂) (.pair t₁' t₂')
  | lamClauses {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {A : TypeExpr} {Ds Ds' : List Clause}
      {C : List SizeConstraint} {T : List SizeVar} :
      CheckClausesInfer sig Ξ Φ Γ Δ A Ds Φ' C T Ds' →
      CheckTerm sig Ξ Φ Γ Δ A (.lamClauses Ds) Φ' C T (.lamClauses Ds')
  | cons {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {c : ConsName} {a : SizeExp} {S : List (ConsName × TypeExpr)} {Sc : TypeExpr}
      {t t' : Term} {C : List SizeConstraint} {T T' : List SizeVar} (j : SizeVar) :
      TypeExpr.lookupCons S c = some Sc →
      j ∉ Φ.dom →
      j ∉ Δ.sizes.dom →
      CheckTerm sig Ξ ((j, .pos) :: Φ) Γ Δ (Sc.normApp (.mu (.var j 0) S)) t Φ' C T t' →
      T' = (if j ∈ (Sc.normApp (.mu (.var j 0) S)).allSizeVars then T else j :: T) →
      CheckTerm sig Ξ Φ Γ Δ (.mu a S) (.cons c none t)
        Φ' (⟨.var j 0, .lt, a⟩ :: C) T' (.cons c (some (.var j 0)) t')
  | pack {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {ι : SKind} {F G G' : TypeExpr} {Ψ : SizeCtx} {t t' : Term}
      {C : List SizeConstraint} {T : List SizeVar} :
      EncodeType .mixed .mixed Δ G Ψ G' →
      List.Disjoint Ψ.dom Φ.dom →
      CheckTerm sig Ξ (Ψ.map (fun d => (d.var, .mixed)) ++ Φ) Γ Δ (F.normApp G') t Φ' C T t' →
      CheckTerm sig Ξ Φ Γ Δ (.exTy (Kind.ofSKind ι) F) (.pack G t) Φ' C T (.pack G' t')
  | sub {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {A Cty : TypeExpr} {r r' : Term}
      {C₁ C₂ : List SizeConstraint} {T : List SizeVar} :
      InferTerm sig Ξ Φ Γ Δ r A Φ' C₁ T r' →
      FlexPolHygiene Φ' Δ A Cty →
      CompareTypes Φ' Δ .star .pos A Cty C₂ →
      CheckTerm sig Ξ Φ Γ Δ Cty r Φ' (C₁ ++ C₂) T r'

/-- Single-clause checking with constraint generation
`Φ; Γ; Δ | C ⊢_{SCT} {q⃗ → t} ⇒ Φ'; C_out; T; {q⃗' → t'}` (Section 6.3.2, p. 51). -/
inductive CheckClauseInfer (sig : GlobalSig) (Ξ : MutualBlock) :
    FlexVars → TermCtx → KindingCtx → TypeExpr → Clause →
    FlexVars → List SizeConstraint → List SizeVar → Clause → Prop where
  | mk {Φ Φ' : FlexVars} {Γ Γ' : TermCtx} {Δ : KindingCtx} {Δ' : List TyDecl}
      {Ψ Ψ' : SizeCtx} {C C' : TypeExpr} {qs qs' : PatSpine} {t t' : Term}
      {Cs : List SizeConstraint} {T : List SizeVar} :
      InferSpine Δ qs C C' Γ' Δ' Ψ qs' →
      Ψ' = trivializeCtx Φ Ψ →
      CheckTerm sig Ξ (Ψ'.map (fun d => (d.var, d.pol)) ++ Φ)
        (Γ ++ Γ') (Δ.append ⟨Ψ', Δ'⟩) C' t Φ' Cs T t' →
      CheckClauseInfer sig Ξ Φ Γ Δ C (.mk qs t) Φ' Cs T (.mk qs' t')

/-- Multi-clause checking with constraint generation
`Φ; Γ; Δ | C ⊢_{SCT} D⃗ ⇒ Φ'; C_out; T; D⃗'` (Section 6.3.2, p. 51). -/
inductive CheckClausesInfer (sig : GlobalSig) (Ξ : MutualBlock) :
    FlexVars → TermCtx → KindingCtx → TypeExpr → List Clause →
    FlexVars → List SizeConstraint → List SizeVar → List Clause → Prop where
  | nil (Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (C : TypeExpr) :
      CheckClausesInfer sig Ξ Φ Γ Δ C [] Φ [] [] []
  | cons {Φ Φ₁ Φ₂ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx} {C : TypeExpr}
      {D D' : Clause} {Ds Ds' : List Clause}
      {C₁ C₂ : List SizeConstraint} {T₁ T₂ : List SizeVar} :
      CheckClauseInfer sig Ξ Φ Γ Δ C D Φ₁ C₁ T₁ D' →
      CheckClausesInfer sig Ξ Φ₁ Γ Δ C Ds Φ₂ C₂ T₂ Ds' →
      CheckClausesInfer sig Ξ Φ Γ Δ C (D :: Ds) Φ₂ (C₁ ++ C₂) (T₁ ++ T₂) (D' :: Ds')

end

/-- Hypotheses of Theorem 11 (Nature of rigid variables, Section 6.3.4, pp. 53–54)
for a set `X : List SizeVar` of rigid variables of polarity `π ∈ {+, −}`:
1. every `i ∈ X` is recorded in `Φ₀` with polarity `π` (`(i, π) ∈ Φ₀`);
2. for every `(x, Bₖ) ∈ Γ`, either `Δ ⊢ (fk, i) ∈_π Bₖ` or `i` does not occur in `Bₖ`;
3. for the checked type `A`, either `Δ ⊢ (fk, i) ∈_{−π} A` or `i` does not occur in `A`;
4. if `π = +`, all occurrences of `i` in `Γ` and `A` have `fk = .mu`; if `π = −`, all have `fk = .nu`. -/
def RigidVarHypotheses (π : Polarity) (X : List SizeVar) (Φ₀ : FlexVars)
    (Γ : TermCtx) (Δ : KindingCtx) (A : TypeExpr) : Prop :=
  (π = .pos ∨ π = .neg) ∧
  let fk : FixKind := if π == .pos then .mu else .nu
  ∀ i ∈ X,
    Φ₀.lookupPol i = some π ∧
    (∀ p ∈ Γ, SizeOccursFixPol Δ fk i π p.2 ∨ ¬ SizeOccursIn i p.2) ∧
    (SizeOccursFixPol Δ fk i (Polarity.comp .neg π) A ∨ ¬ SizeOccursIn i A)

/-! ## Sections 6.4–6.5: Constraint Solving (Algorithm 1) & Termination Checker (Algorithm 2) (pp. 56–60) -/

/-- Flexible substitution `φ : SizeVar → SizeExp` mapping flexible variables to size expressions
over a rigid context `Ψ` (Section 6.4, p. 56). -/
abbrev FlexSubst := SizeVar → SizeExp

/-- Apply a flexible substitution `φ` to a `SizeExp` (`φ(a)`). -/
def SizeExp.applyFlex (φ : FlexSubst) (a : SizeExp) : SizeExp :=
  a.subst (a.vars.map (fun k => (k, φ k)))

mutual

/-- Functorial extension `φ(t)` of a flexible substitution `φ` to a term `t`
(Section 6.4, p. 56). -/
def Term.applyFlex (φ : FlexSubst) : Term → Term
  | .var x => .var x
  | .funRef f as => .funRef f (as.map (·.applyFlex φ))
  | .app r e => .app (r.applyFlex φ) (e.applyFlex φ)
  | .unit => .unit
  | .pair t₁ t₂ => .pair (t₁.applyFlex φ) (t₂.applyFlex φ)
  | .cons c ma t => .cons c (ma.map (·.applyFlex φ)) (t.applyFlex φ)
  | .pack G t => .pack (G.substSizes (G.allSizeVars.map (fun k => (k, φ k)))) (t.applyFlex φ)
  | .lamClauses Ds => .lamClauses (applyFlexClauses φ Ds)
  | .ascr t A => .ascr (t.applyFlex φ) (A.substSizes (A.allSizeVars.map (fun k => (k, φ k))))

/-- Functorial extension `φ(e)` of `φ` to an elimination `e`. -/
def Elim.applyFlex (φ : FlexSubst) : Elim → Elim
  | .term t => .term (t.applyFlex φ)
  | .tyArg G => .tyArg (G.substSizes (G.allSizeVars.map (fun k => (k, φ k))))
  | .proj d ma => .proj d (ma.map (·.applyFlex φ))

/-- Functorial extension `φ(D)` of `φ` to a clause `D`. -/
def Clause.applyFlex (φ : FlexSubst) : Clause → Clause
  | .mk qs t => .mk qs (t.applyFlex φ)

/-- Helper: functorial extension `φ(D⃗)` across a list of clauses. -/
def applyFlexClauses (φ : FlexSubst) : List Clause → List Clause
  | [] => []
  | D :: rest => D.applyFlex φ :: applyFlexClauses φ rest

end

/-- Well-formedness of a flexible substitution `φ : Φ \ Ψ → {a | Ψ ⊢ a}` (Section 6.4, p. 56):
`φ` leaves every rigid variable `i ∈ Ψ.dom` fixed (`φ(i) = .var i 0`) and maps every variable `k`
to a size expression well-formed in `Ψ` (`Ψ ⊢ φ(k)`). -/
def ValidFlexSubst (Ψ : SizeCtx) (φ : FlexSubst) : Prop :=
  (∀ i ∈ Ψ.dom, φ i = .var i 0) ∧
  (∀ k : SizeVar, SizeWf Ψ (φ k))

/-- Coherence of a flexible substitution `Ψ; C ⊢ φ` with respect to a constraint set `C`
(Section 6.4, p. 56):
`φ` is a valid flexible substitution over `Ψ`, and for every `(lhs R rhs) ∈ C`,
`Ψ ⊢ φ(lhs) R φ(rhs)^↑`. -/
def CoherentSubst (Ψ : SizeCtx) (C : List SizeConstraint) (φ : FlexSubst) : Prop :=
  ValidFlexSubst Ψ φ ∧
  ∀ c ∈ C,
    match c.rel with
    | .lt => SizeLt Ψ (c.lhs.applyFlex φ) (c.rhs.applyFlex φ).boundNorm
    | .le => SizeLe Ψ (c.lhs.applyFlex φ) (c.rhs.applyFlex φ).boundNorm

/-- Universal property of closest next bound search `Ψ ⊢ R a ⇒ b` (Section 6.4, p. 57):
`b` is well-formed in `Ψ`, satisfies `Ψ ⊢ a R b^↑`, and for every `c` such that `Ψ ⊢ a R c^↑`,
we have `Ψ ⊢ b ≤ c`. -/
def ClosestNextBound (Ψ : SizeCtx) (R : EdgeRel) (a b : SizeExp) : Prop :=
  SizeWf Ψ b ∧
  (match R with
   | .lt => SizeLt Ψ a b.boundNorm
   | .le => SizeLe Ψ a b.boundNorm) ∧
  ∀ c : SizeExp,
    (match R with
     | .lt => SizeLt Ψ a c.boundNorm
     | .le => SizeLe Ψ a c.boundNorm) →
    SizeLe Ψ b c

/-- Compute the closest next bound `Ψ ⊢ R a ⇒ b` (Section 6.4, p. 57):
- for `R = ≤`, returns `a`
- for `R = <`:
  - if `a = ∞ + n`, returns `∞ + (n + 1)`
  - if `a = a^∧`, replaces each `(j + n) ∈ a^∧` whose bound in `Ψ` is a variable/meet `d_j`
    by `d_j + n`, dropping summands bounded by `∞`, and returning `∞` if all summands are bounded
    by `∞`. -/
def closestNextBound (Ψ : SizeCtx) (R : EdgeRel) (a : SizeExp) : SizeExp :=
  match R with
  | .le => a
  | .lt =>
      match a with
      | .inf n => .inf (n + 1)
      | .meet m =>
          let bounds : List SizeMin :=
            m.toList.filterMap fun sv =>
              match Ψ.find? (fun d => d.var == sv.var) with
              | some d =>
                  match d.bound.shift sv.shift with
                  | .meet bm => some bm
                  | .inf _ => none
              | none => none
          match bounds with
          | [] => .infty
          | b :: bs => .meet (bs.foldl SizeMin.append b)

/-- Universal property of the least upper bound `Ψ ⊢ LUB(b₁, ..., bₘ) ⇒ c` (Section 6.4, p. 57):
`c` is an upper bound (`∀ b ∈ bs, Ψ ⊢ b ≤ c^↑`) and is least among upper bounds
(`∀ d, (∀ b ∈ bs, Ψ ⊢ b ≤ d) → Ψ ⊢ c ≤ d`). -/
def IsLubSize (Ψ : SizeCtx) (bs : List SizeExp) (c : SizeExp) : Prop :=
  SizeWf Ψ c ∧
  (∀ b ∈ bs, SizeLe Ψ b c.boundNorm) ∧
  (∀ d : SizeExp, (∀ b ∈ bs, SizeLe Ψ b d) → SizeLe Ψ c d)

/-- Compute the least upper bound `LUB(b₁, ..., bₘ)` of a list of size expressions in `Ψ`
(Section 6.4, p. 57):
- for `[]`, returns `∞`
- if all non-redundant bounds simplify to a common expression `b` well-formed in `Ψ`, returns `b`,
  and otherwise returns `∞`. -/
def lubSizes (_Ψ : SizeCtx) (bs : List SizeExp) : SizeExp :=
  match bs with
  | [] => .infty
  | b :: rest =>
      if rest.all (· == b) then b else .infty

/-- Formal meet `⋀_{i ∈ Ψ} i` of all rigid variables in `Ψ` (or `∞` if `Ψ` is empty),
used in Step 3 of Algorithm 1 for non-recursive constructor variables `T` (Section 6.4, p. 58). -/
def rigidMeetAll (Ψ : SizeCtx) : SizeExp :=
  match Ψ with
  | [] => .infty
  | d :: rest =>
      .meet ⟨⟨d.var, 0⟩, rest.map (fun d' => ⟨d'.var, 0⟩)⟩

/-- **Algorithm 1**: Computing the optimal coherent substitution `φ*` for a rigid context `Ψ`,
constraint set `C`, and non-recursive flexible variable set `T` (Section 6.4, pp. 57–58).
Processes flexible variables along `C` (assigning rigid variables `i ∈ Ψ.dom` to `.var i 0`
and solving each flexible variable `k` via `closestNextBound` and `lubSizes`, defaulting to `.infty`
on cycles or unconstrained upper bounds so that `Ψ; C ⊢ φ*` is guaranteed whenever no constraint
in `C` has a flexible variable on the LHS and a rigid variable on the RHS). -/
def solveConstraintGraph (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) : FlexSubst :=
  let baseSubst : FlexSubst := fun k =>
    if Ψ.dom.contains k then .var k 0 else .infty
  let candidateSubst : FlexSubst := fun k =>
    if Ψ.dom.contains k then
      .var k 0
    else
      let hasSelfLt :=
        C.any (fun c => c.rel == .lt && c.lhs.vars.contains k && c.rhs.vars.contains k)
      if hasSelfLt then
        .infty
      else
        let incoming : List SizeExp :=
          (C.filter (fun c => c.rhs == .var k 0 && c.lhs.vars.all (fun v => Ψ.dom.contains v))).map
            (fun c => closestNextBound Ψ c.rel c.lhs)
        let withT : List SizeExp :=
          if T.contains k && !Ψ.isEmpty then rigidMeetAll Ψ :: incoming else incoming
        lubSizes Ψ withT
  let candidateOk : Bool :=
    C.all fun c =>
      let lhs' := c.lhs.applyFlex candidateSubst
      let rhs' := (c.rhs.applyFlex candidateSubst).boundNorm
      match rhs' with
      | .inf n =>
          match c.rel, lhs' with
          | .lt, .inf m => m < n
          | .le, .inf m => m < n + 1
          | _, .meet _ => true
      | .meet _ => lhs' == rhs' && c.rel == .le
  if candidateOk then candidateSubst else baseSubst

/-- Extract an invocation graph `G ∈ G_{f, D}(f, g)` for a single call site `g a⃗` inside `f`
(Section 4.5, p. 28 & Section 6.5, Step 7, p. 59):
for each callee argument `aᵢ` (`i < |a⃗|`, left vertex `lᵢ ∈ L_G`) and caller size parameter
`pⱼ ∈ Ψ_f` (`j < |Ψ_f|`, right vertex `rⱼ ∈ R_G`), records `<` if `Ψ ⊢ aᵢ < pⱼ` and `≤` if
`Ψ ⊢ aᵢ ≤ pⱼ`. -/
def buildCallGraph (callerParams : SizeCtx) (calleeArgs : List SizeExp)
    (clauseRigidCtx : SizeCtx) : InvGraph :=
  let leftArity := calleeArgs.length
  let rightArity := callerParams.length
  let lookup (i j : Nat) : Option EdgeRel :=
    match calleeArgs[i]?, callerParams[j]? with
    | some arg, some param =>
        let bnd := closestNextBound clauseRigidCtx .lt arg
        if arg == .var param.var 0 then
          some .le
        else if bnd == .var param.var 0 then
          some .lt
        else
          none
    | _, _ => none
  ⟨leftArity, rightArity, InvGraph.canonicalEdges leftArity rightArity lookup⟩

mutual

/-- Condition 6 of Theorem 13 (p. 57) and Step 7 of Algorithm 2 (p. 59):
for every call `g a⃗` to a function `g ∈ Ξ` occurring in the size-substituted term `u = φ(t')`,
there exists an invocation graph `G ∈ G(f, g)` such that `a⃗ ≺_G Ψ₁` in the clause rigid context
`Ψclause = Ψ₁ ++ Ψ₂`. -/
def LocalCallsConform (Ξ : MutualBlock) (𝒢 : InvGraphFamily)
    (caller : FunName) (Ψ₁ : SizeCtx) (Ψclause : SizeCtx) : Term → Prop
  | .var _ => True
  | .funRef g as =>
      ∀ decl ∈ Ξ, decl.name = g →
        SizeSubstWf Ψclause as decl.sizeParams ∧
        ∃ G ∈ 𝒢.graphs caller g, SyntacticConforms Ψclause G as Ψ₁
  | .app r e =>
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause r ∧
      LocalCallsConformElim Ξ 𝒢 caller Ψ₁ Ψclause e
  | .unit => True
  | .pair t₁ t₂ =>
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t₁ ∧
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t₂
  | .cons _ _ t =>
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t
  | .pack _ t =>
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t
  | .lamClauses Ds =>
      LocalCallsConformClauses Ξ 𝒢 caller Ψ₁ Ψclause Ds
  | .ascr t _ =>
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t

/-- Helper: check `LocalCallsConform` in an elimination `e`. -/
def LocalCallsConformElim (Ξ : MutualBlock) (𝒢 : InvGraphFamily)
    (caller : FunName) (Ψ₁ : SizeCtx) (Ψclause : SizeCtx) : Elim → Prop
  | .term t => LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t
  | .tyArg _ => True
  | .proj _ _ => True

/-- Helper: check `LocalCallsConform` across a list of clauses. -/
def LocalCallsConformClauses (Ξ : MutualBlock) (𝒢 : InvGraphFamily)
    (caller : FunName) (Ψ₁ : SizeCtx) (Ψclause : SizeCtx) : List Clause → Prop
  | [] => True
  | (.mk _ t) :: rest =>
      LocalCallsConform Ξ 𝒢 caller Ψ₁ Ψclause t ∧
      LocalCallsConformClauses Ξ 𝒢 caller Ψ₁ Ψclause rest

end

/-- Well-typed inference witness for a single clause `{q⃗ → t}` produced by Steps 4–7 of
Algorithm 2 (Section 6.5, p. 59):
- Step 4: `InferSpine` on `q⃗` produces `C'`, `Γ`, `Δ'`, `Ψ₂`, and `q⃗'`
- Step 5: `CheckTerm` on the clause body `t` produces `Φ`, `Cs`, `T`, and `t'`
- Step 6: `φ* = solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T`
- Step 7: all recursive calls to `g ∈ Ξannot` in `φ*(t')` conform to `𝒢` (`LocalCallsConform`). -/
structure Algorithm2ClauseRun (sig : GlobalSig) (Ξannot : MutualBlock)
    (𝒢 : InvGraphFamily) (caller : FunName) (Ψ₁ : SizeCtx)
    (A' : TypeExpr) (qs : PatSpine) (t : Term) (D' : Clause) where
  C' : TypeExpr
  Γ : TermCtx
  Δ' : List TyDecl
  Ψ₂ : SizeCtx
  qs' : PatSpine
  Φ : FlexVars
  Cs : List SizeConstraint
  T : List SizeVar
  t' : Term
  inferSpine : InferSpine (KindingCtx.empty.extSizes Ψ₁) qs A' C' Γ Δ' Ψ₂ qs'
  consistentExt : KindingCtxConsistentExt (KindingCtx.empty.extSizes Ψ₁) Δ'
  clauseSizesWf : SizeCtxWf (Ψ₁ ++ Ψ₂)
  checkBody :
    CheckTerm sig Ξannot ((Ψ₁ ++ Ψ₂).map (fun d => (d.var, d.pol)))
      Γ ((KindingCtx.empty.extSizes Ψ₁).append ⟨Ψ₂, Δ'⟩) C' t Φ Cs T t'
  callsConform :
    let φstar := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T
    D' = .mk qs' (t'.applyFlex φstar) ∧
    LocalCallsConform Ξannot 𝒢 caller Ψ₁ (Ψ₁ ++ Ψ₂) (t'.applyFlex φstar)

/-- **Algorithm 2** (`Algorithm2Accepts`, Section 6.5, p. 59):
Given a global signature `sig` (`⊨ Σ`) and an unannotated mutual block `Ξ` in System `F_ω^c`,
Algorithm 2:
1. Iterates over `(f : A = D⃗) ∈ Ξ` and encodes `+; · ⊢_{SCT}^− A ⇒ Ψ₁; A'`;
2. Iterates over clauses `{q⃗ → t} ∈ D⃗`, running `InferSpine`, `CheckTerm`, and `φ*` (Algorithm 1);
3. Collects the invocation graphs `G` for all recursive calls `g ∈ Ξ` in `φ*(t')`;
4. Accepts `Ξ` (producing the size-annotated mutual block `Ξannot`) if `⊢ G` (`SCTValid 𝒢`). -/
def Algorithm2Accepts (sig : GlobalSig) (Ξ : MutualBlock) (Ξannot : MutualBlock) : Prop :=
  ∃ 𝒢 : InvGraphFamily,
    SCTValid 𝒢 ∧
    (∀ decl' ∈ Ξannot, 𝒢.arity decl'.name = decl'.sizeParams.length) ∧
    List.Forall₂
      (fun decl decl' =>
        decl'.name = decl.name ∧
        EncodeType .neg .pos KindingCtx.empty decl.ty decl'.sizeParams decl'.ty ∧
        SignatureFixpointHygiene (KindingCtx.empty.extSizes decl'.sizeParams) decl'.ty ∧
        SizeCtxWf decl'.sizeParams ∧
        KindCheck (KindingCtx.empty.extSizes decl'.sizeParams) decl'.ty .star ∧
        List.Forall₂
          (fun D D' =>
            ∃ qs t,
              D = Clause.mk qs t ∧
              Nonempty (Algorithm2ClauseRun sig Ξannot 𝒢 decl'.name decl'.sizeParams decl'.ty qs t D'))
          decl.clauses decl'.clauses)
      Ξ Ξannot

/-! ## Repaired Kinding-Aware Occurrence, Guarded Comparison, Safe Term Inference, and Checked Solver -/

mutual

/-- Collect size variable names occurring in explicit coinductive `ν` indices. -/
def nuIndexVars : TypeExpr → List SizeVar
  | .atom _ => []
  | .lam _ _ F => nuIndexVars F
  | .app F G => nuIndexVars F ++ nuIndexVars G
  | .mu _ S => nuIndexVarsBranches S
  | .nu a R => a.vars ++ nuIndexVarsBranches R

/-- Collect size variable names occurring in explicit `ν` indices across branches. -/
def nuIndexVarsBranches : List (Nat × TypeExpr) → List SizeVar
  | [] => []
  | (_, F) :: rest => nuIndexVars F ++ nuIndexVarsBranches rest

end

mutual

/-- Kinding-aware signed fixpoint index occurrence in inference mode (`μ` starts at `+`, `ν` at `−`). -/
inductive InferUse : KindingCtx → TypeExpr → Kind → FixKind → SizeVar → Polarity → Prop where
  | muIndex {Δ : KindingCtx} {a : SizeExp} {S : List (Nat × TypeExpr)} {i : SizeVar} :
      KindInfer Δ (.mu a S) .star → i ∈ a.vars →
      InferUse Δ (.mu a S) .star .mu i .pos
  | nuIndex {Δ : KindingCtx} {a : SizeExp} {S : List (Nat × TypeExpr)} {i : SizeVar} :
      KindInfer Δ (.nu a S) .star → i ∈ a.vars →
      InferUse Δ (.nu a S) .star .nu i .neg
  | muBranch {Δ : KindingCtx} {a : SizeExp} {S : List (Nat × TypeExpr)}
      {c : Nat} {F : TypeExpr} {fk : FixKind} {i : SizeVar} {q : Polarity} :
      KindInfer Δ (.mu a S) .star → (c, F) ∈ S →
      CheckUse Δ F functorKind fk i q → InferUse Δ (.mu a S) .star fk i q
  | nuBranch {Δ : KindingCtx} {a : SizeExp} {S : List (Nat × TypeExpr)}
      {c : Nat} {F : TypeExpr} {fk : FixKind} {i : SizeVar} {q : Polarity} :
      KindInfer Δ (.nu a S) .star → (c, F) ∈ S →
      CheckUse Δ F functorKind fk i q → InferUse Δ (.nu a S) .star fk i q
  | appLeft {Δ : KindingCtx} {F G : TypeExpr} {p q : Polarity} {κ κ' : Kind}
      {fk : FixKind} {i : SizeVar} :
      KindInfer Δ F (.arr p κ κ') → KindCheck (Δ.invScalePol p) G κ →
      InferUse Δ F (.arr p κ κ') fk i q → InferUse Δ (.app F G) κ' fk i q
  | appRight {Δ : KindingCtx} {F G : TypeExpr} {p q : Polarity} {κ κ' : Kind}
      {fk : FixKind} {i : SizeVar} :
      KindInfer Δ F (.arr p κ κ') → KindCheck (Δ.invScalePol p) G κ →
      CheckUse (Δ.invScalePol p) G κ fk i q →
      InferUse Δ (.app F G) κ' fk i (Polarity.comp p q)

/-- Kinding-aware signed fixpoint index occurrence in checking mode. -/
inductive CheckUse : KindingCtx → TypeExpr → Kind → FixKind → SizeVar → Polarity → Prop where
  | sub {Δ : KindingCtx} {F : TypeExpr} {κ κ' : Kind} {fk : FixKind}
      {i : SizeVar} {q : Polarity} :
      KindInfer Δ F κ → SubKind Δ.sizes κ κ' →
      InferUse Δ F κ fk i q → CheckUse Δ F κ' fk i q
  | lam {Δ : KindingCtx} {X i : Nat} {ι : SKind} {F : TypeExpr}
      {p q : Polarity} {κ κ' : Kind} {fk : FixKind} :
      X ≠ i → KindWf (Δ.sizes.invScalePol .mixed) (Kind.ofSKind ι) →
      KindCheck (Δ.extType X p κ) F κ' →
      CheckUse (Δ.extType X p κ) F κ' fk i q →
      CheckUse Δ (.lam X ι F) (.arr p κ κ') fk i q

end

mutual

/-- Polarized type comparison with explicit occurrence transport across extensional `lam` steps
(Theorem 10, Section 6.3.4, pp. 52–53). -/
inductive GuardedCompareTypes (i : SizeVar) (Φ : FlexVars) :
    KindingCtx → SKind → Polarity → TypeExpr → TypeExpr → List SizeConstraint → Prop where
  | atom (Δ : KindingCtx) (ι : SKind) (π : Polarity) (K : TyAtom) :
      GuardedCompareTypes i Φ Δ ι π (.atom K) (.atom K) []
  | app {Δ : KindingCtx} {π₁ π : Polarity} {ι₁ ι₂ : SKind}
      {F F' G G' : TypeExpr} {C₁ C₂ : List SizeConstraint} :
      KindInfer Δ F (.arr π₁ (Kind.ofSKind ι₁) (Kind.ofSKind ι₂)) →
      KindInfer Δ F' (.arr π₁ (Kind.ofSKind ι₁) (Kind.ofSKind ι₂)) →
      GuardedCompareTypes i Φ Δ (.arr π₁ ι₁ ι₂) π F F' C₁ →
      GuardedCompareTypes i Φ (Δ.invScalePol π₁) ι₁ (Polarity.comp π₁ π) G G' C₂ →
      GuardedCompareTypes i Φ Δ ι₂ π (.app F G) (.app F' G') (C₁ ++ C₂)
  | lam {Δ : KindingCtx} {π₁ π : Polarity} {ι₁ ι₂ : SKind}
      {F F' : TypeExpr} {X : TyVar} {C : List SizeConstraint} :
      CompareFresh X Δ Φ F F' →
      CompareKinded Δ (.arr π₁ ι₁ ι₂) F →
      CompareKinded Δ (.arr π₁ ι₁ ι₂) F' →
      (∀ fk q, SizeOccursFixPol (Δ.extType X π₁ (Kind.ofSKind ι₁)) fk i q
          (F.normApp (.atom (.var X))) → SizeOccursFixPol Δ fk i q F) →
      (∀ fk q, SizeOccursFixPol (Δ.extType X π₁ (Kind.ofSKind ι₁)) fk i q
          (F'.normApp (.atom (.var X))) → SizeOccursFixPol Δ fk i q F') →
      GuardedCompareTypes i Φ (Δ.extType X π₁ (Kind.ofSKind ι₁)) ι₂ π
        (F.normApp (.atom (.var X))) (F'.normApp (.atom (.var X))) C →
      GuardedCompareTypes i Φ Δ (.arr π₁ ι₁ ι₂) π F F' C
  | mu {Δ : KindingCtx} {π π₁ π₂ : Polarity} {a b : SizeExp}
      {S S' : List (ConsName × TypeExpr)} {C : List SizeConstraint} :
      Φ.lookupSizePol .pos a = some π₁ →
      Φ.lookupSizePol .pos b = some π₂ →
      GuardedCompareBranches i Φ Δ π S S' C →
      GuardedCompareTypes i Φ Δ .star π (.mu a S) (.mu b S')
        (SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax π₁ π₂) π) a b ++ C)
  | nu {Δ : KindingCtx} {π π₁ π₂ : Polarity} {a b : SizeExp}
      {R R' : List (ProjName × TypeExpr)} {C : List SizeConstraint} :
      Φ.lookupSizePol .neg a = some π₁ →
      Φ.lookupSizePol .neg b = some π₂ →
      GuardedCompareBranches i Φ Δ π R R' C →
      GuardedCompareTypes i Φ Δ .star π (.nu a R) (.nu b R')
        (SizeConstraint.ofPol (Polarity.comp (Polarity.infoMax π₁ π₂) π) a b ++ C)

/-- Branch/field counterpart of `GuardedCompareTypes`. -/
inductive GuardedCompareBranches (i : SizeVar) (Φ : FlexVars) :
    KindingCtx → Polarity → List (Nat × TypeExpr) → List (Nat × TypeExpr) →
      List SizeConstraint → Prop where
  | nil (Δ : KindingCtx) (π : Polarity) :
      GuardedCompareBranches i Φ Δ π [] [] []
  | cons {Δ : KindingCtx} {π : Polarity} {nm : Nat} {F F' : TypeExpr}
      {rest rest' : List (Nat × TypeExpr)} {C₁ C₂ : List SizeConstraint} :
      GuardedCompareTypes i Φ Δ fwFunctorSKind π F F' C₁ →
      GuardedCompareBranches i Φ Δ π rest rest' C₂ →
      GuardedCompareBranches i Φ Δ π ((nm, F) :: rest) ((nm, F') :: rest') (C₁ ++ C₂)

end

/-- No constraint in `Cs` has an incoming edge from a distinct variable `j ≠ i` into `.var i 0`. -/
def NoDistinctIncoming (i : SizeVar) (Cs : List SizeConstraint) : Prop :=
  ∀ c ∈ Cs, ∀ j ≠ i, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)

/-- No constraint in `Cs` has an incoming edge from a flexible variable `j ∉ dom` into `.var i 0`. -/
def NoOutsideIncoming (dom : List SizeVar) (i : SizeVar) (Cs : List SizeConstraint) : Prop :=
  ∀ c ∈ Cs, ∀ j ∉ dom, ¬ (c.lhs = .var j 0 ∧ c.rhs = .var i 0)

mutual

/-- Term inference guarded by the structural emission invariants for a tracked rigid variable `i`
(Theorems 11–12, Section 6.3.4, pp. 53–56). -/
inductive SafeInferTerm (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar) :
    FlexVars → TermCtx → KindingCtx → Term →
    TypeExpr → FlexVars → List SizeConstraint → List SizeVar → Term → Prop where
  | var {Φ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx} {x : TermVar} {A : TypeExpr} :
      (x, A) ∈ Γ →
      SafeInferTerm sig Ξ i Φ Γ Δ (.var x) A Φ [] [] (.var x)
  | appTerm {Φ Φ₁ Φ₂ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {r r' s s' : Term} {A B : TypeExpr}
      {C₁ C₂ : List SizeConstraint} {T₁ T₂ : List SizeVar} :
      SafeInferTerm sig Ξ i Φ Γ Δ r (.arrTy A B) Φ₁ C₁ T₁ r' →
      SafeCheckTerm sig Ξ i Φ₁ Γ Δ A s Φ₂ C₂ T₂ s' →
      SafeInferTerm sig Ξ i Φ Γ Δ (.app r (.term s)) B Φ₂ (C₁ ++ C₂) (T₁ ++ T₂)
        (.app r' (.term s'))
  | proj {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {r r' : Term} {a : SizeExp} {R : List (ProjName × TypeExpr)}
      {d : ProjName} {Rd : TypeExpr}
      {C : List SizeConstraint} {T T' : List SizeVar} (j : SizeVar) :
      SafeInferTerm sig Ξ i Φ Γ Δ r (.nu a R) Φ' C T r' →
      i ∉ nuIndexVars (.nu a R) →
      TypeExpr.lookupProj R d = some Rd →
      j ∉ Φ'.dom →
      j ∉ Δ.sizes.dom →
      T' = (if j ∈ (Rd.normApp (.nu (.var j 0) R)).allSizeVars then T else j :: T) →
      SafeInferTerm sig Ξ i Φ Γ Δ (.app r (.proj d none))
        (Rd.normApp (.nu (.var j 0) R))
        ((j, .neg) :: Φ') (⟨.var j 0, .lt, a⟩ :: C) T'
        (.app r' (.proj d (some (.var j 0))))
  | appTy {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {r r' : Term} {G G' F : TypeExpr} {ι : SKind} {Ψ : SizeCtx}
      {C : List SizeConstraint} {T : List SizeVar} :
      EncodeType .mixed .mixed Δ G Ψ G' →
      List.Disjoint Ψ.dom Φ'.dom →
      SafeInferTerm sig Ξ i Φ Γ Δ r (.allTy (Kind.ofSKind ι) F) Φ' C T r' →
      SafeInferTerm sig Ξ i Φ Γ Δ (.app r (.tyArg G))
        (F.normApp G')
        (Ψ.map (fun d => (d.var, .mixed)) ++ Φ') C T
        (.app r' (.tyArg G'))
  | ascr {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {t t' : Term} {A A' : TypeExpr} {Ψ : SizeCtx}
      {C : List SizeConstraint} {T : List SizeVar} :
      EncodeType .mixed .mixed Δ A Ψ A' →
      List.Disjoint Ψ.dom Φ'.dom →
      SafeCheckTerm sig Ξ i Φ Γ Δ A' t Φ' C T t' →
      SafeInferTerm sig Ξ i Φ Γ Δ (.ascr t A) A'
        (Ψ.map (fun d => (d.var, .mixed)) ++ Φ') C T
        (.ascr t' A')
  | funCall {Φ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {decl : FunDecl} {flexVars : List (SizeVar × Polarity)} {as : List SizeExp} :
      decl ∈ sig ++ Ξ →
      flexVars.length = decl.sizeParams.length →
      flexVars.Nodup →
      List.Disjoint (flexVars.map (·.1)) Φ.dom →
      List.Disjoint (flexVars.map (·.1)) Δ.sizes.dom →
      (∀ p ∈ decl.sizeParams.zip flexVars,
        (SizeOccursFixPol (Δ.extSizes decl.sizeParams) .mu p.1.var .neg decl.ty → p.2.2 = .pos) ∧
        (SizeOccursFixPol (Δ.extSizes decl.sizeParams) .nu p.1.var .pos decl.ty → p.2.2 = .neg) ∧
        (p.2.2 = .pos ∨ p.2.2 = .neg ∨ p.2.2 = .mixed)) →
      as = flexVars.map (fun p => SizeExp.var p.1 0) →
      SafeInferTerm sig Ξ i Φ Γ Δ (.funRef decl.name [])
        (decl.ty.substSizes (decl.sizeParams.dom.zip as))
        (flexVars ++ Φ) [] []
        (.funRef decl.name as)

/-- Term checking guarded by the structural emission invariants for `i`. -/
inductive SafeCheckTerm (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar) :
    FlexVars → TermCtx → KindingCtx → TypeExpr → Term →
    FlexVars → List SizeConstraint → List SizeVar → Term → Prop where
  | unit (Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) :
      SafeCheckTerm sig Ξ i Φ Γ Δ .unitTy .unit Φ [] [] .unit
  | pair {Φ Φ₁ Φ₂ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {A₁ A₂ : TypeExpr} {t₁ t₁' t₂ t₂' : Term}
      {C₁ C₂ : List SizeConstraint} {T₁ T₂ : List SizeVar} :
      SafeCheckTerm sig Ξ i Φ Γ Δ A₁ t₁ Φ₁ C₁ T₁ t₁' →
      SafeCheckTerm sig Ξ i Φ₁ Γ Δ A₂ t₂ Φ₂ C₂ T₂ t₂' →
      SafeCheckTerm sig Ξ i Φ Γ Δ (.prodTy A₁ A₂) (.pair t₁ t₂)
        Φ₂ (C₁ ++ C₂) (T₁ ++ T₂) (.pair t₁' t₂')
  | lamClauses {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {A : TypeExpr} {Ds Ds' : List Clause}
      {C : List SizeConstraint} {T : List SizeVar} :
      SafeCheckClausesInfer sig Ξ i Φ Γ Δ A Ds Φ' C T Ds' →
      SafeCheckTerm sig Ξ i Φ Γ Δ A (.lamClauses Ds) Φ' C T (.lamClauses Ds')
  | cons {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {c : ConsName} {a : SizeExp} {S : List (ConsName × TypeExpr)} {Sc : TypeExpr}
      {t t' : Term} {C : List SizeConstraint} {T T' : List SizeVar} (j : SizeVar) :
      KindCheck Δ (.mu a S) .star →
      ¬ CheckUse Δ (.mu a S) .star .mu i .pos →
      TypeExpr.lookupCons S c = some Sc →
      j ∉ Φ.dom →
      j ∉ Δ.sizes.dom →
      SafeCheckTerm sig Ξ i ((j, .pos) :: Φ) Γ Δ (Sc.normApp (.mu (.var j 0) S)) t Φ' C T t' →
      T' = (if j ∈ (Sc.normApp (.mu (.var j 0) S)).allSizeVars then T else j :: T) →
      SafeCheckTerm sig Ξ i Φ Γ Δ (.mu a S) (.cons c none t)
        Φ' (⟨.var j 0, .lt, a⟩ :: C) T' (.cons c (some (.var j 0)) t')
  | pack {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {ι : SKind} {F G G' : TypeExpr} {Ψ : SizeCtx} {t t' : Term}
      {C : List SizeConstraint} {T : List SizeVar} :
      EncodeType .mixed .mixed Δ G Ψ G' →
      List.Disjoint Ψ.dom Φ.dom →
      SafeCheckTerm sig Ξ i (Ψ.map (fun d => (d.var, .mixed)) ++ Φ) Γ Δ (F.normApp G') t Φ' C T t' →
      SafeCheckTerm sig Ξ i Φ Γ Δ (.exTy (Kind.ofSKind ι) F) (.pack G t) Φ' C T (.pack G' t')
  | sub {Φ Φ' : FlexVars} {Γ : TermCtx} {Δ : KindingCtx}
      {A Cty : TypeExpr} {r r' : Term}
      {C₁ C₂ : List SizeConstraint} {T : List SizeVar} :
      SafeInferTerm sig Ξ i Φ Γ Δ r A Φ' C₁ T r' →
      FlexPolHygiene Φ' Δ A Cty →
      CompareTypes Φ' Δ .star .pos A Cty C₂ →
      NoDistinctIncoming i C₂ →
      SafeCheckTerm sig Ξ i Φ Γ Δ Cty r Φ' (C₁ ++ C₂) T r'

/-- Single-clause checking guarded by the structural emission invariants for `i`. -/
inductive SafeCheckClauseInfer (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar) :
    FlexVars → TermCtx → KindingCtx → TypeExpr → Clause →
    FlexVars → List SizeConstraint → List SizeVar → Clause → Prop where
  | mk {Φ Φ' : FlexVars} {Γ Γ' : TermCtx} {Δ : KindingCtx} {Δ' : List TyDecl}
      {Ψ Ψ' : SizeCtx} {C C' : TypeExpr} {qs qs' : PatSpine} {t t' : Term}
      {Cs : List SizeConstraint} {T : List SizeVar} :
      InferSpine Δ qs C C' Γ' Δ' Ψ qs' →
      Ψ' = trivializeCtx Φ Ψ →
      SafeCheckTerm sig Ξ i (Ψ'.map (fun d => (d.var, d.pol)) ++ Φ)
        (Γ ++ Γ') (Δ.append ⟨Ψ', Δ'⟩) C' t Φ' Cs T t' →
      SafeCheckClauseInfer sig Ξ i Φ Γ Δ C (.mk qs t) Φ' Cs T (.mk qs' t')

/-- Multi-clause checking guarded by the structural emission invariants for `i`. -/
inductive SafeCheckClausesInfer (sig : GlobalSig) (Ξ : MutualBlock) (i : SizeVar) :
    FlexVars → TermCtx → KindingCtx → TypeExpr → List Clause →
    FlexVars → List SizeConstraint → List SizeVar → List Clause → Prop where
  | nilClause (Φ : FlexVars) (Γ : TermCtx) (Δ : KindingCtx) (C : TypeExpr) :
      SafeCheckClausesInfer sig Ξ i Φ Γ Δ C [] Φ [] [] []
  | consClause {Φ Φ₁ Φ₂ : FlexVars} {Γ : TermCtx} {Δ : KindingCtx} {C : TypeExpr}
      {D D' : Clause} {Ds Ds' : List Clause}
      {C₁ C₂ : List SizeConstraint} {T₁ T₂ : List SizeVar} :
      SafeCheckClauseInfer sig Ξ i Φ Γ Δ C D Φ₁ C₁ T₁ D' →
      SafeCheckClausesInfer sig Ξ i Φ₁ Γ Δ C Ds Φ₂ C₂ T₂ Ds' →
      SafeCheckClausesInfer sig Ξ i Φ Γ Δ C (D :: Ds) Φ₂ (C₁ ++ C₂) (T₁ ++ T₂) (D' :: Ds')

end

namespace CheckedConstraintSolver

/-- Usable polarities `π ≤ +` in `SizeVarBound`. -/
def usable : Polarity → Bool
  | .mixed => true
  | .pos => true
  | .neg => false
  | .top => false

/-- Check whether `i` has a usable bound in `Ψ`. -/
def hasBound (Ψ : SizeCtx) (i : SizeVar) : Bool :=
  Ψ.any (fun d => (d.var == i) && usable d.pol)

/-- Check whether `i` has usable bound `a` in `Ψ`. -/
def hasBoundEq (Ψ : SizeCtx) (i : SizeVar) (a : SizeExp) : Bool :=
  Ψ.any (fun d => (d.var == i) && usable d.pol && (d.bound == a))

/-- Executable well-formedness check for `SizeWf Ψ a`. -/
def checkWf (Ψ : SizeCtx) : SizeExp → Bool
  | .inf _ => true
  | .meet a => a.toList.all (fun sv => hasBound Ψ sv.var)

/-- Direct non-recursive strict size comparison check. -/
def direct (Ψ : SizeCtx) : SizeExp → SizeExp → Bool
  | .inf n, b =>
      match b with
      | .inf m => decide (n < m)
      | .meet _ => false
  | .meet am, b =>
      match am.tail with
      | _ :: _ => false
      | [] =>
        match b with
        | .inf _ => hasBoundEq Ψ am.head.var .infty
        | .meet bm =>
          match bm.tail with
          | _ :: _ => false
          | [] => (am.head.var == bm.head.var) &&
              decide (am.head.shift < bm.head.shift) && hasBound Ψ am.head.var

/-- Fuel-bounded sound checker for `SizeLt Ψ a b`. -/
def checkSizeLt : Nat → SizeCtx → SizeExp → SizeExp → Bool
  | 0, _, _, _ => false
  | fuel + 1, Ψ, a, b =>
    direct Ψ a b ||
    (match b with
     | .meet bm =>
         if bm.tail.isEmpty then false
         else bm.toList.all (fun sv => checkSizeLt fuel Ψ a (.var sv.var sv.shift))
     | .inf _ => false) ||
    (match a with
     | .meet am =>
         if am.tail.isEmpty then false
         else checkWf Ψ (.meet am) &&
           am.toList.any (fun sv => checkSizeLt fuel Ψ (.var sv.var sv.shift) b)
     | .inf _ => false) ||
    (match a with
     | .inf _ => false
     | .meet am =>
       match am.tail with
       | _ :: _ => false
       | [] => Ψ.any (fun d => (d.var == am.head.var) && usable d.pol &&
           checkSizeLt fuel Ψ (d.bound.shift am.head.shift) (b.shift 1)))

/-- Finite support of variables mentioned in `(Ψ, C, T)`. -/
def support (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) : List SizeVar :=
  Ψ.dom ++ C.flatMap (fun c => c.lhs.vars ++ c.rhs.vars) ++ T

/-- Check a single constraint `c` under flexible substitution `φ`. -/
def constraintCheck (fuel : Nat) (Ψ : SizeCtx) (φ : FlexSubst) (c : SizeConstraint) : Bool :=
  match c.rel with
  | .lt => checkSizeLt fuel Ψ (c.lhs.applyFlex φ) (c.rhs.applyFlex φ).boundNorm
  | .le => checkSizeLt fuel Ψ (c.lhs.applyFlex φ) ((c.rhs.applyFlex φ).boundNorm.shift 1)

/-- Finite boolean certificate verifying that `solveConstraintGraph Ψ C T` is coherent. -/
def certificate (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) : Bool :=
  let φ := solveConstraintGraph Ψ C T
  Ψ.dom.all (fun k => φ k == .var k 0) &&
    (support Ψ C T).all (fun k => checkWf Ψ (φ k)) &&
    C.all (constraintCheck fuel Ψ φ)

/-- Return `some (solveConstraintGraph Ψ C T)` when `certificate fuel Ψ C T` succeeds. -/
def checkedSolve (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) :
    Option FlexSubst :=
  if certificate fuel Ψ C T then some (solveConstraintGraph Ψ C T) else none

end CheckedConstraintSolver

/-- Postchecked clause run for Algorithm 2 (Section 6.5, p. 59): combines `Algorithm2ClauseRun`
with the verified target body typing `ExprCheck` after applying `φ* = solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T`. -/
structure PostcheckedAlgorithm2ClauseRun (sig : GlobalSig) (Ξannot : MutualBlock)
    (𝒢 : InvGraphFamily) (caller : FunName) (Ψ₁ : SizeCtx)
    (A' : TypeExpr) (qs : PatSpine) (t : Term) (D' : Clause) extends
    Algorithm2ClauseRun sig Ξannot 𝒢 caller Ψ₁ A' qs t D' where
  postcheckedBody :
    let φstar := solveConstraintGraph (Ψ₁ ++ Ψ₂) Cs T
    ExprCheck ⟨sig, Ξannot, 𝒢, caller, Ψ₁⟩
      ((KindingCtx.empty.extSizes Ψ₁).extDecls Δ') Γ (t'.applyFlex φstar) C'

/-- Postchecked **Algorithm 2** acceptance (`PostcheckedAlgorithm2Accepts`, Section 6.5, p. 59):
ensures each clause run passes both `Algorithm2ClauseRun` and the target `ExprCheck` postcheck. -/
def PostcheckedAlgorithm2Accepts (sig : GlobalSig) (Ξ : MutualBlock) (Ξannot : MutualBlock) : Prop :=
  ∃ 𝒢 : InvGraphFamily,
    SCTValid 𝒢 ∧
    (∀ decl' ∈ Ξannot, 𝒢.arity decl'.name = decl'.sizeParams.length) ∧
    List.Forall₂
      (fun decl decl' =>
        decl'.name = decl.name ∧
        EncodeType .neg .pos KindingCtx.empty decl.ty decl'.sizeParams decl'.ty ∧
        SignatureFixpointHygiene (KindingCtx.empty.extSizes decl'.sizeParams) decl'.ty ∧
        SizeCtxWf decl'.sizeParams ∧
        KindCheck (KindingCtx.empty.extSizes decl'.sizeParams) decl'.ty .star ∧
        List.Forall₂
          (fun D D' =>
            ∃ qs t,
              D = Clause.mk qs t ∧
              Nonempty (PostcheckedAlgorithm2ClauseRun sig Ξannot 𝒢 decl'.name decl'.sizeParams decl'.ty qs t D'))
          decl.clauses decl'.clauses)
      Ξ Ξannot

end NishtAbel2024V2


