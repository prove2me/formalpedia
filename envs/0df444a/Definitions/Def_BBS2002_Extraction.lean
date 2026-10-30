-- Prove2me | Definitions.Def_BBS2002_Extraction
-- name    : BBS2002_Extraction
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T04:06:53.223255+00:00
-- url     : https://prove2.me/theorems/4f02e7d1-32a1-45a7-88fe-5c2a11920738
-- title:
--   Sections 3-5: Definite and Goal Formulas, Program Extraction, and Modified Realizability
-- statement:
--   Formalizes Sections 3-5 of Berger, Buchholz, and Schwichtenberg (2002): relevant and irrelevant formulas, the mutual inductive classes of goal formulas `G` (`IsGoalFormula`) and definite formulas `D` (`IsDefiniteFormula`), type assignment `τ(A)`, structural program extraction `⟦M⟧`, modified realizability `r mr_A B`, and Section 5 `*`-aware combinators.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Sections 3-5, pp. 8-16 (preprint pp. 6-14).

import Definitions.Def_BBS2002_Arithmetic

/-!
# Definite and Goal Formulas, Program Extraction, and Modified Realizability (Berger–Buchholz–Schwichtenberg 2002, Sections 3–5)

Source: Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg,
"Refined program extraction from classical proofs",
*Annals of Pure and Applied Logic* 114, 2002, pp. 3–25 (Sections 3–5, pp. 8–16 / preprint pp. 6–14).

This module formalizes:
- Section 3 (pp. 6–9):
  - Relevant and irrelevant formulas (`isRelevant`, `isIrrelevant`, p. 6).
  - Goal formulas `G` (`IsGoalFormula`) and definite formulas `D` (`IsDefiniteFormula`, p. 6).
- Section 4 (pp. 11–12):
  - Assignment of types or the symbol `*` (`Option Ty`) to formulas: `τ(A)` (`tau`, p. 11).
  - Extracted program `⟦M⟧` (`extractProgram`, pp. 11–12) for a derivation `M` of `A`
    (returning `none` for the symbol `ε` when `τ(A) = *`, and `some t` when `τ(A) ≠ *`).
  - Comprehension terms `A := λy^ν A₀` (`CompTerm`) and the modified realizability relation
    `r mr_A B` (`mrFormula`, p. 12).
- Section 5 (pp. 12–14):
  - `*`-aware application and abstraction (`applyGoalRealizer`, `optLamVars`, `buildGoalCombinatorTerm`,
    `applyOptTerms`, `extractClassicalTerm`) where arguments and binders of type `*` (`none`)
    are omitted (p. 12).
-/

namespace BBS2002

/-- A formula is *relevant* if it "ends" with `⊥` (Section 3, p. 6):
- `⊥` is relevant,
- if `C` is relevant and `B` is arbitrary, then `B → C` is relevant,
- if `C` is relevant, then `∀x C` is relevant. -/
def isRelevant : Formula → Bool
  | .bot => true
  | .imp _ C => isRelevant C
  | .all _ C => isRelevant C
  | _ => false

/-- A formula which is not relevant is called *irrelevant* (Section 3, p. 6). -/
def isIrrelevant (A : Formula) : Bool :=
  !isRelevant A

mutual
  /-- Inductive class of *goal formulas* `G` (Section 3, p. 6):
  - `P` (where `P` is an atomic `L`-formula, including `⊥`)
  - `D → G` provided `D irrelevant ⇒ D quantifier-free` (with `D` definite and `G` goal)
  - `∀x G` provided `G irrelevant` (with `G` goal). -/
  inductive IsGoalFormula : Formula → Prop where
    | atom {P : Formula} :
        isAtomicL P = true →
        FormulaWellTyped P →
        IsGoalFormula P
    | imp {D G : Formula} :
        IsDefiniteFormula D →
        IsGoalFormula G →
        (isIrrelevant D = true → isQuantifierFree D = true) →
        IsGoalFormula (.imp D G)
    | all (x : Var) {G : Formula} :
        IsGoalFormula G →
        isIrrelevant G = true →
        IsGoalFormula (.all x G)

  /-- Inductive class of *definite formulas* `D` (Section 3, p. 6):
  - `P` (where `P` is an atomic `L`-formula, including `⊥`)
  - `G → D` provided `D irrelevant ⇒ G irrelevant` (with `G` goal and `D` definite)
  - `∀x D` (with `D` definite). -/
  inductive IsDefiniteFormula : Formula → Prop where
    | atom {P : Formula} :
        isAtomicL P = true →
        FormulaWellTyped P →
        IsDefiniteFormula P
    | imp {G D : Formula} :
        IsGoalFormula G →
        IsDefiniteFormula D →
        (isIrrelevant D = true → isIrrelevant G = true) →
        IsDefiniteFormula (.imp G D)
    | all (x : Var) {D : Formula} :
        IsDefiniteFormula D →
        IsDefiniteFormula (.all x D)
end

/-- Section 4 (p. 11): Assignment `τ(A)` of a type (`some ρ`) or the symbol `*` (`none`)
to every formula `A ∈ L[X]`, assuming a proof of `X` carries computational content of type `ν`:
- `τ(X) := ν`
- `τ(P) := *` (in particular `τ(⊥) = *`)
- `τ(∀x^ρ A) := *` if `τ(A) = *`, else `ρ → τ(A)`
- `τ(A → B) := τ(B)` if `τ(A) = *`, `*` if `τ(B) = *`, else `τ(A) → τ(B)`. -/
def tau (ν : Ty) : Formula → Option Ty
  | .varX => some ν
  | .bot | .atom _ => none
  | .all x A =>
      match tau ν A with
      | none => none
      | some σ => some (.arr x.ty σ)
  | .imp A B =>
      match tau ν A, tau ν B with
      | none, τB => τB
      | some _, none => none
      | some τA, some τB => some (.arr τA τB)

/-- Convert an assumption variable `u^A` into its realizer variable `u^{τ(A)}` when `τ(A) = some ρ`,
or `none` (`ε`) when `τ(A) = *` (Section 4, pp. 11–12). -/
def assumpRealizerVar (ν : Ty) (u : AssumpVar) : Option Var :=
  (tau ν u.formula).map (fun ρ => ⟨u.id, ρ⟩)

/-- Realizer term or `ε` (`none`) associated with an assumption variable `u^A` (Section 4, p. 12). -/
def assumpRealizerTerm (ν : Ty) (u : AssumpVar) : Option Term :=
  (assumpRealizerVar ν u).map Term.var

/-- Closed dummy term of type `ρ` built from `dummy^ν : ν` (used for `⟦efq_A⟧`, pp. 11–12). -/
def efqTerm (ν : Ty) (dummy : Term) (ρ : Ty) : Term :=
  if ρ == ν then dummy else defaultTerm ρ

/-- Raw structural Extraction `extractRaw ν dummy M` for a derivation `M` with `τ(A) ≠ *`
(Section 4, pp. 11–12):
- `⟦u^A⟧ := u^{τ(A)}`
- `⟦λu^A M⟧ := ⟦M⟧` if `τ(A) = *`, else `λu^{τ(A)} ⟦M⟧`
- `⟦M^{A→B} N⟧ := ⟦M⟧` if `τ(A) = *`, else `⟦M⟧ ⟦N⟧`
- `⟦λx^ρ M⟧ := λx^ρ ⟦M⟧`
- `⟦M t⟧ := ⟦M⟧ t`
- `⟦Ind_{p,A}⟧ := R_{o,ρ}` with `ρ := τ(A) ≠ *`
- `⟦Ind_{n,A}⟧ := R_{ι,ρ}` with `ρ := τ(A) ≠ *`
- `⟦efq_X⟧ := dummy^ν` (and `efqTerm ν dummy ρ` for general `efq_A` with `τ(A) = some ρ`). -/
def extractRaw (ν : Ty) (dummy : Term) : ProofTerm → Option Term
  | .assump u => assumpRealizerTerm ν u
  | .indBool _ A =>
      (tau ν A).map (fun ρ => .const (.recBool ρ))
  | .indNat _ A =>
      (tau ν A).map (fun ρ => .const (.recNat ρ))
  | .axTrue => none
  | .axFalse A =>
      (tau ν A).map (fun ρ => efqTerm ν dummy ρ)
  | .efq A =>
      (tau ν A).map (fun ρ => efqTerm ν dummy ρ)
  | .lamAssump u M =>
      match tau ν u.formula with
      | none => extractRaw ν dummy M
      | some ρ => (extractRaw ν dummy M).map (fun body => .lam ⟨u.id, ρ⟩ body)
  | .appAssump M N =>
      match extractRaw ν dummy M, extractRaw ν dummy N with
      | none, _ => none
      | some m, none => some m
      | some m, some n => some (.app m n)
  | .lamTerm x M =>
      (extractRaw ν dummy M).map (fun body => .lam x body)
  | .appTerm M t =>
      (extractRaw ν dummy M).map (fun body => .app body t)

/-- Section 4 (pp. 11–12): Extracted program `⟦M⟧` of a derivation `M` of formula `A`:
returns `none` (`ε`) if `τ(A) = *`, and `extractRaw ν dummy M` if `τ(A) ≠ *`. -/
def extractProgram (ν : Ty) (dummy : Term) (M : ProofTerm) (A : Formula) : Option Term :=
  match tau ν A with
  | none => none
  | some _ => extractRaw ν dummy M

/-- Comprehension term `A := λy^ν A₀` with an `L`-formula `A₀` (Section 4, p. 12). -/
structure CompTerm (ν : Ty) where
  var : Var
  body : Formula
  var_ty : var.ty = ν
  body_isL : isLFormula body = true
  body_wt : FormulaWellTyped body

namespace CompTerm

/-- Apply a comprehension term `A(r) := A₀[y^ν := r]` (Section 4, p. 12). -/
def apply {ν : Ty} (comp : CompTerm ν) (r : Term) : Formula :=
  substFormula comp.body comp.var r

end CompTerm

/-- Fresh variable id above `A`, `B`, `comp.body`, and `r`. -/
def freshMrVarId {ν : Ty} (comp : CompTerm ν) (r : Option Term) (A B : Formula) : Nat :=
  let rMax := match r with | none => 0 | some t => maxVarIdTerm t
  Nat.max
    (Nat.max (maxVarIdFormula A) (maxVarIdFormula B))
    (Nat.max (maxVarIdFormula comp.body) (Nat.max comp.var.id rMax)) + 1

/-- Section 4 (p. 12): Modified realizability formula `r mr_A A` (`mrFormula ν comp r A`),
where `r` is `some t` if `τ(A) = some ρ`, or `none` (`ε`) if `τ(A) = *`:
- `r mr_A X = A(r)`
- `r mr_A P = P` for atomic `L`-formulas `P`
- `r mr_A ∀x A = ∀x. ε mr_A A` if `τ(A) = *`, else `∀x. (r x) mr_A A`
- `r mr_A (A → B) =`:
  - `ε mr_A A → r mr_A B` if `τ(A) = *`
  - `∀x. x mr_A A → ε mr_A B` if `τ(A) ≠ * = τ(B)`
  - `∀x. x mr_A A → (r x) mr_A B` if `τ(A) ≠ *` and `τ(B) ≠ *`. -/
def mrFormula (ν : Ty) (comp : CompTerm ν) (r : Option Term) : Formula → Formula
  | .varX =>
      match r with
      | some t => comp.apply t
      | none => comp.apply (defaultTerm ν)
  | .bot => .bot
  | .atom t => .atom t
  | .all x A =>
      match tau ν A with
      | none => .all x (mrFormula ν comp none A)
      | some _ =>
          let rx := r.map (fun t => .app t (.var x))
          .all x (mrFormula ν comp rx A)
  | .imp A B =>
      match tau ν A, tau ν B with
      | none, _ =>
          .imp (mrFormula ν comp none A) (mrFormula ν comp r B)
      | some τA, none =>
          let x : Var := ⟨freshMrVarId comp r A B, τA⟩
          .all x (.imp (mrFormula ν comp (some (.var x)) A) (mrFormula ν comp none B))
      | some τA, some _ =>
          let x : Var := ⟨freshMrVarId comp r A B, τA⟩
          let rx := r.map (fun t => .app t (.var x))
          .all x (.imp (mrFormula ν comp (some (.var x)) A) (mrFormula ν comp rx B))

/-- Conjunction of hypotheses `(G₁ → X) → ⋯ → (Gₘ → X) → X` written `(G⃗ → X) → X`
in Lemma 3.2, Theorem 3.3, and Theorem 5.1 (pp. 9, 12–13):
note that in the paper `∀y⃗(G⃗ → ⊥) → ⊥` abbreviates `∀y⃗(G₁ → ⋯ → Gₘ → ⊥) → ⊥`. -/
def goalImpliesBot (ys : List Var) (Gs : List Formula) : Formula :=
  Formula.neg (Formula.allMany ys (Formula.impMany Gs .bot))

/-- Formula `∀y⃗(G⃗ → X) → X` (Theorem 3.3, p. 9). -/
def goalImpliesX (ys : List Var) (Gs : List Formula) : Formula :=
  .imp (Formula.allMany ys (Formula.impMany Gs .varX)) .varX

/-- Section 5 convention (pp. 12–13): apply goal realizer `s : Term` to `w : Option Var`
(omitted if `w = none`, i.e. of type `*`) and then to `v : Term`. -/
def applyGoalRealizer (s : Term) (w : Option Var) (v : Term) : Term :=
  match w with
  | none => .app s v
  | some wVar => .app (.app s (.var wVar)) v

/-- Section 5 convention (p. 12): Multi-variable abstraction `λw₁ ... wₘ. t` where variables
of type `*` (`none`) are omitted (`λw^* t` stands for `t`). -/
def optLamVars : List (Option Var) → Term → Term
  | [], t => t
  | none :: ws, t => optLamVars ws t
  | some w :: ws, t => .lam w (optLamVars ws t)

/-- Combined realizer `s := λy⃗ λw⃗. s₁ w₁ (... (sₘ wₘ (r y⃗)) ...)` in Theorem 5.1 (p. 13),
using the Section 5 `*`-aware conventions (`applyGoalRealizer`, `optLamVars`) for variables of type `*`. -/
def buildGoalCombinatorTerm
    (ys : List Var) (ws : List (Option Var)) (ss : List Term) (r : Term) : Term :=
  let ry : Term := Term.appMany r (ys.map Term.var)
  let body : Term := (List.zip ss ws).foldr
    (fun (si, wi) acc => applyGoalRealizer si wi acc)
    ry
  Term.lamMany ys (optLamVars ws body)

/-- Section 5 convention (p. 12): Apply `p : Term` to `t₁, ..., tₙ : List (Option Term)`,
where arguments of type `*` (`none`) are omitted (`p t` stands for `p` when `t` has type `*`). -/
def applyOptTerms : Term → List (Option Term) → Term
  | p, [] => p
  | p, none :: ts => applyOptTerms p ts
  | p, some t :: ts => applyOptTerms (.app p t) ts

/-- Extracted program term `⟦M^X⟧ t₁ ... tₙ s` in Theorem 5.1 (p. 13) and Corollary 5.3 (p. 14). -/
def extractClassicalTerm
    (ν : Ty) (dummy : Term) (M : ProofTerm)
    (ts : List (Option Term)) (s : Term) : Term :=
  let p := (extractRaw ν dummy (substBotProof M)).getD dummy
  .app (applyOptTerms p ts) s

/-- All assumption variables (free or bound) occurring in a derivation `M`. -/
def allAssumpVars : ProofTerm → List AssumpVar
  | .assump u => [u]
  | .indNat _ _ | .indBool _ _ | .axTrue | .axFalse _ | .efq _ => []
  | .lamAssump u M => u :: allAssumpVars M
  | .appAssump M N => allAssumpVars M ++ allAssumpVars N
  | .lamTerm _ M => allAssumpVars M
  | .appTerm M _ => allAssumpVars M

/-- All object variables (free or bound) occurring in a derivation `M`. -/
def allVarsProof : ProofTerm → List Var
  | .assump u => allVarsFormula u.formula
  | .indNat n A => n :: allVarsFormula A
  | .indBool p A => p :: allVarsFormula A
  | .axTrue => []
  | .axFalse A | .efq A => allVarsFormula A
  | .lamAssump u M => allVarsFormula u.formula ++ allVarsProof M
  | .appAssump M N => allVarsProof M ++ allVarsProof N
  | .lamTerm x M => x :: allVarsProof M
  | .appTerm M t => allVarsProof M ++ allVarsTerm t

/-- Variable-hygiene and well-typedness condition for program extraction from a derivation `M`
with respect to `dummy : Term` of type `ν` and comprehension term `comp : CompTerm ν` (Section 4, pp. 11–12):
- `dummy` is a closed term of type `ν`,
- assumption variable IDs in `M` are disjoint from object variable IDs in `M` and `comp`,
- assumption variables in `M` with the same `id` carry the same formula,
- object variables bound in `M` are disjoint from the free variables of `comp.body`. -/
def AdmissibleForExtraction (ν : Ty) (dummy : Term) (comp : CompTerm ν) (M : ProofTerm) : Prop :=
  HasType dummy ν ∧
  IsClosedTerm dummy ∧
  (∀ u ∈ allAssumpVars M, ∀ x ∈ allVarsProof M ++ allVarsFormula comp.body, u.id ≠ x.id) ∧
  (∀ u₁ ∈ allAssumpVars M, ∀ u₂ ∈ allAssumpVars M, u₁.id = u₂.id → u₁.formula = u₂.formula) ∧
  (∀ x ∈ allVarsProof M, x = comp.var ∨ x ∉ freeVarsFormula comp.body)

end BBS2002


