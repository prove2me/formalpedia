-- Prove2me | Definitions.Def_ABHS2004_Realizability
-- name    : ABHS2004_Realizability
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:31.253413+00:00
-- url     : https://prove2.me/theorems/4820983d-c521-416a-afd7-67121134b395
-- title:
--   Section 4: Clean Types, Extracted Programs, and Modified Realizability
-- statement:
--   Formalizes Section 4 of Aehlig, Berger, Hofmann, and Schwichtenberg (2004): the type-cleaning map `τ(A)` (`cleanFormulaTy`, `cleanTy`), Harrop formulas (`IsHarropFormula`), program extraction `⟦M⟧` (`extractProgram`, Definition 4.3) mapping natural deduction derivations `M` to terms of the affine λ-calculus (with `⟦Ind_A⟧ = it_{τ(A)}`), and the modified realizability relation `r mr A` (`Realizes`, Definition 4.5).
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Section 4, pp. 18-23.

import Definitions.Def_ABHS2004_Arithmetic

/-!
# Modified Realizability and Program Extraction (ABHS 2004, Section 4)

Source: Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg,
"An arithmetic for non-size-increasing polynomial-time computation",
*Theoretical Computer Science* 318(1–2), 2004, pp. 3–27, Section 4 (pp. 20–26).

This module formalizes:
- Section 4.1: Modified realizability `mr r A` (`r mr A`, Definition 4.1, p. 20).
- Section 4.2: Extracted terms `extractProof M` (`⟦M⟧`, Definition 4.3, pp. 20–21) and
  term cleaning `cleanTerm` / `extractCleaned M` (`⟦M⟧^c := c(⟦M⟧)`, Definition 4.4, p. 22).
- Section 4.3: Context extraction `extractCtx`, `extractCleanCtx`, and realizability
  assumptions `mrAssumptions` for Theorem 4.7 (Soundness of typing, p. 23), Corollary 4.8
  (Underivability, p. 23), Theorem 4.9 (Soundness of modified realizability, p. 24),
  and Corollary 4.11 (Main polytime extraction theorem, p. 26).
-/

namespace ABHS2004

/-- Fresh variable id above a term and two formulas, used when introducing a bound variable
in `mr r (A → B)` and `mr r (A ∨ B)` (Definition 4.1, p. 20). -/
def freshMrVarId (r : Term) (A B : Formula) : Nat :=
  Nat.max (maxVarId r) (Nat.max (maxVarIdFormula A) (maxVarIdFormula B)) + 1

/-- Definition 4.1 (Modified realizability `r mr A`, p. 20):
By induction on `A` we define a formula `mr r A` for arbitrary `r^{τ(A)}`.
- `r mr E_ρ(s) := (r =_ρ s)`
- `r mr P(s⃗) := P(s⃗)`
- `r mr ∀x A := ∀x. r mr A` (renaming `x` if `x ∈ FV(r)`)
- `r mr ∃x A := ∃x. r mr A` (renaming `x` if `x ∈ FV(r)`)
- `r mr (A → B) := ∀x. x mr A → r x mr B`
- `r mr (A ⊗ B) := π₀(r) mr A ∧ π₁(r) mr B`
- `r mr (A ∧ B) := fst r mr A ∧ snd r mr B`
- `r mr (A ∨ B) := (∀x. r = inl x → x mr A) ∧ (∀y. r = inr y → y mr B)`. -/
def mr (r : Term) (A : Formula) : Formula :=
  match A with
  | .existPred ρ s => Formula.eqForm ρ r s
  | .pred P ss => .pred P ss
  | .all x B =>
      if x ∈ freeVarOccurrences r then
        let freshId := Nat.max (maxVarId r) (Nat.max (maxVarIdFormula B) x.id) + 1
        let x' : Var := ⟨freshId, x.ty⟩
        .all x' (mr r (renameFreeVarFormula B x x'))
      else
        .all x (mr r B)
  | .ex x B =>
      if x ∈ freeVarOccurrences r then
        let freshId := Nat.max (maxVarId r) (Nat.max (maxVarIdFormula B) x.id) + 1
        let x' : Var := ⟨freshId, x.ty⟩
        .ex x' (mr r (renameFreeVarFormula B x x'))
      else
        .ex x (mr r B)
  | .imp B C =>
      let x : Var := ⟨freshMrVarId r B C, tau B⟩
      .all x (.imp (mr (.var x) B) (mr (.app r (.var x)) C))
  | .tensor B C =>
      let ρ := tau B
      let σ := tau C
      .conj (mr (Term.pi0 ρ σ r) B) (mr (Term.pi1 ρ σ r) C)
  | .conj B C =>
      let ρ := tau B
      let σ := tau C
      .conj
        (mr (.app (.const (.fst ρ σ)) r) B)
        (mr (.app (.const (.snd ρ σ)) r) C)
  | .disj B C =>
      let ρ := tau B
      let σ := tau C
      let baseId := freshMrVarId r B C
      let x : Var := ⟨baseId, ρ⟩
      let y : Var := ⟨baseId + 1, σ⟩
      let inlx := Term.app (.const (.inl ρ σ)) (.var x)
      let inry := Term.app (.const (.inr ρ σ)) (.var y)
      .conj
        (.all x (.imp (Formula.eqForm (.sum ρ σ) r inlx) (mr (.var x) B)))
        (.all y (.imp (Formula.eqForm (.sum ρ σ) r inry) (mr (.var y) C)))
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

/-- Canonical closed term `ε^ρ` for types whose cleaned type is `U` (or built from dummy terms
for Harrop axiom realizers in Section 4.2, p. 21). -/
def dummyTerm : Ty → Term
  | .unit => .const .eps
  | .diamond => .var ⟨0, .diamond⟩
  | .list ρ => .const (.nil ρ)
  | .lolli ρ σ =>
      let x : Var := ⟨0, ρ⟩
      .lam x (dummyTerm σ)
  | .tensor ρ σ =>
      .app (.app (.const (.tensorIntro ρ σ)) (dummyTerm ρ)) (dummyTerm σ)
  | .prod ρ σ =>
      let u : Var := ⟨0, .unit⟩
      .app (.app (.app (.const (.prodIntro ρ σ .unit))
        (.lam u (dummyTerm ρ)))
        (.lam u (dummyTerm σ)))
        (.const .eps)
  | .sum ρ σ =>
      .app (.const (.inl ρ σ)) (dummyTerm ρ)

/-- Section 4.2 (p. 20): For each assumption variable `u^A` we choose a unique term variable
`x_{u^A}` of type `τ(A)` (using odd variable ids `2 * u.id + 1` to keep them distinct). -/
def assumpRealizerVar (u : AssumpVar) : Var :=
  ⟨2 * u.id + 1, tau u.formula⟩

/-- Definition 4.3 (Extracted terms for core axioms `⟦A⟧`, p. 21). -/
def extractAxiom (ax : CoreAxiom) : Term :=
  match ax with
  | .ax3 A B C => .const (.prodIntro (tau A) (tau B) (tau C))
  | .ax4_left A₀ A₁ => .const (.fst (tau A₀) (tau A₁))
  | .ax4_right A₀ A₁ => .const (.snd (tau A₀) (tau A₁))
  | .ax5 A B => .const (.tensorIntro (tau A) (tau B))
  | .ax6 A B C => .const (.tensorElim (tau A) (tau B) (tau C))
  | .ax7_left A₀ A₁ => .const (.inl (tau A₀) (tau A₁))
  | .ax7_right A₀ A₁ => .const (.inr (tau A₀) (tau A₁))
  | .ax8 A B C =>
      let ρ := tau A
      let σ := tau B
      let τ := tau C
      let z₁ : Var := ⟨0, .prod (.lolli ρ τ) (.lolli σ τ)⟩
      let z₂ : Var := ⟨1, .sum ρ σ⟩
      .lam z₁ (.lam z₂ (.app (.app (.const (.sumElim ρ σ τ)) (.var z₂)) (.var z₁)))
  | .ax9 _ A => Term.idTerm (tau A)
  | .ax10 _ A B =>
      let x : Var := ⟨0, tau A⟩
      let f : Var := ⟨1, .lolli (tau A) (tau B)⟩
      .lam x (.lam f (.app (.var f) (.var x)))
  | .ax16 ρ _ _ => Term.idTerm ρ
  | .ax20_imp ρ σ _ _ => Term.idTerm (.lolli ρ σ)
  | .ax20_mpr ρ σ _ _ => Term.idTerm (.lolli ρ σ)
  | .ax21_imp ρ σ _ => Term.idTerm (.prod ρ σ)
  | .ax21_mpr ρ σ _ => Term.idTerm (.prod ρ σ)
  | .ax22 c => .const c
  | .ax23 ρ σ _ _ _ A =>
      let τ := tau A
      let f : Var := ⟨0, .lolli ρ (.lolli σ τ)⟩
      let z : Var := ⟨1, .tensor ρ σ⟩
      .lam f (.lam z (.app (.app (.const (.tensorElim ρ σ τ)) (.var z)) (.var f)))
  | .ax24 ρ σ _ _ _ A =>
      let τ := tau A
      let z₁ : Var := ⟨0, .prod (.lolli ρ τ) (.lolli σ τ)⟩
      let z₂ : Var := ⟨1, .sum ρ σ⟩
      .lam z₁ (.lam z₂ (.app (.app (.const (.sumElim ρ σ τ)) (.var z₂)) (.var z₁)))
  | other => dummyTerm (tau other.formula)

/-- Definition 4.3 (Extracted terms `⟦M⟧`, pp. 20–21):
- `⟦u^A⟧ := x_u^{τ(A)}`
- `⟦λu^A M^B⟧ := λx_u^{τ(A)} ⟦M⟧`
- `⟦M^{A→B} N⟧ := ⟦M⟧ ⟦N⟧`
- `⟦λx^ρ M^A⟧ := ⟦M⟧`
- `⟦M^{∀x^ρ A} r⟧ := ⟦M⟧`
- `⟦N^{E_{L(ρ)}(t)} {M}⟧ := ⟦N⟧ {⟦M⟧}`. -/
def extractProof : ProofTerm → Term
  | .assump u => .var (assumpRealizerVar u)
  | .ax c => extractAxiom c
  | .lamAssump u M => .lam (assumpRealizerVar u) (extractProof M)
  | .lamTerm _ M => extractProof M
  | .appProof M N => .app (extractProof M) (extractProof N)
  | .appTerm M _ => extractProof M
  | .ind N M => .iter (extractProof N) (extractProof M)

/-- Intrinsic type inference `inferType r` for raw terms (since variables and constants carry
their explicit types in `ABHS2004`). -/
def inferType : Term → Option Ty
  | .var x => some x.ty
  | .const c => some c.ty
  | .lam x r =>
      match inferType r with
      | some σ => some (.lolli x.ty σ)
      | none => none
  | .app r _ =>
      match inferType r with
      | some (.lolli _ σ) => some σ
      | _ => none
  | .iter _ s =>
      match inferType s with
      | some (.lolli .diamond (.lolli _ (.lolli τ _))) => some (.lolli τ τ)
      | _ => none

/-- Definition 4.4 (p. 22): Cleaned variable `x̃^{c(ρ)}` associated with `x^ρ`. -/
def cleanVar (x : Var) : Var :=
  ⟨x.id, cleanTy x.ty⟩

/-- Definition 4.4 (p. 22): Cleaning `c(c)` for constants `c^ρ`. -/
def cleanConst (c : Const) : Term :=
  if cleanTy c.ty == .unit then
    .const .eps
  else
    match c with
    | .eps => .const .eps
    | .nil ρ => .const (.nil (cleanTy ρ))
    | .cons ρ =>
        let cρ := cleanTy ρ
        if cρ == .unit then
          let d : Var := ⟨0, .diamond⟩
          let l : Var := ⟨1, Ty.nat⟩
          .lam d (.lam l (Term.succNat (.var d) (.var l)))
        else
          .const (.cons cρ)
    | .tensorIntro ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cρ == .unit then Term.idTerm cσ
        else if cσ == .unit then Term.idTerm cρ
        else .const (.tensorIntro cρ cσ)
    | .tensorElim ρ σ τ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        let cτ := cleanTy τ
        if cρ == .unit && cσ == .unit then
          Term.idTerm cτ
        else if cρ == .unit then
          let x : Var := ⟨0, cσ⟩
          let f : Var := ⟨1, .lolli cσ cτ⟩
          .lam x (.lam f (.app (.var f) (.var x)))
        else if cσ == .unit then
          let x : Var := ⟨0, cρ⟩
          let f : Var := ⟨1, .lolli cρ cτ⟩
          .lam x (.lam f (.app (.var f) (.var x)))
        else
          .const (.tensorElim cρ cσ cτ)
    | .prodIntro ρ σ τ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        let cτ := cleanTy τ
        if cρ == .unit then
          if cτ == .unit then Term.idTerm cσ
          else
            let g : Var := ⟨0, .lolli cτ cσ⟩
            let z : Var := ⟨1, cτ⟩
            .lam g (.lam z (.app (.var g) (.var z)))
        else if cσ == .unit then
          if cτ == .unit then Term.idTerm cρ
          else
            let f : Var := ⟨0, .lolli cτ cρ⟩
            let z : Var := ⟨1, cτ⟩
            .lam f (.lam z (.app (.var f) (.var z)))
        else if cτ == .unit then
          let x : Var := ⟨0, cρ⟩
          let y : Var := ⟨1, cσ⟩
          let u₁ : Var := ⟨2, .unit⟩
          let u₂ : Var := ⟨3, .unit⟩
          .lam x (.lam y
            (.app (.app (.app (.const (.prodIntro cρ cσ .unit))
              (.lam u₁ (.var x)))
              (.lam u₂ (.var y)))
              (.const .eps)))
        else
          .const (.prodIntro cρ cσ cτ)
    | .fst ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cσ == .unit then Term.idTerm cρ
        else .const (.fst cρ cσ)
    | .snd ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cρ == .unit then Term.idTerm cσ
        else .const (.snd cρ cσ)
    | .inl ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cρ == .unit then .app (.const (.inl .unit cσ)) (.const .eps)
        else .const (.inl cρ cσ)
    | .inr ρ σ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        if cσ == .unit then .app (.const (.inr cρ .unit)) (.const .eps)
        else .const (.inr cρ cσ)
    | .sumElim ρ σ τ =>
        let cρ := cleanTy ρ
        let cσ := cleanTy σ
        let cτ := cleanTy τ
        let branchL := if cρ == .unit then cτ else .lolli cρ cτ
        let branchR := if cσ == .unit then cτ else .lolli cσ cτ
        if cρ == .unit && cσ == .unit then
          let s : Var := ⟨0, .sum .unit .unit⟩
          let p : Var := ⟨1, .prod cτ cτ⟩
          let u₁ : Var := ⟨2, .unit⟩
          let u₂ : Var := ⟨3, .unit⟩
          let q : Var := ⟨4, .prod cτ cτ⟩
          let adaptedPair :=
            Term.app
              (.app (.app (.const (.prodIntro (.lolli .unit cτ) (.lolli .unit cτ) (.prod cτ cτ)))
                (.lam q (.lam u₁ (.app (.const (.fst cτ cτ)) (.var q)))))
                (.lam q (.lam u₂ (.app (.const (.snd cτ cτ)) (.var q)))))
              (.var p)
          .lam s (.lam p (.app (.app (.const (.sumElim .unit .unit cτ)) (.var s)) adaptedPair))
        else if cρ == .unit then
          let s : Var := ⟨0, .sum .unit cσ⟩
          let p : Var := ⟨1, .prod branchL branchR⟩
          let u₁ : Var := ⟨2, .unit⟩
          let q : Var := ⟨3, .prod branchL branchR⟩
          let adaptedPair :=
            Term.app
              (.app (.app (.const (.prodIntro (.lolli .unit cτ) branchR (.prod branchL branchR)))
                (.lam q (.lam u₁ (.app (.const (.fst branchL branchR)) (.var q)))))
                (.lam q (.app (.const (.snd branchL branchR)) (.var q))))
              (.var p)
          .lam s (.lam p (.app (.app (.const (.sumElim .unit cσ cτ)) (.var s)) adaptedPair))
        else if cσ == .unit then
          let s : Var := ⟨0, .sum cρ .unit⟩
          let p : Var := ⟨1, .prod branchL branchR⟩
          let u₂ : Var := ⟨2, .unit⟩
          let q : Var := ⟨3, .prod branchL branchR⟩
          let adaptedPair :=
            Term.app
              (.app (.app (.const (.prodIntro branchL (.lolli .unit cτ) (.prod branchL branchR)))
                (.lam q (.app (.const (.fst branchL branchR)) (.var q))))
                (.lam q (.lam u₂ (.app (.const (.snd branchL branchR)) (.var q)))))
              (.var p)
          .lam s (.lam p (.app (.app (.const (.sumElim cρ .unit cτ)) (.var s)) adaptedPair))
        else
          .const (.sumElim cρ cσ cτ)

/-- Definition 4.4 (Cleaning of terms `c(r)`, p. 22). -/
def cleanTerm (r : Term) : Term :=
  match inferType r with
  | some ρ =>
      if cleanTy ρ == .unit then
        .const .eps
      else
        match r with
        | .var x => .var (cleanVar x)
        | .const c => cleanConst c
        | .lam x body =>
            if cleanTy x.ty == .unit then
              cleanTerm body
            else
              .lam (cleanVar x) (cleanTerm body)
        | .app t s =>
            match inferType s with
            | some σ =>
                if cleanTy σ == .unit then
                  cleanTerm t
                else
                  .app (cleanTerm t) (cleanTerm s)
            | none => .app (cleanTerm t) (cleanTerm s)
        | .iter t s => .iter (cleanTerm t) (cleanTerm s)
  | none => r

/-- Section 4.3 (p. 23): Cleaned extracted term `⟦M⟧^c := c(⟦M⟧)`. -/
def extractCleaned (M : ProofTerm) : Term :=
  cleanTerm (extractProof M)

/-- Section 4.3 (p. 23): Uncleaned context extraction `⟦Π⟧ := {x_u^{τ(A)} | u^A ∈ Π}`. -/
def extractCtx (Δ : ProofContext) : List Var :=
  Δ.map assumpRealizerVar

/-- Section 4.3 (p. 23): Cleaned context extraction
`⟦Π⟧^c := {x̃_u^{τ^c(A)} | u^A ∈ Π, τ^c(A) ≠ U}`. -/
def extractCleanCtx (Δ : ProofContext) : List Var :=
  (Δ.filter (fun u => tauClean u.formula != .unit)).map (fun u => cleanVar (assumpRealizerVar u))

/-- Section 4.3 (Theorem 4.9, p. 24): Realizability context mapping each assumption `u^B ∈ Π`
to an assumption variable `ũ^{x_u mr B}`. -/
def mrContext (Δ : ProofContext) : ProofContext :=
  Δ.map (fun u => ⟨u.id, mr (.var (assumpRealizerVar u)) u.formula⟩)

/-- A derivation `M` (with passive context `Π` and active context `Γ`) is almost closed
if every assumption in `Π ∪ Γ` has cleaned realizer type `⋄` or `U` (in particular, when
`Π = []` and `Γ = []`, or when `⟦Γ⟧^c` contains only variables of type `⋄`, Corollary 4.11, p. 26). -/
def IsAlmostClosedDerivation (Δ Γ : ProofContext) : Prop :=
  (∀ v ∈ extractCleanCtx Δ, v.ty = .diamond) ∧
  (∀ v ∈ extractCleanCtx Γ, v.ty = .diamond)

/-- Freshness condition from Section 4.2 (p. 20: "For each variable `u^A` we choose a unique
variable `x_{u^A}` of type `τ(A)` that is sufficiently different to all variables used so far"):
all assumption variables in `Δ`, `Γ`, and `M` have pairwise distinct ids when their formulas
differ, and their chosen realizer variables `x_{u^A}` do not occur free in `A` or in the
formulas of `Δ ∪ Γ`. -/
def FreshRealizerVars (Δ Γ : ProofContext) (M : ProofTerm) (A : Formula) : Prop :=
  let allU := Δ ++ Γ ++ allAssumpVars M
  (∀ u ∈ allU, ∀ v ∈ allU, u.id = v.id → u = v) ∧
  (∀ u ∈ allU, assumpRealizerVar u ∉ freeVarsFormula A) ∧
  (∀ u ∈ allU, ∀ w ∈ Δ ++ Γ, assumpRealizerVar u ∉ freeVarsFormula w.formula)

end ABHS2004


