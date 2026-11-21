-- Prove2me | Definitions.Def_ABHS2004V2_Realizability
-- name    : ABHS2004V2_Realizability
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T05:20:38.710172+00:00
-- url     : https://prove2.me/theorems/88098487-0397-41c5-bd31-7423cc37e879
-- title:
--   Modified realizability, extraction, and type-directed cleaning
-- statement:
--   The formula of modified realizability, program extraction from proofs, and type-directed cleaning. Axiom 16 uses a function that accepts its unit premise. A cleaned list-iterator step keeps the interface required by the list type. The cleaned-data relation relates canonical input and output representations.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Section 4, Definitions 4.1, 4.3 and 4.4. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_Arithmetic
import Mathlib.Data.Nat.Pairing

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

namespace ABHS2004V2

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
  | .ax16 ρ _ _ =>
      -- The equality premise has realizer type U. The cleaned realizer is the identity.
      .lam ⟨1, .unit⟩ (Term.idTerm ρ)
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

/-- Infer a raw term's weak type by checking the domain of each application and all
three interfaces of each iterator step. -/
def inferType : Term → Option Ty
  | .var x => some x.ty
  | .const c => some c.ty
  | .lam x r =>
      match inferType r with
      | some σ => some (.lolli x.ty σ)
      | none => none
  | .app r s =>
      match inferType r, inferType s with
      | some (.lolli ρ σ), some τ => if ρ == τ then some σ else none
      | _, _ => none
  | .iter r s =>
      match inferType r, inferType s with
      | some (.list ρ), some (.lolli .diamond (.lolli σ (.lolli τ υ))) =>
          if ρ == σ && τ == υ then some (.lolli τ τ) else none
      | _, _ => none

private theorem pair_between_squares (a b : Nat) :
    let m := max a b
    m * m ≤ Nat.pair a b ∧ Nat.pair a b < (m + 1) * (m + 1) := by
  dsimp
  rcases Nat.lt_or_ge a b with hab | hba
  · simp only [Nat.pair, if_pos hab, Nat.max_eq_right (Nat.le_of_lt hab),
      Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc]
    have ha : a < b + (b + 1) := Nat.lt_of_lt_of_le hab (Nat.le_add_right b _)
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left ha _⟩
  · simp only [Nat.pair, if_neg (Nat.not_lt_of_ge hba), Nat.max_eq_left hba,
      Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one, Nat.add_assoc]
    have hb : b < a + 1 := Nat.lt_succ_of_le hba
    exact ⟨Nat.le_add_right _ _, Nat.add_lt_add_left (Nat.add_lt_add_left hb _) _⟩

private theorem pair_coordinates {a b c d : Nat} (h : Nat.pair a b = Nat.pair c d) :
    a = c ∧ b = d := by
  obtain ⟨alo, ahi⟩ := pair_between_squares a b
  obtain ⟨clo, chi⟩ := pair_between_squares c d
  have max_eq : max a b = max c d := by
    rcases Nat.lt_trichotomy (max a b) (max c d) with hlt | heq | hgt
    · have hstep : max a b + 1 ≤ max c d := Nat.succ_le_of_lt hlt
      have hbad := Nat.lt_of_lt_of_le ahi (Nat.le_trans (Nat.mul_le_mul hstep hstep) clo)
      rw [h] at hbad
      exact False.elim (Nat.lt_irrefl _ hbad)
    · exact heq
    · have hstep : max c d + 1 ≤ max a b := Nat.succ_le_of_lt hgt
      have hbad := Nat.lt_of_lt_of_le chi (Nat.le_trans (Nat.mul_le_mul hstep hstep) alo)
      rw [← h] at hbad
      exact False.elim (Nat.lt_irrefl _ hbad)
  rcases Nat.lt_or_ge a b with hab | hba <;> rcases Nat.lt_or_ge c d with hcd | hdc
  · rw [Nat.max_eq_right (Nat.le_of_lt hab), Nat.max_eq_right (Nat.le_of_lt hcd)] at max_eq
    subst d
    simp only [Nat.pair, if_pos hab, if_pos hcd] at h
    exact ⟨Nat.add_left_cancel h, rfl⟩
  · rw [Nat.max_eq_right (Nat.le_of_lt hab), Nat.max_eq_left hdc] at max_eq
    subst c
    simp only [Nat.pair, if_pos hab, if_neg (Nat.not_lt_of_ge hdc), Nat.add_assoc] at h
    have ha := Nat.add_left_cancel h
    exact False.elim (Nat.not_le_of_gt hab (ha ▸ Nat.le_add_right b d))
  · rw [Nat.max_eq_left hba, Nat.max_eq_right (Nat.le_of_lt hcd)] at max_eq
    subst d
    simp only [Nat.pair, if_neg (Nat.not_lt_of_ge hba), if_pos hcd, Nat.add_assoc] at h
    have hc := Nat.add_left_cancel h
    exact False.elim (Nat.not_le_of_gt hcd (hc ▸ Nat.le_add_right a b))
  · rw [Nat.max_eq_left hba, Nat.max_eq_left hdc] at max_eq
    subst c
    simp only [Nat.pair, if_neg (Nat.not_lt_of_ge hba), if_neg (Nat.not_lt_of_ge hdc)] at h
    exact ⟨rfl, Nat.add_left_cancel h⟩


private theorem pair_eq_iff {a b c d : Nat} :
    Nat.pair a b = Nat.pair c d ↔ a = c ∧ b = d :=
  ⟨pair_coordinates, by rintro ⟨rfl, rfl⟩; rfl⟩

private def typeCode : Ty → Nat
  | .unit => Nat.pair 0 0
  | .diamond => Nat.pair 1 0
  | .list ρ => Nat.pair 2 (typeCode ρ)
  | .lolli ρ σ => Nat.pair 3 (Nat.pair (typeCode ρ) (typeCode σ))
  | .tensor ρ σ => Nat.pair 4 (Nat.pair (typeCode ρ) (typeCode σ))
  | .prod ρ σ => Nat.pair 5 (Nat.pair (typeCode ρ) (typeCode σ))
  | .sum ρ σ => Nat.pair 6 (Nat.pair (typeCode ρ) (typeCode σ))

private theorem typeCode_injective : Function.Injective typeCode := by
  intro ρ σ h
  induction ρ generalizing σ <;> cases σ <;> simp [typeCode, -Nat.pair_eq_pair, pair_eq_iff] at h ⊢
  case list.list ρ ih σ => exact ih h
  all_goals
    rcases h with ⟨h₁, h₂⟩
    constructor <;> solve_by_elim

/-- Definition 4.4. Assign different names to distinct typed variables even when their
types coalesce under cleaning. -/
def cleanVar (x : Var) : Var :=
  ⟨Nat.pair x.id (typeCode x.ty), cleanTy x.ty⟩

theorem cleanVar_injective : Function.Injective cleanVar := by
  intro x y h
  obtain ⟨idEq, tyCodeEq⟩ := pair_coordinates (congrArg Var.id h)
  cases x
  cases y
  congr
  exact typeCode_injective tyCodeEq

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

/-- Adapt a cleaned step of type `⋄ ⊸ τ ⊸ τ` to the iterator over unit-valued elements.
Fresh names keep the free variables of the step intact. -/
def restoreUnitIteratorArg (step : Term) : Term :=
  let d : Var := ⟨maxVarId step + 1, .diamond⟩
  let u : Var := ⟨maxVarId step + 2, .unit⟩
  .lam d (.lam u (.app step (.var d)))

/-- Definition 4.4 (Cleaning of terms `c(r)`, p. 22). The raw iterator keeps its element
argument when the element type cleans to unit. -/
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
        | .iter t s =>
            let step := cleanTerm s
            match inferType t with
            | some (.list σ) =>
                .iter (cleanTerm t)
                  (if cleanTy σ == .unit then restoreUnitIteratorArg step else step)
            | _ => .iter (cleanTerm t) step
  | none => r

/-- Section 4.3 (p. 23): Cleaned extracted term `⟦M⟧^c := c(⟦M⟧)`. -/
def extractCleaned (M : ProofTerm) : Term :=
  cleanTerm (extractProof M)

/-- A canonical tensor of cleaned data, erasing a unit component according to
Definition 3.4. -/
def cleanedDataTensor (ρ σ : Ty) (r s : Term) : Term :=
  if cleanTy σ == .unit then r
  else if cleanTy ρ == .unit then s
  else .app (.app (.const (.tensorIntro (cleanTy ρ) (cleanTy σ))) r) s

/-- Canonical encoding of a data object after cleaning (Remark 4.5). This relation
relates constructor forms directly, so the encoded data are canonical even when
cleaning a constructor application introduces an administrative redex. -/
inductive CleansData : Ty → Term → Term → Prop where
  | unit : CleansData .unit (.const .eps) (.const .eps)
  | tensor {ρ σ : Ty} {r r' s s' : Term} :
      CleansData ρ r r' → CleansData σ s s' →
      CleansData (.tensor ρ σ) (.app (.app (.const (.tensorIntro ρ σ)) r) s)
        (cleanedDataTensor ρ σ r' s')
  | inl {ρ σ : Ty} {r r' : Term} :
      CleansData ρ r r' →
      CleansData (.sum ρ σ) (.app (.const (.inl ρ σ)) r)
        (.app (.const (.inl (cleanTy ρ) (cleanTy σ))) r')
  | inr {ρ σ : Ty} {s s' : Term} :
      CleansData σ s s' →
      CleansData (.sum ρ σ) (.app (.const (.inr ρ σ)) s)
        (.app (.const (.inr (cleanTy ρ) (cleanTy σ))) s')
  | nil (ρ : Ty) :
      CleansData (.list ρ) (.const (.nil ρ)) (.const (.nil (cleanTy ρ)))
  | cons {ρ : Ty} (d : Var) (hd : d.ty = .diamond) {r r' rs rs' : Term} :
      CleansData ρ r r' → CleansData (.list ρ) rs rs' →
      CleansData (.list ρ) (.app (.app (.app (.const (.cons ρ)) (.var d)) r) rs)
        (.app (.app (.app (.const (.cons (cleanTy ρ))) (.var (cleanVar d))) r') rs')

/-- Clean each input object, omitting arguments whose cleaned type is unit. -/
inductive CleansDataInputs : List Ty → List Term → List Term → Prop where
  | nil : CleansDataInputs [] [] []
  | cons {ρ : Ty} {ρs : List Ty} {r r' : Term} {rs rs' : List Term} :
      CleansData ρ r r' → CleansDataInputs ρs rs rs' →
      CleansDataInputs (ρ :: ρs) (r :: rs) (if cleanTy ρ == .unit then rs' else r' :: rs')

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

/-- Computational almost-closedness for Corollary 4.11. All free variables in the
cleaned extracted term are diamond tokens. -/
def IsAlmostClosedDerivation (M : ProofTerm) : Prop :=
  IsAlmostClosed (extractCleaned M)

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

end ABHS2004V2


