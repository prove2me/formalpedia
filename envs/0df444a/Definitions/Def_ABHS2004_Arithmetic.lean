-- Prove2me | Definitions.Def_ABHS2004_Arithmetic
-- name    : ABHS2004_Arithmetic
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:19.473132+00:00
-- url     : https://prove2.me/theorems/25cf72d6-0484-4d02-a3f3-4615360888f6
-- title:
--   Section 3: The Arithmetical System N-HA^ω and Natural Deduction
-- statement:
--   Formalizes Section 3 of Aehlig, Berger, Hofmann, and Schwichtenberg (2004): predicates (built from `N`, `=`, and comprehension `{x | A}`), formulas (`∀`, `!∀`, `∃`, `→`, `⊸`) with the linearity restriction on `⊸` and `∀` (only `N` may occur free in the premise of `⊸` or inside `∀`), strictly positive (`s.p.`) occurrences of `N`, the natural deduction system with passive (`Δ`) and linear (`Γ`) proof assumption contexts (Section 3.2), and Equality/Logical/Peano axioms (1)-(24) including binary induction on `s.p.` formulas (Axiom 20).
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Section 3, pp. 14-18.

import Definitions.Def_ABHS2004_TermSystem

/-!
# Linear Arithmetic for Non-Size-Increasing Polytime Computation (ABHS 2004, Section 3)

Source: Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg,
"An arithmetic for non-size-increasing polynomial-time computation",
*Theoretical Computer Science* 318(1–2), 2004, pp. 3–27, Section 3 (pp. 10–19).

This module formalizes:
- Section 3.1: Predicate symbols (`PredSym`), formulas (`Formula`, Definition 3.1),
  abbreviations `bot`, `neg`, `iff` (Remark 3.2), computational content `tau` (Definition 3.3),
  type cleaning `cleanTy` and `tauClean` (Definition 3.4), and Harrop / computationally
  irrelevant formulas `IsHarrop` (Definition 3.5).
- Section 3.2: Assumption variables (`AssumpVar`), core axioms (Definition 3.8, equations
  (3)–(25)), raw proof terms (`ProofTerm`, Definition 3.6), and the two-zone natural
  deduction system `Derives Π Γ M A` (`Π | Γ ⊢ M : A`, Definition 3.7).
-/

namespace ABHS2004

/-- Predicate symbols different from the existence predicates `E_ρ`, including
equality `=_ρ` and arbitrary fixed-arity predicate symbols `P, Q` (Section 3.1, p. 10). -/
inductive PredSym where
  | eq (ρ : Ty) : PredSym
  | rel (id : Nat) (arity : List Ty) : PredSym
  deriving DecidableEq, Repr

/-- Arity (list of argument types) of a predicate symbol. -/
def PredSym.arity : PredSym → List Ty
  | .eq ρ => [ρ, ρ]
  | .rel _ tys => tys

/-- A list of terms `rs` is weakly typed according to the arity `tys` (Section 3.1, p. 10). -/
inductive WeaklyTypedList : List Term → List Ty → Prop where
  | nil : WeaklyTypedList [] []
  | cons {r : Term} {ρ : Ty} {rs : List Term} {ρs : List Ty} :
      WeaklyTyped r ρ →
      WeaklyTypedList rs ρs →
      WeaklyTypedList (r :: rs) (ρ :: ρs)

/-- Definition 3.1 (Formulas, p. 10):
`A, B, C ::= P(r⃗) | E_ρ(r) | A → B | A ⊗ B | A ∧ B | A ∨ B | ∀x^ρ A | ∃x^ρ A`. -/
inductive Formula where
  | pred : PredSym → List Term → Formula
  | existPred : Ty → Term → Formula
  | imp : Formula → Formula → Formula
  | tensor : Formula → Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | all : Var → Formula → Formula
  | ex : Var → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Equality formula `r =_ρ s` (Section 3.1, p. 10). -/
def eqForm (ρ : Ty) (r s : Term) : Formula :=
  .pred (.eq ρ) [r, s]

/-- Remark 3.2 (p. 10): Falsity `⊥ := (tt =_B ff)`. -/
def bot : Formula :=
  eqForm Ty.bool Term.tt Term.ff

/-- Remark 3.2 (p. 10): Negation `¬A := A → ⊥`. -/
def neg (A : Formula) : Formula :=
  .imp A bot

/-- Bi-implication `A ↔ B := (A → B) ∧ (B → A)`. -/
def iffForm (A B : Formula) : Formula :=
  .conj (.imp A B) (.imp B A)

/-- Iterated implication `A₁ → ⋯ → Aₙ → B`. -/
def impMany : List Formula → Formula → Formula
  | [], B => B
  | A :: As, B => .imp A (impMany As B)

/-- Iterated universal quantification `∀ x₁ ... xₙ. A`. -/
def allMany : List Var → Formula → Formula
  | [], A => A
  | x :: xs, A => .all x (allMany xs A)

/-- Iterated existential quantification `∃ x₁ ... xₙ. A`. -/
def exMany : List Var → Formula → Formula
  | [], A => A
  | x :: xs, A => .ex x (exMany xs A)

/-- Relativized universal quantification `∀ x⃗. E(x⃗) → B` (p. 14, 26). -/
def allRel : List Var → Formula → Formula
  | [], B => B
  | x :: xs, B => .all x (.imp (.existPred x.ty (.var x)) (allRel xs B))

/-- Corollary 4.8 (p. 23): The formula `✸ := ∃ p^⋄. E_⋄(p)`. -/
def lozenge : Formula :=
  let p : Var := ⟨0, .diamond⟩
  .ex p (.existPred .diamond (.var p))

end Formula

/-- Free term variables `FV(A)` of a formula `A`. -/
def freeVarsFormula : Formula → List Var
  | .pred _ rs => (rs.foldr (fun r acc => freeVarOccurrences r ++ acc) []).eraseDups
  | .existPred _ r => freeVars r
  | .imp A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .tensor A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .conj A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .disj A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .all x A => (freeVarsFormula A).filter (· != x)
  | .ex x A => (freeVarsFormula A).filter (· != x)

/-- Maximum variable id occurring in a list of terms. -/
def maxVarIdList : List Term → Nat
  | [] => 0
  | r :: rs => Nat.max (maxVarId r) (maxVarIdList rs)

/-- Maximum variable id occurring anywhere in a formula. -/
def maxVarIdFormula : Formula → Nat
  | .pred _ rs => maxVarIdList rs
  | .existPred _ r => maxVarId r
  | .imp A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .tensor A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .conj A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .disj A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .all x A => Nat.max x.id (maxVarIdFormula A)
  | .ex x A => Nat.max x.id (maxVarIdFormula A)

/-- Rename free occurrences of term variable `x` to `y` in a formula `A`. -/
def renameFreeVarFormula (A : Formula) (x y : Var) : Formula :=
  match A with
  | .pred P rs => .pred P (rs.map (fun r => renameFreeVar r x y))
  | .existPred ρ r => .existPred ρ (renameFreeVar r x y)
  | .imp B C => .imp (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .tensor B C => .tensor (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .conj B C => .conj (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .disj B C => .disj (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .all v B => if v == x then .all v B else .all v (renameFreeVarFormula B x y)
  | .ex v B => if v == x then .ex v B else .ex v (renameFreeVarFormula B x y)

/-- Structural size of a formula used for termination of capture-avoiding substitution. -/
def formulaSize : Formula → Nat
  | .pred _ _ => 1
  | .existPred _ _ => 1
  | .imp B C => formulaSize B + formulaSize C + 1
  | .tensor B C => formulaSize B + formulaSize C + 1
  | .conj B C => formulaSize B + formulaSize C + 1
  | .disj B C => formulaSize B + formulaSize C + 1
  | .all _ B => formulaSize B + 1
  | .ex _ B => formulaSize B + 1

theorem renameFreeVarFormula_size (A : Formula) (x y : Var) :
    formulaSize (renameFreeVarFormula A x y) = formulaSize A := by
  induction A with
  | pred P rs => rfl
  | existPred ρ r => rfl
  | imp B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | tensor B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | conj B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | disj B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | all v B ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp [formulaSize, ih]
  | ex v B ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp [formulaSize, ih]

/-- Capture-avoiding substitution `A[s/x]` of term `s` for variable `x` in formula `A`. -/
def substFormula (A : Formula) (x : Var) (s : Term) : Formula :=
  match A with
  | .pred P rs => .pred P (rs.map (fun r => substTerm r x s))
  | .existPred ρ r => .existPred ρ (substTerm r x s)
  | .imp B C => .imp (substFormula B x s) (substFormula C x s)
  | .tensor B C => .tensor (substFormula B x s) (substFormula C x s)
  | .conj B C => .conj (substFormula B x s) (substFormula C x s)
  | .disj B C => .disj (substFormula B x s) (substFormula C x s)
  | .all v B =>
      if v == x then
        .all v B
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .all v' (substFormula (renameFreeVarFormula B v v') x s)
      else
        .all v (substFormula B x s)
  | .ex v B =>
      if v == x then
        .ex v B
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .ex v' (substFormula (renameFreeVarFormula B v v') x s)
      else
        .ex v (substFormula B x s)
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

/-- Sequential substitution of multiple terms into a formula. -/
def substFormulaMany : Formula → List (Var × Term) → Formula
  | A, [] => A
  | A, (x, s) :: rest => substFormulaMany (substFormula A x s) rest

/-- Definition 3.3 (Computational content, p. 11):
For a formula `A`, `tau A` (`τ(A)`) is the type of its potential realizers. -/
def tau : Formula → Ty
  | .existPred ρ _ => ρ
  | .pred _ _ => .unit
  | .imp A B => .lolli (tau A) (tau B)
  | .tensor A B => .tensor (tau A) (tau B)
  | .conj A B => .prod (tau A) (tau B)
  | .disj A B => .sum (tau A) (tau B)
  | .all _ A => tau A
  | .ex _ A => tau A

/-- Definition 3.4 (Cleaning of types, pp. 11–12): `c(ρ)`. -/
def cleanTy : Ty → Ty
  | .unit => .unit
  | .diamond => .diamond
  | .lolli ρ σ =>
      let cρ := cleanTy ρ
      let cσ := cleanTy σ
      if cσ == .unit then .unit
      else if cρ == .unit then cσ
      else .lolli cρ cσ
  | .tensor ρ σ =>
      let cρ := cleanTy ρ
      let cσ := cleanTy σ
      if cσ == .unit then cρ
      else if cρ == .unit then cσ
      else .tensor cρ cσ
  | .prod ρ σ =>
      let cρ := cleanTy ρ
      let cσ := cleanTy σ
      if cσ == .unit then cρ
      else if cρ == .unit then cσ
      else .prod cρ cσ
  | .sum ρ σ => .sum (cleanTy ρ) (cleanTy σ)
  | .list ρ => .list (cleanTy ρ)

/-- Cleaned computational content `τ^c(A) := c(τ(A))` (p. 12). -/
def tauClean (A : Formula) : Ty :=
  cleanTy (tau A)

/-- Definition 3.5 (Harrop / computationally irrelevant formulas, p. 12):
A formula `A` has no computational content (is Harrop / c.i.) iff `τ^c(A) = U`. -/
def IsHarrop (A : Formula) : Prop :=
  tauClean A = .unit

/-- Formula containing neither existence predicates `E_ρ` nor disjunctions `∨`
(Proposition 4.2(1), p. 20 & Corollary 4.11, p. 26). -/
def IsExistAndDisjFree : Formula → Prop
  | .pred _ _ => True
  | .existPred _ _ => False
  | .imp A B => IsExistAndDisjFree A ∧ IsExistAndDisjFree B
  | .tensor A B => IsExistAndDisjFree A ∧ IsExistAndDisjFree B
  | .conj A B => IsExistAndDisjFree A ∧ IsExistAndDisjFree B
  | .disj _ _ => False
  | .all _ A => IsExistAndDisjFree A
  | .ex _ A => IsExistAndDisjFree A

/-- Assumption variable `u^A` (Section 3.2, p. 12). -/
structure AssumpVar where
  id : Nat
  formula : Formula
  deriving DecidableEq, Repr

/-- Proof contexts `Π, Γ` are finite sets of assumption variables (represented as lists). -/
abbrev ProofContext := List AssumpVar

/-- Conversion equations `r =_ρ r'` corresponding to Definition 2.9, where in the equation
`cons_ρ d^⋄ r l {s} t = s d^⋄ r (l {s} t)` the term `l` can be arbitrary (Axiom 13, p. 15). -/
inductive AxiomConvEq : Ty → Term → Term → Prop where
  | beta (x : Var) (r s : Term) (σ : Ty) :
      WeaklyTyped (.lam x r) (.lolli x.ty σ) →
      WeaklyTyped s x.ty →
      AxiomConvEq σ (.app (.lam x r) s) (substTerm r x s)
  | tensorBeta (ρ σ τ : Ty) (r s t : Term) :
      WeaklyTyped r ρ →
      WeaklyTyped s σ →
      WeaklyTyped t (.lolli ρ (.lolli σ τ)) →
      AxiomConvEq τ
        (.app (.app (.const (.tensorElim ρ σ τ))
          (.app (.app (.const (.tensorIntro ρ σ)) r) s)) t)
        (.app (.app t r) s)
  | fstBeta (ρ σ τ : Ty) (r s t : Term) :
      WeaklyTyped r (.lolli τ ρ) →
      WeaklyTyped s (.lolli τ σ) →
      WeaklyTyped t τ →
      AxiomConvEq ρ
        (.app (.const (.fst ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app r t)
  | sndBeta (ρ σ τ : Ty) (r s t : Term) :
      WeaklyTyped r (.lolli τ ρ) →
      WeaklyTyped s (.lolli τ σ) →
      WeaklyTyped t τ →
      AxiomConvEq σ
        (.app (.const (.snd ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app s t)
  | inlBeta (ρ σ τ : Ty) (r s : Term) :
      WeaklyTyped r ρ →
      WeaklyTyped s (.prod (.lolli ρ τ) (.lolli σ τ)) →
      AxiomConvEq τ
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inl ρ σ)) r)) s)
        (.app (.app (.const (.fst (.lolli ρ τ) (.lolli σ τ))) s) r)
  | inrBeta (ρ σ τ : Ty) (r s : Term) :
      WeaklyTyped r σ →
      WeaklyTyped s (.prod (.lolli ρ τ) (.lolli σ τ)) →
      AxiomConvEq τ
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inr ρ σ)) r)) s)
        (.app (.app (.const (.snd (.lolli ρ τ) (.lolli σ τ))) s) r)
  | iterNil (ρ τ : Ty) (s t : Term) :
      WeaklyTyped s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      WeaklyTyped t τ →
      AxiomConvEq τ (.app (.iter (.const (.nil ρ)) s) t) t
  | iterConsArb (ρ τ : Ty) (d r l s t : Term) :
      WeaklyTyped d .diamond →
      WeaklyTyped r ρ →
      WeaklyTyped l (.list ρ) →
      WeaklyTyped s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      WeaklyTyped t τ →
      AxiomConvEq τ
        (.app (.iter (.app (.app (.app (.const (.cons ρ)) d) r) l) s) t)
        (.app (.app (.app s d) r) (.app (.iter l s) t))

/-- Helper building the compatibility chain `x₁ = y₁ → ⋯ → xₙ = yₙ → B`. -/
def eqChainImp : List Ty → List Term → List Term → Formula → Formula
  | ρ :: ρs, x :: xs, y :: ys, B =>
      .imp (Formula.eqForm ρ x y) (eqChainImp ρs xs ys B)
  | _, _, _, B => B

/-- Definition 3.8 (Axioms for the core system, pp. 14–15, equations (3)–(25)).
Each constructor of `CoreAxiom` represents a core axiom instance together with its
canonical formula `CoreAxiom.formula`. -/
inductive CoreAxiom where
  /-- (3) `(C → A) → (C → B) → C → A ∧ B` -/
  | ax3 (A B C : Formula)
  /-- (4) `A₀ ∧ A₁ → A₀` -/
  | ax4_left (A₀ A₁ : Formula)
  /-- (4) `A₀ ∧ A₁ → A₁` -/
  | ax4_right (A₀ A₁ : Formula)
  /-- (5) `A → B → A ⊗ B` -/
  | ax5 (A B : Formula)
  /-- (6) `A ⊗ B → (A → B → C) → C` -/
  | ax6 (A B C : Formula)
  /-- (7) `A₀ → A₀ ∨ A₁` -/
  | ax7_left (A₀ A₁ : Formula)
  /-- (7) `A₁ → A₀ ∨ A₁` -/
  | ax7_right (A₀ A₁ : Formula)
  /-- (8) `(A → C) ∧ (B → C) → A ∨ B → C` -/
  | ax8 (A B C : Formula)
  /-- (9) `∀x.A → ∃x.A` -/
  | ax9 (x : Var) (A : Formula)
  /-- (10) `∃x.A → (∀x.A → B) → B` with `x ∉ FV(B)` -/
  | ax10 (x : Var) (A B : Formula)
  /-- (11) `⊥ → P(r⃗)` -/
  | ax11 (P : PredSym) (rs : List Term)
  /-- (12) Reflexivity `r =_ρ r` -/
  | ax12_refl (ρ : Ty) (r : Term)
  /-- (12) Symmetry `r =_ρ s → s =_ρ r` -/
  | ax12_symm (ρ : Ty) (r s : Term)
  /-- (12) Transitivity `r =_ρ s → s =_ρ t → r =_ρ t` -/
  | ax12_trans (ρ : Ty) (r s t : Term)
  /-- (13) Conversion equation `r =_ρ r'` -/
  | ax13 (ρ : Ty) (r r' : Term)
  /-- (14) `f =_{ρ⊸σ} g → x =_ρ y → f x =_σ g y` -/
  | ax14 (ρ σ : Ty) (f g x y : Term)
  /-- (15) `x₁ = y₁ → ⋯ → xₙ = yₙ → P(x₁,...,xₙ) → P(y₁,...,yₙ)` -/
  | ax15 (P : PredSym) (xs ys : List Term)
  /-- (16) `x =_ρ y → E_ρ(x) → E_ρ(y)` -/
  | ax16 (ρ : Ty) (x y : Term)
  /-- (17) `x =_U ε` -/
  | ax17 (x : Term)
  /-- (18) `(∀x^ρ. f x =_σ g x) → f =_{ρ⊸σ} g` -/
  | ax18 (ρ σ : Ty) (x : Var) (f g : Term)
  /-- (19) `fst z =_ρ fst z' ∧ snd z =_σ snd z' → z =_{ρ×σ} z'` -/
  | ax19 (ρ σ : Ty) (z z' : Term)
  /-- (20→) `E_{ρ⊸σ}(f) → ∀x^ρ. E_ρ(x) → E_σ(f x)` -/
  | ax20_imp (ρ σ : Ty) (x : Var) (f : Term)
  /-- (20←) `(∀x^ρ. E_ρ(x) → E_σ(f x)) → E_{ρ⊸σ}(f)` -/
  | ax20_mpr (ρ σ : Ty) (x : Var) (f : Term)
  /-- (21→) `E_{ρ×σ}(z) → E_ρ(fst z) ∧ E_σ(snd z)` -/
  | ax21_imp (ρ σ : Ty) (z : Term)
  /-- (21←) `E_ρ(fst z) ∧ E_σ(snd z) → E_{ρ×σ}(z)` -/
  | ax21_mpr (ρ σ : Ty) (z : Term)
  /-- (22) `E(c)` for constructor `c ∈ {ε, ⊗⁺, inl, inr, nil, cons}` -/
  | ax22 (c : Const)
  /-- (23) `(∀x^ρ, y^σ. E(x, y) → A[⊗⁺ x y / z]) → ∀z^{ρ⊗σ}. E(z) → A` -/
  | ax23 (ρ σ : Ty) (x y z : Var) (A : Formula)
  /-- (24) `(∀x^ρ. E(x) → A[inl x / z]) ∧ (∀y^σ. E(y) → A[inr y / z]) → ∀z^{ρ+σ}. E(z) → A` -/
  | ax24 (ρ σ : Ty) (x y z : Var) (A : Formula)
  /-- (25) `(E_ρ(x) → A) → A` for c.i. formula `A` -/
  | ax25 (ρ : Ty) (x : Term) (A : Formula)
  deriving DecidableEq, Repr

/-- Side conditions and formula assigned to each `CoreAxiom` (Definition 3.8, pp. 14–15). -/
def CoreAxiom.formula : CoreAxiom → Formula
  | .ax3 A B C => .imp (.imp C A) (.imp (.imp C B) (.imp C (.conj A B)))
  | .ax4_left A₀ A₁ => .imp (.conj A₀ A₁) A₀
  | .ax4_right A₀ A₁ => .imp (.conj A₀ A₁) A₁
  | .ax5 A B => .imp A (.imp B (.tensor A B))
  | .ax6 A B C => .imp (.tensor A B) (.imp (.imp A (.imp B C)) C)
  | .ax7_left A₀ A₁ => .imp A₀ (.disj A₀ A₁)
  | .ax7_right A₀ A₁ => .imp A₁ (.disj A₀ A₁)
  | .ax8 A B C => .imp (.conj (.imp A C) (.imp B C)) (.imp (.disj A B) C)
  | .ax9 x A => .imp (.all x A) (.ex x A)
  | .ax10 x A B => .imp (.ex x A) (.imp (.all x (.imp A B)) B)
  | .ax11 P rs => .imp Formula.bot (.pred P rs)
  | .ax12_refl ρ r => Formula.eqForm ρ r r
  | .ax12_symm ρ r s => .imp (Formula.eqForm ρ r s) (Formula.eqForm ρ s r)
  | .ax12_trans ρ r s t =>
      .imp (Formula.eqForm ρ r s) (.imp (Formula.eqForm ρ s t) (Formula.eqForm ρ r t))
  | .ax13 ρ r r' => Formula.eqForm ρ r r'
  | .ax14 ρ σ f g x y =>
      .imp (Formula.eqForm (.lolli ρ σ) f g)
        (.imp (Formula.eqForm ρ x y) (Formula.eqForm σ (.app f x) (.app g y)))
  | .ax15 P xs ys =>
      eqChainImp P.arity xs ys (.imp (.pred P xs) (.pred P ys))
  | .ax16 ρ x y =>
      .imp (Formula.eqForm ρ x y) (.imp (.existPred ρ x) (.existPred ρ y))
  | .ax17 x => Formula.eqForm .unit x (.const .eps)
  | .ax18 ρ σ x f g =>
      .imp (.all x (Formula.eqForm σ (.app f (.var x)) (.app g (.var x))))
        (Formula.eqForm (.lolli ρ σ) f g)
  | .ax19 ρ σ z z' =>
      .imp
        (.conj
          (Formula.eqForm ρ (.app (.const (.fst ρ σ)) z) (.app (.const (.fst ρ σ)) z'))
          (Formula.eqForm σ (.app (.const (.snd ρ σ)) z) (.app (.const (.snd ρ σ)) z')))
        (Formula.eqForm (.prod ρ σ) z z')
  | .ax20_imp ρ σ x f =>
      .imp (.existPred (.lolli ρ σ) f)
        (.all x (.imp (.existPred ρ (.var x)) (.existPred σ (.app f (.var x)))))
  | .ax20_mpr ρ σ x f =>
      .imp (.all x (.imp (.existPred ρ (.var x)) (.existPred σ (.app f (.var x)))))
        (.existPred (.lolli ρ σ) f)
  | .ax21_imp ρ σ z =>
      .imp (.existPred (.prod ρ σ) z)
        (.conj
          (.existPred ρ (.app (.const (.fst ρ σ)) z))
          (.existPred σ (.app (.const (.snd ρ σ)) z)))
  | .ax21_mpr ρ σ z =>
      .imp
        (.conj
          (.existPred ρ (.app (.const (.fst ρ σ)) z))
          (.existPred σ (.app (.const (.snd ρ σ)) z)))
        (.existPred (.prod ρ σ) z)
  | .ax22 c => .existPred c.ty (.const c)
  | .ax23 ρ σ x y z A =>
      let pairxy := Term.app (.app (.const (.tensorIntro ρ σ)) (.var x)) (.var y)
      .imp
        (.all x (.all y
          (.imp (.existPred ρ (.var x))
            (.imp (.existPred σ (.var y)) (substFormula A z pairxy)))))
        (.all z (.imp (.existPred (.tensor ρ σ) (.var z)) A))
  | .ax24 ρ σ x y z A =>
      let inlx := Term.app (.const (.inl ρ σ)) (.var x)
      let inry := Term.app (.const (.inr ρ σ)) (.var y)
      .imp
        (.conj
          (.all x (.imp (.existPred ρ (.var x)) (substFormula A z inlx)))
          (.all y (.imp (.existPred σ (.var y)) (substFormula A z inry))))
        (.all z (.imp (.existPred (.sum ρ σ) (.var z)) A))
  | .ax25 ρ x A => .imp (.imp (.existPred ρ x) A) A

/-- Side conditions ensuring that a `CoreAxiom` is a valid instance of Definition 3.8. -/
def CoreAxiom.IsValid : CoreAxiom → Prop
  | .ax10 x _ B => x ∉ freeVarsFormula B
  | .ax11 P rs => WeaklyTypedList rs P.arity
  | .ax12_refl ρ r => WeaklyTyped r ρ
  | .ax12_symm ρ r s => WeaklyTyped r ρ ∧ WeaklyTyped s ρ
  | .ax12_trans ρ r s t => WeaklyTyped r ρ ∧ WeaklyTyped s ρ ∧ WeaklyTyped t ρ
  | .ax13 ρ r r' => AxiomConvEq ρ r r'
  | .ax14 ρ σ f g x y =>
      WeaklyTyped f (.lolli ρ σ) ∧ WeaklyTyped g (.lolli ρ σ) ∧
      WeaklyTyped x ρ ∧ WeaklyTyped y ρ
  | .ax15 P xs ys => WeaklyTypedList xs P.arity ∧ WeaklyTypedList ys P.arity
  | .ax16 ρ x y => WeaklyTyped x ρ ∧ WeaklyTyped y ρ
  | .ax17 x => WeaklyTyped x .unit
  | .ax18 ρ σ x f g =>
      x.ty = ρ ∧ x ∉ freeVars f ∧ x ∉ freeVars g ∧
      WeaklyTyped f (.lolli ρ σ) ∧ WeaklyTyped g (.lolli ρ σ)
  | .ax19 ρ σ z z' => WeaklyTyped z (.prod ρ σ) ∧ WeaklyTyped z' (.prod ρ σ)
  | .ax20_imp ρ σ x f => x.ty = ρ ∧ x ∉ freeVars f ∧ WeaklyTyped f (.lolli ρ σ)
  | .ax20_mpr ρ σ x f => x.ty = ρ ∧ x ∉ freeVars f ∧ WeaklyTyped f (.lolli ρ σ)
  | .ax21_imp ρ σ z => WeaklyTyped z (.prod ρ σ)
  | .ax21_mpr ρ σ z => WeaklyTyped z (.prod ρ σ)
  | .ax22 c => c.isConstructor = true
  | .ax23 ρ σ x y z A =>
      x.ty = ρ ∧ y.ty = σ ∧ z.ty = .tensor ρ σ ∧ x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      x ∉ freeVarsFormula A ∧ y ∉ freeVarsFormula A
  | .ax24 ρ σ x y z A =>
      x.ty = ρ ∧ y.ty = σ ∧ z.ty = .sum ρ σ ∧ x ≠ z ∧ y ≠ z ∧
      x ∉ freeVarsFormula A ∧ y ∉ freeVarsFormula A
  | .ax25 ρ x A => WeaklyTyped x ρ ∧ IsHarrop A
  | _ => True

/-- Definition 3.6 (Raw proof terms, p. 12):
`M, N, L ::= u^A | c | λu^A M | λx^ρ M | M N | M r | M {N}`. -/
inductive ProofTerm where
  | assump : AssumpVar → ProofTerm
  | ax : CoreAxiom → ProofTerm
  | lamAssump : AssumpVar → ProofTerm → ProofTerm
  | lamTerm : Var → ProofTerm → ProofTerm
  | appProof : ProofTerm → ProofTerm → ProofTerm
  | appTerm : ProofTerm → Term → ProofTerm
  | ind : ProofTerm → ProofTerm → ProofTerm
  deriving DecidableEq, Repr

/-- Substitute assumption variable `v` for `u` in proof term `M` (`M[v^A / u^A]`,
used in the `(Contraction)` rule of Definition 3.7, p. 14). -/
def substAssumpProof (M : ProofTerm) (u v : AssumpVar) : ProofTerm :=
  match M with
  | .assump w => if w == u then .assump v else .assump w
  | .ax c => .ax c
  | .lamAssump w body =>
      if w == u then .lamAssump w body else .lamAssump w (substAssumpProof body u v)
  | .lamTerm x body => .lamTerm x (substAssumpProof body u v)
  | .appProof M₁ M₂ => .appProof (substAssumpProof M₁ u v) (substAssumpProof M₂ u v)
  | .appTerm M₁ r => .appTerm (substAssumpProof M₁ u v) r
  | .ind N M₁ => .ind (substAssumpProof N u v) (substAssumpProof M₁ u v)

/-- Bound assumption variables occurring in a proof term `M`. -/
def boundAssumpVars : ProofTerm → List AssumpVar
  | .assump _ => []
  | .ax _ => []
  | .lamAssump w body => w :: boundAssumpVars body
  | .lamTerm _ body => boundAssumpVars body
  | .appProof M₁ M₂ => boundAssumpVars M₁ ++ boundAssumpVars M₂
  | .appTerm M₁ _ => boundAssumpVars M₁
  | .ind N M₁ => boundAssumpVars N ++ boundAssumpVars M₁

/-- All assumption variables (free or bound) occurring in a proof term `M`. -/
def allAssumpVars : ProofTerm → List AssumpVar
  | .assump w => [w]
  | .ax _ => []
  | .lamAssump w body => w :: allAssumpVars body
  | .lamTerm _ body => allAssumpVars body
  | .appProof M₁ M₂ => allAssumpVars M₁ ++ allAssumpVars M₂
  | .appTerm M₁ _ => allAssumpVars M₁
  | .ind N M₁ => allAssumpVars N ++ allAssumpVars M₁

/-- Disjointness of two proof contexts `Π ∩ Γ = ∅` (by assumption variable id, ensuring
distinct assumption variables in a context have distinct ids). -/
def DisjointProofCtx (Δ Γ : ProofContext) : Prop :=
  ∀ u ∈ Δ, ∀ v ∈ Γ, u.id ≠ v.id

/-- Well-formedness of a proof context: no two distinct assumption variables share an id. -/
def CtxIdsUnique (Δ : ProofContext) : Prop :=
  ∀ u ∈ Δ, ∀ v ∈ Δ, u.id = v.id → u = v

/-- Set-extensional union `Θ = Π ∪ Γ` with `Π ∩ Γ = ∅` (Section 3.2, p. 12:
"We denote proof contexts by `Π, Γ, ...`, and write `Π, Γ` for the union `Π ∪ Γ`,
expressing that `Π` and `Γ` are disjoint."). -/
def IsDisjointCtxUnion (Δ Γ Θ : ProofContext) : Prop :=
  DisjointProofCtx Δ Γ ∧ CtxIdsUnique Θ ∧ ∀ u, u ∈ Θ ↔ (u ∈ Δ ∨ u ∈ Γ)

/-- Variable condition `VarCond` for `(∀⁺)` in Definition 3.7 (pp. 13–14):
"`x` must not be free in the type of any element of `Π ∪ Γ`." -/
def VarCond (x : Var) (Δ Γ : ProofContext) : Prop :=
  (∀ u ∈ Δ, x ∉ freeVarsFormula u.formula) ∧
  (∀ u ∈ Γ, x ∉ freeVarsFormula u.formula)

/-- Step formula in the `(L(τ)-Ind)` rule of Definition 3.7 (p. 14):
`∀ p^⋄, x^τ, l^{L(τ)}. E(p) → E(x) → A → A[cons(p, x, l)/l]`. -/
def indStepFormula (τ : Ty) (p x l : Var) (A : Formula) : Formula :=
  let consTerm := Term.app (.app (.app (.const (.cons τ)) (.var p)) (.var x)) (.var l)
  .all p (.all x (.all l
    (.imp (.existPred .diamond (.var p))
      (.imp (.existPred τ (.var x))
        (.imp A (substFormula A l consTerm))))))

/-- Definition 3.7 (Derivations `Π | Γ ⊢ M : A`, pp. 13–14). -/
inductive Derives : ProofContext → ProofContext → ProofTerm → Formula → Prop where
  /-- `(Assumption)`: `Π | Γ, u^A ⊢ u^A : A` -/
  | assumption (Δ Γ Γ' : ProofContext) (u : AssumpVar) :
      DisjointProofCtx Δ Γ' →
      IsDisjointCtxUnion Γ [u] Γ' →
      Derives Δ Γ' (.assump u) u.formula
  /-- `(Axiom)`: `Π | Γ ⊢ c^A : A` -/
  | axiomRule (Δ Γ : ProofContext) (c : CoreAxiom) :
      DisjointProofCtx Δ Γ →
      c.IsValid →
      Derives Δ Γ (.ax c) c.formula
  /-- `(→⁺)`: from `Π | Γ, u^A ⊢ M : B` infer `Π | Γ ⊢ λu^A M : A → B` -/
  | impIntro {Δ Γ Γ' : ProofContext} {u : AssumpVar} {M : ProofTerm} {B : Formula} :
      IsDisjointCtxUnion Γ [u] Γ' →
      Derives Δ Γ' M B →
      Derives Δ Γ (.lamAssump u M) (.imp u.formula B)
  /-- `(→⁻)`: from `Π | Γ₁ ⊢ M : A → B` and `Π | Γ₂ ⊢ N : A` infer `Π | Γ₁, Γ₂ ⊢ M N : B` -/
  | impElim {Δ Γ₁ Γ₂ Γ : ProofContext} {M N : ProofTerm} {A B : Formula} :
      IsDisjointCtxUnion Γ₁ Γ₂ Γ →
      Derives Δ Γ₁ M (.imp A B) →
      Derives Δ Γ₂ N A →
      Derives Δ Γ (.appProof M N) B
  /-- `(∀⁺)`: from `Π | Γ ⊢ M : A` and `VarCond` infer `Π | Γ ⊢ λx^ρ M : ∀x^ρ A` -/
  | allIntro {Δ Γ : ProofContext} (x : Var) {M : ProofTerm} {A : Formula} :
      Derives Δ Γ M A →
      VarCond x Δ Γ →
      Derives Δ Γ (.lamTerm x M) (.all x A)
  /-- `(∀⁻)`: from `Π | Γ ⊢ M : ∀x^ρ A` and `r` weakly typed by `ρ` infer `Π | Γ ⊢ M r : A[r/x]` -/
  | allElim {Δ Γ : ProofContext} {x : Var} {M : ProofTerm} {A : Formula} (r : Term) :
      Derives Δ Γ M (.all x A) →
      WeaklyTyped r x.ty →
      Derives Δ Γ (.appTerm M r) (substFormula A x r)
  /-- `(Passification)`: from `Π | u^B, Γ ⊢ M : A` and `A` c.i. infer `Π, u^B | Γ ⊢ M : A` -/
  | passification {Δ Δ' Γ Γ' : ProofContext} {u : AssumpVar} {M : ProofTerm} {A : Formula} :
      IsDisjointCtxUnion [u] Γ Γ' →
      IsDisjointCtxUnion Δ [u] Δ' →
      IsHarrop A →
      Derives Δ Γ' M A →
      Derives Δ' Γ M A
  /-- `(Contraction)`: from `u^A, Π | v^A, Γ ⊢ M : B` infer `Π | v^A, Γ ⊢ M[v^A/u^A] : B` -/
  | contraction {Δ Δ' Γ Γ' : ProofContext} {u v : AssumpVar} {M : ProofTerm} {B : Formula} :
      u.formula = v.formula →
      v ∉ boundAssumpVars M →
      IsDisjointCtxUnion [u] Δ Δ' →
      IsDisjointCtxUnion [v] Γ Γ' →
      Derives Δ' Γ' M B →
      Derives Δ Γ' (substAssumpProof M u v) B
  /-- `(L(τ)-Ind)`: list iteration induction rule (p. 14). -/
  | listInd {Δ Γ : ProofContext} {N M : ProofTerm} (τ : Ty) (t : Term)
      (p x l : Var) (A : Formula) :
      p.ty = .diamond →
      x.ty = τ →
      l.ty = .list τ →
      p ≠ x → p ≠ l → x ≠ l →
      p ∉ freeVarsFormula A →
      x ∉ freeVarsFormula A →
      WeaklyTyped t (.list τ) →
      Derives Δ Γ N (.existPred (.list τ) t) →
      Derives Δ [] M (indStepFormula τ p x l A) →
      Derives Δ Γ (.ind N M)
        (.imp (substFormula A l (.const (.nil τ))) (substFormula A l t))

/-- Provability judgment `Π | Γ ⊢ A` (p. 15: "there exists a proof term `M` such that
`Π | Γ ⊢ M : A` is derivable"). -/
def Provable (Δ Γ : ProofContext) (A : Formula) : Prop :=
  ∃ M : ProofTerm, Derives Δ Γ M A

/-- Closed provability `⊢ A` (in empty passive and active contexts). -/
def ClosedProvable (A : Formula) : Prop :=
  Provable [] [] A

end ABHS2004


