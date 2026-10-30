-- Prove2me | Definitions.Def_BBS2002_Arithmetic
-- name    : BBS2002_Arithmetic
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T04:06:42.208603+00:00
-- url     : https://prove2.me/theorems/82c4fc94-8ffe-408d-b006-e3fd31227dc8
-- title:
--   Section 2: System T and the Arithmetical Systems Z^X, Z, Z_0^X, and Z_0
-- statement:
--   Formalizes Section 2 of Berger, Buchholz, and Schwichtenberg (2002): finite types over `ι` and `o`, System `T` constants (`true, false, 0, S, R_{o,ρ}, R_{ι,ρ}`), capture-avoiding substitution, `βR`-equality, formulas of `L[X]` and `L`, and natural deduction derivations for the four arithmetical systems `Z^X, Z, Z_0^X, Z_0`.
-- source:
--   Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg, 'Refined program extraction from classical proofs', Annals of Pure and Applied Logic 114(1-3), 2002, pp. 3-25 (doi:10.1016/S0168-0072(01)00073-2). Section 2, pp. 5-7 (preprint pp. 3-5).

import Std

/-!
# Arithmetic for Functionals: System T and the Systems Z^X, Z, Z_0^X, Z_0 (Berger–Buchholz–Schwichtenberg 2002, Section 2)

Source: Ulrich Berger, Wilfried Buchholz, and Helmut Schwichtenberg,
"Refined program extraction from classical proofs",
*Annals of Pure and Applied Logic* 114, 2002, pp. 3–25 (Section 2, pp. 5–7 / preprint pp. 3–5).

This module formalizes:
- Simple types (`Ty`) over ground types `ι` (natural numbers, `Ty.iota`) and `o` (booleans, `Ty.bool`).
- System `T` constants (`Const`): `true^o`, `false^o`, `0^ι`, `S^{ι→ι}`, boolean recursion
  `R_{o,ρ} : ρ → ρ → o → ρ`, and primitive recursion `R_{ι,ρ} : ρ → (ι → ρ → ρ) → ι → ρ`.
- Typed terms (`Term`, `HasType`), capture-avoiding substitution (`substTerm`), conversions
  `↦_βR` (`ConvStep`, `Step`), and the meta-level equality `=_{βR}` (`BetaREq`, p. 4).
- Formulas of `L[X]` and `L` (`Formula`): `⊥`, `X`, `atom(t^o)`, `A → B`, and `∀x^ρ A`,
  together with `¬A := A → ⊥`, `C^X := C[⊥ := X]` (`substBotWithX`), and `A^F := A[⊥ := atom(false)]`
  (`substBotWithFalse`).
- Natural deduction proof terms (`ProofTerm`) and the derivability relation `Derivable sys M A`
  parameterized by `SysConfig` covering the four systems `Z^X`, `Z`, `Z_0^X`, and `Z_0` (p. 4).
-/

namespace BBS2002

/-- Finite types built from ground types `ι` (natural numbers) and `o` (booleans) by `ρ → σ`
(Section 2, p. 3). -/
inductive Ty where
  | iota : Ty
  | bool : Ty
  | arr : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Multi-argument arrow type `ρ₁ → ⋯ → ρₖ → σ`. -/
def arrMany : List Ty → Ty → Ty
  | [], σ => σ
  | ρ :: ρs, σ => .arr ρ (arrMany ρs σ)

end Ty

/-- Constants of System `T` over `ι` and `o` (Section 2, pp. 3–4):
- `true^o`, `false^o`
- `0^ι`, `S^{ι→ι}`
- `R_{o,ρ} : ρ → ρ → o → ρ` (boolean cases / recursion)
- `R_{ι,ρ} : ρ → (ι → ρ → ρ) → ι → ρ` (primitive recursion). -/
inductive Const where
  | trueConst : Const
  | falseConst : Const
  | zero : Const
  | succ : Const
  | recBool : Ty → Const
  | recNat : Ty → Const
  deriving DecidableEq, Repr

namespace Const

/-- Type of a constant symbol (Section 2, pp. 3–4). -/
def ty : Const → Ty
  | .trueConst => .bool
  | .falseConst => .bool
  | .zero => .iota
  | .succ => .arr .iota .iota
  | .recBool ρ => .arr ρ (.arr ρ (.arr .bool ρ))
  | .recNat ρ => .arr ρ (.arr (.arr .iota (.arr ρ ρ)) (.arr .iota ρ))

end Const

/-- Typed object variable `x^ρ` (Section 2, p. 4). -/
structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

/-- Terms of System `T` (Section 2, p. 4): `x^ρ`, `c^ρ`, `λx^ρ r`, `r s`. -/
inductive Term where
  | var : Var → Term
  | const : Const → Term
  | lam : Var → Term → Term
  | app : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Left-associated application `r s₁ ... sₖ`. -/
def appMany : Term → List Term → Term
  | r, [] => r
  | r, s :: ss => appMany (.app r s) ss

/-- Multi-variable abstraction `λx₁ ... xₖ. r`. -/
def lamMany : List Var → Term → Term
  | [], r => r
  | x :: xs, r => .lam x (lamMany xs r)

/-- Abbreviation `t + 1 := S^{ι→ι} t` (Section 2, p. 4). -/
def succTerm (t : Term) : Term :=
  .app (.const .succ) t

end Term

/-- Typing relation `HasType r ρ` for System `T` terms (Section 2, p. 4). -/
inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | const (c : Const) :
      HasType (.const c) c.ty
  | lam (x : Var) {r : Term} {σ : Ty} :
      HasType r σ →
      HasType (.lam x r) (.arr x.ty σ)
  | app {r s : Term} {ρ σ : Ty} :
      HasType r (.arr ρ σ) →
      HasType s ρ →
      HasType (.app r s) σ

/-- Free variable occurrences in a term `r`. -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x r => (freeVarOccurrences r).filter (· != x)
  | .app r s => freeVarOccurrences r ++ freeVarOccurrences s

/-- Duplicate-free list of free variables `FV(r)` in `r`. -/
def freeVars (r : Term) : List Var :=
  (freeVarOccurrences r).eraseDups

/-- All variables (free or bound) occurring in `r`. -/
def allVarsTerm : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x r => x :: allVarsTerm r
  | .app r s => allVarsTerm r ++ allVarsTerm s

/-- Whether a term `r` is closed (`FV(r) = ∅`). -/
def IsClosedTerm (r : Term) : Prop :=
  freeVars r = []

/-- Maximum variable `id` occurring in a term `r`. -/
def maxVarIdTerm : Term → Nat
  | .var x => x.id
  | .const _ => 0
  | .lam x r => Nat.max x.id (maxVarIdTerm r)
  | .app r s => Nat.max (maxVarIdTerm r) (maxVarIdTerm s)

/-- Structural size of a term `r`. -/
def rawSize : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ r => rawSize r + 1
  | .app r s => rawSize r + rawSize s + 1

/-- Replace free occurrences of `x` with `y` in `r`. -/
def renameFreeVar (r : Term) (x y : Var) : Term :=
  match r with
  | .var v => if v == x then .var y else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)
  | .app t s => .app (renameFreeVar t x y) (renameFreeVar s x y)

theorem renameFreeVar_rawSize (r : Term) (x y : Var) :
    rawSize (renameFreeVar r x y) = rawSize r := by
  induction r with
  | var v => simp only [renameFreeVar]; split <;> rfl
  | const c => rfl
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]
  | app t s iht ihs => simp [renameFreeVar, rawSize, iht, ihs]

/-- Capture-avoiding substitution `r[x := s]` in a System `T` term. -/
def substTerm (r : Term) (x : Var) (s : Term) : Term :=
  match r with
  | .var v => if v == x then s else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then
        .lam v body
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarIdTerm body) (Nat.max (maxVarIdTerm s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .lam v' (substTerm (renameFreeVar body v v') x s)
      else
        .lam v (substTerm body x s)
  | .app t u => .app (substTerm t x s) (substTerm u x s)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Canonical closed default term of each type `ρ` (built from `0^ι` and `false^o`). -/
def defaultTerm : Ty → Term
  | .iota => .const .zero
  | .bool => .const .falseConst
  | .arr ρ σ => .lam ⟨0, ρ⟩ (defaultTerm σ)

/-- α-equivalence on System `T` terms. -/
inductive AlphaEqTerm : Term → Term → Prop where
  | refl (r : Term) : AlphaEqTerm r r
  | symm {r s : Term} : AlphaEqTerm r s → AlphaEqTerm s r
  | trans {r s t : Term} : AlphaEqTerm r s → AlphaEqTerm s t → AlphaEqTerm r t
  | app {r r' s s' : Term} :
      AlphaEqTerm r r' → AlphaEqTerm s s' → AlphaEqTerm (.app r s) (.app r' s')
  | lam_rename (x y : Var) (r : Term) :
      x.ty = y.ty →
      (y = x ∨ y ∉ allVarsTerm r) →
      AlphaEqTerm (.lam x r) (.lam y (renameFreeVar r x y))
  | lam_congr (x : Var) {r s : Term} :
      AlphaEqTerm r s → AlphaEqTerm (.lam x r) (.lam x s)

/-- Conversion rules `↦_βR` for System `T` (Section 2, p. 4):
- `(λx. r) s ↦_β r[x := s]`
- `R_{o,ρ} r s true ↦_R r`
- `R_{o,ρ} r s false ↦_R s`
- `R_{ι,ρ} r s 0 ↦_R r`
- `R_{ι,ρ} r s (t + 1) ↦_R s t (R_{ι,ρ} r s t)`. -/
inductive ConvStep : Term → Term → Prop where
  | beta (x : Var) (r s : Term) :
      ConvStep (.app (.lam x r) s) (substTerm r x s)
  | recBoolTrue (ρ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.app (.const (.recBool ρ)) r) s) (.const .trueConst))
        r
  | recBoolFalse (ρ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.app (.const (.recBool ρ)) r) s) (.const .falseConst))
        s
  | recNatZero (ρ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.app (.const (.recNat ρ)) r) s) (.const .zero))
        r
  | recNatSucc (ρ : Ty) (r s t : Term) :
      ConvStep
        (.app (.app (.app (.const (.recNat ρ)) r) s) (Term.succTerm t))
        (.app (.app s t) (.app (.app (.app (.const (.recNat ρ)) r) s) t))

/-- Meta-level `βR`-equality `r =_{βR} s` (Section 2, p. 4). -/
inductive BetaREq : Term → Term → Prop where
  | of_alpha {r s : Term} : AlphaEqTerm r s → BetaREq r s
  | of_conv {r s : Term} : ConvStep r s → BetaREq r s
  | refl (r : Term) : BetaREq r r
  | symm {r s : Term} : BetaREq r s → BetaREq s r
  | trans {r s t : Term} : BetaREq r s → BetaREq s t → BetaREq r t
  | lam (x : Var) {r s : Term} : BetaREq r s → BetaREq (.lam x r) (.lam x s)
  | app {r r' s s' : Term} : BetaREq r r' → BetaREq s s' → BetaREq (.app r s) (.app r' s')

/-- Formulas of `L[X]` (Section 2, p. 4):
`⊥`, `X`, `atom(t^o)`, `A → B`, `∀x^ρ A`. -/
inductive Formula where
  | bot : Formula
  | varX : Formula
  | atom : Term → Formula
  | imp : Formula → Formula → Formula
  | all : Var → Formula → Formula
  deriving DecidableEq, Repr

namespace Formula

/-- Abbreviation `¬A := A → ⊥` (Section 2, p. 4). -/
def neg (A : Formula) : Formula :=
  .imp A .bot

/-- Double negation `¬¬A := (A → ⊥) → ⊥` (Lemma 2.2, p. 5). -/
def dneg (A : Formula) : Formula :=
  neg (neg A)

/-- Formula `F := atom(false)` (Lemma 2.1, p. 5). -/
def falseAtom : Formula :=
  .atom (.const .falseConst)

/-- Iterated implication `A₁ → ⋯ → Aₙ → B`. -/
def impMany : List Formula → Formula → Formula
  | [], B => B
  | A :: As, B => .imp A (impMany As B)

/-- Iterated universal quantification `∀y₁ ... ∀yₖ. A`. -/
def allMany : List Var → Formula → Formula
  | [], A => A
  | y :: ys, A => .all y (allMany ys A)

end Formula

/-- Whether every `atom(t)` in `A` has `HasType t .bool`. -/
inductive FormulaWellTyped : Formula → Prop where
  | bot : FormulaWellTyped .bot
  | varX : FormulaWellTyped .varX
  | atom {t : Term} : HasType t .bool → FormulaWellTyped (.atom t)
  | imp {A B : Formula} : FormulaWellTyped A → FormulaWellTyped B → FormulaWellTyped (.imp A B)
  | all (x : Var) {A : Formula} : FormulaWellTyped A → FormulaWellTyped (.all x A)

/-- Whether a formula belongs to `L` (contains no occurrences of `X`, Section 2, pp. 4–5). -/
def isLFormula : Formula → Bool
  | .bot => true
  | .varX => false
  | .atom _ => true
  | .imp A B => isLFormula A && isLFormula B
  | .all _ A => isLFormula A

/-- Whether a formula is an atomic `L`-formula (`⊥` or `atom(t)`, Section 2, p. 5 & Section 3, p. 6). -/
def isAtomicL : Formula → Bool
  | .bot => true
  | .atom _ => true
  | _ => false

/-- Whether a formula is quantifier-free (contains no `∀`, Section 2, p. 5 & Section 3, p. 6). -/
def isQuantifierFree : Formula → Bool
  | .bot | .varX | .atom _ => true
  | .imp A B => isQuantifierFree A && isQuantifierFree B
  | .all _ _ => false

/-- Replace `⊥` with `B` throughout a formula `C` (`C[⊥ := B]`, Section 2, pp. 4–5). -/
def substBotFormula (C B : Formula) : Formula :=
  match C with
  | .bot => B
  | .varX => .varX
  | .atom t => .atom t
  | .imp A₁ A₂ => .imp (substBotFormula A₁ B) (substBotFormula A₂ B)
  | .all x A => .all x (substBotFormula A B)

/-- `C^X := C[⊥ := X]` (Section 2, p. 4). -/
def substBotWithX (C : Formula) : Formula :=
  substBotFormula C .varX

/-- `A^F := A[⊥ := atom(false)]` (Lemma 2.1, p. 5). -/
def substBotWithFalse (A : Formula) : Formula :=
  substBotFormula A Formula.falseAtom

/-- Free object variables `FV(A)` of a formula `A`. -/
def freeVarsFormula : Formula → List Var
  | .bot | .varX => []
  | .atom t => freeVars t
  | .imp A B => (freeVarsFormula A ++ freeVarsFormula B).eraseDups
  | .all x A => (freeVarsFormula A).filter (· != x)

/-- Maximum variable `id` occurring in a formula `A`. -/
def maxVarIdFormula : Formula → Nat
  | .bot | .varX => 0
  | .atom t => maxVarIdTerm t
  | .imp A B => Nat.max (maxVarIdFormula A) (maxVarIdFormula B)
  | .all x A => Nat.max x.id (maxVarIdFormula A)

/-- Structural size of a formula `A`. -/
def formulaSize : Formula → Nat
  | .bot | .varX => 1
  | .atom _ => 1
  | .imp A B => formulaSize A + formulaSize B + 1
  | .all _ A => formulaSize A + 1

/-- Replace free occurrences of object variable `x` with `y` in a formula `A`. -/
def renameFreeVarFormula (A : Formula) (x y : Var) : Formula :=
  match A with
  | .bot => .bot
  | .varX => .varX
  | .atom t => .atom (renameFreeVar t x y)
  | .imp B C => .imp (renameFreeVarFormula B x y) (renameFreeVarFormula C x y)
  | .all v B =>
      if v == x then .all v B else .all v (renameFreeVarFormula B x y)

theorem renameFreeVarFormula_size (A : Formula) (x y : Var) :
    formulaSize (renameFreeVarFormula A x y) = formulaSize A := by
  induction A with
  | bot | varX | atom _ => rfl
  | imp B C ihB ihC => simp [renameFreeVarFormula, formulaSize, ihB, ihC]
  | all v B ih =>
      simp only [renameFreeVarFormula]
      split
      · rfl
      · simp [formulaSize, ih]

/-- Capture-avoiding substitution `A[x^ρ := t^ρ]` of a term `t` into a formula `A` (Section 2, p. 4). -/
def substFormula (A : Formula) (x : Var) (t : Term) : Formula :=
  match A with
  | .bot => .bot
  | .varX => .varX
  | .atom s => .atom (substTerm s x t)
  | .imp B C => .imp (substFormula B x t) (substFormula C x t)
  | .all v B =>
      if v == x then
        .all v B
      else if v ∈ freeVarOccurrences t then
        let freshId := Nat.max (maxVarIdFormula B) (Nat.max (maxVarIdTerm t) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .all v' (substFormula (renameFreeVarFormula B v v') x t)
      else
        .all v (substFormula B x t)
termination_by formulaSize A
decreasing_by
  all_goals
    simp_wf
    simp [formulaSize, renameFreeVarFormula_size]
    try omega

/-- Simultaneous substitution `A[y₁ := t₁, ..., yₖ := tₖ]` into a formula `A`. -/
def substFormulaMany : Formula → List (Var × Term) → Formula
  | A, [] => A
  | A, (y, t) :: rest => substFormulaMany (substFormula A y t) rest

/-- All object variables (free or bound) occurring in a formula `A`. -/
def allVarsFormula : Formula → List Var
  | .bot | .varX => []
  | .atom t => allVarsTerm t
  | .imp A B => allVarsFormula A ++ allVarsFormula B
  | .all x A => x :: allVarsFormula A

/-- Formula equality modulo α-renaming of bound variables and meta-level `=_{βR}` on embedded terms
(Section 2, p. 4). -/
inductive FormulaBetaREq : Formula → Formula → Prop where
  | refl (A : Formula) : FormulaBetaREq A A
  | symm {A B : Formula} : FormulaBetaREq A B → FormulaBetaREq B A
  | trans {A B C : Formula} : FormulaBetaREq A B → FormulaBetaREq B C → FormulaBetaREq A C
  | bot : FormulaBetaREq .bot .bot
  | varX : FormulaBetaREq .varX .varX
  | atom {t s : Term} : BetaREq t s → FormulaBetaREq (.atom t) (.atom s)
  | imp {A A' B B' : Formula} :
      FormulaBetaREq A A' → FormulaBetaREq B B' → FormulaBetaREq (.imp A B) (.imp A' B')
  | all (x : Var) {A A' : Formula} :
      FormulaBetaREq A A' → FormulaBetaREq (.all x A) (.all x A')
  | all_rename (x y : Var) (A : Formula) :
      x.ty = y.ty →
      (y = x ∨ y ∉ allVarsFormula A) →
      FormulaBetaREq (.all x A) (.all y (renameFreeVarFormula A x y))

/-- Assumption variable `u^B` in natural deduction derivations (Section 2, p. 4). -/
structure AssumpVar where
  id : Nat
  formula : Formula
  deriving DecidableEq, Repr

/-- Natural deduction proof terms in Curry–Howard style (Section 2, p. 4):
- `u^B` (assumptions)
- axioms `Ind_{n,A}`, `Ind_{p,A}`, `ax_true`, `ax_{false,A}`, `efq_A`
- `(λu^A M^B)^{A→B}`, `(M^{A→B} N^A)^B`
- `(λx^ρ M^A)^{∀x^ρ A}`, `(M^{∀x^ρ A} t^ρ)^{A[x^ρ := t^ρ]}`. -/
inductive ProofTerm where
  | assump : AssumpVar → ProofTerm
  | indNat : Var → Formula → ProofTerm
  | indBool : Var → Formula → ProofTerm
  | axTrue : ProofTerm
  | axFalse : Formula → ProofTerm
  | efq : Formula → ProofTerm
  | lamAssump : AssumpVar → ProofTerm → ProofTerm
  | appAssump : ProofTerm → ProofTerm → ProofTerm
  | lamTerm : Var → ProofTerm → ProofTerm
  | appTerm : ProofTerm → Term → ProofTerm
  deriving DecidableEq, Repr

/-- Free assumption variables `FA(M)` of a derivation `M` (Section 2, p. 4). -/
def freeAssumpVars : ProofTerm → List AssumpVar
  | .assump u => [u]
  | .indNat _ _ | .indBool _ _ | .axTrue | .axFalse _ | .efq _ => []
  | .lamAssump u M => (freeAssumpVars M).filter (· != u)
  | .appAssump M N => (freeAssumpVars M ++ freeAssumpVars N).eraseDups
  | .lamTerm _ M => freeAssumpVars M
  | .appTerm M _ => freeAssumpVars M

/-- Substitute `X` for `⊥` throughout a `Z_0`-derivation `M` to obtain `M^X` (Section 2, p. 4). -/
def substBotProof : ProofTerm → ProofTerm
  | .assump u => .assump ⟨u.id, substBotWithX u.formula⟩
  | .indNat n A => .indNat n (substBotWithX A)
  | .indBool p A => .indBool p (substBotWithX A)
  | .axTrue => .axTrue
  | .axFalse A => .axFalse (substBotWithX A)
  | .efq A => .efq (substBotWithX A)
  | .lamAssump u M => .lamAssump ⟨u.id, substBotWithX u.formula⟩ (substBotProof M)
  | .appAssump M N => .appAssump (substBotProof M) (substBotProof N)
  | .lamTerm x M => .lamTerm x (substBotProof M)
  | .appTerm M t => .appTerm (substBotProof M) t

/-- Configuration flags selecting one of the four systems `Z^X, Z, Z_0^X, Z_0` (Section 2, p. 4):
- `allowX`: whether the propositional symbol `X` is permitted in formulas (`L[X]` vs. `L`)
- `allowEfq`: whether the `efq_A : ⊥ → A` axiom scheme is permitted. -/
structure SysConfig where
  allowX : Bool
  allowEfq : Bool
  deriving DecidableEq, Repr

namespace SysConfig

/-- System `Z^X`: intuitionistic arithmetic over `L[X]` with `efq_A` (p. 4). -/
def ZX : SysConfig := ⟨true, true⟩

/-- System `Z`: intuitionistic arithmetic over `L` (`X`-free) with `efq_A` (p. 4). -/
def Z : SysConfig := ⟨false, true⟩

/-- System `Z_0^X`: minimal arithmetic over `L[X]` without `efq_A` (p. 4). -/
def ZX0 : SysConfig := ⟨true, false⟩

/-- System `Z_0`: minimal arithmetic over `L` (`X`-free) without `efq_A` (p. 4). -/
def Z0 : SysConfig := ⟨false, false⟩

/-- Whether a formula `A` is allowed in system `sys`. -/
def allowsFormula (sys : SysConfig) (A : Formula) : Prop :=
  FormulaWellTyped A ∧ (sys.allowX = true ∨ isLFormula A = true)

end SysConfig

/-- Induction axiom formula `Ind_{n,A} : A[n := 0] → ∀n(A → A[n := n + 1]) → ∀n A` (p. 2 & p. 4). -/
def indNatFormula (n : Var) (A : Formula) : Formula :=
  .imp
    (substFormula A n (.const .zero))
    (.imp
      (.all n (.imp A (substFormula A n (Term.succTerm (.var n)))))
      (.all n A))

/-- Boolean induction axiom formula `Ind_{p,A} : A[p := true] → A[p := false] → ∀p A` (p. 2 & p. 4). -/
def indBoolFormula (p : Var) (A : Formula) : Formula :=
  .imp
    (substFormula A p (.const .trueConst))
    (.imp
      (substFormula A p (.const .falseConst))
      (.all p A))

/-- Typing / derivability judgment `Derivable sys M A` for natural deduction proof terms `M`
in system `sys ∈ {Z^X, Z, Z_0^X, Z_0}` (Section 2, p. 4). -/
inductive Derivable (sys : SysConfig) : ProofTerm → Formula → Prop where
  | assump (u : AssumpVar) :
      sys.allowsFormula u.formula →
      Derivable sys (.assump u) u.formula
  | indNat (n : Var) (A : Formula) :
      n.ty = .iota →
      sys.allowsFormula A →
      Derivable sys (.indNat n A) (indNatFormula n A)
  | indBool (p : Var) (A : Formula) :
      p.ty = .bool →
      sys.allowsFormula A →
      Derivable sys (.indBool p A) (indBoolFormula p A)
  | axTrue :
      Derivable sys .axTrue (.atom (.const .trueConst))
  | axFalse (A : Formula) :
      sys.allowsFormula A →
      Derivable sys (.axFalse A) (.imp Formula.falseAtom A)
  | efq (A : Formula) :
      sys.allowEfq = true →
      sys.allowsFormula A →
      Derivable sys (.efq A) (.imp .bot A)
  | lamAssump (u : AssumpVar) {M : ProofTerm} {B : Formula} :
      sys.allowsFormula u.formula →
      Derivable sys M B →
      Derivable sys (.lamAssump u M) (.imp u.formula B)
  | appAssump {M N : ProofTerm} {A B : Formula} :
      Derivable sys M (.imp A B) →
      Derivable sys N A →
      Derivable sys (.appAssump M N) B
  | lamTerm (x : Var) {M : ProofTerm} {A : Formula} :
      (∀ u ∈ freeAssumpVars M, x ∉ freeVarsFormula u.formula) →
      Derivable sys M A →
      Derivable sys (.lamTerm x M) (.all x A)
  | appTerm {M : ProofTerm} {x : Var} {A : Formula} (t : Term) :
      HasType t x.ty →
      Derivable sys M (.all x A) →
      Derivable sys (.appTerm M t) (substFormula A x t)
  | conv {M : ProofTerm} {A B : Formula} :
      Derivable sys M A →
      sys.allowsFormula B →
      FormulaBetaREq A B →
      Derivable sys M B

/-- Closed derivability `sys ⊢ A` (`Provable sys A`, Section 2, pp. 4–5):
there is a derivation `M` of `A` in `sys` with no free assumption variables (`FA(M) = ∅`). -/
def Provable (sys : SysConfig) (A : Formula) : Prop :=
  ∃ M : ProofTerm, Derivable sys M A ∧ freeAssumpVars M = []

end BBS2002


