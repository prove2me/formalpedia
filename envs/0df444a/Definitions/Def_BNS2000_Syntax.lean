-- Prove2me | Definitions.Def_BNS2000_Syntax
-- name    : BNS2000_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T04:07:45.680737+00:00
-- url     : https://prove2.me/theorems/524b25b3-0657-4c05-9ec3-3206a0778e9e
-- title:
--   Sections 2-3: Simple Types, Binary Word Constants, Higher-Type Recursion, and the Bellantoni-Cook Algebra BC
-- statement:
--   Formalizes Sections 2-3 of Bellantoni, Niggl, and Schwichtenberg (2000): ground types `ι_j` and arrow types, binary word constants `0, S₀, S₁, P, C, R_σ`, capture-avoiding substitution, conversion rules `(β_ι), (β_→), (C), (R)`, term equivalence `≃`, the Bellantoni-Cook safe recursion algebra `BC` (`BCFunc`, `evalBC`), and polynomials (`IsPolyBound`, `IsUnivariatePoly`).
-- source:
--   Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg, 'Higher type recursion, ramification and polynomial time', Annals of Pure and Applied Logic 104, 2000, pp. 17-30 (doi:10.1016/S0168-0072(00)00006-3). Sections 2-3, pp. 18-21.

import Std

/-!
# Types, Constants, Terms, Conversions, and Semantics (Bellantoni–Niggl–Schwichtenberg 2000, Section 2)

Source: Stephen Bellantoni, Karl-Heinz Niggl, and Helmut Schwichtenberg,
"Higher type recursion, ramification and polynomial time",
*Annals of Pure and Applied Logic* 104, 2000, pp. 17–30 (Section 2, pp. 18–19 / preprint pp. 2–3).

This module formalizes:
- Ramified types `Ty`: ground type `ι` (`Ty.iota`), function types `σ → τ` (`Ty.arr`),
  and complete types `!σ` (`Ty.bang`).
- Type classifications: `IsComplete`, `IsIncomplete`, `level`, `IsGround`, `IsHigherType`,
  and `IsSafe` (`!`-free types).
- Constants `Const`: `0`, `s₀`, `s₁`, `p`, `c_σ` (for safe `σ`), and `R_σ` (for safe `σ`).
- Typed terms `Term` with `λ`-abstraction, application, `!r`, and `rκ`, along with typing
  `HasType`, term length `|t|` (`termLength`), free variables `FV(t)` (`freeVars`), and
  free occurrence count `FO(x, t)` (`freeOccCount`).
- Binary numerals (`IsBinaryNumeral`, `IsPositiveBinaryNumeral`), general numerals
  (`IsNumeral`, preceded by any number of `!`'s), and the conversion rules (`ConvStep`),
  one-step reduction (`Step`), multi-step reduction (`ReducesTo`), normal forms (`IsNormal`,
  `IsNormalFormOf`), and term equivalence (`TermEquiv`).
- Set-theoretic denotational semantics `⟦t⟧_φ` (`SemTy`, `evalTerm`) identifying `⟦!σ⟧` with `⟦σ⟧`
  and `⟦ι⟧` with `Nat`.
-/

namespace BNS2000

/-- Ramified finite types (Section 2, p. 18):
`σ, τ ::= ι | σ → τ | !σ`. -/
inductive Ty where
  | iota : Ty
  | arr : Ty → Ty → Ty
  | bang : Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Types of the form `!σ` are *complete*; all others are *incomplete* (Section 2, p. 18). -/
def isComplete : Ty → Bool
  | .bang _ => true
  | _ => false

/-- Incomplete types (Section 2, p. 18). -/
def isIncomplete (σ : Ty) : Bool :=
  !isComplete σ

/-- Type level `l(σ)` (Section 2, p. 18):
- `l(ι) = 0`
- `l(!σ) = l(σ)`
- `l(σ → τ) = max(l(τ), 1 + l(σ))`. -/
def level : Ty → Nat
  | .iota => 0
  | .bang σ => level σ
  | .arr σ τ => Nat.max (level τ) (1 + level σ)

/-- *Ground types* are the types of level `0` (Section 2, p. 18). -/
def isGround (σ : Ty) : Bool :=
  level σ == 0

/-- A *higher type* is any type of level at least `1` (Section 2, pp. 18–19). -/
def isHigherType (σ : Ty) : Bool :=
  decide (level σ ≥ 1)

/-- `!`-free types are called *safe* (Section 2, p. 19). -/
def isSafe : Ty → Bool
  | .iota => true
  | .arr σ τ => isSafe σ && isSafe τ
  | .bang _ => false

/-- Iterated arrow type `σ₁ → ⋯ → σₖ → τ`. -/
def arrMany : List Ty → Ty → Ty
  | [], τ => τ
  | σ :: σs, τ => .arr σ (arrMany σs τ)

end Ty

/-- Constant symbols (Section 2, p. 19):
- `0 : ι`
- `s₀ : ι → ι` (`x ↦ 2 · x`)
- `s₁ : ι → ι` (`x ↦ 2 · x + 1`)
- `p : ι → ι` (`x ↦ ⌊x / 2⌋`)
- `c_σ : ι → σ → σ → σ → σ` for `σ` safe (cases in type `σ`)
- `R_σ : σ → !(!ι → σ → σ) → !ι → σ` for `σ` safe (recursion on notation in type `σ`). -/
inductive Const where
  | zero : Const
  | s0 : Const
  | s1 : Const
  | pred : Const
  | cases : Ty → Const
  | recursor : Ty → Const
  deriving DecidableEq, Repr

namespace Const

/-- Side condition that `c_σ` and `R_σ` are admitted for safe (`!`-free) types `σ` only (p. 19). -/
def isWellFormed : Const → Bool
  | .zero | .s0 | .s1 | .pred => true
  | .cases σ | .recursor σ => σ.isSafe

/-- Type of a constant symbol (Section 2, p. 19). -/
def ty : Const → Ty
  | .zero => .iota
  | .s0 => .arr .iota .iota
  | .s1 => .arr .iota .iota
  | .pred => .arr .iota .iota
  | .cases σ => .arr .iota (.arr σ (.arr σ (.arr σ σ)))
  | .recursor σ => .arr σ (.arr (.bang (.arr (.bang .iota) (.arr σ σ))) (.arr (.bang .iota) σ))

end Const

/-- Typed variable `x^σ` (Section 2, p. 19). -/
structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

/-- Terms built from constants and typed variables by introduction and elimination rules
for `σ → τ` and `!σ` (Section 2, p. 19):
`x^σ`, `c`, `(λx^σ. r^τ)^{σ→τ}`, `(r^{σ→τ} s^σ)^τ`, `(!r^σ)^{!σ}`, `(r^{!σ} κ)^σ`. -/
inductive Term where
  | var : Var → Term
  | const : Const → Term
  | lam : Var → Term → Term
  | app : Term → Term → Term
  | bang : Term → Term
  | kappa : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Left-associated application of a term `t` to a list of argument terms `s₁ ... sₙ`. -/
def appMany : Term → List Term → Term
  | t, [] => t
  | t, s :: ss => appMany (.app t s) ss

/-- Multi-variable λ-abstraction `λx₁ ... xₖ. r`. -/
def lamMany : List Var → Term → Term
  | [], r => r
  | x :: xs, r => .lam x (lamMany xs r)

end Term

/-- Typing relation `HasType r τ` (Section 2, p. 19), including the requirement that all
`c_σ` and `R_σ` constants have safe `σ`. -/
inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | const (c : Const) :
      c.isWellFormed = true →
      HasType (.const c) c.ty
  | lam (x : Var) {r : Term} {τ : Ty} :
      HasType r τ →
      HasType (.lam x r) (.arr x.ty τ)
  | app {r s : Term} {σ τ : Ty} :
      HasType r (.arr σ τ) →
      HasType s σ →
      HasType (.app r s) τ
  | bang {r : Term} {σ : Ty} :
      HasType r σ →
      HasType (.bang r) (.bang σ)
  | kappa {r : Term} {σ : Ty} :
      HasType r (.bang σ) →
      HasType (.kappa r) σ

/-- Every well-typed term `t` has a unique intrinsic type `inferTy t`. -/
def inferTy : Term → Ty
  | .var x => x.ty
  | .const c => c.ty
  | .lam x r => .arr x.ty (inferTy r)
  | .app r _ =>
      match inferTy r with
      | .arr _ τ => τ
      | τ => τ
  | .bang r => .bang (inferTy r)
  | .kappa r =>
      match inferTy r with
      | .bang σ => σ
      | σ => σ

/-- The length `|t|` of a term `t` (Section 2, p. 19):
- `|x| = |c| = 1`
- `|λx. r| = |!r| = |rκ| = |r| + 1`
- `|r s| = |r| + |s| + 1`. -/
def termLength : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ r => termLength r + 1
  | .app r s => termLength r + termLength s + 1
  | .bang r => termLength r + 1
  | .kappa r => termLength r + 1

/-- Number of free occurrences `FO(x, t)` of `x` in `t` (Section 2, p. 19). -/
def freeOccCount (x : Var) : Term → Nat
  | .var y => if y == x then 1 else 0
  | .const _ => 0
  | .lam y r => if y == x then 0 else freeOccCount x r
  | .app r s => freeOccCount x r + freeOccCount x s
  | .bang r => freeOccCount x r
  | .kappa r => freeOccCount x r

/-- List of all free variable occurrences in `t`. -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x r => (freeVarOccurrences r).filter (· != x)
  | .app r s => freeVarOccurrences r ++ freeVarOccurrences s
  | .bang r => freeVarOccurrences r
  | .kappa r => freeVarOccurrences r

/-- Set of free variables `FV(t)` (duplicate-free list, Section 2, p. 19). -/
def freeVars (t : Term) : List Var :=
  (freeVarOccurrences t).eraseDups

/-- All variables (both free and bound) occurring in `t`. -/
def allVars : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x r => x :: allVars r
  | .app r s => allVars r ++ allVars s
  | .bang r => allVars r
  | .kappa r => allVars r

/-- A term `t` is closed if `FV(t) = ∅`. -/
def IsClosed (t : Term) : Prop :=
  freeVars t = []

/-- Maximum variable `id` occurring in `t`. -/
def maxVarId : Term → Nat
  | .var x => x.id
  | .const _ => 0
  | .lam x r => Nat.max x.id (maxVarId r)
  | .app r s => Nat.max (maxVarId r) (maxVarId s)
  | .bang r => maxVarId r
  | .kappa r => maxVarId r

/-- Replace free occurrences of `x` with `y` in `t`. -/
def renameFreeVar (t : Term) (x y : Var) : Term :=
  match t with
  | .var v => if v == x then .var y else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)
  | .app r s => .app (renameFreeVar r x y) (renameFreeVar s x y)
  | .bang r => .bang (renameFreeVar r x y)
  | .kappa r => .kappa (renameFreeVar r x y)

theorem renameFreeVar_termLength (t : Term) (x y : Var) :
    termLength (renameFreeVar t x y) = termLength t := by
  induction t with
  | var v => simp only [renameFreeVar]; split <;> rfl
  | const c => rfl
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [termLength, ih]
  | app r s ihr ihs => simp [renameFreeVar, termLength, ihr, ihs]
  | bang r ih => simp [renameFreeVar, termLength, ih]
  | kappa r ih => simp [renameFreeVar, termLength, ih]

/-- Capture-avoiding substitution `r[s/x]` (Section 2, p. 19). -/
def substTerm (r : Term) (x : Var) (s : Term) : Term :=
  match r with
  | .var v => if v == x then s else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then
        .lam v body
      else if v ∈ freeVarOccurrences s then
        let freshId := Nat.max (maxVarId body) (Nat.max (maxVarId s) x.id) + 1
        let v' : Var := ⟨freshId, v.ty⟩
        .lam v' (substTerm (renameFreeVar body v v') x s)
      else
        .lam v (substTerm body x s)
  | .app t u => .app (substTerm t x s) (substTerm u x s)
  | .bang t => .bang (substTerm t x s)
  | .kappa t => .kappa (substTerm t x s)
termination_by termLength r
decreasing_by
  all_goals
    simp_wf
    simp [termLength, renameFreeVar_termLength]
    try omega

/-- Simultaneous environment substitution `t[n⃗/x⃗]` for closed/disjoint environment terms `n⃗` (p. 23). -/
def substEnv : Term → List (Var × Term) → Term
  | t, [] => t
  | t, (x, n) :: rest => substEnv (substTerm t x n) rest

/-- Non-zero binary numerals `s_{i₁} ... s_{iₖ} s₁ 0` where `iⱼ ∈ {0, 1}` (Section 2, p. 19). -/
def isPositiveBinaryNumeral : Term → Bool
  | .app (.const .s1) (.const .zero) => true
  | .app (.const .s0) n => isPositiveBinaryNumeral n
  | .app (.const .s1) n => isPositiveBinaryNumeral n
  | _ => false

/-- A *binary numeral* is either `0` or `s_{i₁} ... s_{iₖ} s₁ 0` where `iⱼ ∈ {0, 1}` (Section 2, p. 19). -/
def isBinaryNumeral (t : Term) : Bool :=
  (t == .const .zero) || isPositiveBinaryNumeral t

/-- A *numeral* is a binary numeral preceded by any number of `!`'s (Section 4, p. 22). -/
def isNumeral : Term → Bool
  | .bang r => isNumeral r
  | t => isBinaryNumeral t

/-- Prepend `m` applications of `!` to a term `t`. -/
def bangRepeat : Nat → Term → Term
  | 0, t => t
  | m + 1, t => .bang (bangRepeat m t)

/-- Canonical positive binary numeral for `n + 1` via binary digits. -/
def posBinaryNumeralOfNat (n : Nat) : Term :=
  if h : n == 0 then
    .app (.const .s1) (.const .zero)
  else
    let m := n + 1
    let half := m / 2 - 1
    if m % 2 == 0 then
      .app (.const .s0) (posBinaryNumeralOfNat half)
    else
      .app (.const .s1) (posBinaryNumeralOfNat half)
termination_by n
decreasing_by
  all_goals
    simp_wf
    have hne : n ≠ 0 := by
      intro h0
      subst h0
      contradiction
    omega

/-- Canonical binary numeral for `n : Nat` (Section 2, p. 19). -/
def binaryNumeralOfNat : Nat → Term
  | 0 => .const .zero
  | n + 1 => posBinaryNumeralOfNat n

/-- Value `natOfBinaryNumeral t` of a binary numeral `t` (or arbitrary ground term built from `0, s₀, s₁`). -/
def natOfBinaryNumeral : Term → Nat
  | .const .zero => 0
  | .app (.const .s0) n => 2 * natOfBinaryNumeral n
  | .app (.const .s1) n => 2 * natOfBinaryNumeral n + 1
  | .bang r => natOfBinaryNumeral r
  | .kappa r => natOfBinaryNumeral r
  | _ => 0

/-- Binary length `|n| = ⌈log₂(n + 1)⌉` of a natural number `n` (Section 1, p. 17). -/
def binaryBitLength (n : Nat) : Nat :=
  if h : n == 0 then 0 else binaryBitLength (n / 2) + 1
termination_by n
decreasing_by
  simp_wf
  have hne : n ≠ 0 := by intro h0; subst h0; contradiction
  omega

/-- Conversion rules `redex ↦ contractum` (Section 2, p. 19):
- `(λx. r) s ↦ r[s/x]`
- `(!r) κ ↦ r`
- `s₀ 0 ↦ 0`
- `p 0 ↦ 0`
- `p (sᵢ n) ↦ n` (where `sᵢ n` is a binary numeral, hence distinct from `0`)
- `c 0 r t₀ t₁ ↦ r`
- `c (sᵢ n) r t₀ t₁ ↦ tᵢ` (where `sᵢ n` is a binary numeral)
- `R g h !0 ↦ g`
- `R g h !(sᵢ n) ↦ h κ !(sᵢ n) (R g h !n)` (where `sᵢ n` is a binary numeral). -/
inductive ConvStep : Term → Term → Prop where
  | beta (x : Var) (r s : Term) :
      ConvStep (.app (.lam x r) s) (substTerm r x s)
  | bangKappa (r : Term) :
      ConvStep (.kappa (.bang r)) r
  | s0Zero :
      ConvStep (.app (.const .s0) (.const .zero)) (.const .zero)
  | predZero :
      ConvStep (.app (.const .pred) (.const .zero)) (.const .zero)
  | predSucc0 (n : Term) :
      isPositiveBinaryNumeral (.app (.const .s0) n) = true →
      ConvStep (.app (.const .pred) (.app (.const .s0) n)) n
  | predSucc1 (n : Term) :
      isPositiveBinaryNumeral (.app (.const .s1) n) = true →
      ConvStep (.app (.const .pred) (.app (.const .s1) n)) n
  | casesZero (σ : Ty) (r t₀ t₁ : Term) :
      ConvStep
        (.app (.app (.app (.app (.const (.cases σ)) (.const .zero)) r) t₀) t₁)
        r
  | casesSucc0 (σ : Ty) (n r t₀ t₁ : Term) :
      isPositiveBinaryNumeral (.app (.const .s0) n) = true →
      ConvStep
        (.app (.app (.app (.app (.const (.cases σ)) (.app (.const .s0) n)) r) t₀) t₁)
        t₀
  | casesSucc1 (σ : Ty) (n r t₀ t₁ : Term) :
      isPositiveBinaryNumeral (.app (.const .s1) n) = true →
      ConvStep
        (.app (.app (.app (.app (.const (.cases σ)) (.app (.const .s1) n)) r) t₀) t₁)
        t₁
  | recZero (σ : Ty) (g h : Term) :
      ConvStep
        (.app (.app (.app (.const (.recursor σ)) g) h) (.bang (.const .zero)))
        g
  | recSucc0 (σ : Ty) (g h n : Term) :
      isPositiveBinaryNumeral (.app (.const .s0) n) = true →
      ConvStep
        (.app (.app (.app (.const (.recursor σ)) g) h) (.bang (.app (.const .s0) n)))
        (.app (.app (.kappa h) (.bang (.app (.const .s0) n)))
          (.app (.app (.app (.const (.recursor σ)) g) h) (.bang n)))
  | recSucc1 (σ : Ty) (g h n : Term) :
      isPositiveBinaryNumeral (.app (.const .s1) n) = true →
      ConvStep
        (.app (.app (.app (.const (.recursor σ)) g) h) (.bang (.app (.const .s1) n)))
        (.app (.app (.kappa h) (.bang (.app (.const .s1) n)))
          (.app (.app (.app (.const (.recursor σ)) g) h) (.bang n)))

/-- One-step contextual reduction `r → r'` (Section 2, p. 19 & Section 3, p. 20). -/
inductive Step : Term → Term → Prop where
  | conv {r r' : Term} : ConvStep r r' → Step r r'
  | lam (x : Var) {r r' : Term} : Step r r' → Step (.lam x r) (.lam x r')
  | appLeft {r r' s : Term} : Step r r' → Step (.app r s) (.app r' s)
  | appRight {r s s' : Term} : Step s s' → Step (.app r s) (.app r s')
  | bang {r r' : Term} : Step r r' → Step (.bang r) (.bang r')
  | kappa {r r' : Term} : Step r r' → Step (.kappa r) (.kappa r')

/-- Reflexive-transitive reduction `r →* r'`. -/
inductive ReducesTo : Term → Term → Prop where
  | refl (r : Term) : ReducesTo r r
  | step {r s t : Term} : Step r s → ReducesTo s t → ReducesTo r t

/-- A term `t` is a redex if `ConvStep t t'` holds for some `t'` (Section 2, p. 19). -/
def IsRedex (t : Term) : Prop :=
  ∃ t' : Term, ConvStep t t'

/-- A term `t` is in *normal form* if it contains no redex, i.e. cannot be reduced (Section 2, p. 19). -/
def IsNormal (t : Term) : Prop :=
  ¬∃ t' : Term, Step t t'

/-- `nf_t` is the normal form `nf(t)` of `t` (Section 2, p. 19). -/
def IsNormalFormOf (t nf_t : Term) : Prop :=
  ReducesTo t nf_t ∧ IsNormal nf_t

/-- Two terms are *equivalent* if they have the same normal form (Section 2, p. 19). -/
def TermEquiv (t s : Term) : Prop :=
  ∃ u : Term, IsNormalFormOf t u ∧ IsNormalFormOf s u

/-- Set-theoretic interpretation of types (Section 2, p. 19):
- `⟦ι⟧ = Nat`
- `⟦!σ⟧ = ⟦σ⟧`
- `⟦σ → τ⟧ = ⟦σ⟧ → ⟦τ⟧`. -/
def SemTy : Ty → Type
  | .iota => Nat
  | .bang σ => SemTy σ
  | .arr σ τ => SemTy σ → SemTy τ

/-- Binary recursion on notation `recNat G H n` over `Nat`:
- `recNat G H 0 = G`
- `recNat G H m = H m (recNat G H (m / 2))` for `m > 0`. -/
def recNat {α : Type} (G : α) (H : Nat → α → α) (n : Nat) : α :=
  if h : n == 0 then
    G
  else
    H n (recNat G H (n / 2))
termination_by n
decreasing_by
  simp_wf
  have hne : n ≠ 0 := by intro h0; subst h0; contradiction
  omega

/-- Set-theoretic interpretation `⟦c⟧` of constants (Section 2, p. 19). -/
def evalConst : (c : Const) → SemTy c.ty
  | .zero => (0 : Nat)
  | .s0 => fun (x : Nat) => 2 * x
  | .s1 => fun (x : Nat) => 2 * x + 1
  | .pred => fun (x : Nat) => x / 2
  | .cases _ => fun (n : Nat) r t₀ t₁ =>
      if n == 0 then r else if n % 2 == 0 then t₀ else t₁
  | .recursor _ => fun g h n => recNat g h n

/-- Set-theoretic environment `φ` mapping each variable `x^σ` to `SemTy σ`. -/
abbrev SemEnv := (x : Var) → SemTy x.ty

/-- Update a semantic environment `φ[x ↦ v]`. -/
def updateSemEnv (φ : SemEnv) (x : Var) (v : SemTy x.ty) : SemEnv :=
  fun y => if h : y = x then h ▸ v else φ y

/-- Default inhabitant of `SemTy τ` (with `0 : Nat` at base type `ι`). -/
def defaultSem : (τ : Ty) → SemTy τ
  | .iota => (0 : Nat)
  | .bang σ => defaultSem σ
  | .arr _ τ => fun _ => defaultSem τ

/-- Coerce a semantic value from `SemTy σ` to `SemTy τ` when `σ = τ`. -/
def castSem (σ τ : Ty) (v : SemTy σ) : SemTy τ :=
  if h : σ = τ then h ▸ v else defaultSem τ

/-- Set-theoretic value `⟦t⟧_φ` of a term `t` at type `τ` in environment `φ` (Section 2, p. 19),
where `⟦!r⟧_φ := ⟦r⟧_φ` and `⟦rκ⟧_φ := ⟦r⟧_φ`. -/
def evalTerm (t : Term) (τ : Ty) (φ : SemEnv) : SemTy τ :=
  match t, τ with
  | .var x, τ => castSem x.ty τ (φ x)
  | .const c, τ => castSem c.ty τ (evalConst c)
  | .lam x r, .arr σ ρ =>
      fun v => evalTerm r ρ (updateSemEnv φ x (castSem σ x.ty v))
  | .app r s, τ =>
      let σ := inferTy s
      (evalTerm r (.arr σ τ) φ) (evalTerm s σ φ)
  | .bang r, .bang σ => evalTerm r σ φ
  | .kappa r, τ => evalTerm r (.bang τ) φ
  | _, τ => defaultSem τ

end BNS2000


