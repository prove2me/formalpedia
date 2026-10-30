-- Prove2me | Definitions.Def_ABHS2004_TermSystem
-- name    : ABHS2004_TermSystem
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:06.366373+00:00
-- url     : https://prove2.me/theorems/aee9d687-6c4e-4dcc-8a9a-6a87e20650f5
-- title:
--   Section 2: Types, Linear/Passive Contexts, Affine Terms, and Denotational Semantics
-- statement:
--   Formalizes Section 2 of Aehlig, Berger, Hofmann, and Schwichtenberg (2004): the full and `!`-free type systems, constants (including `if`, `case`, `destr`, and higher-type iteration `it_ρ` restricted to `!`-free result types), linear (`Γ`) and passive (`Δ`) typing judgments `Δ; Γ ⊢ M : ρ`, the operational reduction relation `↦` (Definitions 2.5 and 2.7), term and value size bounds `|M|` and `‖v‖` (Definition 2.9), polynomial-time Turing computability, and set-theoretic denotational semantics `⟦M⟧_η`.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Section 2, pp. 6-14.

import Std

/-!
# Term system for non-size-increasing polynomial-time computation (ABHS 2004, Section 2)

Source: Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg,
"An arithmetic for non-size-increasing polynomial-time computation",
*Theoretical Computer Science* 318(1–2), 2004, pp. 3–27, Section 2 (pp. 3–9).

This module formalizes:
- Definition 2.1: Finite linear types (`Ty`) and Remark 2.3 abbreviations (`B`, `N`, `Bin`).
- Definition 2.2: Set model carrier `SetModel` (`S^ρ`).
- Definition 2.4 & 2.5: Raw terms (`Term`) and typed constants (`Const`).
- Definition 2.6: Linear typing judgment `HasType` (`r^ρ`) and weak typing `WeaklyTyped`
  (Section 3.1, p. 10).
- Definition 2.8, 2.9, 2.10: Lists (`listEntryCount`, `IsListTerm`), conversions (`ConvStep`),
  one-step reduction (`RedStep`), multi-step reduction (`RedStar`, `RedSteps`), and normal
  forms (`IsNormal`).
- Definition 2.12 & Proposition 2.13: Almost closed terms (`IsAlmostClosed`) and canonical
  normal forms (`HasCanonicalNormalForm`).
- Definition 2.14, 2.15, 2.16: Projections `pi0`, `pi1` and pairing helpers.
- Definition 2.17 & 2.20: List bound `#_n(r)` (`hashBound`), polynomial step measure
  `ϑ_n(r)` (`theta`), bounded-free-variable reduction `RedStepBounded` (`r →_n r'`),
  iteration nesting depth (`iterNesting`), and syntactical length (`termLength`).
- Definition 2.24: Data types (`IsDataType`), data objects (`IsDataObject`), and
  non-size-increasing polynomial-time computability on data objects.
-/

namespace ABHS2004

/-- Definition 2.1 (Finite linear types, p. 3):
`ρ, σ ::= U | ⋄ | L(ρ) | ρ ⊸ σ | ρ ⊗ σ | ρ × σ | ρ + σ`. -/
inductive Ty where
  | unit : Ty
  | diamond : Ty
  | list : Ty → Ty
  | lolli : Ty → Ty → Ty
  | tensor : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  | sum : Ty → Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Remark 2.3 (p. 3): Booleans `B := U + U`. -/
def bool : Ty := .sum .unit .unit

/-- Remark 2.3 (p. 3): Unary natural numbers `N := L(U)`. -/
def nat : Ty := .list .unit

/-- Remark 2.3 (p. 3): Binary natural numbers `Bin := L(B)`. -/
def bin : Ty := .list bool

/-- Iterated linear function type `ρ₁ ⊸ ⋯ ⊸ ρₙ ⊸ τ`. -/
def lolliMany : List Ty → Ty → Ty
  | [], τ => τ
  | ρ :: ρs, τ => .lolli ρ (lolliMany ρs τ)

end Ty

/-- Definition 2.2 (Set model, p. 3):
In the naive set model every type `ρ` is interpreted by the set `S^ρ`, where `U` is a
singleton set, `⋄` is an unspecified nonempty set (modeled here by `Unit`), `L(ρ)` is `List S^ρ`,
`ρ ⊸ σ` is the full function space `S^ρ → S^σ`, `ρ ⊗ σ` and `ρ × σ` are the Cartesian product,
and `ρ + σ` is the disjoint sum. -/
def SetModel : Ty → Type
  | .unit => PUnit
  | .diamond => Unit
  | .list ρ => List (SetModel ρ)
  | .lolli ρ σ => SetModel ρ → SetModel σ
  | .tensor ρ σ => SetModel ρ × SetModel σ
  | .prod ρ σ => SetModel ρ × SetModel σ
  | .sum ρ σ => Sum (SetModel ρ) (SetModel σ)

/-- Typed term variable `x^ρ` (p. 4). Each variable has an identifier and a fixed type `ρ`. -/
structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

/-- Definition 2.5 (Constants, p. 4). -/
inductive Const where
  | eps : Const
  | nil : Ty → Const
  | cons : Ty → Const
  | tensorIntro : Ty → Ty → Const
  | tensorElim : Ty → Ty → Ty → Const
  | prodIntro : Ty → Ty → Ty → Const
  | fst : Ty → Ty → Const
  | snd : Ty → Ty → Const
  | inl : Ty → Ty → Const
  | inr : Ty → Ty → Const
  | sumElim : Ty → Ty → Ty → Const
  deriving DecidableEq, Repr

/-- Type assignment `c : ρ` for constants from Definition 2.5 (p. 4). -/
def Const.ty : Const → Ty
  | .eps => .unit
  | .nil ρ => .list ρ
  | .cons ρ => .lolli .diamond (.lolli ρ (.lolli (.list ρ) (.list ρ)))
  | .tensorIntro ρ σ => .lolli ρ (.lolli σ (.tensor ρ σ))
  | .tensorElim ρ σ τ => .lolli (.tensor ρ σ) (.lolli (.lolli ρ (.lolli σ τ)) τ)
  | .prodIntro ρ σ τ =>
      .lolli (.lolli τ ρ) (.lolli (.lolli τ σ) (.lolli τ (.prod ρ σ)))
  | .fst ρ σ => .lolli (.prod ρ σ) ρ
  | .snd ρ σ => .lolli (.prod ρ σ) σ
  | .inl ρ σ => .lolli ρ (.sum ρ σ)
  | .inr ρ σ => .lolli σ (.sum ρ σ)
  | .sumElim ρ σ τ =>
      .lolli (.sum ρ σ) (.lolli (.prod (.lolli ρ τ) (.lolli σ τ)) τ)

/-- Constructors of the term calculus (Axiom 22, p. 15 & Remark 3.11(4), p. 16):
`ε, ⊗⁺, inl, inr, nil, cons`. -/
def Const.isConstructor : Const → Bool
  | .eps => true
  | .tensorIntro _ _ => true
  | .inl _ _ => true
  | .inr _ _ => true
  | .nil _ => true
  | .cons _ => true
  | _ => false

/-- Definition 2.4 (Terms, p. 4):
`r, s ::= x^ρ | c | λx^ρ r | rs | r{s}`. -/
inductive Term where
  | var : Var → Term
  | const : Const → Term
  | lam : Var → Term → Term
  | app : Term → Term → Term
  | iter : Term → Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Multi-argument application `r s₁ ... sₙ`. -/
def appMany : Term → List Term → Term
  | r, [] => r
  | r, s :: ss => appMany (.app r s) ss

/-- Multi-variable lambda abstraction `λ x₁ ... xₙ. r`. -/
def lamMany : List Var → Term → Term
  | [], r => r
  | x :: xs, r => .lam x (lamMany xs r)

/-- Identity combinator `id_ρ := λ x^ρ. x^ρ`. -/
def idTerm (ρ : Ty) : Term :=
  let x : Var := ⟨0, ρ⟩
  .lam x (.var x)

/-- Boolean constant `tt := inl_{U,U} ε` (Remark 3.2, p. 10). -/
def tt : Term := .app (.const (.inl .unit .unit)) (.const .eps)

/-- Boolean constant `ff := inr_{U,U} ε` (Remark 3.2, p. 10). -/
def ff : Term := .app (.const (.inr .unit .unit)) (.const .eps)

/-- Zero numeral `0 := nil_U` (Example 2.15, p. 6). -/
def zeroNat : Term := .const (.nil .unit)

/-- Successor operation `S d r := cons_U d ε r` (Example 2.15, p. 6). -/
def succNat (d r : Term) : Term :=
  .app (.app (.app (.const (.cons .unit)) d) (.const .eps)) r

/-- Definition 2.14 (Projections, p. 6):
`π₀(r) := ⊗⁻_{ρσρ} r (λx^ρ, y^σ. x)`. -/
def pi0 (ρ σ : Ty) (r : Term) : Term :=
  let x : Var := ⟨0, ρ⟩
  let y : Var := ⟨1, σ⟩
  .app (.app (.const (.tensorElim ρ σ ρ)) r) (.lam x (.lam y (.var x)))

/-- Definition 2.14 (Projections, p. 6):
`π₁(r) := ⊗⁻_{ρσσ} r (λx^ρ, y^σ. y)`. -/
def pi1 (ρ σ : Ty) (r : Term) : Term :=
  let x : Var := ⟨0, ρ⟩
  let y : Var := ⟨1, σ⟩
  .app (.app (.const (.tensorElim ρ σ σ)) r) (.lam x (.lam y (.var y)))

end Term

/-- Free variable occurrences of a term `r`, as a list preserving multiplicity
(Definition 2.4, p. 4 and Definition 2.20, p. 8: `|FV(s)|` is the number of occurrences
of free variables in `s`). -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x r => (freeVarOccurrences r).filter (· != x)
  | .app r s => freeVarOccurrences r ++ freeVarOccurrences s
  | .iter r s => freeVarOccurrences r ++ freeVarOccurrences s

/-- Underlying set of free variables `FV(r)` (represented as a duplicate-free list). -/
def freeVars (r : Term) : List Var :=
  (freeVarOccurrences r).eraseDups

/-- Number of occurrences of free variables `|FV(r)|` (Definition 2.20, p. 8). -/
def freeVarCount (r : Term) : Nat :=
  (freeVarOccurrences r).length

/-- Disjointness of free variables `FV(r) ∩ FV(s) = ∅`. -/
def DisjointFV (r s : Term) : Prop :=
  ∀ v, v ∈ freeVarOccurrences r → v ∉ freeVarOccurrences s

/-- A term is closed if `FV(r) = ∅`. -/
def IsClosed (r : Term) : Prop :=
  freeVarOccurrences r = []

/-- Definition 2.12 (Almost closed terms, p. 6):
A term is almost closed if all its free variables are of type `⋄`. -/
def IsAlmostClosed (r : Term) : Prop :=
  ∀ v ∈ freeVarOccurrences r, v.ty = .diamond

/-- Maximum variable id occurring anywhere in a term (bound or free). -/
def maxVarId : Term → Nat
  | .var x => x.id
  | .const _ => 0
  | .lam x r => Nat.max x.id (maxVarId r)
  | .app r s => Nat.max (maxVarId r) (maxVarId s)
  | .iter r s => Nat.max (maxVarId r) (maxVarId s)

/-- Replace free occurrences of variable `x` with variable `y` in `r`. -/
def renameFreeVar (r : Term) (x y : Var) : Term :=
  match r with
  | .var v => if v == x then .var y else .var v
  | .const c => .const c
  | .lam v body =>
      if v == x then .lam v body else .lam v (renameFreeVar body x y)
  | .app t s => .app (renameFreeVar t x y) (renameFreeVar s x y)
  | .iter t s => .iter (renameFreeVar t x y) (renameFreeVar s x y)

/-- Syntactic size of a raw term used for termination of capture-avoiding substitution. -/
def rawSize : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ r => rawSize r + 1
  | .app r s => rawSize r + rawSize s + 1
  | .iter r s => rawSize r + rawSize s + 1

theorem renameFreeVar_rawSize (r : Term) (x y : Var) :
    rawSize (renameFreeVar r x y) = rawSize r := by
  induction r with
  | var v =>
      simp only [renameFreeVar]
      split <;> rfl
  | const c => rfl
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]
  | app t s iht ihs =>
      simp [renameFreeVar, rawSize, iht, ihs]
  | iter t s iht ihs =>
      simp [renameFreeVar, rawSize, iht, ihs]

/-- Capture-avoiding substitution `r[s/x]` (Definition 2.4, p. 4):
substitutes `s` for every free occurrence of `x` in `r`, renaming bound variables in `r`
if necessary to avoid capturing free variables of `s`. -/
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
  | .iter t u => .iter (substTerm t x s) (substTerm u x s)
termination_by rawSize r
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Simultaneous substitution `r[s₁/x₁, ..., sₙ/xₙ]` applied sequentially. -/
def substMany : Term → List (Var × Term) → Term
  | r, [] => r
  | r, (x, s) :: rest => substMany (substTerm r x s) rest

/-- Definition 2.6 (Typing, pp. 4–5):
The relation `HasType r ρ` (`r^ρ`, read "`r` has type `ρ`"). -/
inductive HasType : Term → Ty → Prop where
  | var (x : Var) :
      HasType (.var x) x.ty
  | const (c : Const) :
      HasType (.const c) c.ty
  | lam (x : Var) {r : Term} {σ : Ty} :
      HasType r σ →
      HasType (.lam x r) (.lolli x.ty σ)
  | app {r s : Term} {ρ σ : Ty} :
      HasType r (.lolli ρ σ) →
      HasType s ρ →
      DisjointFV r s →
      HasType (.app r s) σ
  | iter {r s : Term} {ρ τ : Ty} :
      HasType r (.list ρ) →
      HasType s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      IsClosed s →
      HasType (.iter r s) (.lolli τ τ)

/-- Weak typing (Section 3.1, p. 10):
"all restrictions on free variables (when typing terms of the form `rs` or `r{s}`) are dropped." -/
inductive WeaklyTyped : Term → Ty → Prop where
  | var (x : Var) :
      WeaklyTyped (.var x) x.ty
  | const (c : Const) :
      WeaklyTyped (.const c) c.ty
  | lam (x : Var) {r : Term} {σ : Ty} :
      WeaklyTyped r σ →
      WeaklyTyped (.lam x r) (.lolli x.ty σ)
  | app {r s : Term} {ρ σ : Ty} :
      WeaklyTyped r (.lolli ρ σ) →
      WeaklyTyped s ρ →
      WeaklyTyped (.app r s) σ
  | iter {r s : Term} {ρ τ : Ty} :
      WeaklyTyped r (.list ρ) →
      WeaklyTyped s (.lolli .diamond (.lolli ρ (.lolli τ τ))) →
      WeaklyTyped (.iter r s) (.lolli τ τ)

/-- Definition 2.8 (Lists, p. 5):
Terms of the form `cons_ρ d₁ r₁ (... (cons_ρ dₙ rₙ nil_ρ))` are lists with `n` entries.
`listEntryCount t` returns `some n` if `t` has this spine with `n` entries, and `none` otherwise. -/
def listEntryCount : Term → Option Nat
  | .const (.nil _) => some 0
  | .app (.app (.app (.const (.cons _)) _) _) l =>
      match listEntryCount l with
      | some k => some (k + 1)
      | none => none
  | _ => none

/-- Predicate asserting that `t` is a list in the sense of Definition 2.8 (p. 5). -/
def IsListTerm (t : Term) : Prop :=
  ∃ n, listEntryCount t = some n

/-- Definition 2.9 (Conversions, p. 5): `r ↦ r'`. -/
inductive ConvStep : Term → Term → Prop where
  | beta (x : Var) (r s : Term) :
      ConvStep (.app (.lam x r) s) (substTerm r x s)
  | tensorBeta (ρ σ τ : Ty) (r s t : Term) :
      ConvStep
        (.app (.app (.const (.tensorElim ρ σ τ))
          (.app (.app (.const (.tensorIntro ρ σ)) r) s)) t)
        (.app (.app t r) s)
  | fstBeta (ρ σ τ : Ty) (r s t : Term) :
      ConvStep
        (.app (.const (.fst ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app r t)
  | sndBeta (ρ σ τ : Ty) (r s t : Term) :
      ConvStep
        (.app (.const (.snd ρ σ))
          (.app (.app (.app (.const (.prodIntro ρ σ τ)) r) s) t))
        (.app s t)
  | inlBeta (ρ σ τ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inl ρ σ)) r)) s)
        (.app (.app (.const (.fst (.lolli ρ τ) (.lolli σ τ))) s) r)
  | inrBeta (ρ σ τ : Ty) (r s : Term) :
      ConvStep
        (.app (.app (.const (.sumElim ρ σ τ))
          (.app (.const (.inr ρ σ)) r)) s)
        (.app (.app (.const (.snd (.lolli ρ τ) (.lolli σ τ))) s) r)
  | iterNil (ρ : Ty) (s t : Term) :
      ConvStep (.app (.iter (.const (.nil ρ)) s) t) t
  | iterCons (ρ : Ty) (d r l s t : Term) :
      IsListTerm l →
      ConvStep
        (.app (.iter (.app (.app (.app (.const (.cons ρ)) d) r) l) s) t)
        (.app (.app (.app s d) r) (.app (.iter l s) t))

/-- Definition 2.10 (Reduction, p. 5): `r → r'`.
To reduce a term we may convert anywhere, except under `λ`. -/
inductive RedStep : Term → Term → Prop where
  | conv {r r' : Term} :
      ConvStep r r' → RedStep r r'
  | appLeft {r r' : Term} (s : Term) :
      RedStep r r' → RedStep (.app r s) (.app r' s)
  | appRight (r : Term) {s s' : Term} :
      RedStep s s' → RedStep (.app r s) (.app r s')
  | iterLeft {r r' : Term} (s : Term) :
      RedStep r r' → RedStep (.iter r s) (.iter r' s)
  | iterRight (r : Term) {s s' : Term} :
      RedStep s s' → RedStep (.iter r s) (.iter r s')

/-- Reflexive-transitive closure of reduction `r →* r'` (p. 6). -/
inductive RedStar : Term → Term → Prop where
  | refl (r : Term) : RedStar r r
  | step {r s t : Term} : RedStep r s → RedStar s t → RedStar r t

/-- Exact `k`-step reduction chain `r →^k r'`. -/
inductive RedSteps : Nat → Term → Term → Prop where
  | zero (r : Term) : RedSteps 0 r r
  | succ {k : Nat} {r s t : Term} :
      RedStep r s → RedSteps k s t → RedSteps (k + 1) r t

/-- A term is normal if it cannot be reduced (p. 6). -/
def IsNormal (r : Term) : Prop :=
  ¬ ∃ r', RedStep r r'

/-- Proposition 2.13 (Canonical forms of normal almost closed terms, p. 6):
- `U`: `ε`
- `⋄`: variable
- `L(ρ)`: list
- `ρ ⊗ σ`: `⊗⁺ r s`
- `ρ × σ`: `×⁺_{ρ,σ,τ} r s t`
- `ρ + σ`: `inl r` or `inr r`
- `ρ ⊸ σ`: `λx r` or `c r⃗` or `r{s}`. -/
def HasCanonicalNormalForm (τ : Ty) (w : Term) : Prop :=
  match τ with
  | .unit => w = .const .eps
  | .diamond => ∃ x : Var, x.ty = .diamond ∧ w = .var x
  | .list _ => IsListTerm w
  | .tensor ρ σ => ∃ r s, w = .app (.app (.const (.tensorIntro ρ σ)) r) s
  | .prod ρ σ => ∃ ν r s t, w = .app (.app (.app (.const (.prodIntro ρ σ ν)) r) s) t
  | .sum ρ σ =>
      (∃ r, w = .app (.const (.inl ρ σ)) r) ∨
      (∃ r, w = .app (.const (.inr ρ σ)) r)
  | .lolli _ _ =>
      (∃ x r, w = .lam x r) ∨
      (∃ c args, w = Term.appMany (.const c) args) ∨
      (∃ r s, w = .iter r s)

/-- Definition 2.17 (p. 7): `#_n(r)` returns `k` if `r` is a list with `k` entries and `k ≤ n`,
and `n` otherwise. -/
def hashBound (n : Nat) (r : Term) : Nat :=
  match listEntryCount r with
  | some k => if k ≤ n then k else n
  | none => n

/-- Definition 2.17 (pp. 7–8): Step-bounding functional `ϑ_n(r)`. -/
def theta (n : Nat) : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .app r s => theta n r + theta n s
  | .lam _ r => theta n r + 1
  | .iter r s => theta n r + (hashBound n r + 1) * theta n s

/-- Nesting depth of `{.}` in a term `r` (Section 2.3, pp. 7–9). -/
def iterNesting : Term → Nat
  | .var _ => 0
  | .const _ => 0
  | .lam _ r => iterNesting r
  | .app r s => Nat.max (iterNesting r) (iterNesting s)
  | .iter r s => Nat.max (iterNesting r) (iterNesting s + 1)

/-- Ordinary syntactical length `length(s)` of a term (Proposition 2.23, p. 9). -/
def termLength : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ r => termLength r + 1
  | .app r s => termLength r + termLength s
  | .iter r s => termLength r + termLength s

/-- Predicate stating that a term contains no `{.}` (Proposition 2.23, p. 9). -/
def IsIterFree (r : Term) : Prop :=
  iterNesting r = 0

/-- Definition 2.20 (p. 8): `r →_n r'` holds if `r → r'` by converting a subterm `s` of `r`
with `|FV(s)| ≤ n`, where `|FV(s)|` is the number of occurrences of free variables in `s`. -/
inductive RedStepBounded (n : Nat) : Term → Term → Prop where
  | conv {r r' : Term} :
      ConvStep r r' →
      freeVarCount r ≤ n →
      RedStepBounded n r r'
  | appLeft {r r' : Term} (s : Term) :
      RedStepBounded n r r' →
      RedStepBounded n (.app r s) (.app r' s)
  | appRight (r : Term) {s s' : Term} :
      RedStepBounded n s s' →
      RedStepBounded n (.app r s) (.app r s')
  | iterLeft {r r' : Term} (s : Term) :
      RedStepBounded n r r' →
      RedStepBounded n (.iter r s) (.iter r' s)
  | iterRight (r : Term) {s s' : Term} :
      RedStepBounded n s s' →
      RedStepBounded n (.iter r s) (.iter r s')

/-- Definition 2.24 (Data types, p. 9):
A type is called a data type if it is built from `U`, `L(.)`, `⊗`, and `+` only. -/
inductive IsDataType : Ty → Prop where
  | unit : IsDataType .unit
  | list {ρ : Ty} : IsDataType ρ → IsDataType (.list ρ)
  | tensor {ρ σ : Ty} : IsDataType ρ → IsDataType σ → IsDataType (.tensor ρ σ)
  | sum {ρ σ : Ty} : IsDataType ρ → IsDataType σ → IsDataType (.sum ρ σ)

/-- Definition 2.24 (Data objects, p. 9):
A data object of data type `τ` is an almost closed term `w^τ` in normal form. -/
def IsDataObject (τ : Ty) (w : Term) : Prop :=
  IsDataType τ ∧ HasType w τ ∧ IsAlmostClosed w ∧ IsNormal w

/-- A tuple of terms `ws` is a tuple of data objects of types `τs` with pairwise disjoint
free variables (and disjoint from a given program term `r`), so that the application
`r w₁ ... wₙ` is well-typed. -/
inductive ValidDataInputs : Term → List Ty → List Term → Prop where
  | nil (r : Term) : ValidDataInputs r [] []
  | cons {r : Term} {τ : Ty} {w : Term} {τs : List Ty} {ws : List Term} :
      IsDataObject τ w →
      DisjointFV r w →
      ValidDataInputs (.app r w) τs ws →
      ValidDataInputs r (τ :: τs) (w :: ws)

/-- Sum of syntactical lengths of a tuple of input terms. -/
def totalTermLength : List Term → Nat
  | [] => 0
  | w :: ws => termLength w + totalTermLength ws

/-- Sum of free-variable counts of a tuple of input terms. -/
def totalFreeVarCount : List Term → Nat
  | [] => 0
  | w :: ws => freeVarCount w + totalFreeVarCount ws

/-- A function `B : Nat → Nat` is bounded by a polynomial of degree at most `d`
if there exist constants `c₀, c₁ : Nat` such that `B n ≤ c₀ * (n + 1)^d + c₁` for all `n`. -/
def BoundedByPolyOfDegree (B : Nat → Nat) (d : Nat) : Prop :=
  ∃ c₀ c₁ : Nat, ∀ n : Nat, B n ≤ c₀ * (n + 1) ^ d + c₁

end ABHS2004


