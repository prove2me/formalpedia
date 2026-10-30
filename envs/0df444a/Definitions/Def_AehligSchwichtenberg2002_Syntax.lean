-- Prove2me | Definitions.Def_AehligSchwichtenberg2002_Syntax
-- name    : AehligSchwichtenberg2002_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-10-30T01:55:58.414293+00:00
-- url     : https://prove2.me/theorems/1ce7bcef-c3e9-422e-924f-1735c5fbc4d9
-- title:
--   Section 2: Affine Non-Size-Increasing Types, Terms, and Head-Controlled Reduction
-- statement:
--   Formalizes Section 2 of Aehlig and Schwichtenberg (2002): types `ρ, σ ::= B | ⋄ | ρ ⊸ σ | !ρ → σ` (with `B = L(⋄)`), constructors `c_i`, destructors `d_i`, higher-type iteration `it_ρ` (for `!`-free `ρ`), explicit affine typing `Δ; Γ ⊢ r : ρ`, and the head-controlled one-step reduction relation `↦` (Definition 2.4) that prevents duplication of unreduced `!`-arguments during recursion.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Section 2, pp. 385-391.

import Std

/-!
# Syntax, Typing, and Reductions for Aehlig–Schwichtenberg (2002, Sections 2–3)

Source: Klaus Aehlig and Helmut Schwichtenberg,
"A syntactical analysis of non-size-increasing polynomial time computation",
*Proceedings of the 15th IEEE Symposium on Logic in Computer Science (LICS 2000)*, pp. 84–91;
expanded version in *ACM Transactions on Computational Logic* 3(3), 2002, pp. 383–401
(arXiv:cs/0011037v2), Sections 2–3 (pp. 3–9).

This module formalizes:
- Definition 2.1: Finite linear types (`Ty`).
- Definition 2.2 & 2.3: Raw terms (`Term`) and constructor symbols (`Constructor`).
- Definition 2.4: Context-indexed affine linear typing `HasType Γ t τ` (`Γ ⊢ t^τ`), where
  eliminations for `×`, `B`, `⊗`, and `L(τ)` are written in application notation.
- Definition 3.1, 3.2, 3.3: Lists (`listEntryCount`, `IsListTerm`), conversions (`ConvStep`),
  one-step and multi-step reduction (`RedStep`, `RedStar`, `RedSteps`), normal forms (`IsNormal`),
  and almost closed terms (`IsAlmostClosed`).
-/

namespace AehligSchwichtenberg2002

/-- Definition 2.1 (Finite types, p. 3):
`ρ, τ ::= ⋄ | B | τ ⊸ ρ | τ ⊗ ρ | τ × ρ | L(τ)`. -/
inductive Ty where
  | diamond : Ty
  | bool : Ty
  | lolli : Ty → Ty → Ty
  | tensor : Ty → Ty → Ty
  | prod : Ty → Ty → Ty
  | list : Ty → Ty
  deriving DecidableEq, Repr

namespace Ty

/-- Binary numerals `L(B)` (Section 2, p. 3 & Corollary 4.9, p. 14). -/
def bin : Ty := .list .bool

/-- Iterated linear function type `τ₁ ⊸ ⋯ ⊸ τₙ ⊸ ρ`. -/
def lolliMany : List Ty → Ty → Ty
  | [], ρ => ρ
  | τ :: τs, ρ => .lolli τ (lolliMany τs ρ)

end Ty

/-- Typed variable `x^τ` (Section 2, p. 4). -/
structure Var where
  id : Nat
  ty : Ty
  deriving DecidableEq, Repr

/-- Definition 2.3 (Constructor symbols, p. 4):
`tt : B`, `ff : B`, `nil_τ : L(τ)`, `cons_τ : ⋄ ⊸ τ ⊸ L(τ) ⊸ L(τ)`, `⊗_{τ,ρ} : τ ⊸ ρ ⊸ τ ⊗ ρ`. -/
inductive Constructor where
  | tt : Constructor
  | ff : Constructor
  | nil : Ty → Constructor
  | cons : Ty → Constructor
  | tensorPair : Ty → Ty → Constructor
  deriving DecidableEq, Repr

/-- Type assignment for constructor symbols (Definition 2.3, p. 4). -/
def Constructor.ty : Constructor → Ty
  | .tt => .bool
  | .ff => .bool
  | .nil τ => .list τ
  | .cons τ => .lolli .diamond (.lolli τ (.lolli (.list τ) (.list τ)))
  | .tensorPair τ ρ => .lolli τ (.lolli ρ (.tensor τ ρ))

/-- Definition 2.2 (Terms, p. 4):
`r, s, t ::= x^τ | c | λx^τ. t | ⟨t, s⟩ | t s | {t}`. -/
inductive Term where
  | var : Var → Term
  | const : Constructor → Term
  | lam : Var → Term → Term
  | pair : Term → Term → Term
  | app : Term → Term → Term
  | brace : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Multi-argument application `t s₁ ... sₙ`. -/
def appMany : Term → List Term → Term
  | t, [] => t
  | t, s :: ss => appMany (.app t s) ss

end Term

/-- A context `Γ` is a finite set of variables (Section 2, p. 4), represented as a list. -/
abbrev Context := List Var

/-- Disjointness of two contexts `Γ₁ ∩ Γ₂ = ∅`. -/
def DisjointCtx (Γ₁ Γ₂ : Context) : Prop :=
  ∀ v, v ∈ Γ₁ → v ∉ Γ₂

/-- Set-extensional union `Γ = Γ₁ ∪ Γ₂` with no disjointness requirement. -/
def IsCtxUnion (Γ₁ Γ₂ Γ : Context) : Prop :=
  ∀ v, v ∈ Γ ↔ (v ∈ Γ₁ ∨ v ∈ Γ₂)

/-- Set-extensional disjoint union `Γ = Γ₁, Γ₂` (Section 2, p. 4:
"For two contexts `Γ₁` and `Γ₂` the notation `Γ₁, Γ₂` stands for the union, expressing that
`Γ₁` and `Γ₂` are disjoint."). -/
def IsDisjointCtxUnion (Γ₁ Γ₂ Γ : Context) : Prop :=
  DisjointCtx Γ₁ Γ₂ ∧ IsCtxUnion Γ₁ Γ₂ Γ

/-- Free variable occurrences of a term `t`. -/
def freeVarOccurrences : Term → List Var
  | .var x => [x]
  | .const _ => []
  | .lam x t => (freeVarOccurrences t).filter (· != x)
  | .pair t s => freeVarOccurrences t ++ freeVarOccurrences s
  | .app t s => freeVarOccurrences t ++ freeVarOccurrences s
  | .brace t => freeVarOccurrences t

/-- Underlying set of free variables `FV(t)` (duplicate-free list). -/
def freeVars (t : Term) : List Var :=
  (freeVarOccurrences t).eraseDups

/-- Cardinality `|FV(t)|` of the set of free variables of `t`. -/
def freeVarCard (t : Term) : Nat :=
  (freeVars t).length

/-- Almost closed terms (Section 3, p. 8): terms with free variables of type `⋄` only. -/
def IsAlmostClosed (t : Term) : Prop :=
  ∀ v ∈ freeVars t, v.ty = .diamond

/-- Closed terms: terms with no free variables. -/
def IsClosed (t : Term) : Prop :=
  freeVars t = []

/-- Maximum variable id occurring anywhere in a term. -/
def maxVarId : Term → Nat
  | .var x => x.id
  | .const _ => 0
  | .lam x t => Nat.max x.id (maxVarId t)
  | .pair t s => Nat.max (maxVarId t) (maxVarId s)
  | .app t s => Nat.max (maxVarId t) (maxVarId s)
  | .brace t => maxVarId t

/-- Rename free occurrences of `x` to `y` in `t`. -/
def renameFreeVar (t : Term) (x y : Var) : Term :=
  match t with
  | .var v => if v == x then .var y else .var v
  | .const c => .const c
  | .lam v body => if v == x then .lam v body else .lam v (renameFreeVar body x y)
  | .pair r s => .pair (renameFreeVar r x y) (renameFreeVar s x y)
  | .app r s => .app (renameFreeVar r x y) (renameFreeVar s x y)
  | .brace r => .brace (renameFreeVar r x y)

/-- Structural size of a raw term used for termination of capture-avoiding substitution. -/
def rawSize : Term → Nat
  | .var _ => 1
  | .const _ => 1
  | .lam _ t => rawSize t + 1
  | .pair t s => rawSize t + rawSize s + 1
  | .app t s => rawSize t + rawSize s + 1
  | .brace t => rawSize t + 1

theorem renameFreeVar_rawSize (t : Term) (x y : Var) :
    rawSize (renameFreeVar t x y) = rawSize t := by
  induction t with
  | var v => simp only [renameFreeVar]; split <;> rfl
  | const c => rfl
  | lam v body ih =>
      simp only [renameFreeVar]
      split
      · rfl
      · simp [rawSize, ih]
  | pair r s ihr ihs => simp [renameFreeVar, rawSize, ihr, ihs]
  | app r s ihr ihs => simp [renameFreeVar, rawSize, ihr, ihs]
  | brace r ihr => simp [renameFreeVar, rawSize, ihr]

/-- Capture-avoiding substitution `t[s/x]` (Section 2, p. 4 & Definition 3.2, p. 7). -/
def substTerm (t : Term) (x : Var) (s : Term) : Term :=
  match t with
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
  | .pair r u => .pair (substTerm r x s) (substTerm u x s)
  | .app r u => .app (substTerm r x s) (substTerm u x s)
  | .brace r => .brace (substTerm r x s)
termination_by rawSize t
decreasing_by
  all_goals
    simp_wf
    simp [rawSize, renameFreeVar_rawSize]
    try omega

/-- Simultaneous substitution `r[t, s / x, y]` for two distinct variables `x, y`
(used in `⊗_{τ,ρ} t s (λx^τ, y^ρ. r) ↦ r[t, s / x, y]`, Definition 3.2, p. 7). -/
def substTwo (r : Term) (x y : Var) (t s : Term) : Term :=
  if y ∈ freeVarOccurrences t then
    let freshId := Nat.max (maxVarId r) (Nat.max (maxVarId t) (Nat.max (maxVarId s) (Nat.max x.id y.id))) + 1
    let y' : Var := ⟨freshId, y.ty⟩
    substTerm (substTerm (renameFreeVar r y y') x t) y' s
  else
    substTerm (substTerm r x t) y s

/-- Definition 2.4 (Typing `Γ ⊢ t^τ`, pp. 4–5). -/
inductive HasType : Context → Term → Ty → Prop where
  /-- `(Var)`: `Γ, x^τ ⊢ x^τ` -/
  | var {Γ Γ' : Context} (x : Var) :
      IsDisjointCtxUnion Γ [x] Γ' →
      HasType Γ' (.var x) x.ty
  /-- `(Const)`: `Γ ⊢ c^τ` -/
  | const (Γ : Context) (c : Constructor) :
      HasType Γ (.const c) c.ty
  /-- `(⊸⁺)`: from `Γ ∪ {x^τ} ⊢ t^ρ` infer `Γ ⊢ (λx^τ. t)^{τ⊸ρ}` -/
  | lam {Γ Γ' : Context} (x : Var) {t : Term} {ρ : Ty} :
      IsCtxUnion Γ [x] Γ' →
      HasType Γ' t ρ →
      HasType Γ (.lam x t) (.lolli x.ty ρ)
  /-- `(⊸⁻)`: from `Γ₁ ⊢ t^{τ⊸ρ}` and `Γ₂ ⊢ s^τ` infer `Γ₁, Γ₂ ⊢ (t s)^ρ` -/
  | app {Γ₁ Γ₂ Γ : Context} {t s : Term} {τ ρ : Ty} :
      IsDisjointCtxUnion Γ₁ Γ₂ Γ →
      HasType Γ₁ t (.lolli τ ρ) →
      HasType Γ₂ s τ →
      HasType Γ (.app t s) ρ
  /-- `(×⁺)`: from `Γ ⊢ t^τ` and `Γ ⊢ s^ρ` infer `Γ ⊢ ⟨t, s⟩^{τ×ρ}` -/
  | pair {Γ : Context} {t s : Term} {τ ρ : Ty} :
      HasType Γ t τ →
      HasType Γ s ρ →
      HasType Γ (.pair t s) (.prod τ ρ)
  /-- `(×₁⁻)`: from `Γ ⊢ t^{τ×ρ}` infer `Γ ⊢ (t tt)^τ` -/
  | projLeft {Γ : Context} {t : Term} {τ ρ : Ty} :
      HasType Γ t (.prod τ ρ) →
      HasType Γ (.app t (.const .tt)) τ
  /-- `(×₀⁻)`: from `Γ ⊢ t^{τ×ρ}` infer `Γ ⊢ (t ff)^ρ` -/
  | projRight {Γ : Context} {t : Term} {τ ρ : Ty} :
      HasType Γ t (.prod τ ρ) →
      HasType Γ (.app t (.const .ff)) ρ
  /-- `(B⁻)`: from `Γ₁ ⊢ t^B`, `Γ₂ ⊢ s^τ`, `Γ₂ ⊢ r^τ` infer `Γ₁, Γ₂ ⊢ (t ⟨s, r⟩)^τ` -/
  | boolElim {Γ₁ Γ₂ Γ : Context} {t s r : Term} {τ : Ty} :
      IsDisjointCtxUnion Γ₁ Γ₂ Γ →
      HasType Γ₁ t .bool →
      HasType Γ₂ s τ →
      HasType Γ₂ r τ →
      HasType Γ (.app t (.pair s r)) τ
  /-- `(⊗⁻)`: from `Γ₁ ⊢ t^{τ⊗ρ}` and `Γ₂, x^τ, y^ρ ⊢ s^σ` infer `Γ₁, Γ₂ ⊢ (t (λx^τ, y^ρ. s))^σ` -/
  | tensorElim {Γ₁ Γ₂ Γ₂' Γ : Context} {t s : Term} (x y : Var) {σ : Ty} :
      x ≠ y →
      IsDisjointCtxUnion Γ₂ [x, y] Γ₂' →
      IsDisjointCtxUnion Γ₁ Γ₂ Γ →
      HasType Γ₁ t (.tensor x.ty y.ty) →
      HasType Γ₂' s σ →
      HasType Γ (.app t (.lam x (.lam y s))) σ
  /-- `(L(τ)⁻)`: from `Γ ⊢ t^{L(τ)}` and `∅ ⊢ s^{⋄⊸τ⊸ρ⊸ρ}` infer `Γ ⊢ (t {s})^{ρ⊸ρ}` -/
  | listElim {Γ : Context} {t s : Term} {τ ρ : Ty} :
      HasType Γ t (.list τ) →
      HasType [] s (.lolli .diamond (.lolli τ (.lolli ρ ρ))) →
      HasType Γ (.app t (.brace s)) (.lolli ρ ρ)

/-- Definition 3.1 (Lists, p. 7):
Lists `ℓ` (with `n` entries) are terms of the form `cons_τ d₁ a₁ (... (cons_τ dₙ aₙ nil_τ))`. -/
def listEntryCount : Term → Option Nat
  | .const (.nil _) => some 0
  | .app (.app (.app (.const (.cons _)) _) _) l =>
      match listEntryCount l with
      | some k => some (k + 1)
      | none => none
  | _ => none

/-- Predicate asserting that `l` is a list in the sense of Definition 3.1 (p. 7). -/
def IsListTerm (l : Term) : Prop :=
  ∃ n, listEntryCount l = some n

/-- Definition 3.2 (Conversions, p. 7): `t ↦ t'`. -/
inductive ConvStep : Term → Term → Prop where
  | beta (x : Var) (t s : Term) :
      ConvStep (.app (.lam x t) s) (substTerm t x s)
  | projTt (t s : Term) :
      ConvStep (.app (.pair t s) (.const .tt)) t
  | projFf (t s : Term) :
      ConvStep (.app (.pair t s) (.const .ff)) s
  | ifTt (t s : Term) :
      ConvStep (.app (.const .tt) (.pair t s)) t
  | ifFf (t s : Term) :
      ConvStep (.app (.const .ff) (.pair t s)) s
  | tensorBeta (τ ρ : Ty) (t s : Term) (x y : Var) (r : Term) :
      x.ty = τ → y.ty = ρ → x ≠ y →
      ConvStep
        (.app (.app (.app (.const (.tensorPair τ ρ)) t) s) (.lam x (.lam y r)))
        (substTwo r x y t s)
  | iterNil (τ : Ty) (t s : Term) :
      ConvStep (.app (.app (.const (.nil τ)) (.brace t)) s) s
  | iterCons (τ : Ty) (d a l t s : Term) :
      IsListTerm l →
      ConvStep
        (.app (.app (.app (.app (.app (.const (.cons τ)) d) a) l) (.brace t)) s)
        (.app (.app (.app t d) a) (.app (.app l (.brace t)) s))

/-- Definition 3.3 (Reduction `t → t'`, p. 8). -/
inductive RedStep : Term → Term → Prop where
  | conv {t t' : Term} :
      ConvStep t t' → RedStep t t'
  | appLeft {t t' : Term} (s : Term) :
      RedStep t t' → RedStep (.app t s) (.app t' s)
  | appRight (t : Term) {s s' : Term} :
      RedStep s s' → RedStep (.app t s) (.app t s')

/-- Reflexive-transitive closure of reduction `t →* t'`. -/
inductive RedStar : Term → Term → Prop where
  | refl (t : Term) : RedStar t t
  | step {t s u : Term} : RedStep t s → RedStar s u → RedStar t u

/-- Exact `k`-step reduction chain `t →^k t'`. -/
inductive RedSteps : Nat → Term → Term → Prop where
  | zero (t : Term) : RedSteps 0 t t
  | succ {k : Nat} {t s u : Term} :
      RedStep t s → RedSteps k s u → RedSteps (k + 1) t u

/-- A term `t` is normal if there is no `t'` such that `t → t'` (Section 3, p. 8). -/
def IsNormal (t : Term) : Prop :=
  ¬ ∃ t', RedStep t t'

end AehligSchwichtenberg2002


