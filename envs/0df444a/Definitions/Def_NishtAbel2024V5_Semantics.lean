-- Prove2me | Definitions.Def_NishtAbel2024V5_Semantics
-- name    : NishtAbel2024V5_Semantics
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:15:51.509202+00:00
-- url     : https://prove2.me/theorems/47995e65-6240-4422-9bfa-392f75d48fc8
-- title:
--   Chapter 5 (V5): Operational Semantics and Ordinal-Indexed Reducibility Candidates for System $F_\omega^{\mathsf{cop,SCT}}$
-- statement:
--   Operational semantics and semantic model of kinds, sizes, and types for System $F_\omega^{\mathsf{cop,SCT}}$ from Chapter 5 of Nisht and Abel (2024). Defines deterministic first-match clause selection, weak reduction $t \mapsto_W t^\prime$ over a world $W$ of recursive declarations, and strong normalization $\mathsf{SN}_W$.\n\nSizes are interpreted in `Ordinal` with closure ordinal $\Omega = (\mathsf{succ}\,\#\mathsf{Tm}).\mathsf{ord}$, mapping $\infty + n \mapsto \Omega + n$ and $a \wedge b \mapsto \min(\llbracket a \rrbracket_\rho, \llbracket b \rrbracket_\rho)$. Each simple kind $\iota$ is interpreted by a set-theoretic domain $\mathsf{Sem}\,\iota$, with polarized goodness $\mathsf{Good}_W\,\kappa$ and semantic inclusion $\mathsf{SemLe}_W\,\kappa$ at higher kinds. Inductive and coinductive fixpoints $\mu^a S$ and $\nu^a R$ are interpreted by transfinite iteration up to $\llbracket a \rrbracket_\rho$, accommodating both positive ($+$) and mixed-variance ($\circ$) functors.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Chapter 5, pp. 31-38, Sections 5.1-5.4

import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Logic.Relation
import Definitions.Def_NishtAbel2024V5_Syntax

/-!
# Nisht & Abel (2024), V5: operational semantics and interpretation of kinds and types

* Deterministic first-match clause selection and weak reduction of closed terms (as in V3/V4).
* Sizes are ordinals: `∞ + n` is `Ω + n` with `Ω = (succ #Tm).ord`, and meets are minima.
* Each simple kind `ι` has a semantic domain `Sem ι`: sets of terms for `*`, functions for
  `ι → ι'`. For a kind with variances `κ`, `Good W κ` singles out the reducibility candidates at
  `*` and, at `π κ₁ → κ₂`, the functions that map good arguments to good results and respect the
  variance `π`; `SemLe W κ` is the pointwise inclusion order.
* Type variables are interpreted by kind-polymorphic values `PSem = (ι : SKind) → Sem ι`, so
  syntactic substitution corresponds to updating the environment without kinding side
  conditions.
* `∀X:κ` and `∃X:κ` range over the good values of kind `κ`; `∀(j < a)` and `∃(j < a)` over the
  ordinals below `⟦a⟧`; `μ` and `ν` are interpreted by transfinite iteration, which needs no
  monotonicity of the functor.
-/

namespace NishtAbel2024V5

open NishtAbel2024V2 (FunName)

/-! ## Matching and head reduction -/

/-- Outcome of matching: success with a substitution, a definite mismatch, or undecided. -/
inductive MatchRes where
  | yes : TmSubst → MatchRes
  | no : MatchRes
  | stuck : MatchRes

/-- Combine the outcomes of two independent matches. -/
def MatchRes.and : MatchRes → MatchRes → MatchRes
  | .no, _ => .no
  | _, .no => .no
  | .yes σ₁, .yes σ₂ => .yes (σ₁ ++ σ₂)
  | _, _ => .stuck

/-- Match a pattern against a term. A mismatch is definite only between distinct
introduction forms. -/
def matchPat : Pat → Tm → MatchRes
  | .var x, t => .yes [(x, t)]
  | .unit, .unit => .yes []
  | .unit, .pair _ _ => .no
  | .unit, .cons _ _ => .no
  | .unit, .pack _ => .no
  | .unit, _ => .stuck
  | .pair p q, .pair t u => (matchPat p t).and (matchPat q u)
  | .pair _ _, .unit => .no
  | .pair _ _, .cons _ _ => .no
  | .pair _ _, .pack _ => .no
  | .pair _ _, _ => .stuck
  | .cons c p, .cons c' t => if c = c' then matchPat p t else .no
  | .cons _ _, .unit => .no
  | .cons _ _, .pair _ _ => .no
  | .cons _ _, .pack _ => .no
  | .cons _ _, _ => .stuck
  | .pack p, .pack t => matchPat p t
  | .pack _, .unit => .no
  | .pack _, .pair _ _ => .no
  | .pack _, .cons _ _ => .no
  | .pack _, _ => .stuck

def matchCopat : Copat → Elim → MatchRes
  | .pat p, .term t => matchPat p t
  | .pat _, .proj _ => .no
  | .pat _, .inst => .no
  | .proj d, .proj d' => if d = d' then .yes [] else .no
  | .proj _, .term _ => .no
  | .proj _, .inst => .no
  | .inst, .inst => .yes []
  | .inst, .term _ => .no
  | .inst, .proj _ => .no

/-- Match a copattern spine against a prefix of an elimination spine. -/
def matchSpine : List Copat → List Elim → MatchRes
  | [], _ => .yes []
  | _ :: _, [] => .stuck
  | q :: qs, e :: es => (matchCopat q e).and (matchSpine qs es)

/-- First-match clause selection; returns the contractum. -/
def selectClause : List Clause → List Elim → Option Tm
  | [], _ => none
  | .mk qs t :: D, es =>
      match matchSpine qs es with
      | .yes σ => some (Tm.appSpine (t.subst σ) (es.drop qs.length))
      | .no => selectClause D es
      | .stuck => none

/-- Split a term into its head and its elimination spine. -/
def Tm.headSpine : Tm → Tm × List Elim
  | .app r e => ((r.headSpine).1, (r.headSpine).2 ++ [e])
  | t => (t, [])

/-- A world: all function declarations in scope at run time. -/
abbrev World := List FunDecl

def World.lookup (W : World) (f : FunName) : Option FunDecl :=
  W.find? (fun d => d.name == f)

/-- Deterministic weak-head step. -/
def headStep (W : World) (t : Tm) : Option Tm :=
  match t.headSpine.1 with
  | .lam D => selectClause D t.headSpine.2
  | .fn f =>
      match W.lookup f with
      | some d => selectClause d.clauses t.headSpine.2
      | none => none
  | _ => none

/-- Weak reduction: head steps and congruences, never under `λ{D⃗}`. -/
inductive Step (W : World) : Tm → Tm → Prop where
  | head {t u : Tm} : headStep W t = some u → Step W t u
  | appFun {r r' : Tm} {e : Elim} : Step W r r' → Step W (.app r e) (.app r' e)
  | appArg {r s s' : Tm} : Step W s s' → Step W (.app r (.term s)) (.app r (.term s'))
  | pairL {t t' u : Tm} : Step W t t' → Step W (.pair t u) (.pair t' u)
  | pairR {t u u' : Tm} : Step W u u' → Step W (.pair t u) (.pair t u')
  | cons {c : Nat} {t t' : Tm} : Step W t t' → Step W (.cons c t) (.cons c t')
  | pack {t t' : Tm} : Step W t t' → Step W (.pack t) (.pack t')

/-- Reflexive-transitive closure of `Step`. -/
def Steps (W : World) : Tm → Tm → Prop := Relation.ReflTransGen (Step W)

/-- Strong normalization: every reduction sequence from `t` is finite. -/
def SN (W : World) (t : Tm) : Prop := Acc (fun u t => Step W t u) t

/-- Closed and strongly normalizing. -/
def SNc (W : World) (t : Tm) : Prop := t.Closed ∧ SN W t

/-- Introduction forms. -/
def IsIntro : Tm → Prop
  | .unit => True
  | .pair _ _ => True
  | .cons _ _ => True
  | .pack _ => True
  | _ => False

/-- Neutral terms: not an introduction, and every head step of an extension `t e⃗` comes from a
head step of `t` itself. -/
def IsNeutral (W : World) (t : Tm) : Prop :=
  ¬ IsIntro t ∧
  ∀ (es : List Elim) (u : Tm), headStep W (Tm.appSpine t es) = some u →
    ∃ t', headStep W t = some t' ∧ u = Tm.appSpine t' es

/-- Reducibility candidates over closed strongly normalizing terms. -/
structure Cand (W : World) (𝒜 : Set Tm) : Prop where
  sn : ∀ t ∈ 𝒜, SNc W t
  red : ∀ t ∈ 𝒜, ∀ t', Step W t t' → t' ∈ 𝒜
  neutral : ∀ t, t.Closed → IsNeutral W t → (∀ t', Step W t t' → t' ∈ 𝒜) → t ∈ 𝒜

/-! ## Sizes -/

/-- The interpretation of `∞`: the initial ordinal of the successor cardinal of `#Tm`. -/
noncomputable def Omega : Ordinal.{0} := (Order.succ (Cardinal.mk Tm)).ord

/-- Valuation of free size variables. -/
abbrev SizeVal := Nat → Ordinal.{0}

/-- Valuation of bound size variables. -/
abbrev SzEnv := Nat → Ordinal.{0}

def SzEnv.cons (β : Ordinal.{0}) (ζ : SzEnv) : SzEnv
  | 0 => β
  | n + 1 => ζ n

def SzEnv.zero : SzEnv := fun _ => 0

/-- `⟦a⟧ρζ`: `∞ + n` is `Ω + n`, and a meet is a minimum. -/
noncomputable def sizeVal (ρ : SizeVal) (ζ : SzEnv) : Size → Ordinal.{0}
  | .inf n => Omega + n
  | .var i n => ρ i + n
  | .bvar k n => ζ k + n
  | .meet a b => min (sizeVal ρ ζ a) (sizeVal ρ ζ b)

/-- `ρ ∈ ⟦Ψ⟧`: every declared variable is below its bound. -/
def ValidVal (Ψ : SizeCtx) (ρ : SizeVal) : Prop :=
  ∀ p ∈ Ψ, ρ p.1 < sizeVal ρ SzEnv.zero p.2

/-! ## Semantic domains of kinds -/

/-- The semantic domain of a simple kind. -/
def Sem : SKind → Type
  | .star => Set Tm
  | .arr ι₁ ι₂ => Sem ι₁ → Sem ι₂

/-- A default element of each domain. -/
def Sem.dflt : (ι : SKind) → Sem ι
  | .star => (∅ : Set Tm)
  | .arr _ ι₂ => fun _ => Sem.dflt ι₂

/-- Kind-polymorphic semantic values, used to interpret type variables. -/
abbrev PSem := (ι : SKind) → Sem ι

/-- The kind-polymorphic value that is `X` at `ι` and the default elsewhere. -/
def PSem.ofSem (ι : SKind) (X : Sem ι) : PSem :=
  fun ι' => if h : ι = ι' then h ▸ X else Sem.dflt ι'

/-- Variance-directed comparison of arguments: `≤` for `+`, `≥` for `−`, both for `◦`, nothing
for `⊤`. -/
def polRelOf {α : Type} (le : α → α → Prop) : Pol → α → α → Prop
  | .pos, X, Y => le X Y
  | .neg, X, Y => le Y X
  | .mix, X, Y => le X Y ∧ le Y X
  | .top, _, _ => True

/-- Goodness and order of semantic values of simple kind `ι` at the kind `κ`, defined together
by recursion. Both are empty unless `ι` is the simple kind underlying `κ`. -/
def KRel (W : World) : Kind → (ι : SKind) → (Sem ι → Prop) × (Sem ι → Sem ι → Prop)
  | .star, .star => (fun (A : Set Tm) => Cand W A, fun (A B : Set Tm) => A ⊆ B)
  | .arr π κ₁ κ₂, .arr ι₁ ι₂ =>
      ((fun F => (∀ X, (KRel W κ₁ ι₁).1 X → (KRel W κ₂ ι₂).1 (F X)) ∧
          ∀ X Y, (KRel W κ₁ ι₁).1 X → (KRel W κ₁ ι₁).1 Y → polRelOf (KRel W κ₁ ι₁).2 π X Y →
            (KRel W κ₂ ι₂).2 (F X) (F Y)),
       fun F G => ∀ X Y, (KRel W κ₁ ι₁).1 X → (KRel W κ₁ ι₁).1 Y →
          polRelOf (KRel W κ₁ ι₁).2 π X Y → (KRel W κ₂ ι₂).2 (F X) (G Y))
  | .star, .arr _ _ => (fun _ => False, fun _ _ => False)
  | .arr _ _ _, .star => (fun _ => False, fun _ _ => False)

/-- `X` is a good semantic value of kind `κ`: a reducibility candidate at `*`, and at
`π κ₁ → κ₂` a function mapping good arguments to good results and respecting the variance. -/
def Good (W : World) (κ : Kind) {ι : SKind} : Sem ι → Prop := (KRel W κ ι).1

/-- The semantic order at kind `κ`: inclusion at `*`, pointwise along the variance at arrows. -/
def SemLe (W : World) (κ : Kind) {ι : SKind} : Sem ι → Sem ι → Prop := (KRel W κ ι).2

/-! ## Semantic types -/

/-- Closed strongly normalizing terms all of whose introduction-form reducts satisfy `P`. -/
def IntroSet (W : World) (P : Tm → Prop) : Set Tm :=
  {t | SNc W t ∧ ∀ v, Steps W t v → IsIntro v → P v}

def UnitSet (W : World) : Set Tm := IntroSet W (fun v => v = .unit)

def ProdSet (W : World) (𝒜 ℬ : Set Tm) : Set Tm :=
  IntroSet W (fun v => ∃ t u, v = .pair t u ∧ t ∈ 𝒜 ∧ u ∈ ℬ)

def ArrSet (W : World) (𝒜 ℬ : Set Tm) : Set Tm :=
  {t | SNc W t ∧ ∀ s ∈ 𝒜, Tm.app t (.term s) ∈ ℬ}

/-- `∀X:κ. F X`: instantiations land in `F X` for every good `X` of kind `κ`. -/
def AllTSet (W : World) (κ : Kind) (F : Sem κ.erase → Set Tm) : Set Tm :=
  {t | SNc W t ∧ ∀ X, Good W κ X → Tm.app t .inst ∈ F X}

/-- `∃X:κ. F X`: packs of a member of `F X` for some good `X` of kind `κ`. -/
def ExTSet (W : World) (κ : Kind) (F : Sem κ.erase → Set Tm) : Set Tm :=
  IntroSet W (fun v => ∃ t X, v = .pack t ∧ Good W κ X ∧ t ∈ F X)

/-- `∀(j < α). F j`: instantiations land in `F β` for every `β < α`. -/
def AllSSet (W : World) (α : Ordinal.{0}) (F : Ordinal.{0} → Set Tm) : Set Tm :=
  {t | SNc W t ∧ ∀ β < α, Tm.app t .inst ∈ F β}

/-- `∃(j < α). F j`: packs of a member of `F β` for some `β < α`. -/
def ExSSet (W : World) (α : Ordinal.{0}) (F : Ordinal.{0} → Set Tm) : Set Tm :=
  IntroSet W (fun v => ∃ t β, v = .pack t ∧ β < α ∧ t ∈ F β)

/-- Stage `α` of an inductive type with branch interpretation `F`. -/
noncomputable def MuSet (W : World) (F : Nat → Set Tm → Set Tm) : Ordinal.{0} → Set Tm :=
  WellFounded.fix Ordinal.lt_wf (C := fun _ => Set Tm) fun α ih =>
    IntroSet W (fun v => ∃ c t β, ∃ h : β < α, v = .cons c t ∧ t ∈ F c (ih β h))

/-- Stage `α` of a coinductive type with `n` projections interpreted by `G`. -/
noncomputable def NuSet (W : World) (n : Nat) (G : Nat → Set Tm → Set Tm) :
    Ordinal.{0} → Set Tm :=
  WellFounded.fix Ordinal.lt_wf (C := fun _ => Set Tm) fun α ih =>
    {t | SNc W t ∧ ∀ β (h : β < α), ∀ d < n, Tm.app t (.proj d) ∈ G d (ih β h)}

/-- Environment for bound type variables. -/
abbrev Env := Nat → PSem

def Env.cons (X : PSem) (η : Env) : Env
  | 0 => X
  | n + 1 => η n

def Env.empty : Env := fun _ ι => Sem.dflt ι

/-- Valuation of free type variables. -/
abbrev TEnv := Nat → PSem

def TEnv.empty : TEnv := fun _ ι => Sem.dflt ι

/-- A set of terms as an element of `Sem ι` (the default unless `ι = *`). -/
def Sem.ofStar (S : Set Tm) : (ι : SKind) → Sem ι
  | .star => S
  | .arr ι₁ ι₂ => Sem.dflt (.arr ι₁ ι₂)

/-- A family of functions as an element of `Sem ι` (the default unless `ι` is an arrow). -/
def Sem.ofFun (f : (ι₁ ι₂ : SKind) → Sem ι₁ → Sem ι₂) : (ι : SKind) → Sem ι
  | .star => Sem.dflt .star
  | .arr ι₁ ι₂ => f ι₁ ι₂

mutual

/-- `⟦F⟧ρθζη` at simple kind `ι`: `ρ` and `θ` interpret free size and type variables, `ζ` and
`η` bound ones. An application `F G` interprets `F` at the arrow kind `ι_G → ι` and applies it to
`⟦G⟧` at `ι_G`. -/
noncomputable def interp (W : World) (ρ : SizeVal) (θ : TEnv) :
    Ty → (ι : SKind) → SzEnv → Env → Sem ι
  | .unit, ι, _, _ => Sem.ofStar (UnitSet W) ι
  | .prod A B, ι, ζ, η =>
      Sem.ofStar (ProdSet W (interp W ρ θ A .star ζ η) (interp W ρ θ B .star ζ η)) ι
  | .arr A B, ι, ζ, η =>
      Sem.ofStar (ArrSet W (interp W ρ θ A .star ζ η) (interp W ρ θ B .star ζ η)) ι
  | .var k, ι, _, η => η k ι
  | .fvar X, ι, _, _ => θ X ι
  | .lam _ F, ι, ζ, η =>
      Sem.ofFun (fun ι₁ ι₂ X => interp W ρ θ F ι₂ ζ (Env.cons (PSem.ofSem ι₁ X) η)) ι
  | .app F G ι₁, ι, ζ, η => interp W ρ θ F (.arr ι₁ ι) ζ η (interp W ρ θ G ι₁ ζ η)
  | .mu a S, ι, ζ, η =>
      Sem.ofStar (MuSet W (fun c 𝒳 => interpAt W ρ θ S c ζ (Env.cons (PSem.ofSem .star 𝒳) η))
        (sizeVal ρ ζ a)) ι
  | .nu a R, ι, ζ, η =>
      Sem.ofStar (NuSet W R.length
        (fun d 𝒳 => interpAt W ρ θ R d ζ (Env.cons (PSem.ofSem .star 𝒳) η)) (sizeVal ρ ζ a)) ι
  | .allT κ B, ι, ζ, η =>
      Sem.ofStar (AllTSet W κ
        (fun X => interp W ρ θ B .star ζ (Env.cons (PSem.ofSem κ.erase X) η))) ι
  | .exT κ B, ι, ζ, η =>
      Sem.ofStar (ExTSet W κ
        (fun X => interp W ρ θ B .star ζ (Env.cons (PSem.ofSem κ.erase X) η))) ι
  | .allS a B, ι, ζ, η =>
      Sem.ofStar (AllSSet W (sizeVal ρ ζ a)
        (fun β => interp W ρ θ B .star (SzEnv.cons β ζ) η)) ι
  | .exS a B, ι, ζ, η =>
      Sem.ofStar (ExSSet W (sizeVal ρ ζ a)
        (fun β => interp W ρ θ B .star (SzEnv.cons β ζ) η)) ι

/-- `⟦S[c]⟧` at `*`, empty when `c` is out of range. -/
noncomputable def interpAt (W : World) (ρ : SizeVal) (θ : TEnv) :
    List Ty → Nat → SzEnv → Env → Set Tm
  | [], _, _, _ => ∅
  | A :: _, 0, ζ, η => interp W ρ θ A .star ζ η
  | _ :: S, c + 1, ζ, η => interpAt W ρ θ S c ζ η

end

/-- The interpretation of a type of kind `*`. -/
noncomputable abbrev interpT (W : World) (ρ : SizeVal) (θ : TEnv) (A : Ty) (ζ : SzEnv)
    (η : Env) : Set Tm :=
  interp W ρ θ A .star ζ η

/-- `W ⊨ D`: every declaration in `D`, at every valid size instance, is in its type. -/
def SemValid (W : World) (D : List FunDecl) : Prop :=
  ∀ d ∈ D, ∀ ρ : SizeVal, ValidVal d.sizeParams ρ →
    Tm.fn d.name ∈ interpT W ρ TEnv.empty d.ty SzEnv.zero Env.empty

end NishtAbel2024V5


