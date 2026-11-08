-- Prove2me | Definitions.Def_Abel2018_Syntax
-- name    : Abel2018_Syntax
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T13:32:22.511869+00:00
-- url     : https://prove2.me/theorems/6f33aa49-d8da-4731-b2d5-ea5ea2748575
-- title:
--   Section 2.1: De Bruijn Syntax, Weakenings, Parallel Substitutions, and Weak-Head Normal Forms
-- statement:
--   Formalizes the untyped de Bruijn syntax and syntactic operations of Section 2.1 (`Definition/Untyped.agda`): raw terms `Term` ($U, \Pi A\, B, \mathbb{N}, \mathsf{var}(x), \lambda t, t\, u, 0, \mathsf{suc}(t), \mathsf{natrec}(A, z, s, n)$), newest-first contexts `Context`, inductive weakenings `Wk` (`id`, `step`, `lift`) and term weakening `wk`, parallel substitutions `Subst := Nat → Term` and `subst`, single-variable substitution `subst0` ($t[a]$) and lifted substitution `substKeep` ($t[a]\uparrow$), the recursor step motive type `recStepType`, canonical numerals `suck` ($\mathsf{suc}^k(0)$), neutral terms `Neutral`, weak-head normal forms `Whnf`, and WHNF shape views (`NaturalView`, `SmallTypeView`, `FunctionView`).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages 2(POPL), Article 23, 2018, pp. 23:1-23:29 (doi:10.1145/3158111); Agda artifact mr-ohman/logrel-mltt v2.1 (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Section 2.1, pp. 23:5-23:6; Definition/Untyped.agda.

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: Andreas Abel, Joakim Öhman, and Andrea Vezzosi,
"Decidability of Conversion for Type Theory in Type Theory",
Proceedings of the ACM on Programming Languages 2(POPL), Article 23, 2018
(doi:10.1145/3158111), and Agda artifact mr-ohman/logrel-mltt v2.1
(commit eb2b15ab1c4b45923025834d3bb798943cb44b8e), Definition/Untyped.agda.
-/
import Init

namespace Abel2018

/-- Raw de Bruijn syntax for the source lambda-Pi-U-N calculus. -/
inductive Term where
  | univ : Term
  | pi : Term → Term → Term
  | nat : Term
  | var : Nat → Term
  | lam : Term → Term
  | app : Term → Term → Term
  | zero : Term
  | succ : Term → Term
  | natrec : Term → Term → Term → Term → Term
  deriving DecidableEq, Repr

/-- Newest-first representation of the source's snoc contexts: Γ ∙ A becomes A :: Γ. -/
abbrev Context := List Term

def liftRen (ρ : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => ρ n + 1

/-- Renaming lifts under precisely the Pi codomain, lambda body, and recursor motive. -/
def rename (ρ : Nat → Nat) : Term → Term
  | .univ => .univ
  | .pi A B => .pi (rename ρ A) (rename (liftRen ρ) B)
  | .nat => .nat
  | .var x => .var (ρ x)
  | .lam t => .lam (rename (liftRen ρ) t)
  | .app t u => .app (rename ρ t) (rename ρ u)
  | .zero => .zero
  | .succ t => .succ (rename ρ t)
  | .natrec A z s n =>
      .natrec (rename (liftRen ρ) A) (rename ρ z) (rename ρ s) (rename ρ n)

/-- Syntactic weakenings from the source, retaining its inductive presentation. -/
inductive Wk where
  | id : Wk
  | step : Wk → Wk
  | lift : Wk → Wk
  deriving DecidableEq, Repr

def wkVar : Wk → Nat → Nat
  | .id, n => n
  | .step ρ, n => wkVar ρ n + 1
  | .lift _, 0 => 0
  | .lift ρ, n + 1 => wkVar ρ n + 1

def wk (ρ : Wk) : Term → Term
  | .univ => .univ
  | .pi A B => .pi (wk ρ A) (wk (.lift ρ) B)
  | .nat => .nat
  | .var x => .var (wkVar ρ x)
  | .lam t => .lam (wk (.lift ρ) t)
  | .app t u => .app (wk ρ t) (wk ρ u)
  | .zero => .zero
  | .succ t => .succ (wk ρ t)
  | .natrec A z s n =>
      .natrec (wk (.lift ρ) A) (wk ρ z) (wk ρ s) (wk ρ n)

def wk1 : Term → Term := wk (.step .id)

def compWk : Wk → Wk → Wk
  | .id, ρ' => ρ'
  | .step ρ, ρ' => .step (compWk ρ ρ')
  | .lift ρ, .id => .lift ρ
  | .lift ρ, .step ρ' => .step (compWk ρ ρ')
  | .lift ρ, .lift ρ' => .lift (compWk ρ ρ')

abbrev Subst := Nat → Term

def liftSubst (σ : Subst) : Subst
  | 0 => .var 0
  | n + 1 => wk1 (σ n)

def subst (σ : Subst) : Term → Term
  | .univ => .univ
  | .pi A B => .pi (subst σ A) (subst (liftSubst σ) B)
  | .nat => .nat
  | .var x => σ x
  | .lam t => .lam (subst (liftSubst σ) t)
  | .app t u => .app (subst σ t) (subst σ u)
  | .zero => .zero
  | .succ t => .succ (subst σ t)
  | .natrec A z s n =>
      .natrec (subst (liftSubst σ) A) (subst σ z) (subst σ s) (subst σ n)

def consSubst (σ : Subst) (a : Term) : Subst
  | 0 => a
  | n + 1 => σ n

def idSubst : Subst := Term.var

def sgSubst (a : Term) : Subst := consSubst idSubst a

def toSubst (ρ : Wk) : Subst := fun x ↦ .var (wkVar ρ x)

def headSubst (σ : Subst) : Term := σ 0

def tailSubst (σ : Subst) : Subst := fun n ↦ σ (n + 1)

def wk1Subst (σ : Subst) : Subst := fun n ↦ wk1 (σ n)

def compSubst (σ τ : Subst) : Subst := fun n ↦ subst σ (τ n)

def wkSubst (ρ : Wk) (σ : Subst) : Subst := fun n ↦ wk ρ (σ n)

def substWk (σ : Subst) (ρ : Wk) : Subst := fun n ↦ σ (wkVar ρ n)

/-- Replace index zero and remove its binder, corresponding to source t [ a ]. -/
def subst0 (t a : Term) : Term := subst (consSubst idSubst a) t

/-- Replace index zero while retaining the context, corresponding to source t [ a ]↑. -/
def substKeep (t a : Term) : Term := subst (consSubst (wk1Subst idSubst) a) t

/-- Nondependent arrow: source A ▹▹ B. -/
def arr (A B : Term) : Term := .pi A (wk1 B)

/-- Type of the step argument of natrec, in the context outside its motive binder. -/
def recStepType (F : Term) : Term :=
  .pi .nat (arr F (substKeep F (.succ (.var 0))))

/-- Numeral representation `sucᵏ k` of a natural number `k` (`sucᵏ`). -/
def suck : Nat → Term
  | 0 => .zero
  | n + 1 => .succ (suck n)

inductive Neutral : Term → Prop where
  | var (n : Nat) : Neutral (.var n)
  | app {k u} : Neutral k → Neutral (.app k u)
  | natrec {C z s k} : Neutral k → Neutral (.natrec C z s k)

inductive Whnf : Term → Prop where
  | univ : Whnf .univ
  | pi {A B} : Whnf (.pi A B)
  | nat : Whnf .nat
  | lam {t} : Whnf (.lam t)
  | zero : Whnf .zero
  | succ {t} : Whnf (.succ t)
  | neutral {n} : Neutral n → Whnf n

/-- Source view Natural: the weak-head forms of natural-number terms. -/
inductive NaturalView : Term → Prop where
  | zero : NaturalView .zero
  | succ {t} : NaturalView (.succ t)
  | neutral {n} : Neutral n → NaturalView n

/-- Source view Type: small types in weak-head form; the universe is excluded. -/
inductive SmallTypeView : Term → Prop where
  | pi {A B} : SmallTypeView (.pi A B)
  | nat : SmallTypeView .nat
  | neutral {n} : Neutral n → SmallTypeView n

/-- Source view Function: weak-head forms of function terms. -/
inductive FunctionView : Term → Prop where
  | lam {t} : FunctionView (.lam t)
  | neutral {n} : Neutral n → FunctionView n

end Abel2018


