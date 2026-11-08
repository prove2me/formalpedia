-- Prove2me | Definitions.Def_Abel2018_Judgments
-- name    : Abel2018_Judgments
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T13:32:30.755354+00:00
-- url     : https://prove2.me/theorems/1ad49b3d-418c-43fc-83d4-74d43137d688
-- title:
--   Declarative Typing, Judgmental Equality, Typed Weak-Head Reduction, and Abstract Equality Interface
-- statement:
--   Section 2.1, Section 2.2 & Section 3.1: Context membership (`Member`), the 5-way mutual declarative typing and judgmental equality system (`CtxWf`, `TypeWf`, `HasType`, `TypeEq`, `TermEq`) with a Russell-style universe `univ` (`TypeWf.fromUniv`, `TypeEq.fromUniv`) and conversion rules, typed one-step and multi-step weak-head reduction (`Step`, `TypeStep`, `Star`, `TypeStar`, `TypeStarWf`, `StarWf`), well-typed substitutions (`SubstWf`, `SubstEq`), typed context weakening (`WkCtx`), and the abstract equality relation interface `EqRelSet`.
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Sections 2.1, 2.2, and 3.1.

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: Andreas Abel, Joakim Öhman, and Andrea Vezzosi,
"Decidability of Conversion for Type Theory in Type Theory",
Proceedings of the ACM on Programming Languages 2(POPL), Article 23, 2018
(doi:10.1145/3158111), and Agda artifact mr-ohman/logrel-mltt v2.1
(commit eb2b15ab1c4b45923025834d3bb798943cb44b8e),
Definition/Typed.agda, Definition/Typed/Weakening.agda, and
Definition/Typed/EqualityRelation.agda.
-/
import Definitions.Def_Abel2018_Syntax

namespace Abel2018

/-- Variable lookup includes the source's shifts across every context extension. -/
inductive Member : Nat → Term → Context → Prop where
  | here {Γ A} : Member 0 (wk1 A) (A :: Γ)
  | there {Γ A B x} : Member x A Γ → Member (x + 1) (wk1 A) (B :: Γ)

mutual
  inductive CtxWf : Context → Prop where
    | nil : CtxWf []
    | cons {Γ A} : CtxWf Γ → TypeWf Γ A → CtxWf (A :: Γ)

  inductive TypeWf : Context → Term → Prop where
    | nat {Γ} : CtxWf Γ → TypeWf Γ .nat
    | univ {Γ} : CtxWf Γ → TypeWf Γ .univ
    | pi {Γ F G} : TypeWf Γ F → TypeWf (F :: Γ) G → TypeWf Γ (.pi F G)
    | fromUniv {Γ A} : HasType Γ A .univ → TypeWf Γ A

  inductive HasType : Context → Term → Term → Prop where
    | nat {Γ} : CtxWf Γ → HasType Γ .nat .univ
    | pi {Γ F G} : HasType Γ F .univ → HasType (F :: Γ) G .univ →
        HasType Γ (.pi F G) .univ
    | var {Γ A x} : CtxWf Γ → Member x A Γ → HasType Γ (.var x) A
    | lam {Γ F G t} : TypeWf Γ F → HasType (F :: Γ) t G →
        HasType Γ (.lam t) (.pi F G)
    | app {Γ g a F G} : HasType Γ g (.pi F G) → HasType Γ a F →
        HasType Γ (.app g a) (subst0 G a)
    | zero {Γ} : CtxWf Γ → HasType Γ .zero .nat
    | succ {Γ n} : HasType Γ n .nat → HasType Γ (.succ n) .nat
    | natrec {Γ G s z n} : TypeWf (.nat :: Γ) G → HasType Γ z (subst0 G .zero) →
        HasType Γ s (recStepType G) → HasType Γ n .nat →
        HasType Γ (.natrec G z s n) (subst0 G n)
    | conv {Γ t A B} : HasType Γ t A → TypeEq Γ A B → HasType Γ t B

  inductive TypeEq : Context → Term → Term → Prop where
    | fromUniv {Γ A B} : TermEq Γ A B .univ → TypeEq Γ A B
    | refl {Γ A} : TypeWf Γ A → TypeEq Γ A A
    | symm {Γ A B} : TypeEq Γ A B → TypeEq Γ B A
    | trans {Γ A B C} : TypeEq Γ A B → TypeEq Γ B C → TypeEq Γ A C
    | pi {Γ F H G E} : TypeWf Γ F → TypeEq Γ F H → TypeEq (F :: Γ) G E →
        TypeEq Γ (.pi F G) (.pi H E)

  inductive TermEq : Context → Term → Term → Term → Prop where
    | refl {Γ t A} : HasType Γ t A → TermEq Γ t t A
    | symm {Γ t u A} : TermEq Γ t u A → TermEq Γ u t A
    | trans {Γ t u r A} : TermEq Γ t u A → TermEq Γ u r A → TermEq Γ t r A
    | conv {Γ A B t u} : TermEq Γ t u A → TypeEq Γ A B → TermEq Γ t u B
    | pi {Γ E F G H} : TypeWf Γ F → TermEq Γ F H .univ →
        TermEq (F :: Γ) G E .univ → TermEq Γ (.pi F G) (.pi H E) .univ
    | app {Γ a b f g F G} : TermEq Γ f g (.pi F G) → TermEq Γ a b F →
        TermEq Γ (.app f a) (.app g b) (subst0 G a)
    | beta {Γ a t F G} : TypeWf Γ F → HasType (F :: Γ) t G → HasType Γ a F →
        TermEq Γ (.app (.lam t) a) (subst0 t a) (subst0 G a)
    | eta {Γ f g F G} : TypeWf Γ F → HasType Γ f (.pi F G) →
        HasType Γ g (.pi F G) →
        TermEq (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G →
        TermEq Γ f g (.pi F G)
    | succ {Γ m n} : TermEq Γ m n .nat → TermEq Γ (.succ m) (.succ n) .nat
    | natrec {Γ z z' s s' n n' F F'} : TypeEq (.nat :: Γ) F F' →
        TermEq Γ z z' (subst0 F .zero) → TermEq Γ s s' (recStepType F) →
        TermEq Γ n n' .nat →
        TermEq Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n)
    | natrecZero {Γ z s F} : TypeWf (.nat :: Γ) F → HasType Γ z (subst0 F .zero) →
        HasType Γ s (recStepType F) →
        TermEq Γ (.natrec F z s .zero) z (subst0 F .zero)
    | natrecSucc {Γ n z s F} : HasType Γ n .nat → TypeWf (.nat :: Γ) F →
        HasType Γ z (subst0 F .zero) → HasType Γ s (recStepType F) →
        TermEq Γ (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
          (subst0 F (.succ n))
end

/-- Typed weak-head reduction; in particular there is no reduction under a lambda or successor. -/
inductive Step (Γ : Context) : Term → Term → Term → Prop where
  | conv {A B t u} : Step Γ t u A → TypeEq Γ A B → Step Γ t u B
  | app {A B t u a} : Step Γ t u (.pi A B) → HasType Γ a A →
      Step Γ (.app t a) (.app u a) (subst0 B a)
  | beta {A B a t} : TypeWf Γ A → HasType (A :: Γ) t B → HasType Γ a A →
      Step Γ (.app (.lam t) a) (subst0 t a) (subst0 B a)
  | natrec {z s n n' F} : TypeWf (.nat :: Γ) F → HasType Γ z (subst0 F .zero) →
      HasType Γ s (recStepType F) → Step Γ n n' .nat →
      Step Γ (.natrec F z s n) (.natrec F z s n') (subst0 F n)
  | natrecZero {z s F} : TypeWf (.nat :: Γ) F → HasType Γ z (subst0 F .zero) →
      HasType Γ s (recStepType F) → Step Γ (.natrec F z s .zero) z (subst0 F .zero)
  | natrecSucc {n z s F} : HasType Γ n .nat → TypeWf (.nat :: Γ) F →
      HasType Γ z (subst0 F .zero) → HasType Γ s (recStepType F) →
      Step Γ (.natrec F z s (.succ n)) (.app (.app s n) (.natrec F z s n))
        (subst0 F (.succ n))

inductive TypeStep (Γ : Context) : Term → Term → Prop where
  | fromUniv {A B} : Step Γ A B .univ → TypeStep Γ A B

/-- Source reflexive-transitive closure, whose reflexive case requires a typing derivation. -/
inductive Star (Γ : Context) : Term → Term → Term → Prop where
  | refl {A t} : HasType Γ t A → Star Γ t t A
  | step {A t t' u} : Step Γ t t' A → Star Γ t' u A → Star Γ t u A

inductive TypeStar (Γ : Context) : Term → Term → Prop where
  | refl {A} : TypeWf Γ A → TypeStar Γ A A
  | step {A A' B} : TypeStep Γ A A' → TypeStar Γ A' B → TypeStar Γ A B

def TypeWhnf (Γ : Context) (A B : Term) : Prop := TypeStar Γ A B ∧ Whnf B

def TermWhnf (Γ : Context) (t u A : Term) : Prop := Star Γ t u A ∧ Whnf u

/-- The source's type equality bundled with well-formed endpoints. -/
def TypeEqWf (Γ : Context) (A B : Term) : Prop :=
  TypeWf Γ A ∧ TypeWf Γ B ∧ TypeEq Γ A B

/-- The source's term equality bundled with well-typed endpoints. -/
def TermEqWf (Γ : Context) (t u A : Term) : Prop :=
  HasType Γ t A ∧ HasType Γ u A ∧ TermEq Γ t u A

structure TypeStarWf (Γ : Context) (A B : Term) : Prop where
  source : TypeWf Γ A
  target : TypeWf Γ B
  reduction : TypeStar Γ A B

structure StarWf (Γ : Context) (t u A : Term) : Prop where
  source : HasType Γ t A
  target : HasType Γ u A
  reduction : Star Γ t u A

/-- The source's substitution judgment; it does not assert ambient context validity. -/
inductive SubstWf (Δ : Context) : Subst → Context → Prop where
  | nil {σ} : SubstWf Δ σ []
  | cons {Γ A σ} : SubstWf Δ (tailSubst σ) Γ →
      HasType Δ (headSubst σ) (subst (tailSubst σ) A) → SubstWf Δ σ (A :: Γ)

inductive SubstEq (Δ : Context) : Subst → Subst → Context → Prop where
  | nil {σ σ'} : SubstEq Δ σ σ' []
  | cons {Γ A σ σ'} : SubstEq Δ (tailSubst σ) (tailSubst σ') Γ →
      TermEq Δ (headSubst σ) (headSubst σ') (subst (tailSubst σ) A) →
      SubstEq Δ σ σ' (A :: Γ)

/-- Typed weakening relation `ρ ∷ Δ ⊆ Γ` on newest-first contexts. -/
inductive WkCtx : Wk → Context → Context → Prop where
  | id {Γ} : WkCtx .id Γ Γ
  | step {Γ Δ A ρ} : WkCtx ρ Δ Γ → WkCtx (.step ρ) (A :: Δ) Γ
  | lift {Γ Δ A ρ} : WkCtx ρ Δ Γ → WkCtx (.lift ρ) (wk ρ A :: Δ) (A :: Γ)

/-- Generic equality relation interface (`EqRelSet` from `Definition.Typed.EqualityRelation`). -/
structure EqRelSet where
  TypeEqRel : Context → Term → Term → Prop
  TermEqRel : Context → Term → Term → Term → Prop
  NeEqRel : Context → Term → Term → Term → Prop
  neToTerm : ∀ {Γ k l A}, NeEqRel Γ k l A → TermEqRel Γ k l A
  typeToEq : ∀ {Γ A B}, TypeEqRel Γ A B → TypeEq Γ A B
  termToEq : ∀ {Γ t u A}, TermEqRel Γ t u A → TermEq Γ t u A
  univ : ∀ {Γ A B}, TermEqRel Γ A B .univ → TypeEqRel Γ A B
  symmType : ∀ {Γ A B}, TypeEqRel Γ A B → TypeEqRel Γ B A
  symmTerm : ∀ {Γ t u A}, TermEqRel Γ t u A → TermEqRel Γ u t A
  symmNe : ∀ {Γ k l A}, NeEqRel Γ k l A → NeEqRel Γ l k A
  transType : ∀ {Γ A B C}, TypeEqRel Γ A B → TypeEqRel Γ B C → TypeEqRel Γ A C
  transTerm : ∀ {Γ t u v A}, TermEqRel Γ t u A → TermEqRel Γ u v A → TermEqRel Γ t v A
  transNe : ∀ {Γ k l m A}, NeEqRel Γ k l A → NeEqRel Γ l m A → NeEqRel Γ k m A
  convTerm : ∀ {Γ t u A B}, TermEqRel Γ t u A → TypeEq Γ A B → TermEqRel Γ t u B
  convNe : ∀ {Γ k l A B}, NeEqRel Γ k l A → TypeEq Γ A B → NeEqRel Γ k l B
  wkType : ∀ {Γ Δ A B ρ}, WkCtx ρ Δ Γ → CtxWf Δ → TypeEqRel Γ A B → TypeEqRel Δ (wk ρ A) (wk ρ B)
  wkTerm : ∀ {Γ Δ t u A ρ}, WkCtx ρ Δ Γ → CtxWf Δ → TermEqRel Γ t u A →
    TermEqRel Δ (wk ρ t) (wk ρ u) (wk ρ A)
  wkNe : ∀ {Γ Δ k l A ρ}, WkCtx ρ Δ Γ → CtxWf Δ → NeEqRel Γ k l A →
    NeEqRel Δ (wk ρ k) (wk ρ l) (wk ρ A)
  redType : ∀ {Γ A A' B B'}, TypeStar Γ A A' → TypeStar Γ B B' →
    Whnf A' → Whnf B' → TypeEqRel Γ A' B' → TypeEqRel Γ A B
  redTerm : ∀ {Γ a a' b b' A B}, TypeStar Γ A B → Star Γ a a' B → Star Γ b b' B →
    Whnf B → Whnf a' → Whnf b' → TermEqRel Γ a' b' B → TermEqRel Γ a b A
  univRefl : ∀ {Γ}, CtxWf Γ → TypeEqRel Γ .univ .univ
  natRefl : ∀ {Γ}, CtxWf Γ → TypeEqRel Γ .nat .nat
  natTermRefl : ∀ {Γ}, CtxWf Γ → TermEqRel Γ .nat .nat .univ
  piCong : ∀ {Γ F G H E}, TypeWf Γ F → TypeEqRel Γ F H → TypeEqRel (F :: Γ) G E →
    TypeEqRel Γ (.pi F G) (.pi H E)
  piTermCong : ∀ {Γ F G H E}, TypeWf Γ F → TermEqRel Γ F H .univ → TermEqRel (F :: Γ) G E .univ →
    TermEqRel Γ (.pi F G) (.pi H E) .univ
  zeroRefl : ∀ {Γ}, CtxWf Γ → TermEqRel Γ .zero .zero .nat
  succCong : ∀ {Γ m n}, TermEqRel Γ m n .nat → TermEqRel Γ (.succ m) (.succ n) .nat
  etaEq : ∀ {Γ f g F G}, TypeWf Γ F → HasType Γ f (.pi F G) → HasType Γ g (.pi F G) →
    Whnf f → Whnf g → TermEqRel (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G →
    TermEqRel Γ f g (.pi F G)
  varRefl : ∀ {Γ x A}, HasType Γ (.var x) A → NeEqRel Γ (.var x) (.var x) A
  appCong : ∀ {Γ a b f g F G}, NeEqRel Γ f g (.pi F G) → TermEqRel Γ a b F →
    NeEqRel Γ (.app f a) (.app g b) (subst0 G a)
  natrecCong : ∀ {Γ z z' s s' n n' F F'}, TypeEqRel (.nat :: Γ) F F' →
    TermEqRel Γ z z' (subst0 F .zero) → TermEqRel Γ s s' (recStepType F) →
    NeEqRel Γ n n' .nat → NeEqRel Γ (.natrec F z s n) (.natrec F' z' s' n') (subst0 F n)

end Abel2018


