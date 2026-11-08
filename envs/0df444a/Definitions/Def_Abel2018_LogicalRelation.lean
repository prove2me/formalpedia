-- Prove2me | Definitions.Def_Abel2018_LogicalRelation
-- name    : Abel2018_LogicalRelation
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T13:32:52.076868+00:00
-- url     : https://prove2.me/theorems/56cd6235-65e0-4e4e-9413-bd0611ca046a
-- title:
--   Parameterized Kripke Logical Relation, Relation-Bundle Equivalence, and Semantic Validity
-- statement:
--   Section 3.2 to Section 3.6: Reducibility predicates for neutral types (`RedNe`) and natural numbers (`RedNat`, `RedNatTerm`, `RedNatTermEq`), the Kripke logical relation (`LogRel`, `LogRelAt`) parameterized by `eqrel : EqRelSet` and stratified across the two-element metatheoretic index `TypeLevel` (`zero < one`) to represent the paper's inductive-recursive universe reducibility in Lean 4, relation bundles (`RedRel`) and bundle equivalence (`RedRelEquiv`), decoded reducibility judgments (`RedType`, `RedEq`, `RedTerm`, `RedTermEq`), and semantic substitution validity (`ValidSubst`, `ValidSubstEq`, `FundCtxMotive`, `FundTypeMotive`, `FundTermMotive`, `FundTypeEqMotive`, `FundTermEqMotive`).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Sections 3.2-3.6 (`LogicalRelation.agda`, `Valid.agda`).

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean translation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: Andreas Abel, Joakim Öhman, and Andrea Vezzosi,
"Decidability of Conversion for Type Theory in Type Theory",
Proceedings of the ACM on Programming Languages 2(POPL), Article 23, 2018
(doi:10.1145/3158111), Section 3, and Agda artifact mr-ohman/logrel-mltt v2.1
(commit eb2b15ab1c4b45923025834d3bb798943cb44b8e),
Definition/LogicalRelation.agda, Definition/LogicalRelation/Substitution.agda,
and Definition/LogicalRelation/Fundamental.agda.
-/
import Definitions.Def_Abel2018_Algorithm

namespace Abel2018

/-- Reducible neutral type with explicit WHNF `K` (`Γ ⊩ne A`). -/
structure RedNeAt (eqrel : EqRelSet) (Γ : Context) (A K : Term) : Prop where
  D : TypeStarWf Γ A K
  neK : Neutral K
  KeqK : eqrel.NeEqRel Γ K K .univ

/-- Reducible neutral type (`Γ ⊩ne A`). -/
inductive RedNe (eqrel : EqRelSet) (Γ : Context) (A : Term) : Prop where
  | mk (K : Term) (D : TypeStarWf Γ A K) (neK : Neutral K) (KeqK : eqrel.NeEqRel Γ K K .univ)

/-- Reducible neutral type equality (`Γ ⊩ne A ≡ B / [A]`). -/
inductive RedNeEq (eqrel : EqRelSet) (Γ : Context) (K B : Term) : Prop where
  | mk (M : Term) (D' : TypeStarWf Γ B M) (neM : Neutral M) (KeqM : eqrel.NeEqRel Γ K M .univ)

/-- Reducible neutral term in WHNF (`Γ ⊩neNf k ∷ A`). -/
structure RedNeNf (eqrel : EqRelSet) (Γ : Context) (k A : Term) : Prop where
  neK : Neutral k
  hk : HasType Γ k A
  keqk : eqrel.NeEqRel Γ k k A

/-- Reducible neutral term (`Γ ⊩ne t ∷ A / [A]`). -/
inductive RedNeTerm (eqrel : EqRelSet) (Γ : Context) (K t : Term) : Prop where
  | mk (k : Term) (d : StarWf Γ t k K) (nf : RedNeNf eqrel Γ k K)

/-- Reducible neutral term equality in WHNF (`Γ ⊩neNf k ≡ m ∷ A`). -/
structure RedNeNfEq (eqrel : EqRelSet) (Γ : Context) (k m A : Term) : Prop where
  neK : Neutral k
  neM : Neutral m
  keqm : eqrel.NeEqRel Γ k m A

/-- Reducible neutral term equality (`Γ ⊩ne t ≡ u ∷ A / [A]`). -/
inductive RedNeTermEq (eqrel : EqRelSet) (Γ : Context) (K t u : Term) : Prop where
  | mk (k m : Term) (d : StarWf Γ t k K) (d' : StarWf Γ u m K) (nf : RedNeNfEq eqrel Γ k m K)

/-- Reducible natural number type (`Γ ⊩ℕ A`). -/
abbrev RedNat (Γ : Context) (A : Term) : Prop :=
  TypeStarWf Γ A .nat

/-- Reducible natural number type equality (`Γ ⊩ℕ A ≡ B`). -/
abbrev RedNatEq (Γ : Context) (B : Term) : Prop :=
  TypeStar Γ B .nat

mutual
  /-- Reducible natural number term (`Γ ⊩ℕ t ∷ℕ`). -/
  inductive RedNatTerm (eqrel : EqRelSet) (Γ : Context) : Term → Prop where
    | mk (t n : Term)
        (d : StarWf Γ t n .nat)
        (neqn : eqrel.TermEqRel Γ n n .nat)
        (prop : NaturalProp eqrel Γ n) :
        RedNatTerm eqrel Γ t

  /-- WHNF property of reducible natural number terms (`Natural-prop`). -/
  inductive NaturalProp (eqrel : EqRelSet) (Γ : Context) : Term → Prop where
    | suc {n : Term} : RedNatTerm eqrel Γ n → NaturalProp eqrel Γ (.succ n)
    | zero : NaturalProp eqrel Γ .zero
    | ne {n : Term} : RedNeNf eqrel Γ n .nat → NaturalProp eqrel Γ n
end

mutual
  /-- Reducible natural number term equality (`Γ ⊩ℕ t ≡ u ∷ℕ`). -/
  inductive RedNatTermEq (eqrel : EqRelSet) (Γ : Context) : Term → Term → Prop where
    | mk (t u k k' : Term)
        (d : StarWf Γ t k .nat)
        (d' : StarWf Γ u k' .nat)
        (keqk' : eqrel.TermEqRel Γ k k' .nat)
        (prop : NaturalEqProp eqrel Γ k k') :
        RedNatTermEq eqrel Γ t u

  /-- WHNF property of reducible natural number term equality (`[Natural]-prop`). -/
  inductive NaturalEqProp (eqrel : EqRelSet) (Γ : Context) : Term → Term → Prop where
    | suc {n n' : Term} : RedNatTermEq eqrel Γ n n' → NaturalEqProp eqrel Γ (.succ n) (.succ n')
    | zero : NaturalEqProp eqrel Γ .zero .zero
    | ne {n n' : Term} : RedNeNfEq eqrel Γ n n' .nat → NaturalEqProp eqrel Γ n n'
end

/-- Universe levels `⁰` and `¹`. -/
inductive TypeLevel where
  | zero
  | one
  deriving DecidableEq, Repr

/-- Strict ordering `⁰ < ¹` on `TypeLevel`. -/
inductive TypeLevelLT : TypeLevel → TypeLevel → Prop where
  | zeroLT : TypeLevelLT .zero .one

/-- Bundle of decoded relations for a reducible type:
type equality (`eqType`), term reducibility (`hasTerm`), and term equality (`eqTerm`). -/
structure RedRel : Type 1 where
  eqType : Term → Prop
  hasTerm : Term → Prop
  eqTerm : Term → Term → Prop

/-- Equivalence of two `RedRel` bundles across all three decoded predicates. -/
def RedRelEquiv (rel₁ rel₂ : RedRel) : Prop :=
  (∀ {B}, rel₁.eqType B ↔ rel₂.eqType B) ∧
  (∀ {t}, rel₁.hasTerm t ↔ rel₂.hasTerm t) ∧
  (∀ {t u}, rel₁.eqTerm t u ↔ rel₂.eqTerm t u)

/-- Reducible universe type with explicit lower level `l'` (`Γ ⊩¹U`). -/
structure RedUAt (l' l : TypeLevel) (Γ : Context) : Prop where
  lt : TypeLevelLT l' l
  wf : CtxWf Γ

/-- Reducible universe type (`Γ ⊩¹U`). -/
inductive RedU (l : TypeLevel) (Γ : Context) : Prop where
  | mk (l' : TypeLevel) (lt : TypeLevelLT l' l) (wf : CtxWf Γ)

/-- Reducible term of universe type (`Γ ⊩¹U t ∷U/ l<`). -/
inductive RedUTerm (eqrel : EqRelSet) (rec : Context → Term → RedRel → Prop)
    (Γ : Context) (t : Term) : Prop where
  | mk (A : Term)
      (d : StarWf Γ t A .univ)
      (typeA : SmallTypeView A)
      (AeqA : eqrel.TermEqRel Γ A A .univ)
      (ht : ∃ rel, rec Γ t rel)

/-- Reducible term equality of universe type (`Γ ⊩¹U t ≡ u ∷U/ l<`). -/
inductive RedUTermEq (eqrel : EqRelSet) (rec : Context → Term → RedRel → Prop)
    (Γ : Context) (t u : Term) : Prop where
  | mk (A B : Term)
      (d : StarWf Γ t A .univ)
      (d' : StarWf Γ u B .univ)
      (typeA : SmallTypeView A)
      (typeB : SmallTypeView B)
      (AeqB : eqrel.TermEqRel Γ A B .univ)
      (relt : RedRel)
      (ht : rec Γ t relt)
      (hu : ∃ relu, rec Γ u relu)
      (tequ : relt.eqType u)

/-- Relation bundle for `U`. -/
def RedURel (eqrel : EqRelSet) (rec : Context → Term → RedRel → Prop) (Γ : Context) : RedRel where
  eqType B := B = .univ
  hasTerm t := RedUTerm eqrel rec Γ t
  eqTerm t u := RedUTermEq eqrel rec Γ t u

/-- Relation bundle for `ℕ`. -/
def RedNatRel (eqrel : EqRelSet) (Γ : Context) : RedRel where
  eqType B := RedNatEq Γ B
  hasTerm t := RedNatTerm eqrel Γ t
  eqTerm t u := RedNatTermEq eqrel Γ t u

/-- Relation bundle for neutral types. -/
def RedNeRel (eqrel : EqRelSet) (Γ : Context) (K : Term) : RedRel where
  eqType B := RedNeEq eqrel Γ K B
  hasTerm t := RedNeTerm eqrel Γ K t
  eqTerm t u := RedNeTermEq eqrel Γ K t u

/-- Helper predicates for domain and codomain relation families in `Π`. -/
abbrev RelFEqType (relF : Wk → Context → RedRel → Prop) (ρ : Wk) (Δ : Context) (B : Term) : Prop :=
  ∃ rel, relF ρ Δ rel ∧ rel.eqType B

abbrev RelFHasTerm (relF : Wk → Context → RedRel → Prop) (ρ : Wk) (Δ : Context) (a : Term) : Prop :=
  ∃ rel, relF ρ Δ rel ∧ rel.hasTerm a

abbrev RelFEqTerm (relF : Wk → Context → RedRel → Prop) (ρ : Wk) (Δ : Context) (a b : Term) : Prop :=
  ∃ rel, relF ρ Δ rel ∧ rel.eqTerm a b

abbrev RelGEqType (relG : Wk → Context → Term → RedRel → Prop)
    (ρ : Wk) (Δ : Context) (a B : Term) : Prop :=
  ∃ rel, relG ρ Δ a rel ∧ rel.eqType B

abbrev RelGHasTerm (relG : Wk → Context → Term → RedRel → Prop)
    (ρ : Wk) (Δ : Context) (a t : Term) : Prop :=
  ∃ rel, relG ρ Δ a rel ∧ rel.hasTerm t

abbrev RelGEqTerm (relG : Wk → Context → Term → RedRel → Prop)
    (ρ : Wk) (Δ : Context) (a t u : Term) : Prop :=
  ∃ rel, relG ρ Δ a rel ∧ rel.eqTerm t u

/-- Reducible `Π`-type equality (`Γ ⊩¹Π A ≡ B / [A]`). -/
inductive RedPiEq (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (B : Term) : Prop where
  | mk (F' G' : Term)
      (D' : TypeStar Γ B (.pi F' G'))
      (AeqB : eqrel.TypeEqRel Γ (.pi F G) (.pi F' G'))
      (FeqF' : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RelFEqType relF ρ Δ (wk ρ F'))
      (GeqG' : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ → RelFHasTerm relF ρ Δ a →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G') a))

/-- Reducible term of `Π`-type (`Γ ⊩¹Π t ∷ A / [A]`). -/
inductive RedPiTerm (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (t : Term) : Prop where
  | mk (f : Term)
      (d : StarWf Γ t f (.pi F G))
      (funcF : FunctionView f)
      (feqf : eqrel.TermEqRel Γ f f (.pi F G))
      (appEq : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqTerm relG ρ Δ a (.app (wk ρ f) a) (.app (wk ρ f) b))
      (appTerm : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelGHasTerm relG ρ Δ a (.app (wk ρ f) a))

/-- Reducible term equality of `Π`-type (`Γ ⊩¹Π t ≡ u ∷ A / [A]`). -/
inductive RedPiTermEq (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop)
    (t u : Term) : Prop where
  | mk (f g : Term)
      (d : StarWf Γ t f (.pi F G))
      (d' : StarWf Γ u g (.pi F G))
      (funcF : FunctionView f)
      (funcG : FunctionView g)
      (feqg : eqrel.TermEqRel Γ f g (.pi F G))
      (ht : RedPiTerm eqrel Γ F G relF relG t)
      (hu : RedPiTerm eqrel Γ F G relF relG u)
      (appEq : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelGEqTerm relG ρ Δ a (.app (wk ρ f) a) (.app (wk ρ g) a))

/-- Relation bundle for `Π`-types. -/
def RedPiRel (eqrel : EqRelSet) (Γ : Context) (F G : Term)
    (relF : Wk → Context → RedRel → Prop)
    (relG : Wk → Context → Term → RedRel → Prop) : RedRel where
  eqType B := RedPiEq eqrel Γ F G relF relG B
  hasTerm t := RedPiTerm eqrel Γ F G relF relG t
  eqTerm t u := RedPiTermEq eqrel Γ F G relF relG t u

/-- One level of the logical relation (`LogRel` in `Definition/LogicalRelation.agda`),
parameterized by the lower-level relation `rec`. -/
inductive LogRel (eqrel : EqRelSet) (l : TypeLevel)
    (rec : ∀ (l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop) :
    Context → Term → RedRel → Prop where
  | U {Γ : Context} {l' : TypeLevel} (hU : RedUAt l' l Γ) :
      LogRel eqrel l rec Γ .univ (RedURel eqrel (rec l' hU.lt) Γ)
  | nat {Γ : Context} {A : Term} (D : RedNat Γ A) :
      LogRel eqrel l rec Γ A (RedNatRel eqrel Γ)
  | ne {Γ : Context} {A K : Term} (neA : RedNeAt eqrel Γ A K) :
      LogRel eqrel l rec Γ A (RedNeRel eqrel Γ K)
  | pi {Γ : Context} {A F G : Term}
      (D : TypeStarWf Γ A (.pi F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G))
      (relF : Wk → Context → RedRel → Prop)
      (relG : Wk → Context → Term → RedRel → Prop)
      (hF_ex : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → ∃ rel, relF ρ Δ rel)
      (derivF : ∀ {ρ Δ} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ) (rel : RedRel),
        relF ρ Δ rel → LogRel eqrel l rec Δ (wk ρ F) rel)
      (hG_ex : ∀ {ρ Δ a}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a → ∃ rel, relG ρ Δ a rel)
      (derivG : ∀ {ρ Δ a} (_hρ : WkCtx ρ Δ Γ) (_hΔ : CtxWf Δ)
        (_ha : RelFHasTerm relF ρ Δ a) (rel : RedRel),
        relG ρ Δ a rel → LogRel eqrel l rec Δ (subst0 (wk (.lift ρ) G) a) rel)
      (Gext : ∀ {ρ Δ a b}, WkCtx ρ Δ Γ → CtxWf Δ →
        RelFHasTerm relF ρ Δ a →
        RelFHasTerm relF ρ Δ b →
        RelFEqTerm relF ρ Δ a b →
        RelGEqType relG ρ Δ a (subst0 (wk (.lift ρ) G) b)) :
      LogRel eqrel l rec Γ A (RedPiRel eqrel Γ F G relF relG)
  | emb {Γ : Context} {A : Term} {l' : TypeLevel} {rel : RedRel}
      (hlt : TypeLevelLT l' l)
      (hA : rec l' hlt Γ A rel) :
      LogRel eqrel l rec Γ A rel

/-- Empty lower-level relation at level `⁰`. -/
def logRelRecZero : ∀ (l' : TypeLevel), TypeLevelLT l' .zero → Context → Term → RedRel → Prop :=
  fun _ hlt ↦ nomatch hlt

/-- Level recursion for `LogRel` (`logRelRec` in `Definition/LogicalRelation.agda`). -/
def logRelRec (eqrel : EqRelSet) :
    ∀ (l l' : TypeLevel), TypeLevelLT l' l → Context → Term → RedRel → Prop
  | .zero => logRelRecZero
  | .one => fun _ .zeroLT ↦ LogRel eqrel .zero logRelRecZero

/-- The logical relation at level `l` (`kit l`). -/
abbrev LogRelAt (eqrel : EqRelSet) (l : TypeLevel) : Context → Term → RedRel → Prop :=
  LogRel eqrel l (logRelRec eqrel l)

/-- Reducibility of a type at level `l` (`Γ ⊩⟨ l ⟩ A`). -/
def RedType (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel

/-- Reducible type equality (`Γ ⊩⟨ l ⟩ A ≡ B / [A]`). -/
def RedEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (_hA : RedType eqrel l Γ A) (B : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel ∧ rel.eqType B

/-- Reducible term (`Γ ⊩⟨ l ⟩ t ∷ A / [A]`). -/
def RedTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (_hA : RedType eqrel l Γ A) (t : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel ∧ rel.hasTerm t

/-- Reducible term equality (`Γ ⊩⟨ l ⟩ t ≡ u ∷ A / [A]`). -/
def RedTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (_hA : RedType eqrel l Γ A) (t u : Term) : Prop :=
  ∃ rel, LogRelAt eqrel l Γ A rel ∧ rel.eqTerm t u

/-- Bundled `Π`-reducibility data with explicit domain `F` and codomain `G` (`Γ ⊩′⟨ l ⟩Π A`). -/
structure RedPiAt (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A F G : Term) : Prop where
  D : TypeStarWf Γ A (.pi F G)
  hF : TypeWf Γ F
  hG : TypeWf (F :: Γ) G
  AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G)
  redF : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RedType eqrel l Δ (wk ρ F)
  redG : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
    RedTerm (redF hρ hΔ) a → RedType eqrel l Δ (subst0 (wk (.lift ρ) G) a)
  Gext : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
    (ha : RedTerm (redF hρ hΔ) a) (_hb : RedTerm (redF hρ hΔ) b),
    RedTermEq (redF hρ hΔ) a b →
    RedEq (redG hρ hΔ ha) (subst0 (wk (.lift ρ) G) b)

/-- Bundled `Π`-reducibility data (`Γ ⊩′⟨ l ⟩Π A`). -/
inductive RedPi (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A : Term) : Prop where
  | mk (F G : Term)
      (D : TypeStarWf Γ A (.pi F G))
      (hF : TypeWf Γ F)
      (hG : TypeWf (F :: Γ) G)
      (AeqA : eqrel.TypeEqRel Γ (.pi F G) (.pi F G))
      (redF : ∀ {ρ Δ}, WkCtx ρ Δ Γ → CtxWf Δ → RedType eqrel l Δ (wk ρ F))
      (redG : ∀ {ρ Δ a} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ),
        RedTerm (redF hρ hΔ) a → RedType eqrel l Δ (subst0 (wk (.lift ρ) G) a))
      (Gext : ∀ {ρ Δ a b} (hρ : WkCtx ρ Δ Γ) (hΔ : CtxWf Δ)
        (ha : RedTerm (redF hρ hΔ) a) (_hb : RedTerm (redF hρ hΔ) b),
        RedTermEq (redF hρ hΔ) a b →
        RedEq (redG hρ hΔ ha) (subst0 (wk (.lift ρ) G) b))

/-- Logical relation for substitutions (`Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ`). -/
def ValidSubst (eqrel : EqRelSet) (Δ : Context) (σ : Subst) : Context → Prop
  | [] => True
  | A :: Γ =>
      ValidSubst eqrel Δ (tailSubst σ) Γ ∧
      ∃ (l : TypeLevel) (pA : RedType eqrel l Δ (subst (tailSubst σ) A)),
        RedTerm pA (headSubst σ)

/-- Logical relation for equality of substitutions (`Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]`). -/
def ValidSubstEq (eqrel : EqRelSet) (Δ : Context) (σ σ' : Subst) : Context → Prop
  | [] => True
  | A :: Γ =>
      ValidSubstEq eqrel Δ (tailSubst σ) (tailSubst σ') Γ ∧
      ∃ (l : TypeLevel) (pA : RedType eqrel l Δ (subst (tailSubst σ) A)),
        RedTermEq pA (headSubst σ) (headSubst σ')

/-- Pointwise type validity at a target context `Δ` and substitution `σ`. -/
structure ValidTypeAt (eqrel : EqRelSet) (l : TypeLevel) (Δ Γ : Context)
    (σ : Subst) (A : Term) : Prop where
  red : RedType eqrel l Δ (subst σ A)
  eq : ∀ {σ' : Subst},
    ValidSubst eqrel Δ σ' Γ →
    ValidSubstEq eqrel Δ σ σ' Γ →
    RedEq red (subst σ' A)

/-- Validity of types (`Γ ⊩ᵛ⟨ l ⟩ A / [Γ]`). -/
def ValidType (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (A : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst},
    CtxWf Δ → ValidSubst eqrel Δ σ Γ →
    ValidTypeAt eqrel l Δ Γ σ A

/-- Validity of contexts (`⊩ᵛ Γ`). -/
inductive ValidCtx (eqrel : EqRelSet) : Context → Prop where
  | nil : ValidCtx eqrel []
  | cons {Γ : Context} {A : Term} {l : TypeLevel} :
      ValidCtx eqrel Γ → ValidType eqrel l Γ A → ValidCtx eqrel (A :: Γ)

/-- Pointwise term validity at a target context `Δ` and substitution `σ`. -/
structure ValidTermAt {eqrel : EqRelSet} {l : TypeLevel} {Δ : Context} (Γ : Context)
    {σ : Subst} {A : Term} (pA : RedType eqrel l Δ (subst σ A)) (t : Term) : Prop where
  term : RedTerm pA (subst σ t)
  eq : ∀ {σ' : Subst},
    ValidSubst eqrel Δ σ' Γ →
    ValidSubstEq eqrel Δ σ σ' Γ →
    RedTermEq pA (subst σ t) (subst σ' t)

/-- Validity of terms (`Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]`). -/
def ValidTerm {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) (t : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst} (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ),
    ValidTermAt Γ (hA hΔ hσ).red t

/-- Validity of type equality (`Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]`). -/
def ValidTypeEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) (B : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst} (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ),
    RedEq (hA hΔ hσ).red (subst σ B)

/-- Validity of term equality (`Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] / [A]`). -/
def ValidTermEq {eqrel : EqRelSet} {l : TypeLevel} {Γ : Context} {A : Term}
    (hA : ValidType eqrel l Γ A) (t u : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst} (hΔ : CtxWf Δ) (hσ : ValidSubst eqrel Δ σ Γ),
    RedTermEq (hA hΔ hσ).red (subst σ t) (subst σ u)

/-- Valid term equality bundled with validity of its type and terms (`[ Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / [Γ] ]`). -/
structure ModelsTermEq (eqrel : EqRelSet) (l : TypeLevel) (Γ : Context) (t u A : Term) : Prop where
  validA : ValidType eqrel l Γ A
  validt : ValidTerm validA t
  validu : ValidTerm validA u
  validEq : ValidTermEq validA t u

/-- Validity of term reduction (`Γ ⊩ᵛ t ⇒ u ∷ A / [Γ]`). -/
def ValidRedTerm (eqrel : EqRelSet) (Γ : Context) (t u A : Term) : Prop :=
  ∀ {Δ : Context} {σ : Subst},
    CtxWf Δ → ValidSubst eqrel Δ σ Γ →
    Step Δ (subst σ t) (subst σ u) (subst σ A)

abbrev FundCtxMotive (eqrel : EqRelSet) (Γ : Context) : Prop :=
  ValidCtx eqrel Γ

abbrev FundTypeMotive (eqrel : EqRelSet) (Γ : Context) (A : Term) : Prop :=
  ValidCtx eqrel Γ ∧ ValidType eqrel .one Γ A

abbrev FundTermMotive (eqrel : EqRelSet) (Γ : Context) (t A : Term) : Prop :=
  ValidCtx eqrel Γ ∧ ∃ (hA : ValidType eqrel .one Γ A), ValidTerm hA t

abbrev FundTypeEqMotive (eqrel : EqRelSet) (Γ : Context) (A B : Term) : Prop :=
  ValidCtx eqrel Γ ∧
  ∃ (hA : ValidType eqrel .one Γ A), ValidType eqrel .one Γ B ∧ ValidTypeEq hA B

abbrev FundTermEqMotive (eqrel : EqRelSet) (Γ : Context) (t u A : Term) : Prop :=
  ValidCtx eqrel Γ ∧ ModelsTermEq eqrel .one Γ t u A

end Abel2018


