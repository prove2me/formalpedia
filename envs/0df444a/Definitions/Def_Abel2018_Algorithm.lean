-- Prove2me | Definitions.Def_Abel2018_Algorithm
-- name    : Abel2018_Algorithm
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T13:32:39.521816+00:00
-- url     : https://prove2.me/theorems/d4906ee7-b52a-487b-a810-befe7f14b6ff
-- title:
--   Executable Fuel-Bounded Conversion Checkers, Algorithmic Conversion Relations, and Injected Neutral Equality
-- statement:
--   Section 4.1 & Section 4.3: Executable fuel-bounded weak-head normalizer (`whnfFuel`) and 6-way mutual executable conversion checkers (`compareNeutralUp`, `compareNeutralDown`, `compareTypeUp`, `compareTypeDown`, `compareTermUp`, `compareTermDown`), together with the 6-way mutual inductive algorithmic conversion specification (`ConvNeUp`, `ConvNeDown`, `ConvTypeUp`, `ConvTypeDown`, `ConvTermUp`, `ConvTermDown`), context equality `CtxEq`, and injected algorithmic neutral equality `ConvNeEq` (`∃ B, TypeEq Γ A B ∧ ConvNeUp Γ k l B`, corresponding to `_~_∷_` in `AlgorithmicEquality.agda` for the `NeEqRel` field of `EqRelSet`).
-- source:
--   Andreas Abel, Joakim Öhman, and Andrea Vezzosi, 'Decidability of Conversion for Type Theory in Type Theory', Proceedings of the ACM on Programming Languages (PACMPL), Vol. 2, No. POPL, Article 23, January 2018, pp. 23:1-23:29 (doi:10.1145/3158111). Mechanized Agda artifact: https://github.com/mr-ohman/logrel-mltt (commit eb2b15ab1c4b45923025834d3bb798943cb44b8e). Sections 4.1 and 4.3 (`AlgorithmicEquality.agda`).

/-
Copyright (c) 2016 Joakim Öhman, Andrea Vezzosi, Andreas Abel.
Lean implementation prepared for the Feasible Univalence project, 2026.
Released under the MIT license; see the source artifact LICENSE.

Source: Andreas Abel, Joakim Öhman, and Andrea Vezzosi,
"Decidability of Conversion for Type Theory in Type Theory",
Proceedings of the ACM on Programming Languages 2(POPL), Article 23, 2018
(doi:10.1145/3158111), Figure 6, and Agda artifact mr-ohman/logrel-mltt v2.1
(commit eb2b15ab1c4b45923025834d3bb798943cb44b8e),
Definition/Conversion.agda and Definition/Conversion/Stability.agda.
-/
import Definitions.Def_Abel2018_Judgments

namespace Abel2018

/-- Syntactic neutral-head test, with precisely the source's neutral constructors. -/
def neutralHead : Term → Bool
  | .var _ => true
  | .app k _ => neutralHead k
  | .natrec _ _ _ k => neutralHead k
  | _ => false

/-- Recover a variable's declared type, weakening once for every traversed binder. -/
def lookupType : Context → Nat → Option Term
  | [], _ => none
  | A :: _, 0 => some (wk1 A)
  | _ :: Γ, x + 1 => (lookupType Γ x).map wk1

/-- Bounded head evaluation. No reduction occurs inside lambda bodies or successors. -/
def whnfFuel : Nat → Term → Option Term
  | 0, _ => none
  | fuel + 1, .app f a => do
      let f' ← whnfFuel fuel f
      match f' with
      | .lam body => whnfFuel fuel (subst0 body a)
      | _ => if neutralHead f' then some (.app f' a) else none
  | fuel + 1, .natrec A z s n => do
      let n' ← whnfFuel fuel n
      match n' with
      | .zero => whnfFuel fuel z
      | .succ k => whnfFuel fuel (.app (.app s k) (.natrec A z s k))
      | _ => if neutralHead n' then some (.natrec A z s n') else none
  | _ + 1, t => some t

mutual
  /-- Compare neutral heads and infer a representative type, before head normalization. -/
  def compareNeutralUp : Nat → Context → Term → Term → Option (Option Term)
    | 0, _, _, _ => none
    | _ + 1, Γ, .var x, .var y =>
        if x == y then some (lookupType Γ x) else some none
    | fuel + 1, Γ, .app k t, .app l v => do
        let inferred ← compareNeutralDown fuel Γ k l
        match inferred with
        | some (.pi F G) =>
            let equal ← compareTermUp fuel Γ t v F
            if equal then some (some (subst0 G t)) else some none
        | _ => some none
    | fuel + 1, Γ, .natrec F a₀ h k, .natrec G b₀ g l => do
        let motives ← compareTypeUp fuel (.nat :: Γ) F G
        if !motives then return none
        let bases ← compareTermUp fuel Γ a₀ b₀ (subst0 F .zero)
        if !bases then return none
        let steps ← compareTermUp fuel Γ h g (recStepType F)
        if !steps then return none
        let inferred ← compareNeutralDown fuel Γ k l
        match inferred with
        | some .nat => some (some (subst0 F k))
        | _ => some none
    | _ + 1, _, _, _ => some none

  /-- Compare neutrals and head-normalize the inferred type. -/
  def compareNeutralDown : Nat → Context → Term → Term → Option (Option Term)
    | 0, _, _, _ => none
    | fuel + 1, Γ, k, l => do
        let inferred ← compareNeutralUp fuel Γ k l
        match inferred with
        | none => some none
        | some A => do
            let B ← whnfFuel fuel A
            some (some B)

  /-- Compare arbitrary well-formed types by head evaluation followed by comparison. -/
  def compareTypeUp : Nat → Context → Term → Term → Option Bool
    | 0, _, _, _ => none
    | fuel + 1, Γ, A, B => do
        let A' ← whnfFuel fuel A
        let B' ← whnfFuel fuel B
        compareTypeDown fuel Γ A' B'

  /-- Compare weak-head type forms; well-formedness is a premise of correctness. -/
  def compareTypeDown : Nat → Context → Term → Term → Option Bool
    | 0, _, _, _ => none
    | _ + 1, _, .univ, .univ => some true
    | _ + 1, _, .nat, .nat => some true
    | fuel + 1, Γ, .pi F G, .pi H E => do
        let domains ← compareTypeUp fuel Γ F H
        if !domains then return false
        compareTypeUp fuel (F :: Γ) G E
    | fuel + 1, Γ, K, L =>
        if neutralHead K && neutralHead L then do
          let inferred ← compareNeutralDown fuel Γ K L
          match inferred with
          | some .univ => some true
          | _ => some false
        else some false

  /-- Head-evaluate the expected type and both terms before type-directed comparison. -/
  def compareTermUp : Nat → Context → Term → Term → Term → Option Bool
    | 0, _, _, _, _ => none
    | fuel + 1, Γ, t, u, A => do
        let B ← whnfFuel fuel A
        let t' ← whnfFuel fuel t
        let u' ← whnfFuel fuel u
        compareTermDown fuel Γ t' u' B

  /-- Type-directed comparison, including eta expansion at dependent function types. -/
  def compareTermDown : Nat → Context → Term → Term → Term → Option Bool
    | 0, _, _, _, _ => none
    | fuel + 1, Γ, t, u, .univ => compareTypeDown fuel Γ t u
    | _ + 1, _, .zero, .zero, .nat => some true
    | fuel + 1, Γ, .succ m, .succ n, .nat => compareTermUp fuel Γ m n .nat
    | fuel + 1, Γ, k, l, .nat =>
        if neutralHead k && neutralHead l then do
          let inferred ← compareNeutralDown fuel Γ k l
          match inferred with
          | some .nat => some true
          | _ => some false
        else some false
    | fuel + 1, Γ, f, g, .pi F G =>
        compareTermUp fuel (F :: Γ) (.app (wk1 f) (.var 0))
          (.app (wk1 g) (.var 0)) G
    | fuel + 1, Γ, k, l, N =>
        if neutralHead N && neutralHead k && neutralHead l then do
          let inferred ← compareNeutralDown fuel Γ k l
          some inferred.isSome
        else some false
end

mutual
  /-- Algorithmic equality of neutrals (`Γ ⊢ k ~ l ↑ A`). -/
  inductive ConvNeUp : Context → Term → Term → Term → Prop where
    | var {Γ x y A} : HasType Γ (.var x) A → x = y → ConvNeUp Γ (.var x) (.var y) A
    | app {Γ k l t v F G} :
        ConvNeDown Γ k l (.pi F G) →
        ConvTermUp Γ t v F →
        ConvNeUp Γ (.app k t) (.app l v) (subst0 G t)
    | natrec {Γ k l h g a₀ b₀ F G} :
        ConvTypeUp (.nat :: Γ) F G →
        ConvTermUp Γ a₀ b₀ (subst0 F .zero) →
        ConvTermUp Γ h g (recStepType F) →
        ConvNeDown Γ k l .nat →
        ConvNeUp Γ (.natrec F a₀ h k) (.natrec G b₀ g l) (subst0 F k)

  /-- Algorithmic equality of neutrals with type in WHNF (`Γ ⊢ k ~ l ↓ B`). -/
  inductive ConvNeDown : Context → Term → Term → Term → Prop where
    | mk {Γ k l A B} :
        TypeStar Γ A B →
        Whnf B →
        ConvNeUp Γ k l A →
        ConvNeDown Γ k l B

  /-- Algorithmic equality of types (`Γ ⊢ A [conv↑] B`). -/
  inductive ConvTypeUp : Context → Term → Term → Prop where
    | mk {Γ A B A' B'} :
        TypeStar Γ A A' →
        TypeStar Γ B B' →
        Whnf A' →
        Whnf B' →
        ConvTypeDown Γ A' B' →
        ConvTypeUp Γ A B

  /-- Algorithmic equality of types in WHNF (`Γ ⊢ A [conv↓] B`). -/
  inductive ConvTypeDown : Context → Term → Term → Prop where
    | univRefl {Γ} : CtxWf Γ → ConvTypeDown Γ .univ .univ
    | natRefl {Γ} : CtxWf Γ → ConvTypeDown Γ .nat .nat
    | ne {Γ K L} : ConvNeDown Γ K L .univ → ConvTypeDown Γ K L
    | piCong {Γ F G H E} :
        TypeWf Γ F →
        ConvTypeUp Γ F H →
        ConvTypeUp (F :: Γ) G E →
        ConvTypeDown Γ (.pi F G) (.pi H E)

  /-- Algorithmic equality of terms (`Γ ⊢ t [conv↑] u ∷ A`). -/
  inductive ConvTermUp : Context → Term → Term → Term → Prop where
    | mk {Γ t u A B t' u'} :
        TypeStar Γ A B →
        Star Γ t t' B →
        Star Γ u u' B →
        Whnf B →
        Whnf t' →
        Whnf u' →
        ConvTermDown Γ t' u' B →
        ConvTermUp Γ t u A

  /-- Algorithmic equality of terms and types in WHNF (`Γ ⊢ t [conv↓] u ∷ A`). -/
  inductive ConvTermDown : Context → Term → Term → Term → Prop where
    | natIns {Γ k l} : ConvNeDown Γ k l .nat → ConvTermDown Γ k l .nat
    | neIns {Γ k l M N} :
        HasType Γ k N →
        HasType Γ l N →
        Neutral N →
        ConvNeDown Γ k l M →
        ConvTermDown Γ k l N
    | univ {Γ A B} :
        HasType Γ A .univ →
        HasType Γ B .univ →
        ConvTypeDown Γ A B →
        ConvTermDown Γ A B .univ
    | zeroRefl {Γ} : CtxWf Γ → ConvTermDown Γ .zero .zero .nat
    | succCong {Γ m n} : ConvTermUp Γ m n .nat → ConvTermDown Γ (.succ m) (.succ n) .nat
    | etaEq {Γ f g F G} :
        TypeWf Γ F →
        HasType Γ f (.pi F G) →
        HasType Γ g (.pi F G) →
        Whnf f →
        Whnf g →
        ConvTermUp (F :: Γ) (.app (wk1 f) (.var 0)) (.app (wk1 g) (.var 0)) G →
        ConvTermDown Γ f g (.pi F G)
end

/-- Judgmental equality of contexts (`⊢ Γ ≡ Δ`). -/
inductive CtxEq : Context → Context → Prop where
  | nil : CtxEq [] []
  | cons {Γ Δ : Context} {A B : Term} :
      CtxEq Γ Δ → TypeEq Γ A B → CtxEq (A :: Γ) (B :: Δ)

/-- Algorithmic equality of neutrals with injected type conversion (`Γ ⊢ k ~ l ∷ A`,
from `Definition/Conversion/EqRelInstance.agda`). -/
inductive ConvNeEq (Γ : Context) (k l A : Term) : Prop where
  | mk {B : Term} : TypeEq Γ A B → ConvNeUp Γ k l B → ConvNeEq Γ k l A

end Abel2018


