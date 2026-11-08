-- Prove2me | Definitions.Def_LaarakkerOttenVanDenBerg2026_Model
-- name    : LaarakkerOttenVanDenBerg2026_Model
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T15:41:46.608539+00:00
-- url     : https://prove2.me/theorems/e4a2f6ff-3f8b-4b34-89b6-43e112f55437
-- title:
--   Assemblies, Modest Sets, PERs, CwF Structure, Countable Ordinals ω₁, Modest Reflection, and Concrete SizeCoreTheory
-- statement:
--   Formalizes Section 4 (pp. 12–16) and Appendix C (pp. 27–35) of Laarakker, Otten & van den Berg (FSCD 2026): partial combinatory algebras (`PCA`, `IsPCAFixpoint`, `NatPCA`), assemblies (`Asm`, `AsmHom`, codiscrete assembly $\nabla X$ `nabla`, Definition 12), modest sets (`IsModest`, `ModSet`, `ModHom`, Definition 13), partial equivalence relations (`PER`, `PERHom`, Definition 14), comparison functors $\iota : \mathsf{PER} \to \mathsf{Mod}$ (`iotaMod`) and $\mathcal{E} : \mathsf{Mod} \to \mathsf{PER}$ (`modToPER`, Lemma 15), the Category with Families (CwF) of assemblies (`SemCtx`, `SemTy`, `SemTm`, `tySubst`, `tmSubst`, `ctxExt`, `semU`, `semEl`, `botPER`, `topPER`, `boolPER`, `semIdPER`, `semPi`, `IsModestTy`, `semSmallPi`, `semSigma`, `semSmallSigma`, Definitions 24–35), the semantic size type $\mathsf{Size}_\gamma = \nabla\omega_1$ over countable ordinals (`Omega1`, `omega1Zero`, `omega1Succ`, `semSize`, `semLePER`), the left adjoint modest quotient $\mathsf{M} : \mathsf{Asm} \to \mathsf{Mod}$ (`modestQuotient`, Lemma 17/37), $U$-truncation $\|A\|_\gamma$ (`semTrunc`), the existential quantifier interpretation $\exists i.\,A(i) := \|\Sigma(\mathsf{Size}, \mathrm{El}\,A)\|$ (`semEx`, Definition 38), and the concrete instantiation `perSizeCoreTheory : SizeCoreTheory.{1, 0}` over `PER` and `Omega1`.
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 4 (pp. 12–16) & Appendix C (pp. 27–35)

/-
Formalization of Section 4 and Appendix C of:
  Bastiaan Laarakker, Daniël Otten, and Benno van den Berg (FSCD 2026),
  "Constructing (Co)inductive Types via Large Sizes", arXiv:2602.18921.

This file defines:
  1. Partial combinatory algebras (`PCA`), fixpoint combinators in a PCA
     (`IsPCAFixpoint`, Proposition 16 / Proposition 36, pp. 15, 33), and standard
     computable pairing on `ℕ`.
  2. Assemblies (`Asm`, `AsmHom`, Definition 12, p. 13), the codiscrete assembly functor
     `∇ X := (X, ℕ × X)` (`nabla`, p. 13), modest sets (`IsModest`, `ModSet`, `ModHom`,
     Definition 13, p. 13), partial equivalence relations (`PER`, `PERHom`, Definition 14,
     pp. 13–14), and the comparison functors `iotaMod : PER → ModSet` and
     `modToPER : ModSet → PER` (Lemma 15, p. 14).
  3. The Category with Families (CwF) of assemblies (`SemCtx`, `SemTy`, `SemTm`,
     `tySubst`, `tmSubst`, context extension `ctxExt`, Definition 24, p. 28), the semantic
     universe `U_γ = ∇ PER` and decoder `El_{(γ, R)} = ι(R)` (Definition 25, p. 28),
     base PERs `0`, `1`, `Bool^U` (Definitions 26–28, pp. 28–29), semantic identity types
     (Definition 29, p. 29), large and small dependent products `Π(A, B)` and `π(A, B)`
     (Definitions 30–33, pp. 29–30), and large and small dependent sums `Σ(A, B)` and
     `σ(A, B)` (Definitions 34–35, p. 31).
  4. The semantic size type `Size_γ = ∇ ω₁` over the first uncountable ordinal `ω₁`
     (Section 4.3, p. 15 & Appendix C.7, p. 32), the modest reflection functor
     `M : Asm → Mod` (Lemma 17 / Lemma 37, pp. 16, 33–34), `U`-truncation `‖A‖_γ = M(A_γ)`,
     and the existential quantifier interpretation `∃ i. A(i) := ‖Σ(Size, El A)‖`
     (Definition 38, p. 34).
  5. The concrete interpretation `perSizeCoreTheory : SizeCoreTheory.{1, 0}` of the core
     sized type theory in `PER` over `Omega1` (`U = ULift.{1} PER`, `El R = R.down.Quotient`,
     `Size = Omega1`, `zero = omega1Zero`, `succ = omega1Succ`, `botU = ULift.up botPER`)
     via modest specifications (`ModestSpec`, Lemma 15 & Appendix C, pp. 14, 28–35).
-/
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Relation
import Mathlib.SetTheory.Cardinal.Ordinal
import Definitions.Def_LaarakkerOttenVanDenBerg2026_Encoding

namespace LaarakkerOttenVanDenBerg2026

universe u

/-! ## 1. Partial Combinatory Algebras (Section 4.1, p. 12 & Appendix C, pp. 27, 33) -/

/-- A Partial Combinatory Algebra (PCA) `(A, ·, k, s)` consists of a carrier `A`,
a partial binary application `app : A → A → Option A` (written `m · n`), and combinators
`k, s : A` satisfying the standard combinatory completeness laws (`k a b = a`,
`s a b ↓`, and `s a b c ≃ (a c) (b c)`). -/
structure PCA (A : Type*) where
  app : A → A → Option A
  k : A
  s : A
  idComb : A
  id_app : ∀ (x : A), app idComb x = some x
  k_app₁ : ∀ (a : A), (app k a).isSome
  k_app₂ : ∀ (a b : A), (app k a >>= fun ka => app ka b) = some a
  s_app₁ : ∀ (a : A), (app s a).isSome
  s_app₂ : ∀ (a b : A), (app s a >>= fun sa => app sa b).isSome
  s_app₃ : ∀ (a b c : A),
    (app s a >>= fun sa => app sa b >>= fun sab => app sab c) =
    (app a c >>= fun ac => app b c >>= fun bc => app ac bc)

/-- Proposition 16 (p. 15) / Proposition 36 (p. 33): A fixpoint combinator `fixComb` in a
PCA `(A, ·)` is an element such that for every `f, a ∈ A`, `fixComb · f ↓` and
`(fixComb · f) · a ≃ f · (fixComb · f) · a`. -/
def IsPCAFixpoint {A : Type*} (P : PCA A) (fixComb : A) : Prop :=
  ∀ (f : A), ∃ (ff : A), P.app fixComb f = some ff ∧
    ∀ (a : A), P.app ff a = (P.app f ff >>= fun fff => P.app fff a)

/-- A PCA over `ℕ` equipped with tracked computable pairing and projections
(representing Kleene's first algebra `K₁` with standard pairing `⟨-, -⟩ : ℕ² → ℕ` and
projections `pr₁, pr₂ : ℕ → ℕ`, Section 4.1, p. 12 & Appendix C, p. 27). -/
structure NatPCA extends PCA ℕ where
  compComb : ℕ → ℕ → ℕ
  comp_app : ∀ (d e n : ℕ),
    app (compComb d e) n = (app e n >>= fun en => app d en)
  fstComb : ℕ
  sndComb : ℕ
  fst_app : ∀ (n : ℕ), app fstComb n = some (Nat.unpair n).1
  snd_app : ∀ (n : ℕ), app sndComb n = some (Nat.unpair n).2

/-! ## 2. Assemblies, Modest Sets, and PERs (Definitions 12–14 & Lemma 15, pp. 13–14) -/

/-- Definition 12 (p. 13): An assembly `(X, ⊩_X)` over a PCA on `ℕ` consists of a carrier
type `Carrier` and a realisability relation `realises : ℕ → Carrier → Prop` such that
every `x : Carrier` has at least one realiser `n : ℕ`. -/
structure Asm (P : PCA ℕ) : Type (u + 1) where
  Carrier : Type u
  realises : ℕ → Carrier → Prop
  realised : ∀ (x : Carrier), ∃ (n : ℕ), realises n x

/-- A function `f : X → Y` between assemblies is tracked by `e ∈ ℕ` if whenever `n ⊩_X x`,
`e · n ↓` and `e · n ⊩_Y f(x)` (Definition 12, p. 13). -/
def IsTracked (P : PCA ℕ) {X Y : Asm.{u} P} (f : X.Carrier → Y.Carrier) (e : ℕ) : Prop :=
  ∀ (n : ℕ) (x : X.Carrier), X.realises n x →
    ∃ (m : ℕ), P.app e n = some m ∧ Y.realises m (f x)

/-- Definition 12 (p. 13): A morphism of assemblies `f : (X, ⊩_X) → (Y, ⊩_Y)` is a function
`X → Y` that is tracked by some realiser `e ∈ ℕ` (not part of the data). -/
@[ext]
structure AsmHom (P : PCA ℕ) (X Y : Asm.{u} P) : Type u where
  toFun : X.Carrier → Y.Carrier
  tracked : ∃ (e : ℕ), IsTracked P toFun e

/-- Identity morphism on an assembly `X`, tracked by `P.idComb`. -/
def asmHomId (P : PCA ℕ) (X : Asm.{u} P) : AsmHom P X X where
  toFun := fun x => x
  tracked := ⟨P.idComb, fun n _ hnx => ⟨n, P.id_app n, hnx⟩⟩

/-- Composition of assembly morphisms over a `NatPCA`. -/
def asmHomComp (P : NatPCA) {X Y Z : Asm.{u} P.toPCA}
    (g : AsmHom P.toPCA Y Z) (f : AsmHom P.toPCA X Y) : AsmHom P.toPCA X Z where
  toFun := fun x => g.toFun (f.toFun x)
  tracked := by
    rcases g.tracked with ⟨eg, heg⟩
    rcases f.tracked with ⟨ef, hef⟩
    refine ⟨P.compComb eg ef, fun n x hnx => ?_⟩
    rcases hef n x hnx with ⟨m, hm, hmy⟩
    rcases heg m (f.toFun x) hmy with ⟨k, hk, hkz⟩
    refine ⟨k, ?_, hkz⟩
    rw [P.comp_app, hm]
    exact hk

/-- The codiscrete assembly `∇ T := (T, ℕ × T)` assigning the full realisability relation
to a type `T` (Section 4.1, p. 13). -/
def nabla (P : PCA ℕ) (T : Type u) : Asm.{u} P where
  Carrier := T
  realises := fun _ _ => True
  realised := fun _ => ⟨0, trivial⟩

/-- Definition 13 (p. 13): An assembly `(X, ⊩_X)` is a modest set if every realiser `n ∈ ℕ`
realises at most one element of `X`: `n ⊩_X x₁ ∧ n ⊩_X x₂ → x₁ = x₂`. -/
def IsModest (P : PCA ℕ) (X : Asm.{u} P) : Prop :=
  ∀ (n : ℕ) (x₁ x₂ : X.Carrier), X.realises n x₁ → X.realises n x₂ → x₁ = x₂

/-- Definition 13 (p. 13): The objects of the full subcategory `Mod` of modest sets. -/
structure ModSet (P : PCA ℕ) : Type (u + 1) where
  toAsm : Asm.{u} P
  modest : IsModest P toAsm

/-- Morphisms in `Mod` are assembly morphisms between the underlying assemblies (p. 13). -/
abbrev ModHom (P : PCA ℕ) (X Y : ModSet.{u} P) : Type u :=
  AsmHom P X.toAsm Y.toAsm

/-- Inclusion functor `I : Mod → Asm` on objects (Lemma 17, p. 16). -/
def modInclusionObj (P : PCA ℕ) (X : ModSet.{u} P) : Asm.{u} P := X.toAsm

/-- Definition 14 (pp. 13–14): A Partial Equivalence Relation (PER) on `ℕ` is a symmetric
and transitive binary relation `R ⊆ ℕ × ℕ`. -/
@[ext]
structure PER : Type where
  rel : ℕ → ℕ → Prop
  symm : ∀ {m n : ℕ}, rel m n → rel n m
  trans : ∀ {k m n : ℕ}, rel k m → rel m n → rel k n

namespace PER

/-- Domain `dom(R) := {n ∈ ℕ | n R n}` of a PER `R` (Definition 14, p. 14). -/
def dom (R : PER) : Set ℕ := {n : ℕ | R.rel n n}

/-- Equivalence class `[n]_R := {m ∈ ℕ | n R m}` of `n ∈ ℕ` (Definition 14, p. 14). -/
def equivClass (R : PER) (n : ℕ) : Set ℕ := {m : ℕ | R.rel n m}

/-- Quotient `ℕ / R := {[n]_R | n ∈ dom(R)}` of a PER `R` (Definition 14, p. 14). -/
def Quotient (R : PER) : Type :=
  {c : Set ℕ // ∃ n ∈ R.dom, c = R.equivClass n}

theorem mem_dom_of_rel (R : PER) {m n : ℕ} (h : R.rel m n) : m ∈ R.dom :=
  R.trans h (R.symm h)

theorem equivClass_eq_iff (R : PER) {m n : ℕ} (hm : m ∈ R.dom) :
    R.equivClass m = R.equivClass n ↔ R.rel m n := by
  constructor
  · intro h
    have hmm : m ∈ R.equivClass m := hm
    rw [h] at hmm
    exact R.symm hmm
  · intro hmn
    ext k
    exact ⟨fun hmk => R.trans (R.symm hmn) hmk, fun hnk => R.trans hmn hnk⟩

end PER

/-- A map `f : ℕ/R → ℕ/S` between PER quotients is tracked by `e ∈ ℕ` if for every
`c ∈ ℕ/R` and every `n ∈ c`, `e · n ↓` and `e · n ∈ f(c)` (Definition 14, p. 14). -/
def IsPERTracked (P : PCA ℕ) {R S : PER}
    (f : R.Quotient → S.Quotient) (e : ℕ) : Prop :=
  ∀ (c : R.Quotient) (n : ℕ), n ∈ c.1 →
    ∃ (m : ℕ), P.app e n = some m ∧ m ∈ (f c).1

/-- Definition 14 (p. 14): A morphism in the category `PER` from `R` to `S`. -/
@[ext]
structure PERHom (P : PCA ℕ) (R S : PER) : Type where
  toFun : R.Quotient → S.Quotient
  tracked : ∃ (e : ℕ), IsPERTracked P toFun e

/-- Lemma 15 (p. 14): The inclusion functor `ι : PER → Mod` on objects, mapping a PER `R`
to the modest set `ι(R) := (ℕ / R, ∈)`. -/
def iotaMod (P : PCA ℕ) (R : PER) : ModSet.{0} P where
  toAsm := {
    Carrier := R.Quotient
    realises := fun n c => n ∈ c.1
    realised := fun ⟨c, ⟨n, hn, hc⟩⟩ => ⟨n, by dsimp only; rw [hc]; exact hn⟩
  }
  modest := by
    intro n ⟨c₁, ⟨n₁, _, hc₁⟩⟩ ⟨c₂, ⟨n₂, _, hc₂⟩⟩ h₁ h₂
    apply Subtype.ext
    ext k
    subst hc₁ hc₂
    exact ⟨fun h₁k => R.trans (R.trans h₂ (R.symm h₁)) h₁k,
           fun h₂k => R.trans (R.trans h₁ (R.symm h₂)) h₂k⟩

/-- Lemma 15 (p. 14): The functor `E : Mod → PER` on objects, mapping a modest set
`(X, ⊩_X)` to the PER `n₁ ∼_X n₂ ↔ ∃ x ∈ X, (n₁ ⊩_X x) ∧ (n₂ ⊩_X x)`. -/
def modToPER (P : PCA ℕ) (X : ModSet.{u} P) : PER where
  rel := fun n₁ n₂ => ∃ (x : X.toAsm.Carrier),
    X.toAsm.realises n₁ x ∧ X.toAsm.realises n₂ x
  symm := fun ⟨x, h₁, h₂⟩ => ⟨x, h₂, h₁⟩
  trans := fun ⟨x₁, hk, hm₁⟩ ⟨x₂, hm₂, hn⟩ => by
    have hx : x₁ = x₂ := X.modest _ x₁ x₂ hm₁ hm₂
    subst hx
    exact ⟨x₁, hk, hn⟩

/-! ## 3. CwF Structure on Assemblies (Section 4.1 & Appendix C, pp. 27–31) -/

/-- Semantic contexts in the CwF of assemblies are assemblies `Γ ∈ Asm` (Appendix C.1, p. 27). -/
abbrev SemCtx (P : PCA ℕ) : Type (u + 1) := Asm.{u} P

/-- A semantic type `A ∈ Ty(Γ)` is a `Γ`-indexed family of assemblies `(A_γ)_{γ ∈ Γ}`
(Section 4.1, p. 14 & Appendix C.1, p. 27). -/
structure SemTy (P : PCA ℕ) (Γ : SemCtx.{u} P) : Type (u + 1) where
  fiber : Γ.Carrier → Asm.{u} P

/-- A dependent function `a : (γ : Γ) → A_γ` is tracked by `e ∈ ℕ` if whenever `n ⊩_Γ γ`,
`e · n ↓` and `e · n ⊩_{A_γ} a(γ)` (Section 4.1, p. 14 & Appendix C.1, p. 28). -/
def IsDepTracked (P : PCA ℕ) {Γ : SemCtx.{u} P} {A : SemTy.{u} P Γ}
    (a : (γ : Γ.Carrier) → (A.fiber γ).Carrier) (e : ℕ) : Prop :=
  ∀ (n : ℕ) (γ : Γ.Carrier), Γ.realises n γ →
    ∃ (m : ℕ), P.app e n = some m ∧ (A.fiber γ).realises m (a γ)

/-- A semantic term `a ∈ Tm(Γ, A)` is a tracked dependent morphism `(γ : Γ) → A_γ`
(Section 4.1, p. 14 & Appendix C.1, p. 28). -/
@[ext]
structure SemTm (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ) : Type u where
  toFun : (γ : Γ.Carrier) → (A.fiber γ).Carrier
  tracked : ∃ (e : ℕ), IsDepTracked P toFun e

/-- Semantic type substitution `A[f] ∈ Ty(Δ)` along `f : Δ → Γ`, defined by `A[f]_δ = A_{f(δ)}`
(Appendix C.1, p. 28). -/
def tySubst (P : PCA ℕ) {Δ Γ : SemCtx.{u} P} (f : AsmHom P Δ Γ) (A : SemTy.{u} P Γ) :
    SemTy.{u} P Δ where
  fiber := fun δ => A.fiber (f.toFun δ)

/-- Semantic term substitution `a[f] ∈ Tm(Δ, A[f])` along `f : Δ → Γ` over a `NatPCA`,
defined by `(a[f])_δ = a_{f(δ)}` (Appendix C.1, p. 28). -/
def tmSubst (P : NatPCA) {Δ Γ : SemCtx.{u} P.toPCA} (f : AsmHom P.toPCA Δ Γ)
    {A : SemTy.{u} P.toPCA Γ} (a : SemTm P.toPCA Γ A) :
    SemTm P.toPCA Δ (tySubst P.toPCA f A) where
  toFun := fun δ => a.toFun (f.toFun δ)
  tracked := by
    rcases a.tracked with ⟨ea, hea⟩
    rcases f.tracked with ⟨ef, hef⟩
    refine ⟨P.compComb ea ef, fun n δ hnδ => ?_⟩
    rcases hef n δ hnδ with ⟨m, hm, hmf⟩
    rcases hea m (f.toFun δ) hmf with ⟨k, hk, hka⟩
    refine ⟨k, ?_, hka⟩
    rw [P.comp_app, hm]
    exact hk

/-- Definition 24 (Context extension, p. 28): Given `Γ ∈ Asm` and `A ∈ Ty(Γ)`, the extended
context `Γ.A` has carrier `(γ : Γ) × A_γ` and realisability
`k ⊩_{Γ.A} (γ, a) ↔ (unpair k).1 ⊩_Γ γ ∧ (unpair k).2 ⊩_{A_γ} a`. -/
def ctxExt (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ) : SemCtx.{u} P where
  Carrier := (γ : Γ.Carrier) × (A.fiber γ).Carrier
  realises := fun k p =>
    Γ.realises (Nat.unpair k).1 p.1 ∧ (A.fiber p.1).realises (Nat.unpair k).2 p.2
  realised := fun ⟨γ, a⟩ => by
    rcases Γ.realised γ with ⟨n₁, hn₁⟩
    rcases (A.fiber γ).realised a with ⟨n₂, hn₂⟩
    exact ⟨Nat.pair n₁ n₂, by simp [Nat.unpair_pair, hn₁, hn₂]⟩

/-- Definition 25 (Universe type, p. 28): `U_γ := ∇ PER`. -/
def semU (P : PCA ℕ) (Γ : SemCtx.{0} P) : SemTy.{0} P Γ where
  fiber := fun _ => nabla P PER

/-- Definition 25 (Semantic decoder, p. 28): Given a small semantic type `A : Γ → PER`,
its decoded assembly family `El A ∈ Ty(Γ)` is `(El A)_γ := ι(A_γ)`. -/
def semEl (P : PCA ℕ) (Γ : SemCtx.{0} P) (A : Γ.Carrier → PER) : SemTy.{0} P Γ where
  fiber := fun γ => (iotaMod P (A γ)).toAsm

/-- Definition 26 (Empty PER `0`, p. 28): the initial empty PER on `ℕ`. -/
def botPER : PER where
  rel := fun _ _ => False
  symm := False.elim
  trans := fun h _ => False.elim h

/-- Definition 27 (Unit PER `1`, p. 29): the terminal singleton PER relating all `m, n ∈ ℕ`. -/
def topPER : PER where
  rel := fun _ _ => True
  symm := fun _ => trivial
  trans := fun _ _ => trivial

/-- Definition 28 (Boolean PER `Bool^U`, p. 29): relates `⟨b, m⟩` and `⟨b, n⟩` for `b ∈ {0, 1}`. -/
def boolPER : PER where
  rel := fun k₁ k₂ =>
    ((Nat.unpair k₁).1 = 0 ∧ (Nat.unpair k₂).1 = 0) ∨
    ((Nat.unpair k₁).1 = 1 ∧ (Nat.unpair k₂).1 = 1)
  symm := by
    rintro k₁ k₂ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
    · exact Or.inl ⟨h₂, h₁⟩
    · exact Or.inr ⟨h₂, h₁⟩
  trans := by
    rintro k₁ k₂ k₃ (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩) (⟨h₃, h₄⟩ | ⟨h₃, h₄⟩)
    · exact Or.inl ⟨h₁, h₄⟩
    · omega
    · omega
    · exact Or.inr ⟨h₁, h₄⟩

/-- Definition 29 (Semantic identity PER, p. 29): `Id(A, a, a')_γ` is `topPER` if `a = a'`
and `botPER` if `a ≠ a'`. -/
def semIdPER {α : Type*} (a a' : α) : PER where
  rel := fun _ _ => a = a'
  symm := fun h => h
  trans := fun h _ => h

/-- Definition 30 (Large dependent product `Π(A, B)`, p. 29): for `A ∈ Ty(Γ)` and
`B ∈ Ty(Γ.A)`, `Π(A, B)_γ` consists of all tracked dependent functions `(a : A_γ) → B_{(γ, a)}`. -/
def semPi (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ)
    (B : SemTy.{u} P (ctxExt P Γ A)) : SemTy.{u} P Γ where
  fiber := fun γ => {
    Carrier := {f : (a : (A.fiber γ).Carrier) → (B.fiber ⟨γ, a⟩).Carrier //
      ∃ (e : ℕ), ∀ (n : ℕ) (a : (A.fiber γ).Carrier), (A.fiber γ).realises n a →
        ∃ (m : ℕ), P.app e n = some m ∧ (B.fiber ⟨γ, a⟩).realises m (f a)}
    realises := fun e f =>
      ∀ (n : ℕ) (a : (A.fiber γ).Carrier), (A.fiber γ).realises n a →
        ∃ (m : ℕ), P.app e n = some m ∧ (B.fiber ⟨γ, a⟩).realises m (f.1 a)
    realised := fun ⟨_, e, he⟩ => ⟨e, he⟩
  }

/-- A semantic type `A ∈ Ty(Γ)` is modest if `A_γ` is a modest set for every `γ ∈ Γ`
(Appendix C.5, p. 30). -/
def IsModestTy (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ) : Prop :=
  ∀ (γ : Γ.Carrier), IsModest P (A.fiber γ)

/-- Definition 32 (Small impredicative dependent product `π(A, B)`, p. 30): for any (possibly
large) `A ∈ Ty(Γ)` and small `B : (Γ.A) → PER`, `π(A, B)_γ` is the PER relating `d` and `e`
iff for all `a ∈ A_γ` and `m, n ⊩_{A_γ} a`, `d · m ∼_{B(γ, a)} e · n`. -/
def semSmallPi (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ)
    (B : (ctxExt P Γ A).Carrier → PER) (γ : Γ.Carrier) : PER where
  rel := fun d e =>
    ∀ (a : (A.fiber γ).Carrier) (m n : ℕ),
      (A.fiber γ).realises m a → (A.fiber γ).realises n a →
      ∃ (dm en : ℕ), P.app d m = some dm ∧ P.app e n = some en ∧
        (B ⟨γ, a⟩).rel dm en
  symm := by
    intro d e hde a m n hma hna
    rcases hde a n m hna hma with ⟨en, dm, hen, hdm, hrel⟩
    exact ⟨dm, en, hdm, hen, (B ⟨γ, a⟩).symm hrel⟩
  trans := by
    intro d₁ d₂ d₃ h₁₂ h₂₃ a m n hma hna
    rcases (A.fiber γ).realised a with ⟨k, hka⟩
    rcases h₁₂ a m k hma hka with ⟨dm₁, dk₂, hdm₁, hdk₂, hrel₁⟩
    rcases h₂₃ a k n hka hna with ⟨dk₂', dn₃, hdk₂', hdn₃, hrel₂⟩
    rw [hdk₂] at hdk₂'
    cases hdk₂'
    exact ⟨dm₁, dn₃, hdm₁, hdn₃, (B ⟨γ, a⟩).trans hrel₁ hrel₂⟩

/-- Definition 34 (Large dependent sum `Σ(A, B)`, p. 31): for `A ∈ Ty(Γ)` and `B ∈ Ty(Γ.A)`,
`Σ(A, B)_γ` has carrier `(a : A_γ) × B_{(γ, a)}` and realisability via pairing. -/
def semSigma (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ)
    (B : SemTy.{u} P (ctxExt P Γ A)) : SemTy.{u} P Γ where
  fiber := fun γ => {
    Carrier := (a : (A.fiber γ).Carrier) × (B.fiber ⟨γ, a⟩).Carrier
    realises := fun k p =>
      (A.fiber γ).realises (Nat.unpair k).1 p.1 ∧
      (B.fiber ⟨γ, p.1⟩).realises (Nat.unpair k).2 p.2
    realised := fun ⟨a, b⟩ => by
      rcases (A.fiber γ).realised a with ⟨n₁, hn₁⟩
      rcases (B.fiber ⟨γ, a⟩).realised b with ⟨n₂, hn₂⟩
      exact ⟨Nat.pair n₁ n₂, by simp [Nat.unpair_pair, hn₁, hn₂]⟩
  }

/-- Definition 35 (Small dependent sum `σ(A, B)`, p. 31): given small `A : Γ → PER` and
`B : (Γ.El A) → PER`, `σ(A, B)_γ = E(Σ(El A, El B)_γ)`. -/
def semSmallSigma (P : PCA ℕ) (Γ : SemCtx.{0} P) (A : Γ.Carrier → PER)
    (B : (ctxExt P Γ (semEl P Γ A)).Carrier → PER) (γ : Γ.Carrier) : PER where
  rel := fun k₁ k₂ =>
    ∃ (p : (a : (A γ).Quotient) × (B ⟨γ, a⟩).Quotient),
      (Nat.unpair k₁).1 ∈ p.1.1 ∧ (Nat.unpair k₁).2 ∈ p.2.1 ∧
      (Nat.unpair k₂).1 ∈ p.1.1 ∧ (Nat.unpair k₂).2 ∈ p.2.1
  symm := fun ⟨p, h₁, h₂, h₃, h₄⟩ => ⟨p, h₃, h₄, h₁, h₂⟩
  trans := by
    rintro k₁ k₂ k₃ ⟨⟨a₁, b₁⟩, h₁a, h₁b, h₂a, h₂b⟩ ⟨⟨a₂, b₂⟩, h₂a', h₂b', h₃a, h₃b⟩
    have ha : a₁ = a₂ := (iotaMod P (A γ)).modest (Nat.unpair k₂).1 a₁ a₂ h₂a h₂a'
    subst ha
    have hb : b₁ = b₂ := (iotaMod P (B ⟨γ, a₁⟩)).modest (Nat.unpair k₂).2 b₁ b₂ h₂b h₂b'
    subst hb
    exact ⟨⟨a₁, b₁⟩, h₁a, h₁b, h₃a, h₃b⟩

/-! ## 4. Sizes `∇ ω₁`, Modest Reflection `M`, and `∃` (Section 4.3–4.5 & Appendix C.7–C.9) -/

/-- Lemma 15 (p. 14): Universe-lifted inclusion `ι : PER → ModSet.{u}` mapping a PER `R`
to `ULift.{u} (ℕ / R)` with realisability `n ⊩ ⟨c⟩ ↔ n ∈ c`. -/
def iotaModLift (P : PCA ℕ) (R : PER) : ModSet.{u} P where
  toAsm := {
    Carrier := ULift.{u} R.Quotient
    realises := fun n c => n ∈ c.down.1
    realised := fun ⟨c⟩ => (iotaMod P R).toAsm.realised c
  }
  modest := by
    intro n ⟨c₁⟩ ⟨c₂⟩ h₁ h₂
    congr 1
    exact (iotaMod P R).modest n c₁ c₂ h₁ h₂

/-- Definition 25 (Semantic decoder at universe `u`, p. 28): Given a small semantic type
`A : Γ → PER`, its decoded assembly family `El A ∈ Ty(Γ)` is `(El A)_γ := ι(A_γ)`. -/
def semElLift (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : Γ.Carrier → PER) : SemTy.{u} P Γ where
  fiber := fun γ => (iotaModLift.{u} P (A γ)).toAsm

/-- The first uncountable ordinal `ω₁` represented as the type of all countable ordinals
`{α : Ordinal.{0} // α.card ≤ Cardinal.aleph0}`
(Section 4.3, p. 15 & Appendix C.7, p. 32). -/
abbrev Omega1 : Type 1 :=
  {α : Ordinal.{0} // α.card ≤ Cardinal.aleph0}

/-- Zero size `0 ∈ ω₁` (Appendix C.7, p. 32). -/
def omega1Zero : Omega1 :=
  ⟨0, by simp⟩

/-- Successor size `↑α = α + 1 ∈ ω₁` (Appendix C.7, p. 32). -/
def omega1Succ (α : Omega1) : Omega1 :=
  ⟨α.1 + 1, by
    rw [Ordinal.card_add_one]
    exact Cardinal.add_le_of_le (le_refl _) α.2 Cardinal.one_le_aleph0⟩

instance : LE Omega1 where
  le α β := α.1 ≤ β.1

instance : LT Omega1 where
  lt α β := α.1 < β.1

/-- Semantic type of sizes `Size_γ := ∇ ω₁` (Section 4.3, p. 15 & Appendix C.7, p. 32). -/
def semSize (P : PCA ℕ) (Γ : SemCtx.{1} P) : SemTy.{1} P Γ where
  fiber := fun _ => nabla P Omega1

/-- Semantic size ordering `s₁ ≤^U s₂` interpreted as `topPER` if `s₁ ≤ s₂` and `botPER`
otherwise (Appendix C.7, p. 32). -/
def semLePER (s₁ s₂ : Omega1) : PER where
  rel := fun _ _ => s₁ ≤ s₂
  symm := fun h => h
  trans := fun h _ => h

/-- Generating relation for the modest quotient `M(X)` of an assembly `X ∈ Asm`:
`a₁ ∼_0 a₂ ↔ ∃ n ∈ ℕ, n ⊩_X a₁ ∧ n ⊩_X a₂` (Lemma 17, p. 16 & Lemma 37, p. 33). -/
def sharedRealiserRel (P : PCA ℕ) (X : Asm.{u} P) (a₁ a₂ : X.Carrier) : Prop :=
  ∃ (n : ℕ), X.realises n a₁ ∧ X.realises n a₂

/-- The equivalence relation `∼_M` on an assembly `X` generated by `sharedRealiserRel`
(Lemma 17, p. 16 & Lemma 37, p. 33). -/
def modestEqvRel (P : PCA ℕ) (X : Asm.{u} P) : X.Carrier → X.Carrier → Prop :=
  Relation.EqvGen (sharedRealiserRel P X)

/-- Lemma 17 (p. 16) / Lemma 37 (p. 33): The left adjoint `M : Asm → Mod` to the inclusion
`I : Mod → Asm`, mapping an assembly `X` to the modest set `(X / ∼_M, ⊩_{M(X)})` where
`n ⊩_{M(X)} [a] ↔ ∃ a' ∈ [a], n ⊩_X a'`. -/
def modestQuotient (P : PCA ℕ) (X : Asm.{u} P) : ModSet.{u} P where
  toAsm := {
    Carrier := Quot (sharedRealiserRel P X)
    realises := fun n q => ∃ (a : X.Carrier), Quot.mk (sharedRealiserRel P X) a = q ∧ X.realises n a
    realised := by
      intro q
      refine Quot.inductionOn q (fun a => ?_)
      rcases X.realised a with ⟨n, hn⟩
      exact ⟨n, a, rfl, hn⟩
  }
  modest := by
    rintro n q₁ q₂ ⟨a₁, rfl, h₁⟩ ⟨a₂, rfl, h₂⟩
    exact Quot.sound ⟨n, h₁, h₂⟩

/-- Unit morphism `η_X : X → I(M(X))` sending `a ↦ [a]_{∼_M}`, tracked by `P.idComb`
(Lemma 37, p. 34). -/
def modestQuotientUnit (P : PCA ℕ) (X : Asm.{u} P) :
    AsmHom P X (modestQuotient P X).toAsm where
  toFun := Quot.mk (sharedRealiserRel P X)
  tracked := ⟨P.idComb, fun n a hna => ⟨n, P.id_app n, a, rfl, hna⟩⟩

/-- The `U`-truncation `‖A‖_γ := E(M(A_γ))` of a semantic type `A ∈ Ty(Γ)` as a `Γ`-indexed
family of PERs (Section 4.5, p. 16 & Appendix C.9, p. 34). -/
def semTrunc (P : PCA ℕ) (Γ : SemCtx.{u} P) (A : SemTy.{u} P Γ) (γ : Γ.Carrier) : PER :=
  modToPER P (modestQuotient P (A.fiber γ))

/-- Definition 38 (Existential Type in the Model, p. 34): Given a small size-indexed semantic
type `A : (Γ.Size) → PER`, the existential quantifier `∃ i. A(i)` is interpreted as the
`U`-truncation `‖Σ(Size, El A)‖`. -/
def semEx (P : PCA ℕ) (Γ : SemCtx.{1} P)
    (A : (ctxExt P Γ (semSize P Γ)).Carrier → PER) (γ : Γ.Carrier) : PER :=
  semTrunc P Γ (semSigma P Γ (semSize P Γ) (semElLift P (ctxExt P Γ (semSize P Γ)) A)) γ

/-- Universal size quantifier in the model `∀ i. A(i)` interpreted as the small impredicative
dependent product `π(Size, A)` (Section 4.5, p. 15 & Appendix C.5, p. 30). -/
def semAll (P : PCA ℕ) (Γ : SemCtx.{1} P)
    (A : (ctxExt P Γ (semSize P Γ)).Carrier → PER) (γ : Γ.Carrier) : PER :=
  semSmallPi P Γ (semSize P Γ) A γ

/-! ## 5. Concrete Interpretation of `SizeCoreTheory` in `PER` over `ω₁` (Section 4 & Appendix C) -/

/-- A modest specification on a type `X : Type u` consists of a realisability relation
`realises : ℕ → X → Prop` such that every `x : X` has at least one realiser and every
`n : ℕ` realises at most one element of `X` (Definitions 12–13 & Lemma 15, pp. 13–14). -/
structure ModestSpec (X : Type u) where
  realises : ℕ → X → Prop
  realised : ∀ (x : X), ∃ (n : ℕ), realises n x
  modest : ∀ {n : ℕ} {x₁ x₂ : X}, realises n x₁ → realises n x₂ → x₁ = x₂

namespace ModestSpec

/-- The PER induced by a modest specification `S : ModestSpec X`, relating `m` and `n`
iff they realise a common element `x : X` (Lemma 15, p. 14). -/
def toPER {X : Type u} (S : ModestSpec X) : PER where
  rel m n := ∃ (x : X), S.realises m x ∧ S.realises n x
  symm := fun ⟨x, hm, hn⟩ => ⟨x, hn, hm⟩
  trans := fun ⟨x₁, hk, hm₁⟩ ⟨x₂, hm₂, hn⟩ => by
    cases S.modest hm₁ hm₂
    exact ⟨x₁, hk, hn⟩

theorem decode_exists {X : Type u} (S : ModestSpec X) (q : S.toPER.Quotient) :
    ∃ (x : X), ∃ n ∈ q.1, S.realises n x := by
  rcases q with ⟨_, n, ⟨x, hnx, _⟩, rfl⟩
  exact ⟨x, n, ⟨x, hnx, hnx⟩, hnx⟩

/-- Decode a PER equivalence class `q` to the unique `x : X` realised by its elements. -/
noncomputable def decode {X : Type u} (S : ModestSpec X) (q : S.toPER.Quotient) : X :=
  Classical.choose (S.decode_exists q)

theorem decode_spec {X : Type u} (S : ModestSpec X) (q : S.toPER.Quotient) :
    ∃ n ∈ q.1, S.realises n (S.decode q) :=
  Classical.choose_spec (S.decode_exists q)

/-- Encode `x : X` as the equivalence class `{k : ℕ | S.realises k x}`. -/
def encode {X : Type u} (S : ModestSpec X) (x : X) : S.toPER.Quotient :=
  ⟨{k : ℕ | S.realises k x}, by
    rcases S.realised x with ⟨n, hnx⟩
    refine ⟨n, ⟨x, hnx, hnx⟩, ?_⟩
    ext k
    exact ⟨fun hkx => ⟨x, hnx, hkx⟩,
      fun ⟨x', hnx', hkx'⟩ => S.modest hnx' hnx ▸ hkx'⟩⟩

/-- Canonical equivalence between the quotient `(S.toPER).Quotient` and `X`, sending
each equivalence class `[n]` to the unique `x : X` realised by `n` (Lemma 15, p. 14). -/
noncomputable def quotEquiv {X : Type u} (S : ModestSpec X) :
    S.toPER.Quotient ≃ X where
  toFun := S.decode
  invFun := S.encode
  left_inv q := by
    rcases S.decode_spec q with ⟨n₀, hn₀q, hn₀d⟩
    rcases q with ⟨_, m, ⟨xₘ, hmxₘ, _⟩, rfl⟩
    rcases hn₀q with ⟨x₀, hmx₀, hn₀x₀⟩
    have h₁ : xₘ = x₀ := S.modest hmxₘ hmx₀
    have h₂ : S.decode ⟨S.toPER.equivClass m, m, ⟨xₘ, hmxₘ, hmxₘ⟩, rfl⟩ = x₀ :=
      S.modest hn₀d hn₀x₀
    apply Subtype.ext
    ext k
    change S.realises k (S.decode _) ↔ ∃ x, S.realises m x ∧ S.realises k x
    rw [h₂, ← h₁]
    exact ⟨fun hkx => ⟨xₘ, hmxₘ, hkx⟩,
      fun ⟨x', hmx', hkx'⟩ => S.modest hmx' hmxₘ ▸ hkx'⟩
  right_inv x := by
    rcases S.decode_spec (S.encode x) with ⟨n, hnx, hnd⟩
    exact S.modest hnd hnx

theorem mem_symm_iff {X : Type u} (S : ModestSpec X) (x : X) (n : ℕ) :
    n ∈ (S.quotEquiv.symm x).1 ↔ S.realises n x := Iff.rfl

theorem mem_iff {X : Type u} (S : ModestSpec X) (q : S.toPER.Quotient) (n : ℕ) :
    n ∈ q.1 ↔ S.realises n (S.quotEquiv q) := by
  have h := S.mem_symm_iff (S.quotEquiv q) n
  rw [Equiv.symm_apply_apply] at h
  exact h

end ModestSpec

/-- Universe `U := ULift.{1} PER` of small types in the concrete PER model (Definition 25, p. 28). -/
abbrev PerU : Type 1 := ULift.{1} PER

/-- Decoding `El R := R.down.Quotient` of a small PER code `R : PerU` (Definition 25, p. 28). -/
abbrev PerEl (R : PerU) : Type := R.down.Quotient

/-- Realisability relation `n ⊩_R c ↔ n ∈ c.1` on decoded PER quotients (Lemma 15, p. 14). -/
abbrev perRealises {R : PerU} (n : ℕ) (c : PerEl R) : Prop := n ∈ c.1

theorem perRealised {R : PerU} (c : PerEl R) : ∃ (n : ℕ), perRealises n c := by
  rcases c with ⟨_, n, hn, rfl⟩
  exact ⟨n, hn⟩

theorem perModest {R : PerU} (n : ℕ) (c₁ c₂ : PerEl R)
    (h₁ : perRealises n c₁) (h₂ : perRealises n c₂) : c₁ = c₂ := by
  rcases c₁ with ⟨_, n₁, _, rfl⟩
  rcases c₂ with ⟨_, n₂, _, rfl⟩
  apply Subtype.ext
  ext k
  exact ⟨fun h₁k => R.down.trans (R.down.trans h₂ (R.down.symm h₁)) h₁k,
         fun h₂k => R.down.trans (R.down.trans h₁ (R.down.symm h₂)) h₂k⟩

/-- Decoding equivalence `botPER.Quotient ≃ Empty` (Definition 26, p. 28). -/
def perBotEquiv : PerEl (ULift.up botPER) ≃ Empty where
  toFun q := False.elim (by rcases q with ⟨_, _, hn, _⟩; exact hn)
  invFun x := Empty.elim x
  left_inv q := False.elim (by rcases q with ⟨_, _, hn, _⟩; exact hn)
  right_inv x := Empty.elim x

/-- Modest specification for `⊤^U` (`Unit`, Definition 27, p. 29). -/
def perTopSpec : ModestSpec Unit where
  realises _ _ := True
  realised _ := ⟨0, trivial⟩
  modest _ _ := rfl

/-- Modest specification for `Bool^U` (`Bool`, Definition 28, p. 29). -/
def perBoolSpec : ModestSpec Bool where
  realises n b := n = Bool.toNat b
  realised b := ⟨Bool.toNat b, rfl⟩
  modest {n b₁ b₂} h₁ h₂ := by
    cases b₁ <;> cases b₂ <;> cases h₁.symm.trans h₂ <;> rfl

/-- Modest specification for small dependent products `Π^U A B` (Definition 32, p. 30). -/
def perPiSpec (A : PerU) (B : PerEl A → PerU) :
    ModestSpec
      {f : (x : PerEl A) → PerEl (B x) //
        ∃ (c : TrackerCode), ∀ (x : PerEl A) (n : ℕ),
          perRealises n x → perRealises (evalTracker c n) (f x)} where
  realises e f :=
    ∀ (x : PerEl A) (n : ℕ),
      perRealises n x → perRealises (evalTracker (decodeTracker e) n) (f.1 x)
  realised := fun ⟨_, c, hc⟩ =>
    ⟨encodeTracker c, by simpa [decodeTracker_encodeTracker] using hc⟩
  modest {e f₁ f₂} h₁ h₂ := by
    apply Subtype.ext
    funext x
    rcases perRealised x with ⟨n, hnx⟩
    exact perModest (evalTracker (decodeTracker e) n) (f₁.1 x) (f₂.1 x)
      (h₁ x n hnx) (h₂ x n hnx)

/-- Modest specification for small dependent sums `Σ^U A B` (Definition 35, p. 31). -/
def perSigmaSpec (A : PerU) (B : PerEl A → PerU) :
    ModestSpec ((x : PerEl A) × PerEl (B x)) where
  realises n p :=
    perRealises (Nat.unpair n).1 p.1 ∧ perRealises (Nat.unpair n).2 p.2
  realised := fun ⟨a, b⟩ => by
    rcases perRealised a with ⟨n₁, h₁⟩
    rcases perRealised b with ⟨n₂, h₂⟩
    exact ⟨Nat.pair n₁ n₂, by simp [Nat.unpair_pair, h₁, h₂]⟩
  modest {n p₁ p₂} h₁ h₂ := by
    rcases p₁ with ⟨a₁, b₁⟩
    rcases p₂ with ⟨a₂, b₂⟩
    cases perModest (Nat.unpair n).1 a₁ a₂ h₁.1 h₂.1
    cases perModest (Nat.unpair n).2 b₁ b₂ h₁.2 h₂.2
    rfl

/-- Modest specification for small identity types `=^U_A` (Definition 29, p. 29). -/
def perIdSpec (A : PerU) (x y : PerEl A) : ModestSpec (PLift (x = y)) where
  realises _ _ := True
  realised _ := ⟨0, trivial⟩
  modest _ _ := Subsingleton.elim _ _

/-- Modest specification for the small size preorder `i ≤^U j` (Appendix C.7, p. 32). -/
def perLeSpec (i j : Omega1) : ModestSpec (PLift (i ≤ j)) where
  realises _ _ := True
  realised _ := ⟨0, trivial⟩
  modest _ _ := Subsingleton.elim _ _

/-- Generating relation for the existential quotient `∃ i : ω₁. A(i)` (Definition 38, p. 34). -/
def ExRel (A : Omega1 → PerU) (p₁ p₂ : (i : Omega1) × PerEl (A i)) : Prop :=
  ∃ (n : ℕ), perRealises n p₁.2 ∧ perRealises n p₂.2

/-- Modest specification for `∃ i : ω₁. A(i)` (Definition 38, p. 34). -/
def perExSpec (A : Omega1 → PerU) : ModestSpec (Quot (ExRel A)) where
  realises n q :=
    ∃ (p : (i : Omega1) × PerEl (A i)), Quot.mk (ExRel A) p = q ∧ perRealises n p.2
  realised q := by
    refine Quot.inductionOn q (fun p => ?_)
    rcases perRealised p.2 with ⟨n, hn⟩
    exact ⟨n, p, rfl, hn⟩
  modest {n q₁ q₂} := by
    rintro ⟨p₁, rfl, h₁⟩ ⟨p₂, rfl, h₂⟩
    exact Quot.sound ⟨n, h₁, h₂⟩

/-- Existential introduction `⟨s, a⟩^∃` in the concrete PER model. -/
noncomputable def perPairEx {A : Omega1 → PerU} (s : Omega1) (a : PerEl (A s)) :
    PerEl (ULift.up (perExSpec A).toPER) :=
  (perExSpec A).quotEquiv.symm (Quot.mk (ExRel A) ⟨s, a⟩)

theorem perRealises_cast {α : Type*} {P : α → PerU} {z₁ z₂ : α}
    (h : z₁ = z₂) (y : PerEl (P z₁)) (m : ℕ) :
    perRealises m (h ▸ y) ↔ perRealises m y := by
  cases h
  rfl

theorem sigma_ext_of_cast_eq {α : Type*} {β : α → Type*}
    {z₁ z₂ : α} {y₁ : β z₁} {y₂ : β z₂}
    (hz : z₁ = z₂) (hy : hz ▸ y₁ = y₂) :
    (⟨z₁, y₁⟩ : Sigma β) = ⟨z₂, y₂⟩ := by
  cases hz
  cases hy
  rfl

theorem sigma_snd_cast_eq {α : Type*} {β : α → Type*}
    {p : Sigma β} {z : α} {y : β z}
    (h : p = ⟨z, y⟩) (hfst : p.1 = z) :
    hfst ▸ p.2 = y := by
  cases h
  rfl

/-- Existential elimination `ind_∃` in the concrete PER model (Section 4.5, p. 16). -/
noncomputable def perIndEx {A : Omega1 → PerU}
    (P : PerEl (ULift.up (perExSpec A).toPER) → PerU)
    (p : (i : Omega1) → (x : PerEl (A i)) → PerEl (P (perPairEx i x)))
    (hp : ∃ (c : TrackerCode), ∀ (i : Omega1) (x : PerEl (A i)) (n : ℕ),
      perRealises n x → perRealises (evalTracker c n) (p i x))
    (z : PerEl (ULift.up (perExSpec A).toPER)) : PerEl (P z) :=
  let F_raw : (i : Omega1) × PerEl (A i) →
      (w : PerEl (ULift.up (perExSpec A).toPER)) × PerEl (P w) :=
    fun w => ⟨perPairEx w.1 w.2, p w.1 w.2⟩
  have hF_raw : ∀ w₁ w₂, ExRel A w₁ w₂ → F_raw w₁ = F_raw w₂ := by
    rintro ⟨i₁, a₁⟩ ⟨i₂, a₂⟩ ⟨n, h₁, h₂⟩
    rcases hp with ⟨c, hc⟩
    have hz : perPairEx i₁ a₁ = perPairEx i₂ a₂ :=
      congrArg (perExSpec A).quotEquiv.symm (Quot.sound ⟨n, h₁, h₂⟩)
    have hm₁ : perRealises (evalTracker c n) (hz ▸ p i₁ a₁) :=
      (perRealises_cast hz (p i₁ a₁) (evalTracker c n)).mpr (hc i₁ a₁ n h₁)
    have hm₂ : perRealises (evalTracker c n) (p i₂ a₂) := hc i₂ a₂ n h₂
    exact sigma_ext_of_cast_eq hz (perModest (evalTracker c n) _ _ hm₁ hm₂)
  let lifted := Quot.lift F_raw hF_raw ((perExSpec A).quotEquiv z)
  have hfst : lifted.1 = z := by
    have hq : ∀ (q : Quot (ExRel A)),
        (Quot.lift F_raw hF_raw q).1 = (perExSpec A).quotEquiv.symm q :=
      fun q => Quot.inductionOn q (fun _ => rfl)
    exact (hq ((perExSpec A).quotEquiv z)).trans ((perExSpec A).quotEquiv.symm_apply_apply z)
  hfst ▸ lifted.2

theorem perIndEx_beta {A : Omega1 → PerU}
    (P : PerEl (ULift.up (perExSpec A).toPER) → PerU)
    (p : (i : Omega1) → (x : PerEl (A i)) → PerEl (P (perPairEx i x)))
    (hp : ∃ (c : TrackerCode), ∀ (i : Omega1) (x : PerEl (A i)) (n : ℕ),
      perRealises n x → perRealises (evalTracker c n) (p i x))
    (s : Omega1) (a : PerEl (A s)) :
    perIndEx P p hp (perPairEx s a) = p s a := by
  dsimp only [perIndEx]
  apply sigma_snd_cast_eq (β := fun w => PerEl (P w))
  dsimp only [perPairEx]
  rw [Equiv.apply_symm_apply]

/-- Modest specification for `∀ i : ω₁. A(i)` (Section 4.5, p. 15 & Appendix C.6, p. 30). -/
def perAllSpec (A : Omega1 → PerU) :
    ModestSpec
      {f : (i : Omega1) → PerEl (A i) //
        ∃ (n : ℕ), ∀ (i : Omega1), perRealises n (f i)} where
  realises n f := ∀ (i : Omega1), perRealises n (f.1 i)
  realised := fun ⟨_, n, hn⟩ => ⟨n, hn⟩
  modest {n f₁ f₂} h₁ h₂ := by
    apply Subtype.ext
    funext i
    exact perModest n (f₁.1 i) (f₂.1 i) (h₁ i) (h₂ i)

/-- Generating relation for bounded existential `∃ j < i. X(j, p)` (Appendix C.7, p. 32). -/
def DiamondBRel (i : Omega1)
    (X : (j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → PerU)
    (p₁ p₂ : (j : Omega1) × (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)) × PerEl (X j p)) :
    Prop :=
  ∃ (n : ℕ), perRealises n p₁.2.2 ∧ perRealises n p₂.2.2

/-- Modest specification for bounded existential `∃ j < i. X(j, p)` (Appendix C.7, p. 32). -/
def perDiamondBSpec (i : Omega1)
    (X : (j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → PerU) :
    ModestSpec (Quot (DiamondBRel i X)) where
  realises n q :=
    ∃ (w : (j : Omega1) × (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)) × PerEl (X j p)),
      Quot.mk (DiamondBRel i X) w = q ∧ perRealises n w.2.2
  realised q := by
    refine Quot.inductionOn q (fun w => ?_)
    rcases perRealised w.2.2 with ⟨n, hn⟩
    exact ⟨n, w, rfl, hn⟩
  modest {n q₁ q₂} := by
    rintro ⟨w₁, rfl, h₁⟩ ⟨w₂, rfl, h₂⟩
    exact Quot.sound ⟨n, h₁, h₂⟩

/-- Bounded existential introduction `pairDiamondB` in the concrete PER model. -/
noncomputable def perPairDiamondB {i : Omega1}
    {X : (j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → PerU}
    (j : Omega1) (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER))
    (a : PerEl (X j p)) : PerEl (ULift.up (perDiamondBSpec i X).toPER) :=
  (perDiamondBSpec i X).quotEquiv.symm (Quot.mk (DiamondBRel i X) ⟨j, p, a⟩)

/-- Bounded existential elimination `indDiamondB` in the concrete PER model. -/
noncomputable def perIndDiamondB {i : Omega1}
    {X : (j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → PerU}
    (P : PerEl (ULift.up (perDiamondBSpec i X).toPER) → PerU)
    (f : (j : Omega1) → (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)) →
      (a : PerEl (X j p)) → PerEl (P (perPairDiamondB j p a)))
    (hf : ∃ (c : TrackerCode), ∀ (j : Omega1)
      (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER))
      (a : PerEl (X j p)) (n : ℕ),
      perRealises n a → perRealises (evalTracker c n) (f j p a))
    (z : PerEl (ULift.up (perDiamondBSpec i X).toPER)) : PerEl (P z) :=
  let F_raw : (j : Omega1) × (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)) × PerEl (X j p) →
      (w : PerEl (ULift.up (perDiamondBSpec i X).toPER)) × PerEl (P w) :=
    fun w => ⟨perPairDiamondB w.1 w.2.1 w.2.2, f w.1 w.2.1 w.2.2⟩
  have hF_raw : ∀ w₁ w₂, DiamondBRel i X w₁ w₂ → F_raw w₁ = F_raw w₂ := by
    rintro ⟨j₁, p₁, a₁⟩ ⟨j₂, p₂, a₂⟩ ⟨n, h₁, h₂⟩
    rcases hf with ⟨c, hc⟩
    have hz : perPairDiamondB j₁ p₁ a₁ = perPairDiamondB j₂ p₂ a₂ :=
      congrArg (perDiamondBSpec i X).quotEquiv.symm (Quot.sound ⟨n, h₁, h₂⟩)
    have hm₁ : perRealises (evalTracker c n) (hz ▸ f j₁ p₁ a₁) :=
      (perRealises_cast hz (f j₁ p₁ a₁) (evalTracker c n)).mpr (hc j₁ p₁ a₁ n h₁)
    have hm₂ : perRealises (evalTracker c n) (f j₂ p₂ a₂) := hc j₂ p₂ a₂ n h₂
    exact sigma_ext_of_cast_eq hz (perModest (evalTracker c n) _ _ hm₁ hm₂)
  let lifted := Quot.lift F_raw hF_raw ((perDiamondBSpec i X).quotEquiv z)
  have hfst : lifted.1 = z := by
    have hq : ∀ (q : Quot (DiamondBRel i X)),
        (Quot.lift F_raw hF_raw q).1 = (perDiamondBSpec i X).quotEquiv.symm q :=
      fun q => Quot.inductionOn q (fun _ => rfl)
    exact (hq ((perDiamondBSpec i X).quotEquiv z)).trans
      ((perDiamondBSpec i X).quotEquiv.symm_apply_apply z)
  hfst ▸ lifted.2

theorem perIndDiamondB_beta {i : Omega1}
    {X : (j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → PerU}
    (P : PerEl (ULift.up (perDiamondBSpec i X).toPER) → PerU)
    (f : (j : Omega1) → (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)) →
      (a : PerEl (X j p)) → PerEl (P (perPairDiamondB j p a)))
    (hf : ∃ (c : TrackerCode), ∀ (j : Omega1)
      (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER))
      (a : PerEl (X j p)) (n : ℕ),
      perRealises n a → perRealises (evalTracker c n) (f j p a))
    (j : Omega1) (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER))
    (a : PerEl (X j p)) :
    perIndDiamondB P f hf (perPairDiamondB j p a) = f j p a := by
  dsimp only [perIndDiamondB]
  apply sigma_snd_cast_eq (β := fun w => PerEl (P w))
  dsimp only [perPairDiamondB]
  rw [Equiv.apply_symm_apply]

/-- Modest specification for bounded universal `∀ j < i. X(j, p)` (Appendix C.7, p. 32). -/
def perBoxBSpec (i : Omega1)
    (X : (j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → PerU) :
    ModestSpec
      {f : (j : Omega1) → (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)) → PerEl (X j p) //
        ∃ (n : ℕ), ∀ (j : Omega1) (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)),
          perRealises n (f j p)} where
  realises n f :=
    ∀ (j : Omega1) (p : PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER)),
      perRealises n (f.1 j p)
  realised := fun ⟨_, n, hn⟩ => ⟨n, hn⟩
  modest {n f₁ f₂} h₁ h₂ := by
    apply Subtype.ext
    funext j p
    exact perModest n (f₁.1 j p) (f₂.1 j p) (h₁ j p) (h₂ j p)

/-- Well-foundedness of `<` on `Omega1` (Appendix C.7, p. 32). -/
theorem omega1_lt_wf : WellFounded (fun (s₁ s₂ : Omega1) => s₁ < s₂) :=
  InvImage.wf (fun s : Omega1 => s.1) Ordinal.lt_wf

/-- Well-founded size recursion `fix` in the concrete PER model over `Omega1`
(Appendix C.8, pp. 32–33). -/
noncomputable def perFix {A : Omega1 → Type 1}
    (f : (i : Omega1) →
      ((j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → A j) → A i)
    (i : Omega1) : A i :=
  omega1_lt_wf.fix
    (fun i ih => f i (fun j hji =>
      ih j (Order.lt_add_one_iff.mpr (le_refl j.1) |>.trans_le
        ((perLeSpec (omega1Succ j) i).quotEquiv hji).down))) i

theorem perFix_beta {A : Omega1 → Type 1}
    (f : (i : Omega1) →
      ((j : Omega1) → PerEl (ULift.up (perLeSpec (omega1Succ j) i).toPER) → A j) → A i)
    (i : Omega1) :
    perFix f i = f i (fun j _ => perFix f j) :=
  omega1_lt_wf.fix_eq _ i

/-- The concrete interpretation `perSizeCoreTheory : SizeCoreTheory.{1, 0}` of the core
sized type theory in `PER` over `Omega1` (`U = ULift.{1} PER`, `El R = R.down.Quotient`,
`Size = Omega1`, `zero = omega1Zero`, `succ = omega1Succ`, `botU = ULift.up botPER`,
Section 4 & Appendix C, pp. 12–16, 27–35). -/
noncomputable def perSizeCoreTheory : SizeCoreTheory.{1, 0} where
  U := PerU
  El := PerEl
  realises := perRealises
  realised := perRealised
  modest := perModest

  botU := ULift.up botPER
  El_botU := perBotEquiv

  topU := ULift.up perTopSpec.toPER
  El_topU := perTopSpec.quotEquiv
  realises_topU x := (perTopSpec.mem_iff x 0).mpr trivial

  boolU := ULift.up perBoolSpec.toPER
  El_boolU := perBoolSpec.quotEquiv

  piU A B := ULift.up (perPiSpec A B).toPER
  El_piU A B := (perPiSpec A B).quotEquiv
  realises_piU g e := (perPiSpec _ _).mem_iff g e

  sigmaU A B := ULift.up (perSigmaSpec A B).toPER
  El_sigmaU A B := (perSigmaSpec A B).quotEquiv
  realises_sigmaU p n := (perSigmaSpec _ _).mem_iff p n

  idU A x y := ULift.up (perIdSpec A x y).toPER
  El_idU A x y := (perIdSpec A x y).quotEquiv
  realises_idU {A x y} p := ((perIdSpec A x y).mem_iff p 0).mpr trivial

  Size := Omega1
  zero := omega1Zero
  succ := omega1Succ
  leU i j := ULift.up (perLeSpec i j).toPER
  le_zero i := (perLeSpec omega1Zero i).quotEquiv.symm ⟨(zero_le : (0 : Ordinal.{0}) ≤ i.1)⟩
  le_succ i := (perLeSpec i (omega1Succ i)).quotEquiv.symm
    ⟨(Order.lt_add_one_iff.mpr (le_refl i.1)).le⟩
  le_refl i := (perLeSpec i i).quotEquiv.symm ⟨le_rfl⟩
  le_trans h₁ h₂ := (perLeSpec _ _).quotEquiv.symm
    ⟨((perLeSpec _ _).quotEquiv h₁).down.trans ((perLeSpec _ _).quotEquiv h₂).down⟩
  le_eq p q := (perLeSpec _ _).quotEquiv.injective (Subsingleton.elim _ _)
  realises_leU {i j} p := ((perLeSpec i j).mem_iff p 0).mpr trivial

  exU A := ULift.up (perExSpec A).toPER
  pairEx s a := perPairEx s a
  realises_pairEx s a n hna := ((perExSpec _).mem_symm_iff _ n).mpr ⟨⟨s, a⟩, rfl, hna⟩
  realises_exU z n hnz := by
    rcases ((perExSpec _).mem_iff z n).mp hnz with ⟨⟨s, a⟩, hq, hna⟩
    refine ⟨s, a, ?_, hna⟩
    change (perExSpec _).quotEquiv.symm (Quot.mk (ExRel _) ⟨s, a⟩) = z
    rw [hq, Equiv.symm_apply_apply]
  indEx P p hp z := perIndEx P p hp z
  indEx_beta P p hp s a := perIndEx_beta P p hp s a

  allU A := ULift.up (perAllSpec A).toPER
  lamAll a ha := (perAllSpec _).quotEquiv.symm ⟨a, ha⟩
  appAll f i := ((perAllSpec _).quotEquiv f).1 i
  realises_allU f n := (perAllSpec _).mem_iff f n
  all_beta a ha s := by
    rw [Equiv.apply_symm_apply]
  all_eta f hf := by
    change (perAllSpec _).quotEquiv.symm ⟨((perAllSpec _).quotEquiv f).1, hf⟩ = f
    exact (perAllSpec _).quotEquiv.symm_apply_apply f

  diamondBoundedU i X := ULift.up (perDiamondBSpec i X).toPER
  pairDiamondB j p a := perPairDiamondB j p a
  realises_pairDiamondB j p a n hna :=
    ((perDiamondBSpec _ _).mem_symm_iff _ n).mpr ⟨⟨j, p, a⟩, rfl, hna⟩
  realises_diamondBoundedU z n hnz := by
    rcases ((perDiamondBSpec _ _).mem_iff z n).mp hnz with ⟨⟨j, p, a⟩, hq, hna⟩
    refine ⟨j, p, a, ?_, hna⟩
    change (perDiamondBSpec _ _).quotEquiv.symm (Quot.mk (DiamondBRel _ _) ⟨j, p, a⟩) = z
    rw [hq, Equiv.symm_apply_apply]
  indDiamondB P f hf z := perIndDiamondB P f hf z
  indDiamondB_beta P f hf j p a := perIndDiamondB_beta P f hf j p a

  boxBoundedU i X := ULift.up (perBoxBSpec i X).toPER
  lamBoxB f hf := (perBoxBSpec _ _).quotEquiv.symm ⟨f, hf⟩
  appBoxB g j p := ((perBoxBSpec _ _).quotEquiv g).1 j p
  realises_boxBoundedU g n := (perBoxBSpec _ _).mem_iff g n
  boxB_beta f hf j p := by
    rw [Equiv.apply_symm_apply]
  boxB_eta g hg := by
    change (perBoxBSpec _ _).quotEquiv.symm ⟨((perBoxBSpec _ _).quotEquiv g).1, hg⟩ = g
    exact (perBoxBSpec _ _).quotEquiv.symm_apply_apply g

  fix f i := perFix f i
  fix_beta f i := perFix_beta f i

end LaarakkerOttenVanDenBerg2026


