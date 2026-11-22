-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_StatementC
-- name    : Formalism_SatakeDualWeyl_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:08:58.920827+00:00
-- url     : https://prove2.me/theorems/1c5e138a-8c8f-40a8-8024-c1cc0278302a
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/StatementC.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG
section Defs
variable {F E : Type} [Field F] [CommRing E] [Algebra F E] {n : Type} [Fintype n] [DecidableEq n]
def latS (R : Type) [CommRing R] [Algebra F R] (S : Subring (E ⊗[F] R)) {O : Type} [CommRing O]
    [Algebra O E] (Λ : Submodule O (n → E)) : Submodule S (n → E ⊗[F] R) :=
  Submodule.span S ((fun x : n → E => fun i => inclE (F := F) R (x i)) '' (Λ : Set (n → E)))
def levelVL [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix n n E) (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (GL n (E ⊗[F] v.adicCompletion F)) :=
  level (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F)))
    (latS (F := F) (v.adicCompletion F)
      (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ)
def levelAfL [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) :
    Subgroup (GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) :=
  level (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)))
    (latS (F := F) (FiniteAdeleRing (𝓞 F) F)
      (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ)
def evalV (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    FiniteAdeleRing (𝓞 F) F →ₐ[F] v.adicCompletion F where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
def prV [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    E ⊗[F] FiniteAdeleRing (𝓞 F) F →+* E ⊗[F] v.adicCompletion F :=
  (Algebra.TensorProduct.map (AlgHom.id F E) (evalV F v)).toRingHom
end Defs
def PosDefToDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [CommRing E] [Algebra F E] (n : Type) [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    NumberField.IsTotallyReal F → IsTotPosDef σ J → IsTotDef σ J
def StabFunLe : Prop :=
  ∀ (A R M : Type) [CommRing A] [CommRing R] [Algebra R A] [AddCommGroup M] [Module R M]
    (n : Type) [Fintype n] [DecidableEq n] (Λ : Submodule R (n → A)) (f : Λ →ₗ[R] M),
    stabFun Λ f ≤ stabGL Λ
def StabFunEx : Prop :=
  ∃ f : ↥(stdLat (n := Fin 2) (A := ℚ) ℤ) →ₗ[ℤ] ZMod 2,
    stabFun (stdLat (n := Fin 2) (A := ℚ) ℤ) f ≠ stabGL (stdLat (n := Fin 2) (A := ℚ) ℤ)
def LevelAfLStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    levelAfL σ J (stdLat (n := n) (A := E) (𝓞 E)) = levelAf σ J
def LevelVLStd : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (v : HeightOneSpectrum (𝓞 F)),
    levelVL σ J v (stdLat (n := n) (A := E) (𝓞 E)) = levelV σ J v
def ClassSetFiniteL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ Λ : Submodule (𝓞 E) (n → E), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    Finite (ClassSet ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))))
def AdelicStabFiniteL : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    IsHerm (σ : E →+* E) J → IsUnit J.det → IsTotDef σ J →
    ∀ Λ : Submodule (𝓞 E) (n → E), Module.Finite (𝓞 E) Λ → Submodule.span E (Λ : Set (n → E)) = ⊤ →
    ∀ g : UPts σ J (FiniteAdeleRing (𝓞 F) F),
      Finite (stabAt ((ratPts σ J (FiniteAdeleRing (𝓞 F) F)).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F)))
        ((levelAfL σ J Λ).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))) g)
def AfSplitOff : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (v : HeightOneSpectrum (𝓞 F)),
    ∃ (G₂ : Type) (_ : Group G₂) (K₂ : Subgroup G₂)
      (e : UPts σ J (FiniteAdeleRing (𝓞 F) F) ≃* (UPts σ J (v.adicCompletion F) × G₂)),
      (∀ g, (((e g).1 : UPts σ J (v.adicCompletion F)) : GL n (E ⊗[F] v.adicCompletion F)) =
        bc (prV (E := E) v) (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F))) ∧
      (∀ g, (e g).2 = 1 ↔ ∀ w : HeightOneSpectrum (𝓞 F), w ≠ v →
        bc (prV (E := E) w) (g : GL n (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) = 1) ∧
      ((levelAf σ J).subgroupOf (UPts σ J (FiniteAdeleRing (𝓞 F) F))).map e.toMonoidHom =
        ((levelV σ J v).subgroupOf (UPts σ J (v.adicCompletion F))).prod K₂
def LevelVSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
    (v : HeightOneSpectrum (𝓞 F))
    (φ : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
    (∀ x, φ (sigR σ (v.adicCompletion F) x) = swapR _ (φ x)) →
    (∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring ↔
      (φ x).1 ∈ v.adicCompletionIntegers F ∧ (φ x).2 ∈ v.adicCompletionIntegers F) →
    (∃ u ∈ GLint n (v.adicCompletionIntegers F).toSubring,
      (u : Matrix n n (v.adicCompletion F)) = fun i j => (φ (inclE (F := F) (v.adicCompletion F) (J i j))).1) →
    ∀ g ∈ UPts σ J (v.adicCompletion F),
      g ∈ levelV σ J v ↔
        bc ((RingHom.fst _ _).comp φ.toRingHom) g ∈
          GLint n (v.adicCompletionIntegers F).toSubring
def DefSig : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (n : Type) [Fintype n] [DecidableEq n]
    (σ : E →ₐ[F] E) (J : Matrix n n E) (ι : F →+* ℝ) (τ : E →+* ℂ),
    τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ →
    τ.comp (algebraMap F E) = (algebraMap ℝ ℂ).comp ι →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) →
    IsHerm (σ : E →+* E) J → IsUnit J.det →
    (IsDefiniteAt σ J ι ↔
      (HasSignature (J.map τ) (Fintype.card n) 0 ∨ HasSignature (J.map τ) 0 (Fintype.card n)))
def StdFormDef : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : Type) [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E),
    (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) → NumberField.IsTotallyReal F →
    IsHerm (σ : E →+* E) (1 : Matrix n n E) ∧ IsTotDef σ (1 : Matrix n n E) ∧ IsTotDef σ (-1 : Matrix n n E)
end Formalism.UG


