-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:52.948163+00:00
-- url     : https://prove2.me/theorems/1fa07070-2d4f-43c9-92f8-54c89389c13a
-- title:
--   Dual Basis
-- statement:
--   Definitions and structural lemmas for Dual Basis, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SelfDualLocalBasis/DualBasis.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
namespace PI.SelfDualLoc.W
open PI.SelfDualLoc
abbrev Oloc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
abbrev Lloc (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (Oloc F E v) (Fin n → E ⊗[F] v.adicCompletion F) :=
  latS (F := F) (v.adicCompletion F) (Oloc F E v) Lb
abbrev hloc {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (z y : Fin n → E ⊗[F] v.adicCompletion F) : E ⊗[F] v.adicCompletion F :=
  hform (sigR σ (v.adicCompletion F)) (J.map (inclE (F := F) (v.adicCompletion F))) z y
def SigInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)),
    ∀ c ∈ Oloc F E v, sigR σ (v.adicCompletion F) c ∈ Oloc F E v
def UnitLoc : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (s : 𝓞 F), s ∉ v.asIdeal →
    ∃ u ∈ Oloc F E v, inclE (F := F) (v.adicCompletion F) (algebraMap F E (s : F)) * u = 1
def Nondeg : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    T ≠ 0 → ∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y = 0) → y = 0
def SpanTop : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    T ≠ 0 → Submodule.span E (Lb : Set (Fin n → E)) = ⊤
def LocBasis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) (Lb : Submodule (𝓞 E) (Fin n → E)),
    Module.Finite (𝓞 E) Lb → Submodule.span E (Lb : Set (Fin n → E)) = ⊤ →
    ∃ (x : Fin n → Fin n → E) (s : 𝓞 F), s ∉ v.asIdeal ∧ (∀ i, x i ∈ Lb) ∧
      ∀ z ∈ Lb, ∃ a : Fin n → 𝓞 E, algebraMap F E (s : F) • z = ∑ i, ((a i : 𝓞 E) : E) • x i
def DualBasis : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (x : Fin n → Fin n → E),
    Submodule.span E (Set.range x) = ⊤ →
    (∀ y : Fin n → E, (∀ i, hform (σ : E →+* E) J (x i) y = 0) → y = 0) →
    ∃ y : Fin n → Fin n → E, (∀ i j, hform (σ : E →+* E) J (x i) (y j) = if i = j then 1 else 0) ∧
      ∀ w : Fin n → E, ∃ c : Fin n → E, w = ∑ j, c j • y j
def FwdDir : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)),
    (∀ x ∈ Lb, ∀ y ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) →
    ∀ y ∈ Lloc F E n v Lb, ∀ z ∈ Lloc F E n v Lb, hloc σ J v z y ∈ Oloc F E v
def BwdDir : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) (v : HeightOneSpectrum (𝓞 F))
    (Lb : Submodule (𝓞 E) (Fin n → E)) (T : ℕ),
    Module.Finite (𝓞 E) Lb →
    (∀ x ∈ Lb, ∀ y ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) →
    (∀ y : Fin n → E, (∀ x ∈ Lb, hform (σ : E →+* E) J x y ∈ intOE E) → (T : E) • y ∈ Lb) →
    (T : 𝓞 F) ∉ v.asIdeal →
    ∀ y, (∀ z ∈ Lloc F E n v Lb, hloc σ J v z y ∈ Oloc F E v) → y ∈ Lloc F E n v Lb
end PI.SelfDualLoc.W


