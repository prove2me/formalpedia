-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_PlusPolynomialInclusion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:15:33.739324+00:00
-- url     : https://prove2.me/theorems/67b4925e-6487-4022-a160-0baff31fc83e
-- title:
--   Plus Polynomial Inclusion
-- statement:
--   Definitions and structural lemmas for Plus Polynomial Inclusion, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/PlusPolynomialInclusion.lean

import Mathlib
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
open Polynomial TensorProduct Matrix NumberField IsDedekindDomain Formalism.UG
namespace GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion
variable {F E : Type} [Field F] [Field E] [Algebra F E]
def sharp (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : E[X] :=
  C (c (P.coeff 0))⁻¹ * reflect r (P.map (c : E →+* E))
def IsPPol (c : E ≃ₐ[F] E) (r : ℕ) (P : E[X]) : Prop :=
  P.Monic ∧ Irreducible P ∧ P.natDegree = r ∧ P.coeff 0 ≠ 0 ∧ P = sharp c r P
variable {c : E ≃ₐ[F] E} {r : ℕ} {P : E[X]}
theorem isUnit_root (hP : IsPPol c r P) : IsUnit (AdjoinRoot.root P) := by
  haveI : Fact (Irreducible P) := ⟨hP.2.1⟩
  refine Ne.isUnit fun h => hP.2.2.2.1 ?_
  have h1 := AdjoinRoot.eval₂_root P
  rw [h, eval₂_at_zero] at h1
  exact (map_eq_zero_iff _ (AdjoinRoot.of P).injective).1 h1
def alpha (hP : IsPPol c r P) : (AdjoinRoot P)ˣ := (isUnit_root hP).unit
theorem eval₂_conj_inv (hP : IsPPol c r P) :
    P.eval₂ ((AdjoinRoot.of P).comp (c : E →+* E)) ((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) = 0 := by
  rw [← eval₂_map]
  letI : Invertible (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) := Units.invertible _
  have hd : (P.map (c : E →+* E)).natDegree ≤ r := hP.2.2.1 ▸ natDegree_map_le
  rw [← eval₂_reflect_eq_zero_iff _ _ r _ hd]
  have h1 : ⅟(((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) = AdjoinRoot.root P := rfl
  have h2 : reflect r (P.map (c : E →+* E)) = C (c (P.coeff 0)) * P := by
    have hne : c (P.coeff 0) ≠ 0 := by simpa using hP.2.2.2.1
    conv_rhs => rw [hP.2.2.2.2]
    rw [← hP.2.2.2.2]
    conv_rhs => arg 2; rw [hP.2.2.2.2]
    rw [sharp, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hne, C_1, one_mul]
  rw [h1, h2, eval₂_mul, AdjoinRoot.eval₂_root, mul_zero]
def starL (hP : IsPPol c r P) : AdjoinRoot P →ₐ[F] AdjoinRoot P :=
  { AdjoinRoot.lift ((AdjoinRoot.of P).comp (c : E →+* E))
      (((alpha hP)⁻¹ : (AdjoinRoot P)ˣ) : AdjoinRoot P) (eval₂_conj_inv hP) with
    commutes' := fun a => by
      have h : algebraMap F (AdjoinRoot P) a = AdjoinRoot.of P (algebraMap F E a) := rfl
      rw [h]
      simp }
def Lplus (hP : IsPPol c r P) : Subalgebra F (AdjoinRoot P) :=
  AlgHom.equalizer (starL hP) (AlgHom.id F (AdjoinRoot P))
variable (k : Type) [Field k] [Algebra F k]
@[reducible] def algLk (P : E[X]) : Algebra (E ⊗[F] k) (AdjoinRoot P ⊗[F] k) :=
  (Algebra.TensorProduct.map (IsScalarTower.toAlgHom F E (AdjoinRoot P))
    (AlgHom.id F k)).toRingHom.toAlgebra
attribute [local instance] algLk
def starLk (hP : IsPPol c r P) : AdjoinRoot P ⊗[F] k →+* AdjoinRoot P ⊗[F] k :=
  sigR (starL hP) k
def inclPlus (hP : IsPPol c r P) : Lplus hP ⊗[F] k →+* AdjoinRoot P ⊗[F] k :=
  (Algebra.TensorProduct.map (Lplus hP).val (AlgHom.id F k)).toRingHom
def trLk (P : E[X]) : AdjoinRoot P ⊗[F] k →ₗ[F] E ⊗[F] k :=
  TensorProduct.map ((Algebra.trace E (AdjoinRoot P)).restrictScalars F) LinearMap.id
def hx (hP : IsPPol c r P) (x : (Lplus hP ⊗[F] k)ˣ) (y y' : AdjoinRoot P ⊗[F] k) : E ⊗[F] k :=
  trLk k P (inclPlus k hP x * y * starLk k hP y')
def normL (hP : IsPPol c r P) : Subgroup (Lplus hP ⊗[F] k)ˣ :=
  (MonoidHom.id (AdjoinRoot P ⊗[F] k)ˣ * Units.map (starLk k hP).toMonoidHom).range.comap
    (Units.map (inclPlus k hP).toMonoidHom)
def normE (c : E ≃ₐ[F] E) : Subgroup kˣ :=
  (MonoidHom.id (E ⊗[F] k)ˣ * Units.map (sigR (c : E →ₐ[F] E) k).toMonoidHom).range.comap
    (Units.map (Algebra.TensorProduct.includeRight : k →ₐ[F] E ⊗[F] k).toRingHom.toMonoidHom)
def hU (c : E ≃ₐ[F] E) (J : Matrix (Fin r) (Fin r) (E ⊗[F] k)) (u u' : Fin r → E ⊗[F] k) :
    E ⊗[F] k :=
  hform (sigR (c : E →ₐ[F] E) k) J u' u
variable {k}
def IsIsometry (hP : IsPPol c r P) (J : Matrix (Fin r) (Fin r) (E ⊗[F] k))
    (x : (Lplus hP ⊗[F] k)ˣ)
    (φ : (AdjoinRoot P ⊗[F] k) ≃ₗ[E ⊗[F] k] (Fin r → E ⊗[F] k)) : Prop :=
  ∀ y y', hU k c J (φ y) (φ y') = hx k hP x y y'
def Xk (hP : IsPPol c r P) (J : Matrix (Fin r) (Fin r) (E ⊗[F] k)) :
    Set ((Lplus hP ⊗[F] k)ˣ ⧸ normL k hP) :=
  {ξ | ∃ x : (Lplus hP ⊗[F] k)ˣ, (QuotientGroup.mk x : _ ⧸ normL k hP) = ξ ∧
    ∃ φ, IsIsometry hP J x φ}
def classesWith (c : E ≃ₐ[F] E) (P : E[X]) (J : Matrix (Fin r) (Fin r) (E ⊗[F] k)) :
    Set (ConjClasses (UJ (sigR (c : E →ₐ[F] E) k) J)) :=
  {C | ∃ g : UJ (sigR (c : E →ₐ[F] E) k) J, ConjClasses.mk g = C ∧
    ((g : GL (Fin r) (E ⊗[F] k)) : Matrix (Fin r) (Fin r) (E ⊗[F] k)).charpoly
      = P.map (inclE (F := F) k)}
def IsDisc (hP : IsPPol c r P) (x : (Lplus hP ⊗[F] k)ˣ) (δ : kˣ ⧸ normE k c) : Prop :=
  ∃ (b : Module.Basis (Fin r) (E ⊗[F] k) (AdjoinRoot P ⊗[F] k)) (d : kˣ),
    (1 : E) ⊗ₜ[F] (d : k) = (Matrix.of fun i j => hx k hP x (b i) (b j)).det ∧
      (QuotientGroup.mk d : kˣ ⧸ normE k c) = δ
def normPlus (hP : IsPPol c r P) : (Lplus hP ⊗[F] k)ˣ →* kˣ :=
  Units.map ((Algebra.norm k : k ⊗[F] Lplus hP →* k).comp
    (Algebra.TensorProduct.comm F (Lplus hP) k).toAlgHom.toRingHom.toMonoidHom)
variable (k)
def ClassParamAt (hP : IsPPol c r P) : Prop :=
  ∀ J : Matrix (Fin r) (Fin r) (E ⊗[F] k), IsHerm (sigR (c : E →ₐ[F] E) k) J → IsUnit J.det →
    (∀ x : (Lplus hP ⊗[F] k)ˣ, (QuotientGroup.mk x : _ ⧸ normL k hP) ∈ Xk hP J →
      ∃ φ, IsIsometry hP J x φ) ∧
    ∃ Φ : (Lplus hP ⊗[F] k)ˣ ⧸ normL k hP → ConjClasses (UJ (sigR (c : E →ₐ[F] E) k) J),
      (∀ (x : (Lplus hP ⊗[F] k)ˣ) φ, IsIsometry hP J x φ →
        ∃ g : UJ (sigR (c : E →ₐ[F] E) k) J,
          (∀ u, ((g : GL (Fin r) (E ⊗[F] k)) : Matrix (Fin r) (Fin r) (E ⊗[F] k)) *ᵥ u
            = φ ((AdjoinRoot.root P ⊗ₜ[F] (1 : k)) * φ.symm u)) ∧
          Φ (QuotientGroup.mk x) = ConjClasses.mk g) ∧
      Set.BijOn Φ (Xk hP J) (classesWith c P J)
def DiscAt (hP : IsPPol c r P) : Prop :=
  ∀ x : (Lplus hP ⊗[F] k)ˣ, (∃! δ, IsDisc hP x δ) ∧
    ∀ δ δ₁, IsDisc hP x δ → IsDisc hP 1 δ₁ → δ = QuotientGroup.mk (normPlus hP x) * δ₁
def AllFields [NumberField F] (hP : IsPPol c r P) : Prop :=
  (ClassParamAt F hP ∧ DiscAt F hP) ∧
  (∀ v : HeightOneSpectrum (𝓞 F),
    ClassParamAt (v.adicCompletion F) hP ∧ DiscAt (v.adicCompletion F) hP) ∧
  (∀ v : InfinitePlace F, ClassParamAt v.Completion hP ∧ DiscAt v.Completion hP)
def ClassParamCM : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
    ∀ c : E ≃ₐ[F] E, c ≠ 1 → ∀ (r : ℕ) (P : E[X]) (hP : IsPPol c r P), AllFields hP
def ClassParam : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ c : E ≃ₐ[F] E, c ≠ 1 → ∀ r : ℕ, Odd r → ∀ (P : E[X]) (hP : IsPPol c r P), AllFields hP
end GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialInclusion


