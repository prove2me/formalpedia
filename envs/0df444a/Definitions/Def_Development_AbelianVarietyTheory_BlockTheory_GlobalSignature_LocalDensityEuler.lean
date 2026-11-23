-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDensityEuler
-- name    : Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_LocalDensityEuler
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:28.635158+00:00
-- url     : https://prove2.me/theorems/be21059f-7510-4322-b1c6-940fc74f8926
-- title:
--   Local Density Euler
-- statement:
--   Definitions and structural lemmas for Local Density Euler, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/GlobalSignature/LocalDensityEuler.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
section Defs
variable (F : Type) [Field F] [NumberField F]
open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiV_zero (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV F ψ v 0 = 1 := by
  classical
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV
  rw [RestrictedProduct.single_zero]
  exact AddChar.map_zero_eq_one ψ
open scoped TensorProduct in
open NumberField IsDedekindDomain in
variable (F : Type) [Field F] [NumberField F] in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual.psiV_add (ψ : AddChar (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (v : HeightOneSpectrum (𝓞 F))
    (x y : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) :
    _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV F ψ v (x + y) = _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV F ψ v x * _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV F ψ v y := by
  classical
  unfold _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.psiV _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.pairA _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV
  refine Eq.trans ?_ (ψ.map_add_eq_mul _ _)
  congr 1
  refine Prod.ext (add_zero 0).symm ?_
  exact RestrictedProduct.single_add (fun w => HeightOneSpectrum.adicCompletionIntegers F w) v x y
def intV (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Fv F v) :=
  (v.adicCompletionIntegers F).toSubring.toAddSubgroup
def psiDual (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddSubgroup (Fv F v) where
  carrier := {t | ∀ s ∈ v.adicCompletionIntegers F, psiV F ψ v (t * s) = 1}
  zero_mem' := by
    intro s _
    rw [zero_mul, psiV_zero]
  add_mem' := by
    intro a b ha hb s hs
    rw [add_mul, psiV_add, ha s hs, hb s hs, one_mul]
  neg_mem' := by
    intro a ha s hs
    have h := ha (-s) (neg_mem hs)
    rwa [mul_neg, ← neg_mul] at h
def nIdx (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  (((intV F v).relIndex (psiDual F ψ v) : ℕ) : ℝ) / (((psiDual F ψ v).relIndex (intV F v) : ℕ) : ℝ)
def IndexFinite (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  (intV F v).relIndex (psiDual F ψ v) ≠ 0 ∧ (psiDual F ψ v).relIndex (intV F v) ≠ 0
def resCard (v : HeightOneSpectrum (𝓞 F)) : ℕ := Nat.card (𝓞 F ⧸ v.asIdeal)
def stdInf (x : Ainf F) : ℂ :=
  ∏ w : InfinitePlace F,
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (((InfinitePlace.Completion.extensionEmbedding w (x w)).re : ℝ) : ℂ))
def IsStdChar (ψ : AddChar (AF F) ℂ) : Prop :=
  IsCharAF F ψ ∧ ∀ x : Ainf F, psiInf F ψ x = stdInf F x
def IsTwist (ψ ψ₀ : AddChar (AF F) ℂ) (a : Fˣ) : Prop :=
  ∀ x : AF F, ψ x = ψ₀ (algebraMap F (AF F) (a : F) * x)
def ScalesInf (ψ : AddChar (AF F) ℂ) (a : Fˣ) : Prop :=
  ∀ x : Ainf F, psiInf F ψ x = stdInf F (algebraMap F (Ainf F) (a : F) * x)
def absInf (a : Fˣ) : ℝ := ∏ w : InfinitePlace F, w (a : F)
def diffV (v : HeightOneSpectrum (𝓞 F)) : Ideal (v.adicCompletionIntegers F) :=
  (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
def normDiffV (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  Nat.card (v.adicCompletionIntegers F ⧸ diffV F v)
variable (E : Type) [Field E] [Algebra F E]
open Classical in

def eta (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  if IsField (Fv F v ⊗[F] E) then -1 else 1
def eulerInv (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  1 - eta F E v ^ M * (resCard F v : ℝ) ^ (-(M : ℤ))
def locDens (ψ : AddChar (AF F) ℂ) (M : ℕ) (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  nIdx F ψ v ^ ((1 : ℝ) / 2 - (M : ℝ)) * eulerInv F E M v
end Defs
section Statements
variable (F : Type) [Field F] [NumberField F]
def CharsAreTwists : Prop :=
  (∃ ψ₀, IsStdChar F ψ₀) ∧
  ∀ ψ₀, IsStdChar F ψ₀ → ∀ ψ, IsCharAF F ψ → ∃! a : Fˣ, IsTwist F ψ ψ₀ a
def DifferentProduct : Prop :=
  (∀ ψ₀, IsStdChar F ψ₀ → ∀ v : HeightOneSpectrum (𝓞 F),
    (∀ t : Fv F v, t ∈ psiDual F ψ₀ v ↔
      ∀ d ∈ diffV F v, t * (d : Fv F v) ∈ v.adicCompletionIntegers F) ∧
    nIdx F ψ₀ v = (normDiffV F v : ℝ)) ∧
  (∀ v, normDiffV F v ≠ 0) ∧
  (Function.mulSupport (normDiffV F)).Finite ∧
  ((∏ᶠ v, normDiffV F v : ℕ) : ℤ) = |discr F|
variable (E : Type) [Field E] [NumberField E] [Algebra F E] [StarRing E]
def dF : ℝ := (2 * Formalism.HermitianLatticesTheory.vInv E) ^ Formalism.HermitianLatticesTheory.fDeg E
def LValue (M : ℕ) : Prop :=
  Multipliable (fun P : {P : Ideal (𝓞 E) // P.IsMaximal} => Formalism.HermitianLatticesTheory.eulerFac E M P.1) ∧
  0 < Formalism.HermitianLatticesTheory.lValEta E M ∧
  HasProd (fun v => (eulerInv F E M v)⁻¹) (Formalism.HermitianLatticesTheory.lValEta E M)
def DensityProduct (ψ : AddChar (AF F) ℂ) (a : Fˣ) (M : ℕ) : Prop :=
  (∀ v, IndexFinite F ψ v) ∧
  (∀ v, 0 < locDens F E ψ M v) ∧
  Summable (fun v => |locDens F E ψ M v - 1|) ∧
  Multipliable (locDens F E ψ M) ∧
  0 < ∏' v, locDens F E ψ M v ∧
  absInf F a ^ ((M : ℝ) - 1 / 2) * ∏' v, locDens F E ψ M v =
    dF E ^ ((1 : ℝ) / 2 - (M : ℝ)) / Formalism.HermitianLatticesTheory.lValEta E M
end Statements
def EulerProductOfDensities : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Formalism.HermitianLatticesTheory.IsCMUnram E →
    CharsAreTwists F ∧ DifferentProduct F ∧ ((|discr F| : ℤ) : ℝ) = dF E ∧
    ∀ M : ℕ, 2 ≤ M →
      LValue F E M ∧
      ∀ ψ, IsCharAF F ψ →
        (∃ a : Fˣ, ScalesInf F ψ a) ∧ ∀ a : Fˣ, ScalesInf F ψ a → DensityProduct F E ψ a M
end GlobalTheory.IndefiniteRowSideFullHecke.LocalAdditiveCharacterDual


