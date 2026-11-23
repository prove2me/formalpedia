-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
-- name    : Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_QuadraticClassFieldTheory
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T07:02:29.170553+00:00
-- url     : https://prove2.me/theorems/8ff0967a-aabd-42d3-8f94-8871d23855c5
-- title:
--   Quadratic Class Field Theory
-- statement:
--   Definitions and structural lemmas for Quadratic Class Field Theory, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/QuadraticClassFieldTheory.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct
namespace GlobalTheory.QuadSymbol
section Local
variable (K L : Type) [Field K] [Field L] [Algebra K L]
def globalNorms : Subgroup Kˣ := (Units.map (Algebra.norm K : L →* K)).range
def normGroup (A : Type) [CommRing A] [Algebra K A] : Subgroup Aˣ :=
  (Units.map (Algebra.norm A : A ⊗[K] L →* A)).range
open Classical in

def eta (A : Type) [CommRing A] [Algebra K A] (x : Aˣ) : ℤˣ :=
  if x ∈ normGroup K L A then 1 else -1
def toUnits (A : Type) [CommRing A] [Algebra K A] : Kˣ →* Aˣ :=
  Units.map (algebraMap K A : K →* A)
variable {K L}
end Local
section Global
variable (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L]
abbrev FinFam : Type := ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ
abbrev InfFam : Type := ∀ w : InfinitePlace K, (w.Completion)ˣ
def finDiag (t : Kˣ) : FinFam K := fun v => toUnits K (v.adicCompletion K) t
def infDiag (t : Kˣ) : InfFam K := fun w => toUnits K w.Completion t
def AlmostNorm (x : FinFam K) : Prop :=
  {v | x v ∉ normGroup K L (v.adicCompletion K)}.Finite
def EverywhereNorm (x : FinFam K) (y : InfFam K) : Prop :=
  (∀ v, x v ∈ normGroup K L (v.adicCompletion K)) ∧ ∀ w, y w ∈ normGroup K L w.Completion
def etaProd (x : FinFam K) (y : InfFam K) : ℤˣ :=
  (∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v)) *
    ∏ w : InfinitePlace K, eta K L w.Completion (y w)
def LocalCharacters : Prop :=
  (∀ (v : HeightOneSpectrum (𝓞 K)) (a b : (v.adicCompletion K)ˣ),
    eta K L (v.adicCompletion K) (a * b) = eta K L (v.adicCompletion K) a * eta K L (v.adicCompletion K) b) ∧
  ∀ (w : InfinitePlace K) (a b : (w.Completion)ˣ),
    eta K L w.Completion (a * b) = eta K L w.Completion a * eta K L w.Completion b
def NormTheorem : Prop :=
  ∀ t : Kˣ, t ∈ globalNorms K L ↔ EverywhereNorm K L (finDiag K t) (infDiag K t)
def ExactSequence : Prop :=
  (∀ t : Kˣ, AlmostNorm K L (finDiag K t)) ∧
  (∀ t : Kˣ, EverywhereNorm K L (finDiag K t) (infDiag K t) ↔ t ∈ globalNorms K L) ∧
  (∀ (x : FinFam K) (y : InfFam K), AlmostNorm K L x →
    ((∃ t : Kˣ, EverywhereNorm K L (x / finDiag K t) (y / infDiag K t)) ↔ etaProd K L x y = 1)) ∧
  ∃ (x : FinFam K) (y : InfFam K), AlmostNorm K L x ∧ etaProd K L x y = -1
def ProductFormula : Prop :=
  ∀ t : Kˣ, AlmostNorm K L (finDiag K t) ∧ etaProd K L (finDiag K t) (infDiag K t) = 1
end Global
def BaseChangeAt (F E K L A : Type) [Field F] [Field E] [Field K] [Field L] [Field A]
    [Algebra F E] [Algebra F K] [Algebra K L] [Algebra F A] : Prop :=
  ∀ (B : Type) [Field B] [Algebra A B] [FiniteDimensional A B] [Algebra K B] [Algebra F B]
    [IsScalarTower F A B] [IsScalarTower F K B] (x : Bˣ),
    eta K L B x = eta F E A (Units.map (Algebra.norm A : B →* A) x)
end GlobalTheory.QuadSymbol
namespace GlobalTheory.Published
open GlobalTheory.QuadSymbol
def QuadraticClassFieldTheory : Prop :=
  (∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [Algebra.IsQuadraticExtension K L],
    LocalCharacters K L ∧ NormTheorem K L ∧ ExactSequence K L ∧ ProductFormula K L) ∧
  (∀ (F E K L : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra F E] [Algebra F K] [Algebra K L] [Algebra E L] [Algebra F L]
    [IsScalarTower F K L] [IsScalarTower F E L]
    [Algebra.IsQuadraticExtension F E] [Algebra.IsQuadraticExtension K L],
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    (∀ v : HeightOneSpectrum (𝓞 F), BaseChangeAt F E K L (v.adicCompletion F)) ∧
    ∀ v : InfinitePlace F, BaseChangeAt F E K L v.Completion)
end GlobalTheory.Published
end


