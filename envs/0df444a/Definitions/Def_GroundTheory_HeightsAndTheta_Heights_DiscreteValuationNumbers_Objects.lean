-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:26.167839+00:00
-- url     : https://prove2.me/theorems/650ba4bf-a16a-4201-93af-47ac185fe1d5
-- title:
--   Objects
-- statement:
--   Definitions and structural lemmas for Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/Objects.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
section Ring
variable {K : Type*} (ι : K → Type*)
abbrev MRing (R : Type*) [CommRing R] : Type _ := MvPolynomial (Σ k, ι k) R
variable [DecidableEq K]
def blockWeight : (Σ k, ι k) → K → ℕ := fun v => Pi.single v.1 1
variable {ι} {R : Type*} [CommRing R]
def IsMultiHomog (f : MRing ι R) (b : K → ℕ) : Prop :=
  IsWeightedHomogeneous (blockWeight ι) f b
def IsMultiHomogIdeal (I : Ideal (MRing ι R)) : Prop :=
  ∀ f ∈ I, ∀ b : K → ℕ, weightedHomogeneousComponent (blockWeight ι) b f ∈ I
def IsRelevant (I : Ideal (MRing ι R)) : Prop :=
  ∀ k, ∃ i : ι k, (X ⟨k, i⟩ : MRing ι R) ∉ I
structure IsMultiProjPrime (P : Ideal (MRing ι R)) : Prop where
  isPrime : P.IsPrime
  multiHomog : IsMultiHomogIdeal P
  relevant : IsRelevant P
end Ring
section Cycles
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
def multAt (J W : Ideal (MRing ι R)) [W.IsPrime] : ℕ∞ :=
  Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (MRing ι R ⧸ J))
open Classical in

def divCycle (P : Ideal (MRing ι R)) (f : MRing ι R) (W : Ideal (MRing ι R)) : ℤ :=
  if h : W ∈ (P ⊔ Ideal.span {f}).minimalPrimes ∧ IsRelevant W then
    haveI : W.IsPrime := h.1.1.1
    ((multAt (P ⊔ Ideal.span {f}) W).toNat : ℤ)
  else 0
def ratDiv (P : Ideal (MRing ι R)) (f g : MRing ι R) (W : Ideal (MRing ι R)) : ℤ :=
  divCycle P f W - divCycle P g W
def cycEval (n : Ideal (MRing ι R) → ℤ) (Z : Ideal (MRing ι R) → ℤ) : ℤ :=
  ∑ᶠ W, Z W * n W
end Cycles
section Field
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
def gradedPiece (P : Ideal (MRing ι F)) (m : K → ℕ) : Submodule F (MRing ι F ⧸ P) :=
  (weightedHomogeneousSubmodule F (blockWeight ι) m).map (Ideal.Quotient.mkₐ F P).toLinearMap
open Classical in

def hilbFn (P : Ideal (MRing ι F)) (m : K → ℤ) : ℤ :=
  if ∀ k, 0 ≤ m k then (Module.finrank F (gradedPiece P (fun k => (m k).toNat)) : ℤ) else 0
def diffStep (b : K → ℤ) (h : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  fun m => h m - h (m - b)
def mixedDiff {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) : (K → ℤ) → ℤ :=
  (List.ofFn bs).foldr diffStep h
open Classical in

def eventualValue (f : (K → ℤ) → ℤ) : ℤ :=
  if h : ∃ c, ∀ᶠ m in Filter.atTop, f m = c then h.choose else 0
def intNum (F : Type*) [Field F] (P : Ideal (MRing ι F)) {n : ℕ} (bs : Fin n → K → ℤ) : ℤ :=
  eventualValue (mixedDiff bs (hilbFn P))
end Field
section DVR
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
def specialIdeal (W : Ideal (MRing ι O)) : Ideal (MRing ι (IsLocalRing.ResidueField O)) :=
  W.map (MvPolynomial.map (IsLocalRing.residue O))
def genFib (P : Ideal (MRing ι O)) : Ideal (MRing ι (FractionRing O)) :=
  P.map (MvPolynomial.map (algebraMap O (FractionRing O)))
def vNum (W : Ideal (MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) : ℤ :=
  intNum (IsLocalRing.ResidueField O) (specialIdeal W) bs
def gNum (P : Ideal (MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) : ℤ :=
  intNum (FractionRing O) (genFib P) bs
structure IsModelOver [Fintype K] (P : Ideal (MRing ι O)) (d : ℕ) : Prop where
  multiProj : IsMultiProjPrime P
  noTorsion : P.comap (C : O →+* MRing ι O) = ⊥
  dim : ringKrullDim (MRing ι O ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)
structure IsVerticalDivisor (P : Ideal (MRing ι O)) (ϖ : O) (b : K → ℤ) (f g : MRing ι O) :
    Prop where
  degrees : ∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧
    (fun k => (bf k : ℤ) - bg k) = b
  num_not_mem : f ∉ P
  den_not_mem : g ∉ P
  vertical : ∀ W, ratDiv P f g W ≠ 0 → (C ϖ : MRing ι O) ∈ W
  unit_off_special : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W →
    (C ϖ : MRing ι O) ∉ W → ∃ u v : MRing ι O, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ P
end DVR
section Examples
variable {K : Type*} [DecidableEq K] {ι : K → Type*}
end Examples
end
end GroundTheory.Heights₂.Heights.NumbersDVR


