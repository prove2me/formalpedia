-- Prove2me | Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
-- name    : OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T22:18:48.852202+00:00
-- url     : https://prove2.me/theorems/3ea627c8-4653-418c-b6c4-ccbacd935f9a
-- title:
--   Finite Fourier
-- statement:
--   Definitions and structural lemmas for Finite Fourier, from LW56e2 and the credited OpenAI and dependency authors's pinned QRH LW56e2 refinement development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
namespace ShortDraftFiniteGaussFourier
open scoped Classical
open AddChar MulChar
variable {F : Type*} [Field F] [Fintype F]
end ShortDraftFiniteGaussFourier
namespace PoissonChildCRT
open scoped Classical
variable (n : ℕ) (χ : MulChar (ZMod n) ℂ)
def mask (n m : ℕ) : ℂ := if n.Coprime m then 1 else 0
end PoissonChildCRT
namespace PoissonFirstLocal
open scoped Classical
def bit (b : Bool) : ℕ := if b then 1 else 0
def localE (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)
def cExp₁ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 0 else ((1 : ZMod 6) + localE parityBit ε₁ ε₂).val
def cExp₂ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if localE parityBit ε₁ ε₂ = 0 then 0 else ((1 : ZMod 6) - localE parityBit ε₁ ε₂).val
def EExp (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0
def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)
def totalExp₁ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  4 * bit ε₁ + cExp₁ parityBit ε₁ ε₂ + EExp parityBit ε₁ ε₂
def totalExp₂ (parityBit ε₁ ε₂ : Bool) : ℕ :=
  4 * bit ε₂ + cExp₂ parityBit ε₁ ε₂ + EExp parityBit ε₁ ε₂
def mask (n p : ℕ) : ℂ := if n.Coprime p then 1 else 0
def oldFactor (side : Bool) (parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) : ℂ :=
  let q := χ (p : ZMod n)
  mask n p * q ^ (4 * bit (if side then ε₂ else ε₁)) *
    q ^ (if side then cExp₂ parityBit ε₁ ε₂ else cExp₁ parityBit ε₁ ε₂) *
    q ^ EExp parityBit ε₁ ε₂
def newFactor (parityBit ε₁ ε₂ : Bool)
    (n p : ℕ) (χ : MulChar (ZMod n) ℂ) : ℂ :=
  if retained parityBit ε₁ ε₂ then (χ (p : ZMod n)) ^ 4 else mask n p
end PoissonFirstLocal
open Finset Complex
namespace ActualCubicChar
variable {R F : Type*} [CommRing R] [IsDomain R] [Field F]
omit [IsDomain R] in
theorem cubic_roots_surjective (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    Function.Surjective (restrictRootsOfUnity ρ 3) := by
  intro η
  have hη : ((η : Fˣ) : F) ^ 3 = 1 := by
    exact (mem_rootsOfUnity' 3 (η : Fˣ)).mp η.property
  obtain ⟨j, _, hj⟩ := hζF.eq_pow_of_pow_eq_one hη
  let z : rootsOfUnity 3 R := rootsOfUnity.mkOfPowEq ζ hζ.pow_eq_one
  refine ⟨z ^ j, ?_⟩
  apply rootsOfUnity.coe_injective
  change ρ (ζ ^ j) = ((η : Fˣ) : F)
  rw [map_pow]
  exact hj
noncomputable def cubic_roots_equiv (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3) :
    rootsOfUnity 3 R ≃* rootsOfUnity 3 F := by
  classical
  letI : Fintype (rootsOfUnity 3 R) := Fintype.ofFinite _
  letI : Fintype (rootsOfUnity 3 F) := Fintype.ofFinite _
  apply MulEquiv.ofBijective (restrictRootsOfUnity ρ 3)
  apply (Fintype.bijective_iff_surjective_and_card _).2
  constructor
  · exact cubic_roots_surjective ρ ζ hζ hζF
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      hζ.card_rootsOfUnity, hζF.card_rootsOfUnity]
variable [Fintype F]
def euler_to_roots (m : ℕ) (hq : Fintype.card F - 1 = m * 3) :
    Fˣ →* rootsOfUnity 3 F where
  toFun u := rootsOfUnity.mkOfPowEq ((u : F) ^ m) (by
    rw [← pow_mul, ← hq]
    exact FiniteField.pow_card_sub_one_eq_one (u : F) u.ne_zero)
  map_one' := by
    apply rootsOfUnity.coe_injective
    simp
  map_mul' u v := by
    apply rootsOfUnity.coe_injective
    simp [mul_pow]
noncomputable def cubicResidueChar (ρ : R →+* F) (ζ : R)
    (hζ : IsPrimitiveRoot ζ 3) (hζF : IsPrimitiveRoot (ρ ζ) 3)
    (m : ℕ) (hq : Fintype.card F - 1 = m * 3) : MulChar F R :=
  MulChar.ofUnitHom <|
    (Subgroup.subtype _).comp <|
      (cubic_roots_equiv ρ ζ hζ hζF).symm.toMonoidHom.comp
        (euler_to_roots m hq)
end ActualCubicChar
namespace ActualEisensteinCubic
section
open NumberField
abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K
instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ
def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger
def lambda : O := omega - 1
noncomputable instance quotientFintype (P : Ideal O) [P.IsMaximal] :
    Fintype (O ⧸ P) := Fintype.ofFinite _
noncomputable instance quotientField (P : Ideal O) [P.IsMaximal] :
    Field (O ⧸ P) := Ideal.Quotient.field P
theorem omega_primitive : IsPrimitiveRoot omega 3 := by
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_isPrimitiveRoot
def traceLambda : O := 1 + 2 * omega
theorem traceLambda_eq_unit_mul_lambda : traceLambda = -omega * lambda := by
  have hrel : omega ^ 2 + omega + 1 = 0 := by
    simpa only [IsCyclotomicExtension.Rat.Three.coe_eta, omega] using
      (IsCyclotomicExtension.Rat.Three.eta_sq_add_eta_add_one
        (IsCyclotomicExtension.zeta_spec 3 ℚ K))
  dsimp [traceLambda, lambda]
  linear_combination hrel
theorem neg_omega_isUnit : IsUnit (-omega) :=
  (omega_primitive.isUnit (by decide)).neg
theorem traceLambda_mem_iff (P : Ideal O) : traceLambda ∈ P ↔ lambda ∈ P := by
  rw [traceLambda_eq_unit_mul_lambda, mul_comm]
  exact P.mul_unit_mem_iff_mem neg_omega_isUnit
theorem omega_reduced_primitive (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    IsPrimitiveRoot (Ideal.Quotient.mk P omega) 3 := by
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let ρ : O →+* O ⧸ P := Ideal.Quotient.mk P
  have hpow : (ρ omega) ^ 3 = 1 := by
    rw [← map_pow, omega_primitive.pow_eq_one, map_one]
  have hne : ρ omega ≠ 1 := by
    intro he
    apply hgood
    have hz : ρ (omega - 1) = 0 := by rw [map_sub, he, map_one, sub_self]
    exact (Ideal.Quotient.eq_zero_iff_mem).mp hz
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) hpow
  intro l hl0 hl3
  have hl : l = 1 ∨ l = 2 := by omega
  rcases hl with rfl | rfl
  · simpa using hne
  · intro h2
    apply hne
    calc
      ρ omega = (ρ omega) ^ 2 * ρ omega := by rw [h2, one_mul]
      _ = (ρ omega) ^ 3 := by ring
      _ = 1 := hpow
theorem card_sub_one_div_three (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) :
    3 ∣ Nat.card (O ⧸ P) - 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let hζ := omega_reduced_primitive P hgood
  let u : (O ⧸ P)ˣ := (hζ.isUnit (by decide)).unit
  have hu : IsPrimitiveRoot u 3 := hζ.isUnit_unit (by decide)
  have h := orderOf_dvd_natCard u
  rw [← hu.eq_orderOf] at h
  simpa only [Nat.card_eq_fintype_card, Fintype.card_units] using h
noncomputable def cubicChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  let m := (Fintype.card (O ⧸ P) - 1) / 3
  have hq : Fintype.card (O ⧸ P) - 1 = m * 3 :=
    (Nat.div_mul_cancel (by simpa only [Nat.card_eq_fintype_card] using
      card_sub_one_div_three P hgood)).symm
  exact ActualCubicChar.cubicResidueChar (Ideal.Quotient.mk P) omega
    omega_primitive (omega_reduced_primitive P hgood) m hq
noncomputable def conjK : K ≃ₐ[ℚ] K :=
  IsCyclotomicExtension.fromZetaAut
    ((IsCyclotomicExtension.zeta_spec 3 ℚ K).pow_of_coprime 2 (by decide))
    (Polynomial.cyclotomic.irreducible_rat (by decide))
noncomputable def conjO : O ≃+* O :=
  RingOfIntegers.mapRingEquiv conjK.toRingEquiv
end
noncomputable def quadraticCharO (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) O := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite _
  exact (quadraticChar (O ⧸ P)).ringHomComp (Int.castRingHom O)
noncomputable def sexticChar (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) : MulChar (O ⧸ P) O :=
  cubicChar P hgood ^ 2 * quadraticCharO P
theorem hgood_from_trace (P : Ideal O) (hgood : traceLambda ∉ P) :
    lambda ∉ P := by
  intro h
  exact hgood ((traceLambda_mem_iff P).mpr h)
noncomputable def complexEmbedding : K →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift
noncomputable def ringComplex : O →+* ℂ :=
  complexEmbedding.toRingHom.comp (algebraMap O K)
end ActualEisensteinCubic
end
end OAI


