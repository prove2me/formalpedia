-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0464_parallel1
-- name    : PNT_ZeroFree_433_0464_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:19:16.887225+00:00
-- url     : https://prove2.me/theorems/47f1dd3c-256e-4fe8-9900-4043457259fe
-- title:
--   Zero-free region foundations: Reflection.Local, Reflection.Cofactor, Reflection.Partition, Reflection.Sector [0464_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reflection.Local
--   - OAI.NumberTheory.DirichletL.Reflection.Cofactor
--   - OAI.NumberTheory.DirichletL.Reflection.Partition
--   - OAI.NumberTheory.DirichletL.Reflection.Sector
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Local.lean#L11-L53
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Cofactor.lean#L12-L62
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Partition.lean#L9-L66
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Sector.lean#L11-L63

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0009
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0047
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0147
import Definitions.Def_PNT_ZeroFree_433_0149
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0232_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0274_parallel1
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1
import Definitions.Def_PNT_ZeroFree_433_0345_parallel1
import Definitions.Def_PNT_ZeroFree_433_0377_parallel1
import Definitions.Def_PNT_ZeroFree_433_0419_parallel1
import Definitions.Def_PNT_ZeroFree_433_0475_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Local.lean#L11-L53
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Cofactor.lean#L12-L62
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Partition.lean#L9-L66
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Sector.lean#L11-L63
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Reflection.Local
section
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open LocalReflectionBrackets
noncomputable section

lemma scalar_inverse_pair (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : c*a*b=d) : a⁻¹*b⁻¹ = d⁻¹*c := by
  field_simp
  linear_combination -h

theorem marked_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (B z : F)
    (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 0 ε =
      (-tau χ ψ 2)*(χ (-1))⁻¹^2*(χ B)^2*(χ z)^2 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  simp only [phase, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  calc
    _ = (-tau χ ψ 2)*((χ σ)⁻¹*(χ ε)⁻¹)^2 := by ring
    _ = _ := by rw [hi]; ring

theorem residual_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 1 ε =
      (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*
        (χ (-1))⁻¹^3*(χ A)*(χ B)^3*(χ z)^4 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase, show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 0 by decide,
    ↓reduceIte, show (1 : ℕ)+2 = 3 by decide,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  have hid : (χ σ)⁻¹^2*(χ ε)⁻¹^3 = (χ σ)*((χ σ)⁻¹*(χ ε)⁻¹)^3 := by
    field_simp
  calc
    _ = (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*((χ σ)⁻¹^2*(χ ε)⁻¹^3) := by ring
    _ = _ := by rw [hid,hi,hsig]; ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Reflection.Cofactor
section
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance phaseField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def markedPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (-tau χ (quotientTrace p hp) 2)*(χ (-1))⁻¹^2*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^2

def residualPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (tau χ ((quotientTrace p hp).mulShift (-1)) 1*tau χ (quotientTrace p hp) 3)*
    (χ (-1))⁻¹^3*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)))*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^3

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_marked_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 0 (D.epsilon i) =
        markedPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2 := by
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [marked_local_phase _ _ _ _ _ _ he]
  change _ = _
  simp only [markedPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

theorem controlled_residual_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 1 (D.epsilon i) =
        residualPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4 := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [residual_local_phase _ _ _ _ _ _ _ hs he]
  simp only [residualPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

end
end SevenEighths.InverseReflectedPhase

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Reflection.Partition
section
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, if_pos hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, if_neg hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

end
end SevenEighths.InverseReflectedPhase

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Reflection.Sector
section
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem separate_product_congruence {A : Type*} [CommRing A]
    (M f r r₀ P P₀ : A) (hr : M^2 ∣ r-r₀) (hP : M^2 ∣ P-P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  have h := dvd_add (dvd_mul_of_dvd_left hr P) (dvd_mul_of_dvd_right hP r₀)
  convert! dvd_mul_of_dvd_right h f using 1 ; ring

def separateSector (M r P : Eis) :
    (Eis ⧸ Ideal.span {M^2}) × (Eis ⧸ Ideal.span {M^2}) :=
  (Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ P)

theorem separateSector_product (M f r r₀ P P₀ : Eis)
    (h : separateSector M r P = separateSector M r₀ P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  apply separate_product_congruence
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.fst h))
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.snd h))

theorem separate_numerator_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M a c l f r r₀ P P₀ : Eis) (p h : ι → Eis) (p₀ h₀ : κ → Eis)
    (hc : c ∣ M) (hh : ∀ i, M^2 ∣ h i) (hh₀ : ∀ i, M^2 ∣ h₀ i)
    (hp : (∏ i, p i) = f*r*P) (hp₀ : (∏ i, p₀ i) = f*r₀*P₀)
    (hs : separateSector M r P = separateSector M r₀ P₀) :
    M*c ∣ ShortDraftCRT.finiteCrossNumerator a c l p h -
      ShortDraftCRT.finiteCrossNumerator a c l p₀ h₀ := by
  apply ShortDraftCRT.finiteCrossNumerator_fixed_sector M a c l p h p₀ h₀ hc hh hh₀
  rw [hp,hp₀]
  exact separateSector_product M f r r₀ P P₀ hs

theorem controlled_bad_phase_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (hbad : ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1) :
    ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U =
      ShortDraftCusp.A4BadPhase c hc (D₀.matrix (fun _ => 1) 1 1) D₀.U := by
  have hu : ramifiedTraceLambda^3*c ∣ D.U*(∏ i, p i)-1 := by
    refine ⟨-D.w, ?_⟩
    linear_combination D.bezout
  have hu₀ : ramifiedTraceLambda^3*c ∣ D₀.U*(∏ i, p₀ i)-1 := by
    refine ⟨-D₀.w, ?_⟩
    linear_combination D₀.bezout
  have hcop : IsCoprime (ramifiedTraceLambda^3*c) (∏ i, p i) := by
    refine ⟨D.w,D.U,?_⟩
    linear_combination D.bezout
  have he := ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c) (∏ i, p i) (∏ i, p₀ i) D.U D₀.U
    (D.matrix (fun _ => 1) 1 1) (D₀.matrix (fun _ => 1) 1 1)
    hcop (hbad.trans hr) hu hu₀ (hbad.trans hd)
  rw [ShortDraftCusp.A4BadPhase_as_fixed_residue, ShortDraftCusp.A4BadPhase_as_fixed_residue]
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr he)

end
end SevenEighths.InverseReflectedPhase

end OAI

end


