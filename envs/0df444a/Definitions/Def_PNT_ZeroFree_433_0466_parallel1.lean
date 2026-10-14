-- Prove2me | Definitions.Def_PNT_ZeroFree_433_0466_parallel1
-- name    : PNT_ZeroFree_433_0466_parallel1
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-11T14:23:54.03202+00:00
-- url     : https://prove2.me/theorems/94be5e69-2d76-44d8-91c1-0f8782fad957
-- title:
--   Zero-free region foundations: Reflection.Frozen, Reflection.Cross [0466_parallel1]
-- statement:
--   Definitions and proved supporting lemmas from the following source modules:
--
--   - OAI.NumberTheory.DirichletL.Reflection.Frozen
--   - OAI.NumberTheory.DirichletL.Reflection.Cross
--
--   These declarations form part of the analytic and arithmetic foundations of the Dirichlet L-function nonvanishing argument in the half-plane Re(s) > 7/8. The original namespaces and hypotheses are retained. The code is ported to Lean 4.33.1 and the pinned Mathlib environment; every included lemma has a complete proof.
-- source:
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Frozen.lean#L13-L102
--   https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Cross.lean#L9-L102

import Definitions.Def_PNT_ZeroFree_433_0007
import Definitions.Def_PNT_ZeroFree_433_0031
import Definitions.Def_PNT_ZeroFree_433_0041
import Definitions.Def_PNT_ZeroFree_433_0061
import Definitions.Def_PNT_ZeroFree_433_0150
import Definitions.Def_PNT_ZeroFree_433_0150_parallel1
import Definitions.Def_PNT_ZeroFree_433_0229_parallel1
import Definitions.Def_PNT_ZeroFree_433_0240_parallel1
import Definitions.Def_PNT_ZeroFree_433_0280_parallel1
import Definitions.Def_PNT_ZeroFree_433_0292_parallel1
import Definitions.Def_PNT_ZeroFree_433_0293_parallel1
import Definitions.Def_PNT_ZeroFree_433_0294_parallel1
import Definitions.Def_PNT_ZeroFree_433_0306_parallel1
import Definitions.Def_PNT_ZeroFree_433_0326_parallel1
import Definitions.Def_PNT_ZeroFree_433_0339_parallel1
import Definitions.Def_PNT_ZeroFree_433_0366_parallel1
import Definitions.Def_PNT_ZeroFree_433_0369_parallel1
import Definitions.Def_PNT_ZeroFree_433_0391_parallel1
import Definitions.Def_PNT_ZeroFree_433_0439_parallel1
import Definitions.Def_PNT_ZeroFree_433_0464_parallel1
import Definitions.Def_PNT_ZeroFree_433_0480_parallel1
import Definitions.Def_PNT_ZeroFree_433_0600_parallel1
import Definitions.Def_PNT_ZeroFree_433_0616_parallel1
import Definitions.Def_PNT_ZeroFree_433_0623_parallel1

/- Supporting zero-free-region lemmas, grouped by intact source scopes.
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Frozen.lean#L13-L102
https://github.com/OpenAI/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/OAI/NumberTheory/DirichletL/Reflection/Cross.lean#L9-L102
-/
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

-- Source module: OAI.NumberTheory.DirichletL.Reflection.Frozen
section
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma scalar_phase_power (a b : ℂ) (ha : a ≠ 0) (j : ℕ) :
    a⁻¹^2*b⁻¹^(j+2) = a^j*(a⁻¹*b⁻¹)^(j+2) := by
  symm
  calc
    _ = (a^j*(a⁻¹)^j)*(a⁻¹)^2*(b⁻¹)^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by rw [← mul_pow,mul_inv_cancel₀ ha,one_pow,one_mul]

theorem general_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1)
    (j : ℕ) (hj0 : j ≠ 0) (hj4 : j ≠ 4) :
    ((χ⁻¹)^2) σ * phase χ ψ j ε =
      (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2)) *
        (χ (-1))⁻¹^(j+2)*(χ A)^j*(χ B)^(j+2)*(χ z)^(2*j+2) := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase,hj4,hj0,↓reduceIte,MulChar.pow_apply_coe,MulChar.inv_apply_eq_inv']
  calc
    _ = (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2))*((χ σ)⁻¹^2*(χ ε)⁻¹^(j+2)) := by ring
    _ = _ := by
      rw [scalar_phase_power _ _ hs j,hi,hsig]
      simp only [mul_pow,pow_add,show 2*j=j+j by omega]
      ring

theorem exceptional_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A z : F)
    (hsigma : (σ : F) = A*z) :
    ((χ⁻¹)^2) σ * phase χ ψ 4 ε =
      (tau χ (ψ.mulShift (-1)) 4*(χ A)⁻¹^2)*(χ z)⁻¹^2 := by
  simp only [phase,↓reduceIte,hsigma,map_mul,
    ]
  simp only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
  ring

noncomputable local instance frozenField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance frozenFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenPrimeScalar (p c : Eis) [(Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  if j=4 then tau χ ((quotientTrace p hp).mulShift (-1)) 4*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))⁻¹^2
  else if j=0 then markedPrimeScalar p c hp hg
  else (tau χ ((quotientTrace p hp).mulShift (-1)) j*tau χ (quotientTrace p hp) (j+2)) *
    (χ (-1))⁻¹^(j+2)*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))^j*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c)))^(j+2)

def frozenCofactorCharacter (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (j : ℕ) : Eis →* ℂ :=
  (if j=4 then ((actualSextic P hg)⁻¹)^2 else (actualSextic P hg)^(2*j+2)).toMonoidHom.comp
    (Ideal.Quotient.mk P).toMonoidHom

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_frozen_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) (j : ℕ) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i) =
    frozenPrimeScalar (p i) c (hp i) (hg i) j *
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i) := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  by_cases hj4 : j=4
  · subst j
    rw [exceptional_local_phase _ _ _ _ _ _ hs]
    simp only [frozenPrimeScalar,frozenCofactorCharacter,↓reduceIte,MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
    rfl
  · by_cases hj0 : j=0
    · subst j
      rw [marked_local_phase _ _ _ _ _ _ he]
      simp [frozenPrimeScalar,frozenCofactorCharacter,markedPrimeScalar,
        MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
    · rw [general_local_phase _ _ _ _ _ _ _ hs he j hj0 hj4]
      simp only [frozenPrimeScalar,frozenCofactorCharacter,hj4,hj0,↓reduceIte,
        MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MulChar.coe_toMonoidHom,MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0)]
      rfl

end
end SevenEighths.InverseReflectedPhase

end OAI

end

-- Source module: OAI.NumberTheory.DirichletL.Reflection.Cross
section
namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B U : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = U) :
    (∏ i ∈ U, ((∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : U.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, if_pos hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : U.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, if_neg hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

theorem ordered_cross_frozen_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F)
    (hu : (R ∪ P) ∪ F = Finset.univ) :
    (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      (∏ i ∈ R, (∏ k ∈ R.erase i, x i k^a)*(l i*∏ k ∈ F, x i k^a)) *
      (∏ i ∈ P, (∏ k ∈ P.erase i, x i k^b)*(l i*∏ k ∈ F, x i k^b)) *
      (∏ i ∈ R, ∏ k ∈ P, x i k^a*x k i^b) := by
  let ll := fun i => l i*∏ k ∈ F, x i k ^ (if i ∈ R then a else b)
  have hx : (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      ∏ i ∈ R ∪ P, (∏ k ∈ (R ∪ P).erase i,
        x i k ^ (if i ∈ R then a else b))*ll i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ F := fun hf => Finset.disjoint_left.mp hF hi hf
    have he : Finset.univ.erase i = (R ∪ P).erase i ∪ F := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk,or_assoc]
    rw [he,Finset.prod_union (hF.mono_left (Finset.erase_subset _ _))]
    dsimp [ll]
    ring
  rw [hx,ordered_cross_partition_on x ll a b R P (R ∪ P) hRP rfl]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [ll,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [ll,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI

end


