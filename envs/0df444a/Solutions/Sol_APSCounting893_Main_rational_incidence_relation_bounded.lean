-- Prove2me | solution 1 for APSCounting893.Main.rational_incidence_relation_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:25:06.413357+00:00
-- url     : https://prove2.me/submissions/d07dad55-31bd-4b76-adc8-76d04e31cc35

import Definitions.Def_APSCounting893_Main_Geometry
import Definitions.Def_APSCounting893_Main_Resultant
import Mathlib
import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.AlgebraicIndependent.Basic
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.JacobiZariski
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Smooth.Field
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

section Component_0
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma isFractionRing_of_localization_then_fraction {R S T : Type}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (M : Submonoid R) [IsLocalization M S] [IsFractionRing S T]
    (hM : M ≤ nonZeroDivisors R) : IsFractionRing R T := by
  have hinj := IsLocalization.injective S hM
  have heq : (nonZeroDivisors S).comap (algebraMap R S) = nonZeroDivisors R := by
    ext x
    simp only [Submonoid.mem_comap,mem_nonZeroDivisors_iff_ne_zero]
    exact not_congr (map_eq_zero_iff _ hinj)
  have hh := IsLocalization.localization_localization_isLocalization_of_has_all_units
    M (nonZeroDivisors S) T (fun x hx => hx.mem_nonZeroDivisors)
  rwa [heq] at hh

/-- The coefficient fraction field is the fraction field of the two-block polynomial ring. -/
lemma polynomial_fraction_field_isFractionRing (K : Type) [Field K] (ι κ : Type) :
    let A := MvPolynomial ι K
    let E := FractionRing A
    let R := MvPolynomial κ A
    let S := MvPolynomial κ E
    let T := FractionRing S
    letI : Algebra R S := MvPolynomial.algebraMvPolynomial
    letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    IsFractionRing R T := by
  intro A E R S T
  letI : Algebra R S := MvPolynomial.algebraMvPolynomial
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : SMul R S := Algebra.toSMul
  letI : SMul S T := Algebra.toSMul
  letI : SMul R T := Algebra.toSMul
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let M := (nonZeroDivisors A).map (MvPolynomial.C : A →+* R)
  letI : IsLocalization M S := MvPolynomial.isLocalization (nonZeroDivisors A) E
  apply isFractionRing_of_localization_then_fraction (R := R) (S := S) (T := T) M
  rintro x ⟨a,ha,rfl⟩
  rw [mem_nonZeroDivisors_iff_ne_zero]
  simpa only [map_zero] using ((MvPolynomial.C_injective κ A : Function.Injective (MvPolynomial.C : A →+* R)).ne (nonZeroDivisors.ne_zero ha))

end APSCounting893.Main
end Component_0

section Component_1
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

noncomputable def parameterFieldEmbedding (K : Type) [Field K] (ι κ : Type) :
    FractionRing (MvPolynomial κ K) →ₐ[K] FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K))) := by
  let A := MvPolynomial ι K
  let E := FractionRing A
  let R := MvPolynomial κ K
  let S := MvPolynomial κ E
  let T := FractionRing S
  let g : R →ₐ[K] T := (IsScalarTower.toAlgHom K S T).comp
    { toRingHom := MvPolynomial.map (algebraMap K E)
      commutes' := by intro c; exact MvPolynomial.map_C (algebraMap K E) c }
  apply IsFractionRing.liftAlgHom (g := g)
  exact (IsFractionRing.injective S T).comp
    (MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective)

lemma parameterFieldEmbedding_on_polynomial (K : Type) [Field K] (ι κ : Type)
    (p : MvPolynomial κ K) :
    parameterFieldEmbedding K ι κ (algebraMap _ (FractionRing (MvPolynomial κ K)) p) =
      algebraMap _ (FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K))))
        (MvPolynomial.map (algebraMap K (FractionRing (MvPolynomial ι K))) p) := by
  unfold parameterFieldEmbedding
  apply IsFractionRing.lift_algebraMap
  exact (IsFractionRing.injective (MvPolynomial κ (FractionRing (MvPolynomial ι K))) _).comp
    (MvPolynomial.map_injective (algebraMap K (FractionRing (MvPolynomial ι K))) (algebraMap K _).injective)

end APSCounting893.Main
end Component_1

section Component_2
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

noncomputable def parameterPolynomialEmbedding (K : Type) [Field K] (ι κ : Type) :
    MvPolynomial ι (FractionRing (MvPolynomial κ K)) →+*
      FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K))) :=
  MvPolynomial.eval₂Hom (parameterFieldEmbedding K ι κ).toRingHom
    (fun i => algebraMap _ (FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K))))
      ((MvPolynomial.C : FractionRing (MvPolynomial ι K) →+* MvPolynomial κ (FractionRing (MvPolynomial ι K)))
        (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (MvPolynomial.X i))))

lemma parameterPolynomialEmbedding_isFractionRing (K : Type) [Field K] (ι κ : Type) :
    let U := MvPolynomial ι (FractionRing (MvPolynomial κ K))
    let T := FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K)))
    letI : Algebra U T := (parameterPolynomialEmbedding K ι κ).toAlgebra
    IsFractionRing U T := by
  let A := MvPolynomial ι K
  let E := FractionRing A
  let B := MvPolynomial κ K
  let H := FractionRing B
  let R := MvPolynomial κ A
  let S := MvPolynomial κ E
  let T := FractionRing S
  let V := MvPolynomial ι B
  let U := MvPolynomial ι H
  letI : Algebra V U := MvPolynomial.algebraMvPolynomial
  letI : Algebra U T := (parameterPolynomialEmbedding K ι κ).toAlgebra
  letI : Algebra V T := ((algebraMap U T).comp (algebraMap V U)).toAlgebra
  letI : SMul V U := Algebra.toSMul
  letI : SMul U T := Algebra.toSMul
  letI : SMul V T := Algebra.toSMul
  letI : IsScalarTower V U T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsFractionRing R T := polynomial_fraction_field_isFractionRing K ι κ
  have hcomp : algebraMap V T = (parameterPolynomialEmbedding K ι κ).comp (MvPolynomial.map (algebraMap B H)) := rfl
  have hcomm (q : V) : algebraMap V T q =
      algebraMap R T (MvPolynomial.commAlgEquiv K ι κ q) := by
    have heq : (algebraMap V T) = (algebraMap R T).comp (MvPolynomial.commAlgEquiv K ι κ).toRingHom := by
      rw [hcomp]
      apply MvPolynomial.ringHom_ext
      · intro p
        change parameterPolynomialEmbedding K ι κ (MvPolynomial.map (algebraMap B H) (MvPolynomial.C p)) =
          algebraMap S T (MvPolynomial.map (algebraMap A E) (MvPolynomial.commAlgEquiv K ι κ (MvPolynomial.C p)))
        rw [MvPolynomial.map_C,parameterPolynomialEmbedding,MvPolynomial.eval₂Hom_C]
        change parameterFieldEmbedding K ι κ (algebraMap B H p) = _
        rw [parameterFieldEmbedding_on_polynomial,MvPolynomial.commAlgEquiv_C,MvPolynomial.map_map]
        rfl
      · intro i
        change parameterPolynomialEmbedding K ι κ (MvPolynomial.map (algebraMap B H) (MvPolynomial.X i)) =
          algebraMap S T (MvPolynomial.map (algebraMap A E) (MvPolynomial.commAlgEquiv K ι κ (MvPolynomial.X i)))
        rw [MvPolynomial.map_X,parameterPolynomialEmbedding,MvPolynomial.eval₂Hom_X',
          MvPolynomial.commAlgEquiv_X,MvPolynomial.map_C]
    exact RingHom.congr_fun heq q
  letI : IsFractionRing V T := IsFractionRing.of_ringEquiv_left
    (MvPolynomial.commAlgEquiv K ι κ).toRingEquiv hcomm
  let M := (nonZeroDivisors B).map (MvPolynomial.C : B →+* V)
  letI : IsLocalization M U := MvPolynomial.isLocalization (nonZeroDivisors B) H
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M U T

end APSCounting893.Main
end Component_2

section Component_3
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

lemma parameterPolynomialEmbedding_C (K : Type) [Field K] (ι κ : Type)
    (a : FractionRing (MvPolynomial κ K)) :
    parameterPolynomialEmbedding K ι κ (MvPolynomial.C a) = parameterFieldEmbedding K ι κ a :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma parameterPolynomialEmbedding_X (K : Type) [Field K] (ι κ : Type) (i : ι) :
    parameterPolynomialEmbedding K ι κ (MvPolynomial.X i) =
      algebraMap (MvPolynomial κ (FractionRing (MvPolynomial ι K))) (FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K))))
        (MvPolynomial.C (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) (MvPolynomial.X i))) :=
  MvPolynomial.eval₂Hom_X' _ _ _

lemma parameterPolynomialEmbedding_map (K : Type) [Field K] (ι κ : Type) (p : MvPolynomial ι K) :
    parameterPolynomialEmbedding K ι κ (MvPolynomial.map (algebraMap K (FractionRing (MvPolynomial κ K))) p) =
      algebraMap (MvPolynomial κ (FractionRing (MvPolynomial ι K))) (FractionRing (MvPolynomial κ (FractionRing (MvPolynomial ι K))))
        (MvPolynomial.C (algebraMap (MvPolynomial ι K) (FractionRing (MvPolynomial ι K)) p)) := by
  let E := FractionRing (MvPolynomial ι K)
  let H := FractionRing (MvPolynomial κ K)
  let S := MvPolynomial κ E
  let T := FractionRing S
  have heq : (parameterPolynomialEmbedding K ι κ).comp (MvPolynomial.map (algebraMap K H)) =
      (algebraMap S T).comp ((MvPolynomial.C : E →+* S).comp (algebraMap (MvPolynomial ι K) E)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp,Function.comp_apply,MvPolynomial.map_C,
        parameterPolynomialEmbedding_C]
      rw [(parameterFieldEmbedding K ι κ).commutes]
      rfl
    · intro i
      simp only [RingHom.coe_comp,Function.comp_apply,MvPolynomial.map_X,parameterPolynomialEmbedding_X]
      rfl
  exact RingHom.congr_fun heq p

end APSCounting893.Main
end Component_3

section Component_4
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def coefficientDerivationLinear {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) : MvPolynomial σ E →ₗ[K] MvPolynomial σ E :=
  { toFun := AddMonoidAlgebra.map δ.toAddMonoidHom
    map_add' := by
      intro p q
      ext e
      change δ ((p+q).coeff e) = δ (p.coeff e)+δ (q.coeff e)
      rw [MvPolynomial.coeff_add,map_add]
    map_smul' := by
      intro c p
      ext e
      change δ ((c • p).coeff e) = (c • AddMonoidAlgebra.map δ.toAddMonoidHom p).coeff e
      simp only [MvPolynomial.coeff_smul]
      exact δ.map_smul c (p.coeff e) }

lemma coefficientDerivationLinear_monomial {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (e : σ →₀ ℕ) (c : E) :
    coefficientDerivationLinear δ (MvPolynomial.monomial e c) = MvPolynomial.monomial e (δ c) := by
  classical
  ext b
  change δ ((MvPolynomial.monomial e c).coeff b) = (MvPolynomial.monomial e (δ c)).coeff b
  by_cases hb : e=b <;> simp [MvPolynomial.coeff_monomial,hb]

lemma coefficientDerivationLinear_leibniz {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (p q : MvPolynomial σ E) :
    coefficientDerivationLinear δ (p*q) = p*coefficientDerivationLinear δ q + q*coefficientDerivationLinear δ p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | monomial b d =>
      simp only [MvPolynomial.monomial_mul,coefficientDerivationLinear_monomial,Derivation.leibniz,
        smul_eq_mul,map_add,add_comm]
    | add q₁ q₂ h₁ h₂ => simp only [mul_add,map_add,h₁,h₂,add_mul]; abel
  | add p₁ p₂ h₁ h₂ => simp only [add_mul,map_add,h₁,h₂,mul_add]; abel

noncomputable def mvCoefficientDerivation {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) : Derivation K (MvPolynomial σ E) (MvPolynomial σ E) where
  toLinearMap := coefficientDerivationLinear δ
  map_one_eq_zero' := by
    change coefficientDerivationLinear δ (MvPolynomial.monomial 0 1) = 0
    rw [coefficientDerivationLinear_monomial,δ.map_one_eq_zero,MvPolynomial.monomial_zero]
  leibniz' := coefficientDerivationLinear_leibniz δ

lemma mvCoefficientDerivation_C {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (c : E) :
    mvCoefficientDerivation (σ := σ) δ (MvPolynomial.C c) = MvPolynomial.C (δ c) := by
  exact coefficientDerivationLinear_monomial δ 0 c

lemma mvCoefficientDerivation_X {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (j : σ) :
    mvCoefficientDerivation δ (MvPolynomial.X j) = 0 := by
  change coefficientDerivationLinear δ (MvPolynomial.monomial (Finsupp.single j 1) 1) = 0
  rw [coefficientDerivationLinear_monomial,δ.map_one_eq_zero,MvPolynomial.monomial_zero]

end APSCounting893.Main
end Component_4

section Component_5
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

lemma mvCoefficientDerivation_map_eq_zero {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (p : MvPolynomial σ K) :
    mvCoefficientDerivation δ (MvPolynomial.map (algebraMap K E) p) = 0 := by
  ext e
  change δ ((MvPolynomial.map (algebraMap K E) p).coeff e) = 0
  rw [MvPolynomial.coeff_map]
  exact δ.map_algebraMap _

noncomputable def mvCoefficientDerivationOverVariables {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) : Derivation (MvPolynomial σ K) (MvPolynomial σ E) (MvPolynomial σ E) where
  toLinearMap :=
    { toFun := mvCoefficientDerivation δ
      map_add' := (mvCoefficientDerivation δ).map_add
      map_smul' := by
        intro a p
        change mvCoefficientDerivation δ (algebraMap (MvPolynomial σ K) (MvPolynomial σ E) a * p) =
          algebraMap (MvPolynomial σ K) (MvPolynomial σ E) a * mvCoefficientDerivation δ p
        rw [(mvCoefficientDerivation δ).leibniz]
        change _ + p*mvCoefficientDerivation δ (MvPolynomial.map (algebraMap K E) a) = _
        rw [mvCoefficientDerivation_map_eq_zero,mul_zero,add_zero,smul_eq_mul] }
  map_one_eq_zero' := (mvCoefficientDerivation δ).map_one_eq_zero
  leibniz' := (mvCoefficientDerivation δ).leibniz

lemma mvCoefficientDerivationOverVariables_C {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (c : E) :
    mvCoefficientDerivationOverVariables (σ := σ) δ (MvPolynomial.C c) = MvPolynomial.C (δ c) :=
  mvCoefficientDerivation_C δ c

lemma mvCoefficientDerivationOverVariables_X {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (δ : Derivation K E E) (j : σ) :
    mvCoefficientDerivationOverVariables δ (MvPolynomial.X j) = 0 :=
  mvCoefficientDerivation_X δ j

end APSCounting893.Main
end Component_5

section Component_6
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

noncomputable def genericLinearValues {E : Type} [CommRing E] {m r : ℕ} (f : Fin m → E) :
    Fin r → MvPolynomial (Fin r × Fin m) E :=
  fun i => ∑ a : Fin m, MvPolynomial.X (i,a)*MvPolynomial.C (f a)

lemma genericLinearValues_derivation {K E : Type} [CommRing K] [CommRing E] [Algebra K E]
    {m r : ℕ} (δ : Derivation K E E) (f : Fin m → E) (i : Fin r) :
    mvCoefficientDerivationOverVariables δ (genericLinearValues f i) =
      ∑ a : Fin m, MvPolynomial.X (i,a)*MvPolynomial.C (δ (f a)) := by
  classical
  simp only [genericLinearValues,map_sum,Derivation.leibniz,mvCoefficientDerivationOverVariables_X,
    mvCoefficientDerivationOverVariables_C,smul_eq_mul,mul_zero,add_zero]

lemma genericLinearValues_coordinate_eval {E : Type} [CommRing E] {m r : ℕ}
    (f : Fin m → E) (g : Fin r → Fin m) (i : Fin r) :
    eval (fun a : Fin r × Fin m => if a.2=g a.1 then 1 else 0) (genericLinearValues f i) = f (g i) := by
  classical
  simp [genericLinearValues,ite_mul]

end APSCounting893.Main
end Component_6

section Component_7

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace APSCounting893.Main

lemma kahler_mapBaseChange_injective_of_formallySmooth
    (R S T : Type) [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Algebra.FormallySmooth S T] :
    Function.Injective (KaehlerDifferential.mapBaseChange R S T) := by
  apply (LinearMap.injective_iff_eq_zero_of_exact (Algebra.H1Cotangent.exact_δ_mapBaseChange R S T)).mpr
  ext x
  rw [show x = 0 from Subsingleton.elim _ _,map_zero]
  rfl

end APSCounting893.Main
end Component_7

section Component_8

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_differentials {K L : Type} [Field K] [CharZero K] [Field L]
    [Algebra K L] [Algebra.EssFiniteType K L] {r : ℕ} (v : Fin r → L)
    (hv : AlgebraicIndependent K v) :
    LinearIndependent L (fun i => KaehlerDifferential.D K L (v i)) := by
  classical
  let P := MvPolynomial (Fin r) K
  let Q := FractionRing P
  letI : Algebra P L := (MvPolynomial.aeval v).toRingHom.toAlgebra
  letI : IsScalarTower K P L := IsScalarTower.of_algebraMap_eq (fun x => by
    change algebraMap K L x = MvPolynomial.aeval v (MvPolynomial.C x)
    simp)
  let lift : Q →ₐ[K] L := IsFractionRing.liftAlgHom (K := Q) (g := MvPolynomial.aeval v) hv
  letI : Algebra Q L := lift.toRingHom.toAlgebra
  letI : IsScalarTower K Q L := IsScalarTower.of_algebraMap_eq (fun x => (lift.commutes x).symm)
  letI : IsScalarTower P Q L := IsScalarTower.of_algebraMap_eq (fun x => by
    change MvPolynomial.aeval v x = lift (algebraMap P Q x)
    exact (IsFractionRing.lift_algebraMap (K := Q) (L := L)
      (g := (MvPolynomial.aeval (R := K) v).toRingHom)
      (show Function.Injective ((MvPolynomial.aeval (R := K) v).toRingHom) from hv) x).symm)
  letI : Algebra.EssFiniteType Q L := Algebra.EssFiniteType.of_comp K Q L
  letI : Algebra.FormallySmooth Q L := inferInstance
  letI : Algebra.FormallySmooth P Q := Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors P)
  letI : Algebra.FormallySmooth P L := Algebra.FormallySmooth.comp P Q L
  let b := (KaehlerDifferential.mvPolynomialBasis K (Fin r)).baseChange L
  have hinj := kahler_mapBaseChange_injective_of_formallySmooth K P L
  have hh := b.linearIndependent.map' (KaehlerDifferential.mapBaseChange K P L)
    (LinearMap.ker_eq_bot.mpr hinj)
  have he (i : Fin r) : KaehlerDifferential.mapBaseChange K P L (b i) = KaehlerDifferential.D K L (v i) := by
    rw [show b i = 1 ⊗ₜ[P] KaehlerDifferential.D K P (MvPolynomial.X i) from by
      simp only [b,Module.Basis.baseChange_apply,KaehlerDifferential.mvPolynomialBasis_apply]
      rfl,
      KaehlerDifferential.mapBaseChange_tmul,one_smul,KaehlerDifferential.map_D]
    change KaehlerDifferential.D K L (MvPolynomial.aeval v (MvPolynomial.X i)) = _
    rw [MvPolynomial.aeval_X]
  simpa only [Function.comp_def,he] using hh

end APSCounting893.Main
end Component_8

section Component_9
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open Module
namespace APSCounting893.Main

lemma exists_dual_derivations {K E : Type} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra.EssFiniteType K E] {r : ℕ} (v : Fin r → E)
    (hv : AlgebraicIndependent K v) :
    ∃ δ : Fin r → Derivation K E E, ∀ i j, δ j (v i) = if i=j then 1 else 0 := by
  classical
  have hD := algebraicIndependent_differentials v hv
  let b := Module.Basis.sumExtend hD
  have hb (i : Fin r) : b (Sum.inl i) = KaehlerDifferential.D K E (v i) := by
    simp [b,Module.Basis.sumExtend]
    rfl
  refine ⟨fun j => KaehlerDifferential.linearMapEquivDerivation K E (b.coord (Sum.inl j)),?_⟩
  intro i j
  change b.repr (KaehlerDifferential.D K E (v i)) (Sum.inl j) = _
  rw [← hb]
  simp [Finsupp.single_apply]

end APSCounting893.Main
end Component_9

section Component_10
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped TensorProduct
namespace APSCounting893.Main

noncomputable def extendDerivationOfLocalization {K S T : Type} [CommRing K] [CommRing S] [CommRing T]
    [Algebra K S] [Algebra K T] [Algebra S T] [IsScalarTower K S T]
    [Algebra.FormallyEtale S T] (δ : Derivation K S T) : Derivation K T T :=
  KaehlerDifferential.linearMapEquivDerivation K T
    ((LinearMap.liftBaseChange T δ.liftKaehlerDifferential).comp
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K S T).symm.toLinearMap)

lemma extendDerivationOfLocalization_algebraMap {K S T : Type} [CommRing K] [CommRing S] [CommRing T]
    [Algebra K S] [Algebra K T] [Algebra S T] [IsScalarTower K S T]
    [Algebra.FormallyEtale S T] (δ : Derivation K S T) (s : S) :
    extendDerivationOfLocalization δ (algebraMap S T s) = δ s := by
  change (LinearMap.liftBaseChange T δ.liftKaehlerDifferential)
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K S T).symm
      (KaehlerDifferential.D K T (algebraMap S T s))) = δ s
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    LinearMap.liftBaseChange_tmul,one_smul,Derivation.liftKaehlerDifferential_comp_D]

end APSCounting893.Main
end Component_10

section Component_11
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma polynomial_derivation_formula {K M σ : Type} [CommRing K] [Fintype σ]
    [AddCommGroup M] [Module K M] [Module (MvPolynomial σ K) M]
    [IsScalarTower K (MvPolynomial σ K) M]
    (δ : Derivation K (MvPolynomial σ K) M) (p : MvPolynomial σ K) :
    δ p = ∑ j, (MvPolynomial.pderiv j p) • δ (MvPolynomial.X j) := by
  classical
  let b := KaehlerDifferential.mvPolynomialBasis K σ
  have hh := congrArg δ.liftKaehlerDifferential (b.sum_repr (KaehlerDifferential.D K (MvPolynomial σ K) p))
  simpa only [b,KaehlerDifferential.mvPolynomialBasis_apply,KaehlerDifferential.mvPolynomialBasis_repr_apply,
    map_sum,map_smul,Derivation.liftKaehlerDifferential_comp_D] using hh.symm

end APSCounting893.Main
end Component_11

section Component_12
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma derivation_aeval_chain {K L M σ : Type} [CommRing K] [CommRing L] [Algebra K L]
    [AddCommGroup M] [Module L M] [Module K M] [IsScalarTower K L M] [Fintype σ]
    (δ : Derivation K L M) (v : σ → L) (p : MvPolynomial σ K) :
    δ (MvPolynomial.aeval v p) = ∑ i, (MvPolynomial.aeval v (MvPolynomial.pderiv i p)) • δ (v i) := by
  classical
  let P := MvPolynomial σ K
  letI : Algebra P L := (MvPolynomial.aeval v).toRingHom.toAlgebra
  letI : IsScalarTower K P L := IsScalarTower.of_algebraMap_eq (fun c => (MvPolynomial.aeval v).commutes c |>.symm)
  letI : Module P M := Module.compHom M (algebraMap P L)
  letI : IsScalarTower P L M := IsScalarTower.of_algebraMap_smul (fun a m => rfl)
  letI : IsScalarTower K P M := IsScalarTower.of_algebraMap_smul (fun k m => by
    change (algebraMap P L (algebraMap K P k)) • m = k • m
    rw [← IsScalarTower.algebraMap_apply K P L,algebraMap_smul])
  have hh := polynomial_derivation_formula (δ.compAlgebraMap P) p
  change δ (MvPolynomial.aeval v p) = ∑ i,
    MvPolynomial.aeval v (MvPolynomial.pderiv i p) • δ (MvPolynomial.aeval v (MvPolynomial.X i)) at hh
  simpa only [MvPolynomial.aeval_X] using hh

end APSCounting893.Main
end Component_12

section Component_13

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_pderiv_lt {K : Type*} [CommRing K] [IsDomain K] {ι : Type*}
    (p : MvPolynomial (ι) K) (i : ι) (h : pderiv i p ≠ 0) :
    (pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs (e : ι →₀ ℕ) (he : e ∈ (pderiv i p).support) :
      e.sum (fun _ k => k) + 1 ≤ p.totalDegree := by
    have hcoef := MvPolynomial.mem_support_iff.mp he
    rw [MvPolynomial.coeff_pderiv] at hcoef
    have hq : p.coeff (e + Finsupp.single i 1) ≠ 0 :=
      fun hz => hcoef (by rw [hz, zero_mul])
    have hh := MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hq)
    have heq : (e + Finsupp.single i 1).sum (fun _ k => k) = e.sum (fun _ k => k) + 1 := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
      simp
    rwa [heq] at hh
  have hd : 0 < p.totalDegree := by
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr h
    have hh := hs e he
    omega
  have hb : (pderiv i p).totalDegree ≤ p.totalDegree - 1 := by
    rw [MvPolynomial.totalDegree]
    apply Finset.sup_le
    intro e he
    have hh := hs e he
    omega
  omega

lemma eq_C_of_forall_pderiv_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K] {ι : Type*}
    (p : MvPolynomial (ι) K) (hp : ∀ i, pderiv i p = 0) :
    p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext e
  by_cases he : e = 0
  · subst e
    simp
  have hi : ∃ i, e i ≠ 0 := by
    by_contra h
    push Not at h
    exact he (Finsupp.ext h)
  obtain ⟨i, hi⟩ := hi
  have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
  have hre : e - Finsupp.single i 1 + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
  have hc := congrArg (MvPolynomial.coeff (e - Finsupp.single i 1)) (hp i)
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_zero, hre] at hc
  have hval : (e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 = e i := by
    simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
    omega
  have hn : (((e - Finsupp.single i 1 : ι →₀ ℕ) i : ℕ) : K) + 1 ≠ 0 := by
    have hh : (((e - Finsupp.single i 1 : ι →₀ ℕ) i + 1 : ℕ) : K) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega)
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have hpc : p.coeff e = 0 := (mul_eq_zero.mp hc).resolve_right hn
  simp [MvPolynomial.coeff_C, Ne.symm he, hpc]

lemma pderiv_aeval_chain {K : Type*} [CommRing K] [IsDomain K] {ι κ : Type*} [Fintype ι]
    (F : ι → MvPolynomial (κ) K) (p : MvPolynomial (ι) K) (j : κ) :
    pderiv j (MvPolynomial.aeval F p) =
      ∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C c => simp [MvPolynomial.aeval_C, MvPolynomial.pderiv_C]
  | add p q hp hq =>
    simp only [map_add, hp, hq, Finset.sum_add_distrib, add_mul]
  | mul_X p k hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp,
      map_add, MvPolynomial.pderiv_X, map_mul, MvPolynomial.aeval_X]
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 : (∑ i, MvPolynomial.aeval F (pderiv i p) * pderiv j (F i)) * F k =
        ∑ i, MvPolynomial.aeval F (pderiv i p) * F k * pderiv j (F i) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [h1]
    congr 1
    simp [Pi.single_apply, Finset.mul_sum, mul_assoc]

end APSCounting893.Main
end Component_13

section Component_14
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_of_derivation_matrix_det_ne_zero {K L : Type}
    [CommRing K] [IsDomain K] [CharZero K] [Field L] [Algebra K L] [FaithfulSMul K L] {r : ℕ}
    (v : Fin r → L) (δ : Fin r → Derivation K L L)
    (hdet : (Matrix.of (fun i j => δ j (v i))).det ≠ 0) : AlgebraicIndependent K v := by
  classical
  have hkill : ∀ d : ℕ, ∀ p : MvPolynomial (Fin r) K,
      p.totalDegree=d → MvPolynomial.aeval v p=0 → p=0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro p hdeg hp
      let J : Matrix (Fin r) (Fin r) L := fun i j => δ j (v i)
      let u : Fin r → L := fun i => MvPolynomial.aeval v (pderiv i p)
      have hvec : Matrix.vecMul u J=0 := by
        funext j
        change (∑ i, MvPolynomial.aeval v (pderiv i p)*δ j (v i))=0
        simpa only [smul_eq_mul] using (derivation_aeval_chain (δ j) v p).symm.trans (by rw [hp,map_zero])
      have hu := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
      have hpartials (i : Fin r) : pderiv i p=0 := by
        by_cases h : pderiv i p=0
        · exact h
        exact ih (pderiv i p).totalDegree (by rw [← hdeg]; exact totalDegree_pderiv_lt p i h)
          (pderiv i p) rfl (congrFun hu i)
      have hc := eq_C_of_forall_pderiv_zero p hpartials
      have he := congrArg (MvPolynomial.aeval v) hc
      rw [hp,MvPolynomial.aeval_C] at he
      have hz : p.coeff 0=0 := by
        apply FaithfulSMul.algebraMap_injective K L
        simpa using he.symm
      rw [hc,hz,MvPolynomial.C_0]
  apply algebraicIndependent_iff_injective_aeval.mpr
  apply (injective_iff_map_eq_zero (MvPolynomial.aeval v).toRingHom).mpr
  intro p hp
  exact hkill p.totalDegree p rfl hp

end APSCounting893.Main
end Component_14

section Component_15
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

lemma generic_linear_first_rows_independent_over_parameter_ring {K E : Type}
    [Field K] [CharZero K] [Field E] [Algebra K E] [Algebra.EssFiniteType K E]
    {m r k : ℕ} (hrk : r ≤ k) (f : Fin m → E) (g : Fin r → Fin m) (hg : AlgebraicIndependent K (f ∘ g)) :
    let S := MvPolynomial (Fin k × Fin m) E
    let T := FractionRing S
    AlgebraicIndependent (MvPolynomial (Fin k × Fin m) K)
      (fun i : Fin r => algebraMap S T (genericLinearValues f (Fin.castLE hrk i))) := by
  classical
  let R := MvPolynomial (Fin k × Fin m) K
  let S := MvPolynomial (Fin k × Fin m) E
  let T := FractionRing S
  letI : Algebra.FormallyEtale S T := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors S)
  have hinj : Function.Injective (algebraMap R T) := by
    rw [IsScalarTower.algebraMap_eq R S T]
    apply (IsFractionRing.injective S T).comp
    exact MvPolynomial.map_injective (algebraMap K E) (algebraMap K E).injective
  letI : FaithfulSMul R T := (faithfulSMul_iff_algebraMap_injective R T).mpr hinj
  obtain ⟨δ,hδ⟩ := exists_dual_derivations (f ∘ g) hg
  let D : Fin r → Derivation R T T := fun j => extendDerivationOfLocalization
    ((Algebra.linearMap S T).compDer (mvCoefficientDerivationOverVariables (σ := Fin k × Fin m) (δ j)))
  let J : Matrix (Fin r) (Fin r) S := fun i j => genericLinearValues (fun a => δ j (f a)) (Fin.castLE hrk i)
  have hJ : J.det ≠ 0 := by
    intro hz
    let A : Fin k × Fin m → E := fun a => if h : a.1.val < r then if a.2=g ⟨a.1.val,h⟩ then 1 else 0 else 0
    have hm : J.map (eval A) = 1 := by
      ext i j
      change eval A (genericLinearValues (fun a => δ j (f a)) (Fin.castLE hrk i)) = _
      have he : eval A (genericLinearValues (fun a => δ j (f a)) (Fin.castLE hrk i)) = δ j (f (g i)) := by
        simp [genericLinearValues,A,i.isLt,ite_mul]
      rw [he]
      simpa only [Function.comp_apply,Matrix.one_apply] using hδ i j
    have hh := congrArg (eval A) hz
    rw [map_zero,RingHom.map_det] at hh
    change (J.map (eval A)).det = 0 at hh
    rw [hm,Matrix.det_one] at hh
    exact one_ne_zero hh
  have hmatrix : Matrix.of (fun i j => D j (algebraMap S T (genericLinearValues f (Fin.castLE hrk i)))) = J.map (algebraMap S T) := by
    ext i j
    change extendDerivationOfLocalization
      ((Algebra.linearMap S T).compDer (mvCoefficientDerivationOverVariables (δ j)))
      (algebraMap S T (genericLinearValues f (Fin.castLE hrk i))) = algebraMap S T (genericLinearValues (fun a => δ j (f a)) (Fin.castLE hrk i))
    rw [extendDerivationOfLocalization_algebraMap]
    change algebraMap S T (mvCoefficientDerivationOverVariables (δ j) (genericLinearValues f (Fin.castLE hrk i))) = _
    rw [genericLinearValues_derivation]
    rfl
  apply algebraicIndependent_of_derivation_matrix_det_ne_zero _ D
  rw [hmatrix]
  have hm := (algebraMap S T).map_det J
  change algebraMap S T J.det = (J.map (algebraMap S T)).det at hm
  rw [← hm]
  exact fun hz => hJ ((IsFractionRing.injective S T) (by simpa only [map_zero] using hz))

end APSCounting893.Main
end Component_15

section Component_16
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main
lemma totalDegree_eval₂_bounded_general {K L σ : Type} [CommRing K] [CommRing L] {n : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial σ L) (D : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ D * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  rw [← Finset.sum_mul]
  simpa [Finsupp.sum_fintype, Nat.mul_comm] using Nat.mul_le_mul_right D (le_totalDegree he)

end APSCounting893.Main
end Component_16

section Component_17

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma eval_homogenize_monomial {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (z : Fin (n + 1) → K) (e : Fin n →₀ ℕ) (c : R) (d : ℕ) :
    MvPolynomial.eval₂ f z (MvPolynomial.monomial
      (Finsupp.single 0 (d - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) c) =
    f c * z 0 ^ (d - e.sum (fun _ k => k)) * e.prod (fun i k => z i.succ ^ k) := by
  classical
  rw [MvPolynomial.eval₂_monomial]
  rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rw [Finsupp.prod_single_index (h := fun i k => z i ^ k) (pow_zero (z 0))]
  rw [Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  ring

lemma finsupp_prod_scaled {K : Type} [Field K] {n : ℕ}
    (e : Fin n →₀ ℕ) (a : K) (x : Fin n → K) :
    e.prod (fun i k => (a * x i) ^ k) =
      a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k) := by
  classical
  rw [e.prod_fintype _ (fun _ => pow_zero _), e.prod_fintype _ (fun _ => pow_zero _),
    e.sum_fintype _ (fun _ => rfl)]
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

lemma eval_homogenize_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (a : K) (x : Fin n → K) :
    MvPolynomial.eval₂ f (Fin.cases a (fun i => a * x i)) (homogenizeAll d p) =
      a ^ d * MvPolynomial.eval₂ f x p := by
  classical
  rw [homogenizeAll, MvPolynomial.eval₂_sum]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  rw [eval_homogenize_monomial]
  simp only [Fin.cases_zero, Fin.cases_succ]
  rw [finsupp_prod_scaled]
  have hedeg : e.sum (fun _ k => k) ≤ d := (MvPolynomial.le_totalDegree he).trans hd
  have hpow : a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k) = a ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hedeg]
  calc
    f (p.coeff e) * a ^ (d - e.sum (fun _ k => k)) *
        (a ^ e.sum (fun _ k => k) * e.prod (fun i k => x i ^ k)) =
      (a ^ (d - e.sum (fun _ k => k)) * a ^ e.sum (fun _ k => k)) *
        (f (p.coeff e) * e.prod (fun i k => x i ^ k)) := by ring
    _ = _ := by rw [hpow]; rfl

lemma eval_homogenize_dehomogenize {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (f : R →+* K) (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d)
    (z : Fin (n + 1) → K) (hz : z 0 ≠ 0) :
    MvPolynomial.eval₂ f z (homogenizeAll d p) =
      z 0 ^ d * MvPolynomial.eval₂ f (fun i => z i.succ / z 0) p := by
  have heq : Fin.cases (z 0) (fun i => z 0 * (z i.succ / z 0)) = z := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    simp [hz, mul_div_cancel₀, mul_comm]
  simpa only [heq] using eval_homogenize_scaled f p d hd (z 0) (fun i => z i.succ / z 0)

end APSCounting893.Main
end Component_17

section Component_18

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma projectiveRepresentative_rescaling {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) :
    ∃ a : K, a ≠ 0 ∧ projectiveRepresentative z = a • z := by
  classical
  have hS : (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).Nonempty := by
    by_contra h
    apply hz
    funext i
    by_contra hi
    exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let j := (Finset.univ.filter (fun i : Fin n => z i ≠ 0)).min' hS
  have hj : z j ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2
  refine ⟨(z j)⁻¹, inv_ne_zero hj, ?_⟩
  rw [projectiveRepresentative, dif_pos hS]
  funext i
  simp only [div_eq_mul_inv, Pi.smul_apply, smul_eq_mul]
  exact mul_comm _ _

lemma projectiveRepresentative_ne_zero {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) (hz : z ≠ 0) : projectiveRepresentative z ≠ 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  exact smul_ne_zero ha hz

lemma homogenizeAll_homogeneous {R : Type} [CommRing R] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hd : p.totalDegree ≤ d) :
    (homogenizeAll d p).IsHomogeneous d := by
  classical
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  apply MvPolynomial.isHomogeneous_monomial
  rw [map_add, Finsupp.degree_single, Finsupp.degree_mapDomain, Finsupp.degree_eq_sum]
  have hsum : (∑ i : Fin n, e i) = e.sum (fun _ k => k) :=
    (e.sum_fintype (fun _ k => k) (fun _ => rfl)).symm
  rw [hsum]
  exact Nat.sub_add_cancel ((MvPolynomial.le_totalDegree he).trans hd)

lemma homogeneous_eval₂_scaled {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (a : K) (z : Fin n → K) :
    MvPolynomial.eval₂ f (fun i => a * z i) p = a ^ d * MvPolynomial.eval₂ f z p := by
  classical
  conv_lhs => rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [MvPolynomial.eval₂_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  change f (p.coeff e) * e.prod (fun i k => (a * z i) ^ k) =
    a ^ d * (f (p.coeff e) * e.prod (fun i k => z i ^ k))
  rw [finsupp_prod_scaled]
  have hd := hp.degree_eq_sum_deg_support he
  change d = e.sum (fun _ k => k) at hd
  rw [← hd]
  ring

lemma homogeneous_root_projectiveRepresentative {R K : Type} [CommRing R] [Field K] {n : ℕ}
    (p : MvPolynomial (Fin n) R) (d : ℕ) (hp : p.IsHomogeneous d)
    (f : R →+* K) (z : Fin n → K) (hz : z ≠ 0) (hroot : MvPolynomial.eval₂ f z p = 0) :
    MvPolynomial.eval₂ f (projectiveRepresentative z) p = 0 := by
  obtain ⟨a, ha, he⟩ := projectiveRepresentative_rescaling z hz
  rw [he]
  change MvPolynomial.eval₂ f (fun i => a * z i) p = 0
  rw [homogeneous_eval₂_scaled p d hp f a z, hroot, mul_zero]

end APSCounting893.Main
end Component_18

section Component_19
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def clearedRationalSubstitution {K : Type} [CommRing K] {n r : ℕ}
    (Q : MvPolynomial (Fin n) K) (P : Fin r → MvPolynomial (Fin n) K)
    (t : ℕ) (h : MvPolynomial (Fin r) K) : MvPolynomial (Fin n) K :=
  MvPolynomial.eval₂Hom MvPolynomial.C (Fin.cons Q P : Fin (r+1) → MvPolynomial (Fin n) K) (homogenizeAll t h)

lemma clearedRationalSubstitution_degree {K : Type} [Field K] {n r : ℕ}
    (Q : MvPolynomial (Fin n) K) (P : Fin r → MvPolynomial (Fin n) K)
    (d t : ℕ) (hQ : Q.totalDegree ≤ d) (hP : ∀ i, (P i).totalDegree ≤ d)
    (h : MvPolynomial (Fin r) K) (hh : h.totalDegree ≤ t) :
    (clearedRationalSubstitution Q P t h).totalDegree ≤ d*t := by
  have hpoint (i : Fin (r+1)) : ((Fin.cons Q P : Fin (r+1) → MvPolynomial (Fin n) K) i).totalDegree ≤ d := by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact hQ
    · exact hP j
  have hhom := homogenizeAll_homogeneous h t hh
  exact (totalDegree_eval₂_bounded_general (RingHom.id K) (Fin.cons Q P : Fin (r+1) → MvPolynomial (Fin n) K) d hpoint (homogenizeAll t h)).trans
    (Nat.mul_le_mul_left d hhom.totalDegree_le)

lemma clearedRationalSubstitution_fraction {K : Type} [Field K] {n r : ℕ} {E : Type} [Field E] [Algebra K E]
    [Algebra (MvPolynomial (Fin n) K) E] [IsScalarTower K (MvPolynomial (Fin n) K) E]
    (Q : MvPolynomial (Fin n) K) (P : Fin r → MvPolynomial (Fin n) K)
    (v : Fin r → E)
    (hP : ∀ i, algebraMap _ (E) (P i) =
      algebraMap _ (E) Q * v i)
    (t : ℕ) (h : MvPolynomial (Fin r) K) (hh : h.totalDegree ≤ t) :
    algebraMap _ (E) (clearedRationalSubstitution Q P t h) =
      (algebraMap _ (E) Q)^t * MvPolynomial.aeval v h := by
  let S := MvPolynomial (Fin n) K
  let f : S →+* E := algebraMap S E
  have hcoeff : f.comp MvPolynomial.C = algebraMap K E := by
    ext c
    exact (IsScalarTower.algebraMap_apply K S E c).symm
  have hpoint : (fun i : Fin (r+1) => f ((Fin.cons Q P : Fin (r+1) → MvPolynomial (Fin n) K) i)) =
      Fin.cases (f Q) (fun i => f Q*v i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · exact hP j
  rw [clearedRationalSubstitution,MvPolynomial.map_eval₂Hom,hcoeff,hpoint]
  exact eval_homogenize_scaled (algebraMap K E) h t hh (f Q) v

end APSCounting893.Main
end Component_19

section Component_20
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace APSCounting893.Main

lemma linearIndependent_tower_products {K H E ι κ : Type}
    [Field K] [Field H] [Field E] [Algebra K H] [Algebra K E] [Algebra H E] [IsScalarTower K H E]
    [Fintype ι] [Fintype κ] (v : ι → E) (hv : LinearIndependent H v)
    (w : κ → H) (hw : LinearIndependent K w) :
    LinearIndependent K (fun a : ι × κ => w a.2 • v a.1) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc a
  have hs : ∑ i : ι, (∑ j : κ, c (i,j) • w j) • v i = 0 := by
    simpa only [Finset.sum_smul,smul_assoc,Fintype.sum_prod_type] using hc
  have hcoeff := (Fintype.linearIndependent_iff.mp hv) _ hs
  exact (Fintype.linearIndependent_iff.mp hw) (fun j => c (a.1,j)) (hcoeff a.1) a.2

end APSCounting893.Main
end Component_20

section Component_21
set_option autoImplicit false
set_option maxHeartbeats 400000
namespace APSCounting893.Main

lemma linearIndependent_common_multiple {K E ι : Type} [Field K] [Field E] [Algebra K E]
    (v : ι → E) (hv : LinearIndependent K v) (c : E) (hc : c ≠ 0) :
    LinearIndependent K (fun i => c*v i) := by
  let f : E →ₗ[K] E :=
    { toFun := fun x => c*x
      map_add' := mul_add c
      map_smul' := by intro a x; simp [Algebra.smul_def]; ring }
  have hf : Function.Injective f := by
    intro x y h
    exact mul_left_cancel₀ hc h
  exact hv.map' f (LinearMap.ker_eq_bot.mpr hf)

end APSCounting893.Main
end Component_21

section Component_22

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def affineEvaluation {K : Type} [Field K] {n : ℕ} (X : Set (Affine K n)) :
    Polynomials K n →ₗ[K] (X → K) where
  toFun p := fun x => MvPolynomial.eval x.val p
  map_add' p q := by funext x; exact map_add (MvPolynomial.eval x.val) p q
  map_smul' c p := by
    funext x
    simp [MvPolynomial.smul_eq_C_mul]

lemma affineFilteredPiece_eq_map {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) :
    affineFilteredPiece X d = (MvPolynomial.restrictTotalDegree (Fin n) K d).map (affineEvaluation X) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨p, hp, rfl⟩
    exact Submodule.mem_map.mpr ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mpr hp, rfl⟩
  · rintro f ⟨p, hp, rfl⟩
    apply Submodule.subset_span
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mp hp, rfl⟩

instance affineFilteredPiece_finite {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) : Module.Finite K (affineFilteredPiece X d) := by
  rw [affineFilteredPiece_eq_map]
  exact Module.Finite.map (MvPolynomial.restrictTotalDegree (Fin n) K d) (affineEvaluation X)

lemma mem_affineFilteredPiece {K : Type} [Field K] {n : ℕ}
    (X : Set (Affine K n)) (d : ℕ) (f : X → K) :
    f ∈ affineFilteredPiece X d ↔ ∃ p : Polynomials K n, p.totalDegree ≤ d ∧
      f = fun x => MvPolynomial.eval x.val p := by
  rw [affineFilteredPiece_eq_map, Submodule.mem_map]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mp hp, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (MvPolynomial.mem_restrictTotalDegree (Fin n) d p).mpr hp, rfl⟩

lemma totalDegree_eval₂_bounded {K L : Type} [CommRing K] [CommRing L] {n m : ℕ}
    (f : K →+* L) (g : Fin n → MvPolynomial (Fin m) L) (D : ℕ)
    (hg : ∀ i, (g i).totalDegree ≤ D) (p : MvPolynomial (Fin n) K) :
    (eval₂Hom (MvPolynomial.C.comp f) g p).totalDegree ≤ D * p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro e he
  rw [eval₂Hom_monomial]
  apply (totalDegree_mul _ _).trans
  simp only [RingHom.coe_comp, Function.comp_apply, totalDegree_C, zero_add]
  rw [Finsupp.prod_pow]
  apply (totalDegree_finsetProd _ _).trans
  apply le_trans (Finset.sum_le_sum (fun i _ =>
    (totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hg i))))
  rw [← Finset.sum_mul]
  simpa [Finsupp.sum_fintype, Nat.mul_comm] using Nat.mul_le_mul_right D (le_totalDegree he)

end APSCounting893.Main
end Component_22

section Component_23

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma finsupp_nat_sum_eq {n : ℕ} (e : Fin n →₀ ℕ) :
    e.sum (fun _ v => v) = ∑ i, e i := Finsupp.sum_fintype _ _ (fun _ => rfl)

noncomputable def boundedExponentEquivSum (n d : ℕ) :
    {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d} ≃
      {f : Fin (n + 1) → ℕ // ∑ i, f i = d} where
  toFun e := ⟨Fin.cons (d - e.val.sum (fun _ v => v)) e.val, by
    rw [Fin.sum_univ_succ]
    have he := e.property
    rw [finsupp_nat_sum_eq] at he
    simp only [Fin.cons_zero, Fin.cons_succ, finsupp_nat_sum_eq]
    omega⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => f.val i.succ), by
    have hf := f.property
    rw [Fin.sum_univ_succ] at hf
    rw [Finsupp.equivFunOnFinite_symm_sum]
    omega⟩
  left_inv e := by
    apply Subtype.ext
    ext i
    simp
  right_inv f := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · have hf := f.property
      rw [Fin.sum_univ_succ] at hf
      change d - (Finsupp.equivFunOnFinite.symm (fun j : Fin n => f.val j.succ)).sum (fun _ v => v) = f.val 0
      rw [Finsupp.equivFunOnFinite_symm_sum]
      omega
    · simp

noncomputable def boundedExponentEquivSym (n d : ℕ) :
    {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d} ≃ Sym (Fin (n + 1)) d :=
  (boundedExponentEquivSum n d).trans (Sym.equivNatSumOfFintype (Fin (n + 1)) d).symm

lemma restrictTotalDegree_finrank (K : Type) [Field K] (n d : ℕ) :
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K d) = (n + d).choose n := by
  classical
  let E := {e : Fin n →₀ ℕ // e.sum (fun _ v => v) ≤ d}
  let eqv : E ≃ Sym (Fin (n + 1)) d := boundedExponentEquivSym n d
  letI : Fintype E := Fintype.ofEquiv _ eqv.symm
  calc
    Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K d) = Fintype.card E :=
      Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport K _)
    _ = Fintype.card (Sym (Fin (n + 1)) d) := Fintype.card_congr eqv
    _ = (n + d).choose n := by
      rw [Sym.card_sym_eq_choose]
      simp only [Fintype.card_fin]
      rw [show n + 1 + d - 1 = n + d by omega, Nat.choose_symm_add]

lemma affineEvaluation_univ_injective {K : Type} [Field K] [Infinite K] {n : ℕ} :
    Function.Injective (affineEvaluation (Set.univ : Set (Affine K n))) := by
  intro p q h
  apply MvPolynomial.funext
  intro x
  exact congrFun h ⟨x, Set.mem_univ x⟩

lemma univ_affineHilbertFunction {K : Type} [Field K] [Infinite K] (n d : ℕ) :
    affineHilbertFunction (Set.univ : Set (Affine K n)) d = (n + d).choose n := by
  unfold affineHilbertFunction
  rw [affineFilteredPiece_eq_map]
  rw [← (Submodule.equivMapOfInjective (affineEvaluation (Set.univ : Set (Affine K n)))
    affineEvaluation_univ_injective (MvPolynomial.restrictTotalDegree (Fin n) K d)).finrank_eq]
  exact restrictTotalDegree_finrank K n d

end APSCounting893.Main
end Component_23

section Component_24
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma cleared_product_polynomials_independent {K : Type} [Field K] {n r s : ℕ} {E : Type} [Field E] [Algebra K E]
    [Algebra (MvPolynomial (Fin n) K) E] [IsScalarTower K (MvPolynomial (Fin n) K) E]
    [IsFractionRing (MvPolynomial (Fin n) K) E]
    (Q : MvPolynomial (Fin n) K) (hQ : Q ≠ 0) (P : Fin r → MvPolynomial (Fin n) K)
    (v : Fin r → E) (hv : AlgebraicIndependent K v)
    (hP : ∀ i, algebraMap _ (E) (P i) =
      algebraMap _ (E) Q * v i)
    (u : Fin s → MvPolynomial (Fin n) K)
    (hu : LinearIndependent (IntermediateField.adjoin K (Set.range v))
      (fun i => algebraMap _ (E) (u i))) (t : ℕ) :
    LinearIndependent K (fun a : Fin s × {e : Fin r →₀ ℕ // e.sum (fun _ k => k) ≤ t} =>
      u a.1 * clearedRationalSubstitution Q P t (MvPolynomial.monomial a.2.val (1 : K))) := by
  classical
  let A := MvPolynomial (Fin n) K
  let H := IntermediateField.adjoin K (Set.range v)
  let w : Fin r → H := fun i => ⟨v i,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩
  let I := {e : Fin r →₀ ℕ // e.sum (fun _ k => k) ≤ t}
  letI : Fintype I := Fintype.ofEquiv (Sym (Fin (r+1)) t) (boundedExponentEquivSym r t).symm
  have hw : AlgebraicIndependent K w := by
    apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom K H E)
    exact hv
  have hm : LinearIndependent K (fun e : I => MvPolynomial.aeval w (MvPolynomial.monomial e.val (1 : K))) := by
    have hh := (MvPolynomial.basisMonomials (Fin r) K).linearIndependent.map'
      (MvPolynomial.aeval w).toLinearMap (LinearMap.ker_eq_bot.mpr hw)
    have hh' := hh.comp (fun e : I => e.val) Subtype.val_injective
    simpa only [Function.comp_def,MvPolynomial.coe_basisMonomials,AlgHom.coe_toLinearMap,AlgHom.toLinearMap_apply] using hh'
  have htower := linearIndependent_tower_products _ hu _ hm
  have hscale := linearIndependent_common_multiple _ htower ((algebraMap A E Q)^t)
    (pow_ne_zero _ (by simpa only [map_zero] using (IsFractionRing.injective A E).ne hQ))
  have heval (h : MvPolynomial (Fin r) K) :
      algebraMap H E (MvPolynomial.aeval w h) = MvPolynomial.aeval v h := by
    have heq : (IsScalarTower.toAlgHom K H E).comp (MvPolynomial.aeval w) = MvPolynomial.aeval v := by
      ext i <;> simp only [AlgHom.comp_apply,MvPolynomial.aeval_X,MvPolynomial.aeval_C] <;> rfl
    exact congrArg (fun f : MvPolynomial (Fin r) K →ₐ[K] E => f h) heq
  have heq : (fun a : Fin s × I => algebraMap A E
      (u a.1 * clearedRationalSubstitution Q P t (MvPolynomial.monomial a.2.val (1 : K)))) =
      fun a => (algebraMap A E Q)^t * (MvPolynomial.aeval w (MvPolynomial.monomial a.2.val (1 : K)) • algebraMap A E (u a.1)) := by
    funext a
    have hd : (MvPolynomial.monomial a.2.val (1 : K)).totalDegree ≤ t :=
      (MvPolynomial.totalDegree_monomial_le _ _).trans a.2.property
    rw [map_mul,clearedRationalSubstitution_fraction Q P v hP t _ hd,Algebra.smul_def]
    change _ = (algebraMap A E Q)^t * (algebraMap H E (MvPolynomial.aeval w _) * _)
    have he := heval (MvPolynomial.monomial a.2.val (1 : K))
    change (↑(MvPolynomial.aeval w (MvPolynomial.monomial a.2.val (1 : K))) : E) = _ at he
    change _ = (algebraMap A E Q)^t * ((↑(MvPolynomial.aeval w (MvPolynomial.monomial a.2.val (1 : K))) : E) * _)
    erw [he]
    ring
  apply LinearIndependent.of_comp (IsScalarTower.toAlgHom K A E).toLinearMap
  change LinearIndependent K (fun a : Fin s × I => algebraMap A E
    (u a.1 * clearedRationalSubstitution Q P t (MvPolynomial.monomial a.2.val (1 : K))))
  rw [heq]
  exact hscale

end APSCounting893.Main
end Component_24

section Component_25
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma cleared_product_dimension_bound {K : Type} [Field K] {n r s : ℕ} {E : Type} [Field E] [Algebra K E]
    [Algebra (MvPolynomial (Fin n) K) E] [IsScalarTower K (MvPolynomial (Fin n) K) E]
    [IsFractionRing (MvPolynomial (Fin n) K) E]
    (Q : MvPolynomial (Fin n) K) (hQ : Q ≠ 0) (P : Fin r → MvPolynomial (Fin n) K)
    (v : Fin r → E) (hv : AlgebraicIndependent K v)
    (hP : ∀ i, algebraMap _ (E) (P i) =
      algebraMap _ (E) Q * v i)
    (u : Fin s → MvPolynomial (Fin n) K)
    (hu : LinearIndependent (IntermediateField.adjoin K (Set.range v))
      (fun i => algebraMap _ (E) (u i)))
    (C d : ℕ) (hC : ∀ i, (u i).totalDegree ≤ C) (hdQ : Q.totalDegree ≤ d)
    (hdP : ∀ i, (P i).totalDegree ≤ d) (t : ℕ) :
    s*(r+t).choose r ≤ (n+C+d*t).choose n := by
  classical
  let I := {e : Fin r →₀ ℕ // e.sum (fun _ k => k) ≤ t}
  letI : Fintype I := Fintype.ofEquiv (Sym (Fin (r+1)) t) (boundedExponentEquivSym r t).symm
  let V := MvPolynomial.restrictTotalDegree (Fin n) K (C+d*t)
  let p : Fin s × I → MvPolynomial (Fin n) K := fun a =>
    u a.1 * clearedRationalSubstitution Q P t (MvPolynomial.monomial a.2.val 1)
  have hdeg (a : Fin s × I) : (p a).totalDegree ≤ C+d*t := by
    apply (MvPolynomial.totalDegree_mul _ _).trans
    apply Nat.add_le_add (hC a.1)
    exact clearedRationalSubstitution_degree Q P d t hdQ hdP _
      ((MvPolynomial.totalDegree_monomial_le _ _).trans a.2.property)
  let w : Fin s × I → V := fun a => ⟨p a,(MvPolynomial.mem_restrictTotalDegree _ _ _).mpr (hdeg a)⟩
  have hw : LinearIndependent K w := by
    apply LinearIndependent.of_comp V.subtype
    exact cleared_product_polynomials_independent Q hQ P v hv hP u hu t
  have hcard : Fintype.card I = (r+t).choose r := by
    rw [Fintype.card_congr (boundedExponentEquivSym r t),Sym.card_sym_eq_choose]
    simp only [Fintype.card_fin]
    rw [show r+1+t-1=r+t by omega,Nat.choose_symm_add]
  have hh := hw.fintype_card_le_finrank
  change Fintype.card (Fin s × I) ≤ Module.finrank K (MvPolynomial.restrictTotalDegree (Fin n) K (C+d*t)) at hh
  rw [Fintype.card_prod,Fintype.card_fin,hcard,restrictTotalDegree_finrank] at hh
  simpa only [Nat.add_assoc] using hh

end APSCounting893.Main
end Component_25

section Component_26

set_option autoImplicit false
set_option maxHeartbeats 4000000
open Filter Polynomial
namespace APSCounting893.Main

lemma coefficient_le_of_eventual_nat_eval_le (p q : Polynomial ℚ) (n : ℕ)
    (hp : p.natDegree ≤ n) (hq : q.natDegree ≤ n)
    (heval : ∃ N : ℕ, ∀ m ≥ N, p.eval (m : ℚ) ≤ q.eval (m : ℚ)) :
    p.coeff n ≤ q.coeff n := by
  by_contra h
  have hcoeff : (q - p).coeff n < 0 := by rw [coeff_sub]; linarith
  have hne : q - p ≠ 0 := by intro hz; simp [hz] at hcoeff
  have hdeg : (q - p).natDegree = n :=
    le_antisymm ((natDegree_sub_le q p).trans (max_le hq hp))
      (le_natDegree_of_ne_zero (ne_of_lt hcoeff))
  have hlc : (q - p).leadingCoeff < 0 := by simpa only [leadingCoeff, hdeg] using hcoeff
  obtain ⟨N, hN⟩ := heval
  by_cases hn : n = 0
  · have hz : q - p = C ((q - p).coeff 0) := eq_C_of_natDegree_eq_zero (hdeg.trans hn)
    have hval := hN N le_rfl
    have hr : 0 ≤ (q - p).eval (N : ℚ) := by rw [eval_sub]; linarith
    rw [hz, eval_C] at hr
    rw [hn] at hcoeff
    linarith
  · have hdpos : 0 < (q - p).degree := natDegree_pos_iff_degree_pos.mp (by omega)
    have hlim := ((q - p).tendsto_atBot_of_leadingCoeff_nonpos hdpos hlc.le).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℚ)) atTop atTop)
    obtain ⟨m, hm, hneg⟩ := ((eventually_ge_atTop N).and (hlim.eventually_lt_atBot 0)).exists
    change (q - p).eval (m : ℚ) < 0 at hneg
    have hval := hN m hm
    have hr : 0 ≤ (q - p).eval (m : ℚ) := by rw [eval_sub]; linarith
    linarith

end APSCounting893.Main
end Component_26

section Component_27
set_option autoImplicit false
set_option maxHeartbeats 600000
open Polynomial
namespace APSCounting893.Main

lemma multiplicity_le_power_of_choose_bound (r s C d : ℕ) (hd : 0 < d)
    (h : ∀ t : ℕ, s*(r+t).choose r ≤ (r+C+d*t).choose r) : s ≤ d^r := by
  let H := Polynomial.preHilbertPoly ℚ r 0
  let p := Polynomial.C (s : ℚ) * H
  let a := Polynomial.C (d : ℚ) * Polynomial.X + Polynomial.C (C : ℚ)
  let q := H.comp a
  have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast hd.ne'
  have ha : a.natDegree = 1 := by
    dsimp only [a]
    rw [Polynomial.natDegree_add_C,Polynomial.natDegree_C_mul_X _ hdne]
  have hpdeg : p.natDegree ≤ r := by
    change (Polynomial.C (s : ℚ) * H).natDegree ≤ r
    exact (Polynomial.natDegree_mul_le).trans (by simp only [Polynomial.natDegree_C,H,Polynomial.natDegree_preHilbertPoly,zero_add]; rfl)
  have hqdeg : q.natDegree = r := by simp only [q,Polynomial.natDegree_comp,H,Polynomial.natDegree_preHilbertPoly,ha,mul_one]
  have hpc : p.coeff r = (s : ℚ) * (r.factorial : ℚ)⁻¹ := by
    change (Polynomial.C (s : ℚ) * H).coeff r = _
    rw [Polynomial.coeff_C_mul,← Polynomial.natDegree_preHilbertPoly (F := ℚ) r 0,
      Polynomial.coeff_natDegree,Polynomial.leadingCoeff_preHilbertPoly,Polynomial.natDegree_preHilbertPoly]
  have hac : a.leadingCoeff = (d : ℚ) := by
    change (Polynomial.C (d : ℚ)*Polynomial.X+Polynomial.C (C : ℚ)).leadingCoeff = _
    rw [Polynomial.leadingCoeff_add_of_degree_lt']
    · exact Polynomial.leadingCoeff_C_mul_X _
    · exact (Polynomial.degree_C_le).trans_lt (by rw [Polynomial.degree_C_mul_X hdne]; exact WithBot.coe_lt_coe.mpr (by decide))
  have hqc : q.coeff r = (r.factorial : ℚ)⁻¹ * (d : ℚ)^r := by
    have hh := Polynomial.coeff_comp_degree_mul_degree (p := H) (q := a) (by rw [ha]; decide)
    simpa only [q,H,Polynomial.natDegree_preHilbertPoly,ha,mul_one,Polynomial.leadingCoeff_preHilbertPoly,hac] using hh
  have heval : ∃ N : ℕ, ∀ t ≥ N, p.eval (t : ℚ) ≤ q.eval (t : ℚ) := by
    refine ⟨0,fun t _ => ?_⟩
    have hH (u : ℕ) : H.eval (u : ℚ) = ((r+u).choose r : ℚ) := by
      simpa only [H,Nat.sub_zero,Nat.add_comm] using
        Polynomial.preHilbertPoly_eq_choose_sub_add (F := ℚ) r (k := 0) (n := u) (Nat.zero_le _)
    have hav : a.eval (t : ℚ) = ((C+d*t : ℕ) : ℚ) := by simp [a]; ring
    change (Polynomial.C (s : ℚ)*H).eval _ ≤ (H.comp a).eval _
    rw [Polynomial.eval_mul,Polynomial.eval_C,hH,Polynomial.eval_comp,hav,hH]
    exact_mod_cast (by simpa only [Nat.add_assoc] using h t)
  have hc := coefficient_le_of_eventual_nat_eval_le p q r hpdeg hqdeg.le heval
  rw [hpc,hqc] at hc
  have hfac : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hm := mul_le_mul_of_nonneg_right hc (show 0 ≤ (r.factorial : ℚ) by positivity)
  have hs : (s : ℚ) * (r.factorial : ℚ)⁻¹ * (r.factorial : ℚ) = s := by field_simp
  have hds : (r.factorial : ℚ)⁻¹ * (d : ℚ)^r * (r.factorial : ℚ) = (d : ℚ)^r := by field_simp
  rw [hs,hds] at hm
  exact_mod_cast hm
end APSCounting893.Main
end Component_27

section Component_28
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open IntermediateField
namespace APSCounting893.Main

lemma trdeg_lower_of_independent_algebraic_coordinates {K R E : Type}
    [Field K] [Field R] [Field E] [Algebra K R] [Algebra K E] [Algebra R E] [IsScalarTower K R E]
    {r : ℕ} (v : Fin r → E) (hv : AlgebraicIndependent K v) (halg : ∀ i, IsAlgebraic R (v i)) :
    (r : Cardinal) ≤ Algebra.trdeg K R := by
  classical
  let M := IntermediateField.adjoin R (Set.range v)
  letI : Algebra K M := ((algebraMap R M).comp (algebraMap K R)).toAlgebra
  letI : IsScalarTower K R M := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower K M E := IsScalarTower.of_algebraMap_eq (fun k => by
    change algebraMap K E k = algebraMap R E (algebraMap K R k)
    exact IsScalarTower.algebraMap_apply K R E k)
  let w : Fin r → M := fun i => ⟨v i,IntermediateField.subset_adjoin R _ (Set.mem_range_self i)⟩
  letI : Algebra.IsAlgebraic R M := IntermediateField.isAlgebraic_adjoin (by
    rintro x ⟨i,rfl⟩
    exact (halg i).isIntegral)
  have hw : AlgebraicIndependent K w := by
    apply AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom K M E)
    exact hv
  have hcard := hw.cardinalMk_le_trdeg
  have heq := trdeg_add_eq K R (A := M)
  have hz : Algebra.trdeg R M = 0 := trdeg_eq_zero
  rw [hz,add_zero] at heq
  rw [← heq] at hcard
  simpa using hcard

end APSCounting893.Main
end Component_28

section Component_29
set_option autoImplicit false
set_option maxHeartbeats 400000
open Cardinal
namespace APSCounting893.Main

lemma algebraic_over_subfield_of_full_independent_algebraic_coordinates {K R E : Type}
    [Field K] [Field R] [Field E] [Algebra K R] [Algebra K E] [Algebra R E] [IsScalarTower K R E]
    {r : ℕ} (hE : Algebra.trdeg K E = (r : Cardinal))
    (v : Fin r → E) (hv : AlgebraicIndependent K v) (halg : ∀ i, IsAlgebraic R (v i)) :
    Algebra.IsAlgebraic R E := by
  have hlo := trdeg_lower_of_independent_algebraic_coordinates v hv halg
  have hhi := trdeg_le_of_injective (IsScalarTower.toAlgHom K R E) (algebraMap R E).injective
  have hR : Algebra.trdeg K R = (r : Cardinal) := le_antisymm (hhi.trans_eq hE) hlo
  have hsum := trdeg_add_eq K R (A := E)
  rw [hR,hE] at hsum
  have hz : Algebra.trdeg R E = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hsum with hbad | hgood
    · have hh := (le_max_left _ _).trans hbad
      exact False.elim (not_le_of_gt (Cardinal.nat_lt_aleph0 r) hh)
    · exact hgood
  exact trdeg_eq_zero_iff.mp hz

end APSCounting893.Main
end Component_29

section Component_30
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
namespace APSCounting893.Main

lemma rationalFunction_trdeg (K : Type) [Field K] (n : ℕ) :
    Algebra.trdeg K (FractionRing (MvPolynomial (Fin n) K)) = (n : Cardinal) := by
  let P := MvPolynomial (Fin n) K
  let E := FractionRing P
  letI : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have heq := trdeg_add_eq K P (A := E)
  have hz : Algebra.trdeg P E=0 := trdeg_eq_zero
  rw [hz,add_zero] at heq
  rw [MvPolynomial.trdeg_of_isDomain] at heq
  simpa only [Cardinal.mk_fin,Cardinal.lift_natCast] using heq.symm

lemma rationalFunction_trdeg_of_isFractionRing (K : Type) [Field K] (n : ℕ)
    (E : Type) [Field E] [Algebra K E] [Algebra (MvPolynomial (Fin n) K) E]
    [IsScalarTower K (MvPolynomial (Fin n) K) E] [IsFractionRing (MvPolynomial (Fin n) K) E] :
    Algebra.trdeg K E = (n : Cardinal) := by
  let P := MvPolynomial (Fin n) K
  letI : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have heq := trdeg_add_eq K P (A := E)
  have hz : Algebra.trdeg P E = 0 := trdeg_eq_zero
  rw [hz,add_zero] at heq
  rw [MvPolynomial.trdeg_of_isDomain] at heq
  simpa only [Cardinal.mk_fin,Cardinal.lift_natCast] using heq.symm

end APSCounting893.Main
end Component_30

section Component_31
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma rational_function_independent_family_bound {K : Type} [Field K] {r s : ℕ} {E : Type} [Field E] [Algebra K E]
    [Algebra (MvPolynomial (Fin r) K) E] [IsScalarTower K (MvPolynomial (Fin r) K) E]
    [IsFractionRing (MvPolynomial (Fin r) K) E]
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0) (P : Fin r → MvPolynomial (Fin r) K)
    (v : Fin r → E) (hv : AlgebraicIndependent K v)
    (hP : ∀ i, algebraMap _ (E) (P i) =
      algebraMap _ (E) Q * v i)
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d)
    (z : Fin s → E)
    (hz : LinearIndependent (IntermediateField.adjoin K (Set.range v)) z) : s ≤ d^r := by
  classical
  let A := MvPolynomial (Fin r) K
  let H := IntermediateField.adjoin K (Set.range v)
  obtain ⟨D,hD⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors A) z
  choose u hu using hD
  have hDne : algebraMap A E (D : A) ≠ 0 :=
    by simpa only [map_zero] using (IsFractionRing.injective A E).ne (nonZeroDivisors.ne_zero D.property)
  have hu' : (fun i => algebraMap A E (u i)) = fun i => algebraMap A E (D : A)*z i := by
    funext i
    simpa only [Algebra.smul_def] using hu i
  have hui : LinearIndependent H (fun i => algebraMap A E (u i)) := by
    rw [hu']
    exact linearIndependent_common_multiple z hz _ hDne
  let C := Finset.univ.sup (fun i => (u i).totalDegree)
  have hC (i : Fin s) : (u i).totalDegree ≤ C := Finset.le_sup (f := fun i => (u i).totalDegree) (Finset.mem_univ i)
  apply multiplicity_le_power_of_choose_bound r s C d hd
  intro t
  exact cleared_product_dimension_bound Q hQ P v hv hP u hui C d hC hdQ hdP t

lemma rational_function_field_degree_bound {K : Type} [Field K] {r : ℕ} {E : Type} [Field E] [Algebra K E]
    [Algebra (MvPolynomial (Fin r) K) E] [IsScalarTower K (MvPolynomial (Fin r) K) E]
    [IsFractionRing (MvPolynomial (Fin r) K) E]
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0) (P : Fin r → MvPolynomial (Fin r) K)
    (v : Fin r → E) (hv : AlgebraicIndependent K v)
    (hP : ∀ i, algebraMap _ (E) (P i) =
      algebraMap _ (E) Q * v i)
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    let H := IntermediateField.adjoin K (Set.range v)
    Module.Finite H (E) ∧
      Module.finrank H (E) ≤ d^r := by
  classical
  let A := MvPolynomial (Fin r) K
  let H := IntermediateField.adjoin K (Set.range v)
  letI : Algebra.IsAlgebraic H E :=
    algebraic_over_subfield_of_full_independent_algebraic_coordinates (rationalFunction_trdeg_of_isFractionRing K r E)
      v hv (fun i => isAlgebraic_algebraMap (⟨v i,IntermediateField.subset_adjoin K _ (Set.mem_range_self i)⟩ : H))
  letI : Algebra.EssFiniteType A E := Algebra.EssFiniteType.of_isLocalization E (nonZeroDivisors A)
  letI : Algebra.EssFiniteType K E := Algebra.EssFiniteType.comp K A E
  letI : Algebra.EssFiniteType H E := Algebra.EssFiniteType.of_comp K H E
  letI : Module.Finite H E := Algebra.finite_of_essFiniteType_of_isAlgebraic
  refine ⟨inferInstance,?_⟩
  exact rational_function_independent_family_bound Q hQ P v hv hP d hd hdQ hdP
    (Module.finBasis H E) (Module.finBasis H E).linearIndependent

end APSCounting893.Main
end Component_31

section Component_32
set_option autoImplicit false
open MvPolynomial
namespace APSCounting893.Main
lemma coefficientMap_totalDegree_le {K L σ : Type} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (p : MvPolynomial σ K) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  classical
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)
end APSCounting893.Main
end Component_32

section Component_33
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

lemma generic_rational_linear_field_degree {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    let E := FractionRing (MvPolynomial (Fin r) K)
    let S := MvPolynomial (Fin r × Fin m) E
    let T := FractionRing S
    let H := FractionRing (MvPolynomial (Fin r × Fin m) K)
    letI : Algebra H T := (parameterFieldEmbedding K (Fin r) (Fin r × Fin m)).toAlgebra
    let L := IntermediateField.adjoin H (Set.range (fun i : Fin r => algebraMap S T (genericLinearValues v i)))
    Module.Finite L T ∧ Module.finrank L T ≤ d^r := by
  classical
  let A := MvPolynomial (Fin r) K
  let E := FractionRing A
  let B := MvPolynomial (Fin r × Fin m) K
  let S := MvPolynomial (Fin r × Fin m) E
  let T := FractionRing S
  let H := FractionRing B
  let U := MvPolynomial (Fin r) H
  letI : Algebra H T := (parameterFieldEmbedding K (Fin r) (Fin r × Fin m)).toAlgebra
  letI : Algebra U T := (parameterPolynomialEmbedding K (Fin r) (Fin r × Fin m)).toAlgebra
  letI : SMul H U := Algebra.toSMul
  letI : SMul H T := Algebra.toSMul
  letI : SMul U T := Algebra.toSMul
  letI : IsScalarTower H U T := IsScalarTower.of_algebraMap_eq (by
    intro a
    exact (parameterPolynomialEmbedding_C K (Fin r) (Fin r × Fin m) a).symm)
  letI : IsFractionRing U T := parameterPolynomialEmbedding_isFractionRing K (Fin r) (Fin r × Fin m)
  letI : IsScalarTower B H T := IsScalarTower.of_algebraMap_eq (by
    intro b
    exact (parameterFieldEmbedding_on_polynomial K (Fin r) (Fin r × Fin m) b).symm)
  letI : Algebra.IsAlgebraic B H := IsLocalization.isAlgebraic H (nonZeroDivisors B)
  letI : Algebra.EssFiniteType K E := inferInstance
  let l : Fin r → T := fun i => algebraMap S T (genericLinearValues v i)
  have hl : AlgebraicIndependent H l :=
    (generic_linear_first_rows_independent_over_parameter_ring (le_refl r) v g hg).extendScalars H
  let Q' : U := MvPolynomial.map (algebraMap K H) Q
  let P' : Fin r → U := fun i => ∑ j, MvPolynomial.C (algebraMap B H (MvPolynomial.X (i,j))) *
    MvPolynomial.map (algebraMap K H) (P j)
  have hQ' : Q' ≠ 0 := by
    intro hz
    exact hQ ((MvPolynomial.map_injective (algebraMap K H) (algebraMap K H).injective)
      (by simpa only [map_zero] using hz))
  have hQP : algebraMap U T Q' = algebraMap S T (MvPolynomial.C (algebraMap A E Q)) :=
    parameterPolynomialEmbedding_map K (Fin r) (Fin r × Fin m) Q
  have hPP (i : Fin r) : algebraMap U T (P' i) = algebraMap U T Q' * l i := by
    change parameterPolynomialEmbedding K (Fin r) (Fin r × Fin m) (P' i) = _
    rw [show P' i = ∑ j, MvPolynomial.C (algebraMap B H (MvPolynomial.X (i,j))) *
      MvPolynomial.map (algebraMap K H) (P j) from rfl,map_sum,hQP]
    change _ = algebraMap S T (MvPolynomial.C (algebraMap A E Q)) *
      algebraMap S T (∑ j, MvPolynomial.X (i,j)*MvPolynomial.C (v j))
    rw [map_sum,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul]
    have hcj : parameterPolynomialEmbedding K (Fin r) (Fin r × Fin m)
        (MvPolynomial.C (algebraMap B H (MvPolynomial.X (i,j)))) = algebraMap S T (MvPolynomial.X (i,j)) := by
      rw [parameterPolynomialEmbedding_C,parameterFieldEmbedding_on_polynomial,MvPolynomial.map_X]
    have hpj := parameterPolynomialEmbedding_map K (Fin r) (Fin r × Fin m) (P j)
    rw [hcj,hpj,hP j,map_mul,map_mul,map_mul]
    ring
  have hdQ' : Q'.totalDegree ≤ d := (coefficientMap_totalDegree_le _ _).trans hdQ
  have hdP' (i : Fin r) : (P' i).totalDegree ≤ d := by
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C,zero_add] using
        (coefficientMap_totalDegree_le (algebraMap K H) (P j)).trans (hdP j))
  exact rational_function_field_degree_bound Q' hQ' P' l hl hPP d hd hdQ' hdP'

end APSCounting893.Main
end Component_33

section Component_34
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
open IntermediateField
namespace APSCounting893.Main

lemma adjoin_tower_generators {K H E σ τ : Type} [Field K] [Field H] [Field E]
    [Algebra K H] [Algebra K E] [Algebra H E] [IsScalarTower K H E]
    (v : σ → H) (hv : IntermediateField.adjoin K (Set.range v) = ⊤) (w : τ → E) :
    (IntermediateField.adjoin H (Set.range w)).restrictScalars K =
      IntermediateField.adjoin K (Set.range (Sum.elim (fun i => algebraMap H E (v i)) w)) := by
  let J := IntermediateField.adjoin K (Set.range (Sum.elim (fun i => algebraMap H E (v i)) w))
  have hbase (a : H) : algebraMap H E a ∈ J := by
    have ha : a ∈ IntermediateField.adjoin K (Set.range v) := by rw [hv]; trivial
    induction ha using IntermediateField.adjoin_induction with
    | mem a ha =>
      obtain ⟨i,rfl⟩ := ha
      exact IntermediateField.subset_adjoin K _ ⟨Sum.inl i,rfl⟩
    | algebraMap a =>
      rw [← IsScalarTower.algebraMap_apply K H E]
      exact J.algebraMap_mem a
    | add a b _ _ ha hb => simpa only [map_add] using J.add_mem ha hb
    | inv a _ ha => simpa only [map_inv₀] using J.inv_mem ha
    | mul a b _ _ ha hb => simpa only [map_mul] using J.mul_mem ha hb
  apply le_antisymm
  · intro a ha
    change a ∈ IntermediateField.adjoin H (Set.range w) at ha
    induction ha using IntermediateField.adjoin_induction with
    | mem a ha =>
      obtain ⟨i,rfl⟩ := ha
      exact IntermediateField.subset_adjoin K _ ⟨Sum.inr i,rfl⟩
    | algebraMap a => exact hbase a
    | add a b _ _ ha hb => exact J.add_mem ha hb
    | inv a _ ha => exact J.inv_mem ha
    | mul a b _ _ ha hb => exact J.mul_mem ha hb
  · apply IntermediateField.adjoin_le_iff.mpr
    rintro a ⟨i,rfl⟩
    cases i with
    | inl i => exact (IntermediateField.adjoin H (Set.range w)).algebraMap_mem _
    | inr i => exact IntermediateField.subset_adjoin H _ (Set.mem_range_self i)

lemma fraction_polynomial_variables_generate (K σ : Type) [Field K] :
    IntermediateField.adjoin K (Set.range (fun i : σ =>
      algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) (MvPolynomial.X i))) = ⊤ := by
  let A := MvPolynomial σ K
  let H := FractionRing A
  let J := IntermediateField.adjoin K (Set.range (fun i : σ => algebraMap A H (MvPolynomial.X i)))
  have hpoly (p : A) : algebraMap A H p ∈ J := by
    induction p using MvPolynomial.induction_on with
    | C c => exact J.algebraMap_mem c
    | add p q hp hq => simpa only [map_add] using J.add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul]
      exact J.mul_mem hp (IntermediateField.subset_adjoin K _ (Set.mem_range_self i))
  apply top_unique
  intro a _
  obtain ⟨p,q,hq,hpq⟩ := IsFractionRing.div_surjective A a
  rw [← hpq]
  exact J.div_mem (hpoly p) (hpoly q)

end APSCounting893.Main
end Component_34

section Component_35
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

noncomputable def genericFirstRowGenerators {K : Type} [Field K] {r m : ℕ}
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K)) :
    (Fin r × Fin m) ⊕ Fin r → FractionRing (MvPolynomial (Fin r × Fin m) (FractionRing (MvPolynomial (Fin r) K))) :=
  Sum.elim
    (fun a => algebraMap (MvPolynomial (Fin r × Fin m) (FractionRing (MvPolynomial (Fin r) K))) _ (MvPolynomial.X a))
    (fun i => algebraMap _ _ (genericLinearValues v i))

lemma generic_first_row_field_degree {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    let T := FractionRing (MvPolynomial (Fin r × Fin m) (FractionRing (MvPolynomial (Fin r) K)))
    let L := IntermediateField.adjoin K (Set.range (genericFirstRowGenerators v))
    Module.Finite L T ∧ Module.finrank L T ≤ d^r := by
  classical
  let E := FractionRing (MvPolynomial (Fin r) K)
  let B := MvPolynomial (Fin r × Fin m) K
  let S := MvPolynomial (Fin r × Fin m) E
  let T := FractionRing S
  let H := FractionRing B
  letI : Algebra H T := (parameterFieldEmbedding K (Fin r) (Fin r × Fin m)).toAlgebra
  letI : SMul K H := Algebra.toSMul
  letI : SMul K T := Algebra.toSMul
  letI : SMul H T := Algebra.toSMul
  letI : IsScalarTower K H T := IsScalarTower.of_algebraMap_eq (by
    intro c
    exact ((parameterFieldEmbedding K (Fin r) (Fin r × Fin m)).commutes c).symm)
  let l : Fin r → T := fun i => algebraMap S T (genericLinearValues v i)
  let L := IntermediateField.adjoin H (Set.range l)
  have hbound := generic_rational_linear_field_degree Q hQ P v hP g hg d hd hdQ hdP
  have heq := adjoin_tower_generators
    (fun a : Fin r × Fin m => algebraMap B H (MvPolynomial.X a))
    (fraction_polynomial_variables_generate K (Fin r × Fin m)) l
  have hz : (Sum.elim (fun a => algebraMap H T (algebraMap B H (MvPolynomial.X a))) l) =
      genericFirstRowGenerators v := by
    funext a
    cases a with
    | inl a =>
      change parameterFieldEmbedding K (Fin r) (Fin r × Fin m) (algebraMap B H (MvPolynomial.X a)) = _
      rw [parameterFieldEmbedding_on_polynomial,MvPolynomial.map_X]
      rfl
    | inr i => rfl
  rw [hz] at heq
  rw [← heq]
  change Module.Finite L T ∧ Module.finrank L T ≤ d^r
  exact hbound

end APSCounting893.Main
end Component_35

section Component_36
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

lemma clear_polynomial_coefficients {R H τ : Type} [CommRing R] [IsDomain R] [Field H]
    [Algebra R H] [IsFractionRing R H] (q : MvPolynomial τ H) :
    ∃ (D : R) (p : MvPolynomial τ R), D ≠ 0 ∧
      MvPolynomial.map (algebraMap R H) p = MvPolynomial.C (algebraMap R H D)*q ∧
      p.totalDegree ≤ q.totalDegree := by
  classical
  let M := (nonZeroDivisors R).map (MvPolynomial.C : R →+* MvPolynomial τ R)
  letI : IsLocalization M (MvPolynomial τ H) := MvPolynomial.isLocalization (nonZeroDivisors R) H
  obtain ⟨b,p,hp⟩ := IsLocalization.exists_integer_multiple M q
  obtain ⟨D,hD,hDb⟩ := b.property
  refine ⟨D,p,nonZeroDivisors.ne_zero hD,?_,?_⟩
  · change MvPolynomial.map (algebraMap R H) p = _
    change MvPolynomial.map (algebraMap R H) p =
      MvPolynomial.map (algebraMap R H) (b : MvPolynomial τ R)*q at hp
    rw [← hDb,MvPolynomial.map_C] at hp
    exact hp
  · have hmap : (MvPolynomial.map (algebraMap R H) p).totalDegree = p.totalDegree := by
      unfold MvPolynomial.totalDegree
      rw [MvPolynomial.support_map_of_injective p (IsFractionRing.injective R H)]
    rw [← hmap]
    change MvPolynomial.map (algebraMap R H) p =
      MvPolynomial.map (algebraMap R H) (b : MvPolynomial τ R)*q at hp
    rw [hp,← hDb,MvPolynomial.map_C]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

end APSCounting893.Main
end Component_36

section Component_37
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

lemma lift_polynomial_coefficients {R S τ : Type} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (q : MvPolynomial τ S) :
    ∃ p : MvPolynomial τ R, MvPolynomial.map f p = q ∧ p.totalDegree ≤ q.totalDegree := by
  classical
  choose u hu using hf
  let p : MvPolynomial τ R := ∑ e ∈ q.support, MvPolynomial.monomial e (u (q.coeff e))
  refine ⟨p,?_,?_⟩
  · change MvPolynomial.map f (∑ e ∈ q.support, MvPolynomial.monomial e (u (q.coeff e))) = q
    simp only [map_sum,MvPolynomial.map_monomial,hu]
    exact (MvPolynomial.as_sum q).symm
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro e he
    exact (MvPolynomial.totalDegree_monomial_le _ _).trans (MvPolynomial.le_totalDegree he)

noncomputable def adjoinRangePolynomialHom {H E σ : Type} [CommRing H] [CommRing E] [Algebra H E]
    (v : σ → E) : MvPolynomial σ H →ₐ[H] Algebra.adjoin H (Set.range v) :=
  (MvPolynomial.aeval v).codRestrict (Algebra.adjoin H (Set.range v)) (by
    intro p
    rw [← MvPolynomial.aeval_range]
    exact ⟨p,rfl⟩)

lemma adjoinRangePolynomialHom_surjective {H E σ : Type} [CommRing H] [CommRing E] [Algebra H E]
    (v : σ → E) : Function.Surjective (adjoinRangePolynomialHom (H := H) v) := by
  intro a
  have ha : a.val ∈ (MvPolynomial.aeval (R := H) v).range := by
    simpa only [MvPolynomial.aeval_range] using a.property
  obtain ⟨p,hp⟩ := ha
  exact ⟨p,Subtype.ext hp⟩

end APSCounting893.Main
end Component_37

section Component_38
set_option autoImplicit false
set_option maxHeartbeats 400000
open MvPolynomial
namespace APSCounting893.Main

lemma totalDegree_determinant_le_row_bound {R σ ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ R)) (d : ι → ℕ)
    (hd : ∀ i j, (M i j).totalDegree ≤ d i) :
    M.det.totalDegree ≤ ∑ i, d i := by
  classical
  rw [Matrix.det_apply']
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s hs
  have hcast : ((Equiv.Perm.sign s : MvPolynomial σ R)).totalDegree = 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with hh | hh <;> rw [hh] <;> simp
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [hcast,zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    (∑ i, (M (s i) i).totalDegree) ≤ ∑ i, d (s i) := Finset.sum_le_sum (fun i hi => hd _ _)
    _ = ∑ i, d i := Equiv.sum_comp s d

end APSCounting893.Main
end Component_38

section Component_39
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def universalLinearNormMatrix {H E : Type} [Field H] [Field E] [Algebra H E]
    {s m : ℕ} (b : Module.Basis (Fin s) H E) (f : Fin m → E) :
    Matrix (Fin s) (Fin s) (MvPolynomial (Fin (m+1)) H) := fun i j =>
      (if i=j then MvPolynomial.X 0 else 0) -
        ∑ a : Fin m, MvPolynomial.X a.succ * MvPolynomial.C (Algebra.leftMulMatrix b (f a) j i)

noncomputable def universalLinearNorm {H E : Type} [Field H] [Field E] [Algebra H E]
    {s m : ℕ} (b : Module.Basis (Fin s) H E) (f : Fin m → E) :
    MvPolynomial (Fin (m+1)) H := (universalLinearNormMatrix b f).det

lemma universalLinearNorm_degree {H E : Type} [Field H] [Field E] [Algebra H E]
    {s m : ℕ} (b : Module.Basis (Fin s) H E) (f : Fin m → E) :
    (universalLinearNorm b f).totalDegree ≤ s := by
  apply (totalDegree_determinant_le_row_bound _ (fun _ => 1) ?_).trans_eq (by simp)
  intro i j
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · split_ifs <;> simp
  · apply MvPolynomial.totalDegree_finsetSum_le
    intro a _
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

lemma universalLinearNorm_nonzero {H E : Type} [Field H] [Field E] [Algebra H E]
    {s m : ℕ} (b : Module.Basis (Fin s) H E) (f : Fin m → E) : universalLinearNorm b f ≠ 0 := by
  intro hz
  let x : Fin (m+1) → H := Fin.cons 1 (fun _ => 0)
  have hmat : (universalLinearNormMatrix b f).map (MvPolynomial.eval x) = 1 := by
    ext i j
    by_cases hij : i=j <;> simp [universalLinearNormMatrix,x,Matrix.one_apply,hij]
  have hh := congrArg (MvPolynomial.eval x) hz
  rw [universalLinearNorm,RingHom.map_det,map_zero] at hh
  change ((universalLinearNormMatrix b f).map (MvPolynomial.eval x)).det = 0 at hh
  rw [hmat,Matrix.det_one] at hh
  exact one_ne_zero hh

end APSCounting893.Main
end Component_39

section Component_40
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial Matrix
namespace APSCounting893.Main

lemma universalLinearNorm_vanishes {H E S : Type} [Field H] [Field E] [Algebra H E]
    [CommRing S] [IsDomain S] [Algebra E S] [Algebra H S] [IsScalarTower H E S]
    (hinj : Function.Injective (algebraMap E S))
    {s m : ℕ} (b : Module.Basis (Fin s) H E) (f : Fin m → E) (a : Fin m → S) :
    MvPolynomial.aeval (Fin.cons (∑ j, a j * algebraMap E S (f j)) a : Fin (m+1) → S)
      (universalLinearNorm b f) = 0 := by
  classical
  let l := ∑ j, a j * algebraMap E S (f j)
  let x : Fin (m+1) → S := Fin.cons l a
  let N := (universalLinearNormMatrix b f).map (MvPolynomial.aeval x)
  let v : Fin s → S := fun i => algebraMap E S (b i)
  have hreconstruct (k : Fin m) (i : Fin s) :
      ∑ j, algebraMap H S (Algebra.leftMulMatrix b (f k) j i) * v j =
        algebraMap E S (f k * b i) := by
    have hh := congrArg (algebraMap E S) (b.sum_repr (f k*b i))
    simp only [map_sum,Algebra.smul_def,map_mul,← IsScalarTower.algebraMap_apply H E S] at hh
    simpa only [Algebra.leftMulMatrix_eq_repr_mul,v,map_mul] using hh
  have hN (i j : Fin s) : N i j = (if i=j then l else 0) -
      ∑ k : Fin m, a k * algebraMap H S (Algebra.leftMulMatrix b (f k) j i) := by
    change MvPolynomial.aeval x _ = _
    unfold universalLinearNormMatrix
    simp only [map_sub,map_sum,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X]
    by_cases hij : i=j <;> simp [hij,x]
  have hzero : N *ᵥ v = 0 := by
    ext i
    simp only [Matrix.mulVec, dotProduct,hN,sub_mul,Finset.sum_sub_distrib,Finset.sum_mul]
    have hleft : (∑ j : Fin s, (if i=j then l else 0)*v j) = l*v i := by simp [ite_mul]
    rw [hleft,Finset.sum_comm]
    simp_rw [mul_assoc,← Finset.mul_sum,hreconstruct,map_mul]
    simp only [l,Finset.sum_mul]
    simp only [v,Pi.zero_apply,mul_assoc,sub_self]
  haveI : Nonempty (Fin s) := b.index_nonempty
  let i : Fin s := Classical.choice inferInstance
  have hvi : v i ≠ 0 := by
    simpa only [v,map_zero] using hinj.ne (b.ne_zero i)
  have hdet := Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors hzero
    (mem_nonZeroDivisors_iff_ne_zero.mpr hvi)
  change MvPolynomial.aeval x (universalLinearNorm b f) = 0
  rw [universalLinearNorm]
  have hh := (MvPolynomial.aeval x).toRingHom.map_det (universalLinearNormMatrix b f)
  change MvPolynomial.aeval x (universalLinearNormMatrix b f).det = N.det at hh
  exact hh.trans hdet

end APSCounting893.Main
end Component_40

section Component_41
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
open scoped IntermediateField.algebraAdjoinAdjoin
namespace APSCounting893.Main

lemma eval₂Hom_map_coeff {R S T σ : Type} [CommSemiring R] [CommSemiring S] [CommSemiring T]
    (f : R →+* S) (g : σ → T) (φ : S →+* T) (p : MvPolynomial σ R) :
    MvPolynomial.eval₂Hom φ g (MvPolynomial.map f p) =
      MvPolynomial.eval₂Hom (φ.comp f) g p := MvPolynomial.eval₂_map f g φ p

lemma norm_relation_over_generators {K E σ : Type} [Field K] [Field E] [Algebra K E]
    (v : σ → E) [Module.Finite (IntermediateField.adjoin K (Set.range v)) E]
    {m : ℕ} (f : Fin m → E) :
    ∃ p : MvPolynomial (Fin (m+1)) (MvPolynomial σ K),
      p ≠ 0 ∧ p.totalDegree ≤ Module.finrank (IntermediateField.adjoin K (Set.range v)) E ∧
      let S := MvPolynomial (Fin m) E
      let x : Fin (m+1) → S := Fin.cons (∑ j, MvPolynomial.X j * MvPolynomial.C (f j)) MvPolynomial.X
      MvPolynomial.eval₂Hom ((algebraMap E S).comp (MvPolynomial.aeval v).toRingHom) x p = 0 := by
  classical
  let R := Algebra.adjoin K (Set.range v)
  let H := IntermediateField.adjoin K (Set.range v)
  let s := Module.finrank H E
  let b := Module.finBasis H E
  let q := universalLinearNorm b f
  obtain ⟨D,pR,hD,hpR,hdeg⟩ := clear_polynomial_coefficients (R := R) q
  obtain ⟨p,hp,hpd⟩ := lift_polynomial_coefficients (adjoinRangePolynomialHom (H := K) v).toRingHom
    (adjoinRangePolynomialHom_surjective (H := K) v) pR
  have hcoeff : (MvPolynomial.aeval v).toRingHom =
      (algebraMap H E).comp ((algebraMap R H).comp (adjoinRangePolynomialHom (H := K) v).toRingHom) := by
    apply RingHom.ext
    intro p
    rfl
  have hmap : MvPolynomial.map (MvPolynomial.aeval v).toRingHom p =
      MvPolynomial.C (algebraMap H E (algebraMap R H D)) * MvPolynomial.map (algebraMap H E) q := by
    rw [hcoeff,← MvPolynomial.map_map,← MvPolynomial.map_map,hp,hpR,map_mul,MvPolynomial.map_C]
  have hDn : algebraMap H E (algebraMap R H D) ≠ 0 := by
    have hi := (algebraMap H E).injective.comp (IsFractionRing.injective R H)
    simpa only [Function.comp_apply,map_zero] using hi.ne hD
  have hqm : MvPolynomial.map (algebraMap H E) q ≠ 0 := by
    simpa only [map_zero] using (MvPolynomial.map_injective (algebraMap H E) (algebraMap H E).injective).ne
      (universalLinearNorm_nonzero b f)
  have hpn : p ≠ 0 := by
    intro hz
    rw [hz,map_zero] at hmap
    exact (mul_ne_zero (MvPolynomial.C_ne_zero.mpr hDn) hqm) hmap.symm
  refine ⟨p,hpn,hpd.trans (hdeg.trans (universalLinearNorm_degree b f)),?_⟩
  let S := MvPolynomial (Fin m) E
  let x : Fin (m+1) → S := Fin.cons (∑ j, MvPolynomial.X j * MvPolynomial.C (f j)) MvPolynomial.X
  have hvn := universalLinearNorm_vanishes (H := H) (S := S) (MvPolynomial.C_injective _ _) b f MvPolynomial.X
  have heq := congrArg (MvPolynomial.eval₂Hom (algebraMap E S) x) hmap
  rw [eval₂Hom_map_coeff] at heq
  rw [map_mul,MvPolynomial.eval₂Hom_C,eval₂Hom_map_coeff] at heq
  change MvPolynomial.eval₂Hom ((algebraMap E S).comp (MvPolynomial.aeval v).toRingHom) x p = _ at heq
  have hnv : MvPolynomial.eval₂Hom ((algebraMap E S).comp (algebraMap H E)) x q = 0 := by
    exact hvn
  rw [hnv,mul_zero] at heq
  exact heq

end APSCounting893.Main
end Component_41

section Component_42
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def weightedDegreePolynomial {K σ : Type} [CommSemiring K]
    (w : σ → ℕ) : MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) :=
  MvPolynomial.aeval (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X^(w i))

lemma weightedDegreePolynomial_monomial {K σ : Type} [CommSemiring K]
    (w : σ → ℕ) (e : σ →₀ ℕ) (c : K) :
    weightedDegreePolynomial w (MvPolynomial.monomial e c) =
      Polynomial.monomial (e.sum (fun i k => k*w i)) (MvPolynomial.monomial e c) := by
  classical
  rw [weightedDegreePolynomial,MvPolynomial.aeval_monomial]
  rw [show algebraMap K (Polynomial (MvPolynomial σ K)) c = Polynomial.C (MvPolynomial.C c) by rfl]
  simp only [mul_pow,← Polynomial.C_pow,← pow_mul]
  rw [Finsupp.prod_mul]
  have hprod : (e.prod fun i k => Polynomial.C ((MvPolynomial.X i : MvPolynomial σ K) ^ k)) =
      Polynomial.C (e.prod fun i k => (MvPolynomial.X i : MvPolynomial σ K) ^ k) := by
    unfold Finsupp.prod
    rw [map_prod]
  have hpow : (e.prod fun i k => (Polynomial.X : Polynomial (MvPolynomial σ K)) ^ (w i*k)) =
      Polynomial.X ^ (e.sum (fun i k => k*w i)) := by
    unfold Finsupp.prod Finsupp.sum
    rw [Finset.prod_pow_eq_pow_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_comm _ _
  rw [hprod,hpow,← mul_assoc,← map_mul,← MvPolynomial.monomial_eq,Polynomial.C_mul_X_pow_eq_monomial]

lemma weightedDegreePolynomial_coeff_coeff {K σ : Type} [CommSemiring K]
    (w : σ → ℕ) (p : MvPolynomial σ K) (k : ℕ) (e : σ →₀ ℕ) :
    ((weightedDegreePolynomial w p).coeff k).coeff e =
      if e.sum (fun i v => v*w i) = k then p.coeff e else 0 := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    rw [weightedDegreePolynomial_monomial,Polynomial.coeff_monomial]
    by_cases ha : a=e
    · subst a
      by_cases hk : k=e.sum (fun i k => k*w i) <;> simp [MvPolynomial.coeff_monomial,eq_comm,hk]
    · split_ifs <;> simp [MvPolynomial.coeff_monomial,ha,Ne.symm ha]
  | add p q hp hq =>
    simp only [map_add,Polynomial.coeff_add,MvPolynomial.coeff_add,hp,hq]
    split_ifs <;> simp

lemma weightedDegreePolynomial_natDegree {K σ : Type} [CommSemiring K] (w : σ → ℕ)
    (p : MvPolynomial σ K) :
    (weightedDegreePolynomial w p).natDegree = MvPolynomial.weightedTotalDegree w p := by
  classical
  let D := MvPolynomial.weightedTotalDegree w p
  have hweight (e : σ →₀ ℕ) : Finsupp.weight w e = e.sum (fun i k => k*w i) := by
    simp only [Finsupp.weight_apply,smul_eq_mul]
  apply le_antisymm
  · apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    ext e
    rw [weightedDegreePolynomial_coeff_coeff,MvPolynomial.coeff_zero]
    split_ifs with he
    · by_contra hne
      have hh := Finset.le_sup (f := fun e => Finsupp.weight w e) (MvPolynomial.mem_support_iff.mpr hne)
      rw [hweight,he] at hh
      exact (not_le_of_gt hk) hh
    · rfl
  · unfold MvPolynomial.weightedTotalDegree
    apply Finset.sup_le
    intro e he
    apply Polynomial.le_natDegree_of_ne_zero
    intro hz
    have hh := congrArg (fun q : MvPolynomial σ K => q.coeff e) hz
    rw [weightedDegreePolynomial_coeff_coeff,MvPolynomial.coeff_zero] at hh
    rw [hweight,if_pos rfl] at hh
    exact MvPolynomial.mem_support_iff.mp he hh

lemma weightedTotalDegree_mul_eq {K σ : Type} [CommRing K] [IsDomain K]
    (w : σ → ℕ) (p q : MvPolynomial σ K) (hp : p ≠ 0) (hq : q ≠ 0) :
    MvPolynomial.weightedTotalDegree w (p*q) =
      MvPolynomial.weightedTotalDegree w p + MvPolynomial.weightedTotalDegree w q := by
  have hinj : Function.Injective (weightedDegreePolynomial (K := K) w) := by
    intro a b h
    ext e
    have hh := congrArg (fun f : Polynomial (MvPolynomial σ K) => (f.coeff (e.sum (fun i k => k*w i))).coeff e) h
    simpa only [weightedDegreePolynomial_coeff_coeff,if_true] using hh
  rw [← weightedDegreePolynomial_natDegree, map_mul,Polynomial.natDegree_mul]
  · rw [weightedDegreePolynomial_natDegree,weightedDegreePolynomial_natDegree]
  · simpa only [map_zero] using hinj.ne hp
  · simpa only [map_zero] using hinj.ne hq

end APSCounting893.Main
end Component_42

section Component_43
set_option autoImplicit false
set_option maxHeartbeats 600000
open MvPolynomial
namespace APSCounting893.Main

lemma weightedDegree_add_le {K σ : Type} [CommRing K] (w : σ → ℕ) (p q : MvPolynomial σ K) :
    MvPolynomial.weightedTotalDegree w (p+q) ≤ max (MvPolynomial.weightedTotalDegree w p) (MvPolynomial.weightedTotalDegree w q) := by
  rw [← weightedDegreePolynomial_natDegree,← weightedDegreePolynomial_natDegree,← weightedDegreePolynomial_natDegree,map_add]
  exact Polynomial.natDegree_add_le _ _

lemma weightedDegree_mul_le {K σ : Type} [CommRing K] [IsDomain K] (w : σ → ℕ) (p q : MvPolynomial σ K) :
    MvPolynomial.weightedTotalDegree w (p*q) ≤ MvPolynomial.weightedTotalDegree w p + MvPolynomial.weightedTotalDegree w q := by
  rw [← weightedDegreePolynomial_natDegree,← weightedDegreePolynomial_natDegree,← weightedDegreePolynomial_natDegree,map_mul]
  exact Polynomial.natDegree_mul_le

lemma weightedDegree_pow_le {K σ : Type} [CommRing K] [IsDomain K] (w : σ → ℕ) (p : MvPolynomial σ K) (k : ℕ) :
    MvPolynomial.weightedTotalDegree w (p^k) ≤ k*MvPolynomial.weightedTotalDegree w p := by
  rw [← weightedDegreePolynomial_natDegree,← weightedDegreePolynomial_natDegree,map_pow]
  exact Polynomial.natDegree_pow_le

lemma weightedDegree_C {K σ : Type} [CommRing K] (w : σ → ℕ) (c : K) :
    MvPolynomial.weightedTotalDegree w (MvPolynomial.C c) = 0 := by
  rw [← weightedDegreePolynomial_natDegree]
  simp [weightedDegreePolynomial]

lemma weightedDegree_X_le {K σ : Type} [CommRing K] [IsDomain K] (w : σ → ℕ) (i : σ) :
    MvPolynomial.weightedTotalDegree w (MvPolynomial.X (R := K) i) ≤ w i := by
  rw [← weightedDegreePolynomial_natDegree]
  rw [weightedDegreePolynomial,MvPolynomial.aeval_X]
  exact Polynomial.natDegree_mul_le.trans (by simp [Polynomial.natDegree_pow_le])

lemma weightedDegree_finsetSum_le {K σ ι : Type} [CommRing K] (w : σ → ℕ)
    (s : Finset ι) (p : ι → MvPolynomial σ K) (D : ℕ)
    (h : ∀ i ∈ s, MvPolynomial.weightedTotalDegree w (p i) ≤ D) :
    MvPolynomial.weightedTotalDegree w (∑ i ∈ s,p i) ≤ D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.weightedTotalDegree]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (weightedDegree_add_le w _ _).trans (max_le (h a (Finset.mem_insert_self _ _)) (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))))

lemma weightedDegree_finsetProd_le {K σ ι : Type} [CommRing K] [IsDomain K] (w : σ → ℕ)
    (s : Finset ι) (p : ι → MvPolynomial σ K) :
    MvPolynomial.weightedTotalDegree w (∏ i ∈ s,p i) ≤ ∑ i ∈ s,MvPolynomial.weightedTotalDegree w (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty,Finset.sum_empty]
    exact (weightedDegree_C w (1 : K)).le
  | insert a s ha ih =>
    rw [Finset.prod_insert ha,Finset.sum_insert ha]
    exact (weightedDegree_mul_le w _ _).trans (Nat.add_le_add_left ih _)

lemma weightedDegree_eval₂_le {R K σ τ : Type} [CommRing R] [CommRing K] [IsDomain K]
    (w : σ → ℕ) (f : R →+* MvPolynomial σ K) (g : τ → MvPolynomial σ K)
    (hf : ∀ c, MvPolynomial.weightedTotalDegree w (f c)=0) (D : ℕ)
    (hg : ∀ i, MvPolynomial.weightedTotalDegree w (g i) ≤ D) (p : MvPolynomial τ R) :
    MvPolynomial.weightedTotalDegree w (MvPolynomial.eval₂Hom f g p) ≤ D*p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  apply weightedDegree_finsetSum_le
  intro e he
  rw [MvPolynomial.eval₂Hom_monomial]
  apply (weightedDegree_mul_le w _ _).trans
  rw [hf,zero_add]
  unfold Finsupp.prod
  apply (weightedDegree_finsetProd_le w _ _).trans
  calc
    ∑ i ∈ e.support, MvPolynomial.weightedTotalDegree w (g i ^ e i) ≤ ∑ i ∈ e.support, e i * D :=
      Finset.sum_le_sum (fun i _ => (weightedDegree_pow_le w _ _).trans (Nat.mul_le_mul_left _ (hg i)))
    _ = D*e.sum (fun _ k => k) := by unfold Finsupp.sum; rw [← Finset.sum_mul]; exact Nat.mul_comm _ _
    _ ≤ D*p.totalDegree := Nat.mul_le_mul_left _ (MvPolynomial.le_totalDegree he)

end APSCounting893.Main
end Component_43

section Component_44
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def signFlipHom {K σ : Type} [CommRing K] (s : σ → Bool) :
    MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
  MvPolynomial.aeval (fun i => if s i then -MvPolynomial.X i else MvPolynomial.X i)

lemma signFlipHom_involutive {K σ : Type} [CommRing K] (s : σ → Bool) :
    Function.Involutive (signFlipHom (K := K) s) := by
  have heq : (signFlipHom s).comp (signFlipHom s) = AlgHom.id K (MvPolynomial σ K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply]
    dsimp only [signFlipHom]
    rw [MvPolynomial.aeval_X]
    cases h : s i <;> simp [h]
  intro p
  exact AlgHom.congr_fun heq p

noncomputable def signedFlatten {K σ τ ι : Type} [CommRing K] (e : τ ⊕ σ ≃ ι) (s : ι → Bool) :
    MvPolynomial τ (MvPolynomial σ K) →ₐ[K] MvPolynomial ι K :=
  (signFlipHom s).comp ((MvPolynomial.renameEquiv K e).toAlgHom.comp
    (MvPolynomial.sumAlgEquiv K τ σ).symm.toAlgHom)

lemma signedFlatten_injective {K σ τ ι : Type} [CommRing K] (e : τ ⊕ σ ≃ ι) (s : ι → Bool) :
    Function.Injective (signedFlatten (K := K) e s) :=
  (signFlipHom_involutive s).injective.comp ((MvPolynomial.renameEquiv K e).injective.comp
    (MvPolynomial.sumAlgEquiv K τ σ).symm.injective)

lemma signedFlatten_X {K σ τ ι : Type} [CommRing K] (e : τ ⊕ σ ≃ ι) (s : ι → Bool) (i : τ) :
    signedFlatten (K := K) e s (MvPolynomial.X i) =
      if s (e (Sum.inl i)) then -MvPolynomial.X (e (Sum.inl i)) else MvPolynomial.X (e (Sum.inl i)) := by
  simp [signedFlatten,MvPolynomial.sumAlgEquiv_symm_X,signFlipHom]

lemma signedFlatten_C_X {K σ τ ι : Type} [CommRing K] (e : τ ⊕ σ ≃ ι) (s : ι → Bool) (i : σ) :
    signedFlatten (K := K) e s (MvPolynomial.C (MvPolynomial.X i)) =
      if s (e (Sum.inr i)) then -MvPolynomial.X (e (Sum.inr i)) else MvPolynomial.X (e (Sum.inr i)) := by
  simp [signedFlatten,MvPolynomial.sumAlgEquiv_symm_C_X,signFlipHom]

lemma weightedDegree_neg {K σ : Type} [CommRing K] (w : σ → ℕ) (p : MvPolynomial σ K) :
    MvPolynomial.weightedTotalDegree w (-p) = MvPolynomial.weightedTotalDegree w p := by
  rw [← weightedDegreePolynomial_natDegree,← weightedDegreePolynomial_natDegree,map_neg,Polynomial.natDegree_neg]

lemma signedFlatten_weighted_bound {K σ τ ι : Type} [CommRing K] [IsDomain K]
    (e : τ ⊕ σ ≃ ι) (s : ι → Bool) (w : ι → ℕ)
    (hfirst : ∀ i : σ, w (e (Sum.inr i))=0) (hlast : ∀ i : τ, w (e (Sum.inl i))≤1)
    (p : MvPolynomial τ (MvPolynomial σ K)) :
    MvPolynomial.weightedTotalDegree w (signedFlatten e s p) ≤ p.totalDegree := by
  let F := signedFlatten (K := K) e s
  let f : MvPolynomial σ K →+* MvPolynomial ι K := F.toRingHom.comp MvPolynomial.C
  let g : τ → MvPolynomial ι K := fun i => F (MvPolynomial.X i)
  have hf (c : MvPolynomial σ K) : MvPolynomial.weightedTotalDegree w (f c)=0 := by
    have heq : f = (MvPolynomial.aeval (fun i : σ => F (MvPolynomial.C (MvPolynomial.X i)))).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change F (MvPolynomial.C (MvPolynomial.C c)) = (MvPolynomial.aeval (R := K) _) (MvPolynomial.C c)
        rw [MvPolynomial.aeval_C]
        exact F.commutes c
      · intro i
        change F (MvPolynomial.C (MvPolynomial.X i)) = (MvPolynomial.aeval (R := K) _) (MvPolynomial.X i)
        rw [MvPolynomial.aeval_X]
    rw [heq]
    apply Nat.eq_zero_of_le_zero
    have hh := weightedDegree_eval₂_le w (MvPolynomial.C : K →+* MvPolynomial ι K)
      (fun i : σ => F (MvPolynomial.C (MvPolynomial.X i))) (weightedDegree_C w) 0 (fun i => ?_) c
    · change MvPolynomial.weightedTotalDegree w (MvPolynomial.eval₂Hom MvPolynomial.C _ c) ≤ 0
      simpa only [zero_mul] using hh
    · rw [show F (MvPolynomial.C (MvPolynomial.X i)) = _ from signedFlatten_C_X e s i]
      split_ifs <;> try rw [weightedDegree_neg]
      all_goals exact (weightedDegree_X_le w _).trans_eq (hfirst i)
  have hg (i : τ) : MvPolynomial.weightedTotalDegree w (g i) ≤ 1 := by
    rw [show g i = _ from signedFlatten_X e s i]
    split_ifs <;> try rw [weightedDegree_neg]
    all_goals exact (weightedDegree_X_le w _).trans (hlast i)
  have heval : MvPolynomial.eval₂Hom f g p = F p := by
    have hh : MvPolynomial.eval₂Hom f g = F.toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [MvPolynomial.eval₂Hom_C]
        rfl
      · intro i
        rw [MvPolynomial.eval₂Hom_X']
        rfl
    exact RingHom.congr_fun hh p
  have hh := weightedDegree_eval₂_le w f g hf 1 hg p
  simpa only [heval,one_mul] using hh

end APSCounting893.Main
end Component_44

section Component_45
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma signedFlatten_evaluate {K T σ τ ι : Type} [CommRing K] [CommRing T] [Algebra K T]
    (e : τ ⊕ σ ≃ ι) (s : ι → Bool) (a : ι → T)
    (p : MvPolynomial τ (MvPolynomial σ K)) :
    MvPolynomial.aeval a (signedFlatten e s p) =
      MvPolynomial.eval₂Hom
        (MvPolynomial.aeval (fun i : σ => if s (e (Sum.inr i)) then -a (e (Sum.inr i)) else a (e (Sum.inr i)))).toRingHom
        (fun i : τ => if s (e (Sum.inl i)) then -a (e (Sum.inl i)) else a (e (Sum.inl i))) p := by
  let F := signedFlatten (K := K) e s
  let v : σ → T := fun i => if s (e (Sum.inr i)) then -a (e (Sum.inr i)) else a (e (Sum.inr i))
  let w : τ → T := fun i => if s (e (Sum.inl i)) then -a (e (Sum.inl i)) else a (e (Sum.inl i))
  have hc : (MvPolynomial.aeval a).toRingHom.comp (F.toRingHom.comp MvPolynomial.C) =
      (MvPolynomial.aeval v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      change MvPolynomial.aeval a (F (MvPolynomial.C (MvPolynomial.C c))) = MvPolynomial.aeval v (MvPolynomial.C c)
      rw [MvPolynomial.aeval_C]
      rw [show F (MvPolynomial.C (MvPolynomial.C c)) = algebraMap K (MvPolynomial ι K) c from F.commutes c]
      exact (MvPolynomial.aeval a).commutes c
    · intro i
      change MvPolynomial.aeval a (F (MvPolynomial.C (MvPolynomial.X i))) = MvPolynomial.aeval v (MvPolynomial.X i)
      rw [signedFlatten_C_X,MvPolynomial.aeval_X]
      split_ifs <;> simp_all [v]
  have heq : (MvPolynomial.aeval a).toRingHom.comp F.toRingHom = MvPolynomial.eval₂Hom (MvPolynomial.aeval v).toRingHom w := by
    apply MvPolynomial.ringHom_ext
    · intro c
      rw [MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hc c
    · intro i
      change MvPolynomial.aeval a (F (MvPolynomial.X i)) = MvPolynomial.eval₂Hom _ w (MvPolynomial.X i)
      rw [signedFlatten_X,MvPolynomial.eval₂Hom_X']
      split_ifs <;> simp_all [w]
  exact RingHom.congr_fun heq p

end APSCounting893.Main
end Component_45

section Component_46
set_option autoImplicit false
set_option maxHeartbeats 600000
namespace APSCounting893.Main

def incidenceLastRowIndex (r m : ℕ) :
    Fin (m+1) ⊕ ((Fin r × Fin m) ⊕ Fin r) → Fin (r+1) × Fin (m+1)
  | .inl j => (Fin.last r,j)
  | .inr (.inl a) => (Fin.castLE (Nat.le_succ r) a.1,a.2.succ)
  | .inr (.inr i) => (Fin.castLE (Nat.le_succ r) i,0)

lemma incidenceLastRowIndex_injective (r m : ℕ) : Function.Injective (incidenceLastRowIndex r m) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (congrArg (fun x : Fin (r+1) × Fin (m+1) => x.2) h)
    | inr b =>
      cases b with
      | inl b =>
        have hh := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1.val) h
        change r=b.1.val at hh
        have := b.1.isLt
        omega
      | inr b =>
        have hh := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1.val) h
        change r=b.val at hh
        have := b.isLt
        omega
  | inr a =>
    cases b with
    | inl b =>
      cases a with
      | inl a =>
        have hh := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1.val) h
        change a.1.val=r at hh
        have := a.1.isLt
        omega
      | inr a =>
        have hh := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1.val) h
        change a.val=r at hh
        have := a.isLt
        omega
    | inr b =>
      cases a with
      | inl a =>
        cases b with
        | inl b =>
          have h1 := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1.val) h
          have h2 := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.2) h
          exact congrArg (Sum.inr ∘ Sum.inl) (Prod.ext (Fin.ext h1) (Fin.succ_injective _ h2))
        | inr b => exact (Fin.succ_ne_zero a.2 (congrArg (fun x : Fin (r+1) × Fin (m+1) => x.2) h)).elim
      | inr a =>
        cases b with
        | inl b => exact (Fin.succ_ne_zero b.2 (congrArg (fun x : Fin (r+1) × Fin (m+1) => x.2) h).symm).elim
        | inr b =>
          have h1 := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1.val) h
          exact congrArg (Sum.inr ∘ Sum.inr) (Fin.ext h1)

noncomputable def incidenceLastRowEquiv (r m : ℕ) :
    Fin (m+1) ⊕ ((Fin r × Fin m) ⊕ Fin r) ≃ Fin (r+1) × Fin (m+1) :=
  Equiv.ofBijective (incidenceLastRowIndex r m) (by
    refine ⟨incidenceLastRowIndex_injective r m,?_⟩
    intro ⟨i,j⟩
    by_cases hi : i=Fin.last r
    · exact ⟨Sum.inl j,Prod.ext hi.symm rfl⟩
    · have hir : i.val<r := by
        by_contra hn
        have hh : i.val=r := by have := i.isLt; omega
        exact hi (Fin.ext hh)
      refine Fin.cases ?_ (fun j => ?_) j
      · exact ⟨Sum.inr (Sum.inr ⟨i.val,hir⟩),Prod.ext (Fin.ext rfl) rfl⟩
      · exact ⟨Sum.inr (Sum.inl (⟨i.val,hir⟩,j)),Prod.ext (Fin.ext rfl) rfl⟩)

@[simp] lemma incidenceLastRowEquiv_apply (r m : ℕ)
    (i : Fin (m+1) ⊕ ((Fin r × Fin m) ⊕ Fin r)) :
    incidenceLastRowEquiv r m i = incidenceLastRowIndex r m i := rfl

end APSCounting893.Main
end Component_46

section Component_47
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def rowDegree {K ι κ : Type} [CommSemiring K] [DecidableEq ι]
    (i : ι) (p : MvPolynomial (ι × κ) K) : ℕ :=
  MvPolynomial.weightedTotalDegree (fun a : ι × κ => if a.1=i then (1 : ℕ) else 0) p

lemma rowDegree_le_iff {K ι κ : Type} [CommSemiring K] [DecidableEq ι]
    (i : ι) (p : MvPolynomial (ι × κ) K) (d : ℕ) :
    rowDegree i p ≤ d ↔ ∀ e ∈ p.support, e.sum (fun a k => if a.1=i then k else 0) ≤ d := by
  classical
  simp only [rowDegree,MvPolynomial.weightedTotalDegree,Finset.sup_le_iff]
  congr! 3
  simp [Finsupp.weight,Finsupp.linearCombination_apply,Finsupp.sum,smul_eq_mul]

lemma totalDegree_le_sum_rowDegree {K ι κ : Type} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial (ι × κ) K) : p.totalDegree ≤ ∑ i, rowDegree i p := by
  classical
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro e he
  have hs : e.sum (fun _ k => k) = ∑ i : ι, e.sum (fun a k => if a.1=i then k else 0) := by
    unfold Finsupp.sum
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    simp
  rw [hs]
  apply Finset.sum_le_sum
  intro i _
  exact (rowDegree_le_iff i p _).mp le_rfl e he

lemma rowDegree_mul_eq {K ι κ : Type} [CommRing K] [IsDomain K] [DecidableEq ι]
    (i : ι) (p q : MvPolynomial (ι × κ) K) (hp : p ≠ 0) (hq : q ≠ 0) :
    rowDegree i (p*q) = rowDegree i p + rowDegree i q :=
  weightedTotalDegree_mul_eq _ p q hp hq

lemma rowDegree_le_of_dvd {K ι κ : Type} [CommRing K] [IsDomain K] [DecidableEq ι]
    (i : ι) {p q : MvPolynomial (ι × κ) K} (h : p ∣ q) (hq : q ≠ 0) :
    rowDegree i p ≤ rowDegree i q := by
  obtain ⟨b,rfl⟩ := h
  rw [rowDegree_mul_eq i p b (left_ne_zero_of_mul hq) (right_ne_zero_of_mul hq)]
  exact Nat.le_add_right _ _

lemma rowDegree_rename_rows {K ι κ : Type} [CommSemiring K] [DecidableEq ι]
    (e : ι ≃ ι) (i : ι) (p : MvPolynomial (ι × κ) K) :
    rowDegree (e i) (MvPolynomial.rename (fun a : ι × κ => (e a.1,a.2)) p) = rowDegree i p := by
  have hinj : Function.Injective (fun a : ι × κ => (e a.1,a.2)) := by
    intro a b h
    apply Prod.ext
    · exact e.injective (congrArg Prod.fst h)
    · simpa only using congrArg (fun x : ι × κ => x.2) h
  unfold rowDegree
  rw [MvPolynomial.weightedTotalDegree_rename_of_injective hinj]
  congr 1
  funext a
  simp only [Function.comp_apply,Equiv.apply_eq_iff_eq]

lemma totalDegree_le_rows_bound {K ι κ : Type} [CommSemiring K] [Fintype ι] [DecidableEq ι]
    (p : MvPolynomial (ι × κ) K) (d : ℕ) (h : ∀ i, rowDegree i p ≤ d) :
    p.totalDegree ≤ Fintype.card ι * d := by
  apply (totalDegree_le_sum_rowDegree p).trans
  exact (Finset.sum_le_sum (fun i _ => h i)).trans_eq (by simp)

end APSCounting893.Main
end Component_47

section Component_48
set_option autoImplicit false
set_option maxHeartbeats 600000
open MvPolynomial
namespace APSCounting893.Main

noncomputable def incidenceFlatten {K : Type} [CommRing K] (r m : ℕ) :
    MvPolynomial (Fin (m+1)) (MvPolynomial ((Fin r × Fin m) ⊕ Fin r) K) →ₐ[K]
      MvPolynomial (Fin (r+1) × Fin (m+1)) K :=
  signedFlatten (incidenceLastRowEquiv r m) (fun a => decide (a.2=0))

lemma incidenceFlatten_injective {K : Type} [CommRing K] (r m : ℕ) :
    Function.Injective (incidenceFlatten (K := K) r m) := signedFlatten_injective _ _

lemma incidenceFlatten_last_row_degree {K : Type} [CommRing K] [IsDomain K] (r m : ℕ)
    (p : MvPolynomial (Fin (m+1)) (MvPolynomial ((Fin r × Fin m) ⊕ Fin r) K)) :
    rowDegree (Fin.last r) (incidenceFlatten r m p) ≤ p.totalDegree := by
  classical
  apply signedFlatten_weighted_bound
  · intro i
    cases i with
    | inl a =>
      change (if (Fin.castLE (Nat.le_succ r) a.1)=Fin.last r then (1 : ℕ) else 0)=0
      have hn : Fin.castLE (Nat.le_succ r) a.1 ≠ Fin.last r := by
        intro hh
        have hh' := congrArg Fin.val hh
        change a.1.val=r at hh'
        have := a.1.isLt
        omega
      simp [hn]
    | inr i =>
      change (if (Fin.castLE (Nat.le_succ r) i)=Fin.last r then (1 : ℕ) else 0)=0
      have hn : Fin.castLE (Nat.le_succ r) i ≠ Fin.last r := by
        intro hh
        have hh' := congrArg Fin.val hh
        change i.val=r at hh'
        have := i.isLt
        omega
      simp [hn]
  · intro i
    change (if Fin.last r=Fin.last r then (1 : ℕ) else 0)≤1
    simp

end APSCounting893.Main
end Component_48

section Component_49

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open Polynomial
namespace APSCounting893.Main

attribute [local instance] Polynomial.algebra Polynomial.isLocalization

lemma polynomial_prime_height_one_of_contract_zero {R : Type} [CommRing R] [IsDomain R]
    (P : Ideal R[X]) [P.IsPrime] (hP : P ≠ ⊥)
    (hcontract : Ideal.comap Polynomial.C P = ⊥) : P.height = 1 := by
  let K := FractionRing R
  let M : Submonoid R[X] := (nonZeroDivisors R).map Polynomial.C
  let Q : Ideal K[X] := P.map (algebraMap R[X] K[X])
  have hd : Disjoint (M : Set R[X]) (P : Set R[X]) := by
    refine Set.disjoint_left.mpr ?_
    rintro q ⟨r, hr, rfl⟩ hq
    have hr0 : r = 0 := by
      have hh : r ∈ Ideal.comap Polynomial.C P := hq
      rw [hcontract, Ideal.mem_bot] at hh
      exact hh
    exact (nonZeroDivisors.ne_zero hr) hr0
  haveI : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M K[X] P inferInstance hd
  have hinj : Function.Injective (algebraMap R[X] K[X]) :=
    Polynomial.map_injective (algebraMap R K) (IsFractionRing.injective R K)
  have hQ : Q ≠ ⊥ := by
    intro h
    exact hP ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  haveI : Q.IsMaximal := IsPrime.to_maximal_ideal hQ
  have hh := IsPrincipalIdealRing.height_eq_one_of_isMaximal Q (Polynomial.not_isField K)
  have he := IsLocalization.height_map_of_disjoint (S := K[X]) M P hd
  exact he.symm.trans hh

lemma polynomial_prime_principal_of_contract_zero {R : Type} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R]
    (P : Ideal R[X]) [P.IsPrime] (hcontract : Ideal.comap Polynomial.C P = ⊥) :
    P.IsPrincipal := by
  by_cases hP : P = ⊥
  · rw [hP]; infer_instance
  · exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
      (polynomial_prime_height_one_of_contract_zero P hP hcontract)

end APSCounting893.Main
end Component_49

section Component_50

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma mv_prime_principal_of_contract_complement_zero {K σ : Type} [CommRing K] [IsDomain K] [UniqueFactorizationMonoid K]
    (v : σ) (I : Ideal (MvPolynomial σ K)) [I.IsPrime]
    (hcontract : I.comap (MvPolynomial.rename (Subtype.val : {w : σ // w ≠ v} → σ)) = ⊥) :
    I.IsPrincipal := by
  classical
  let e : MvPolynomial σ K ≃ₐ[K] Polynomial (MvPolynomial {w : σ // w ≠ v} K) :=
    (MvPolynomial.renameEquiv K (Equiv.optionSubtypeNe v).symm).trans
      (MvPolynomial.optionEquivLeft K _)
  have he (p : MvPolynomial {w : σ // w ≠ v} K) :
      e (MvPolynomial.rename Subtype.val p) = Polynomial.C p := by
    have hh : e.toRingEquiv.toRingHom.comp (MvPolynomial.rename Subtype.val).toRingHom =
        (Polynomial.C : MvPolynomial {w : σ // w ≠ v} K →+* _) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        simp [e]
      · intro i
        have hsome : (Equiv.optionSubtypeNe v).symm i.1 = some i := by
          apply (Equiv.optionSubtypeNe v).injective
          simp [i.property]
        simp [e,hsome]
    exact RingHom.congr_fun hh p
  let P : Ideal (Polynomial (MvPolynomial {w : σ // w ≠ v} K)) := I.comap e.symm.toRingEquiv.toRingHom
  haveI : P.IsPrime := Ideal.comap_isPrime _ _
  have hP : P.comap Polynomial.C = ⊥ := by
    ext p
    change e.symm (Polynomial.C p) ∈ I ↔ p ∈ (⊥ : Ideal _)
    have hh : e.symm (Polynomial.C p) = MvPolynomial.rename Subtype.val p := by
      apply e.injective
      rw [AlgEquiv.apply_symm_apply,he]
    rw [hh]
    exact SetLike.ext_iff.mp hcontract p
  obtain ⟨p,hgen⟩ := polynomial_prime_principal_of_contract_zero P hP
  refine ⟨e.symm p,?_⟩
  have hmap := congrArg (Ideal.map e.symm.toRingEquiv.toRingHom) hgen
  rw [Ideal.map_span,Set.image_singleton] at hmap
  have hPI : P.map e.symm.toRingEquiv.toRingHom = I :=
    Ideal.map_comap_of_surjective _ e.symm.surjective _
  rwa [hPI] at hmap

end APSCounting893.Main
end Component_50

section Component_51
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

/-- Coordinates on the normalized incidence chart, with the pivot column first. -/
noncomputable def genericIncidenceChartValues {E : Type} [Field E] {r m : ℕ} (f : Fin m → E) :
    Fin (r+1) × Fin (m+1) → FractionRing (MvPolynomial (Fin (r+1) × Fin m) E) :=
  fun a => Fin.cases (-algebraMap _ _ (genericLinearValues f a.1))
    (fun j => algebraMap (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)) (MvPolynomial.X (a.1,j))) a.2

noncomputable def genericIncidenceChartHom (K : Type) {E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) :
    MvPolynomial (Fin (r+1) × Fin (m+1)) K →ₐ[K]
      FractionRing (MvPolynomial (Fin (r+1) × Fin m) E) :=
  MvPolynomial.aeval (genericIncidenceChartValues (r := r) f)

/-- All free coefficients and the first `r` pivot entries are independent. -/
lemma generic_incidence_selected_independent {K E : Type} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra.EssFiniteType K E] {r m : ℕ}
    (f : Fin m → E) (g : Fin r → Fin m) (hg : AlgebraicIndependent K (f ∘ g)) :
    AlgebraicIndependent K (Sum.elim
      (fun i : Fin r => algebraMap _ (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
        (genericLinearValues f (Fin.castLE (Nat.le_succ r) i)))
      (fun a : Fin (r+1) × Fin m => algebraMap (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
        (MvPolynomial.X a))) := by
  let R := MvPolynomial (Fin (r+1) × Fin m) K
  let S := MvPolynomial (Fin (r+1) × Fin m) E
  let T := FractionRing S
  have hx : AlgebraicIndependent K (fun a : Fin (r+1) × Fin m => MvPolynomial.X (R := K) a) :=
    MvPolynomial.algebraicIndependent_X _ _
  have hl := generic_linear_first_rows_independent_over_parameter_ring (Nat.le_succ r) f g hg
  have hh := hx.sumElim_comp hl
  convert hh using 1
  funext a
  cases a with
  | inl i => rfl
  | inr a =>
    change algebraMap S T (MvPolynomial.X a) = algebraMap R T (MvPolynomial.X a)
    rw [IsScalarTower.algebraMap_apply R S T]
    congr 1
    exact (MvPolynomial.map_X (algebraMap K E) a).symm

end APSCounting893.Main
end Component_51

section Component_52
set_option autoImplicit false
set_option maxHeartbeats 600000
open MvPolynomial
namespace APSCounting893.Main

lemma incidenceFlatten_chart_evaluation {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E)
    (p : MvPolynomial (Fin (m+1)) (MvPolynomial ((Fin r × Fin m) ⊕ Fin r) K)) :
    let S := MvPolynomial (Fin (r+1) × Fin m) E
    let T := FractionRing S
    genericIncidenceChartHom K f (incidenceFlatten r m p) =
      MvPolynomial.eval₂Hom
        (MvPolynomial.aeval (Sum.elim
          (fun a : Fin r × Fin m => algebraMap S T (MvPolynomial.X (Fin.castLE (Nat.le_succ r) a.1,a.2)))
          (fun i : Fin r => algebraMap S T (genericLinearValues f (Fin.castLE (Nat.le_succ r) i))))).toRingHom
        (Fin.cons (algebraMap S T (genericLinearValues f (Fin.last r)))
          (fun j => algebraMap S T (MvPolynomial.X (Fin.last r,j))) : Fin (m+1) → T) p := by
  classical
  let S := MvPolynomial (Fin (r+1) × Fin m) E
  let T := FractionRing S
  change MvPolynomial.aeval (genericIncidenceChartValues f) (signedFlatten _ _ p) = _
  rw [signedFlatten_evaluate]
  have hcoeff : (fun i : (Fin r × Fin m) ⊕ Fin r =>
      if decide (((incidenceLastRowEquiv r m) (Sum.inr i)).2=0) then
        -genericIncidenceChartValues f ((incidenceLastRowEquiv r m) (Sum.inr i))
      else genericIncidenceChartValues f ((incidenceLastRowEquiv r m) (Sum.inr i))) =
      Sum.elim (fun a : Fin r × Fin m => algebraMap S T (MvPolynomial.X (Fin.castLE (Nat.le_succ r) a.1,a.2)))
        (fun i : Fin r => algebraMap S T (genericLinearValues f (Fin.castLE (Nat.le_succ r) i))) := by
    funext i
    cases i <;> simp [incidenceLastRowEquiv_apply,incidenceLastRowIndex,genericIncidenceChartValues] <;> rfl
  have hlast : (fun i : Fin (m+1) =>
      if decide (((incidenceLastRowEquiv r m) (Sum.inl i)).2=0) then
        -genericIncidenceChartValues f ((incidenceLastRowEquiv r m) (Sum.inl i))
      else genericIncidenceChartValues f ((incidenceLastRowEquiv r m) (Sum.inl i))) =
      (Fin.cons (algebraMap S T (genericLinearValues f (Fin.last r)))
        (fun j => algebraMap S T (MvPolynomial.X (Fin.last r,j))) : Fin (m+1) → T) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [incidenceLastRowEquiv_apply,incidenceLastRowIndex,genericIncidenceChartValues]
      rfl
    · simp [incidenceLastRowEquiv_apply,incidenceLastRowIndex,genericIncidenceChartValues]
      rfl
  rw [hcoeff,hlast]

end APSCounting893.Main
end Component_52

section Component_53
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

def firstRowsIndex (r m : ℕ) (a : Fin r × Fin m) : Fin (r+1) × Fin m :=
  (Fin.castLE (Nat.le_succ r) a.1,a.2)

lemma firstRowsIndex_injective (r m : ℕ) : Function.Injective (firstRowsIndex r m) := by
  intro a b h
  have h1 := congrArg (fun a : Fin (r+1) × Fin m => a.1.val) h
  have h2 := congrArg (fun a : Fin (r+1) × Fin m => a.2) h
  exact Prod.ext (Fin.ext h1) h2

noncomputable def firstRowsFieldEmbedding (E : Type) [Field E] (r m : ℕ) :
    FractionRing (MvPolynomial (Fin r × Fin m) E) →+*
      FractionRing (MvPolynomial (Fin (r+1) × Fin m) E) := by
  let A := MvPolynomial (Fin r × Fin m) E
  let B := MvPolynomial (Fin (r+1) × Fin m) E
  let T := FractionRing B
  let g : A →+* T := (algebraMap B T).comp (MvPolynomial.rename (firstRowsIndex r m)).toRingHom
  apply IsFractionRing.lift (g := g)
  change Function.Injective ((algebraMap B T) ∘ (MvPolynomial.rename (firstRowsIndex r m)))
  exact (IsFractionRing.injective B T).comp (MvPolynomial.rename_injective (R := E) (firstRowsIndex r m) (firstRowsIndex_injective r m))

lemma firstRowsFieldEmbedding_map (E : Type) [Field E] (r m : ℕ)
    (p : MvPolynomial (Fin r × Fin m) E) :
    firstRowsFieldEmbedding E r m (algebraMap _ (FractionRing (MvPolynomial (Fin r × Fin m) E)) p) =
      algebraMap _ (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
        (MvPolynomial.rename (firstRowsIndex r m) p) := by
  unfold firstRowsFieldEmbedding
  apply IsFractionRing.lift_algebraMap

noncomputable def lastRowPolynomialEmbedding (E : Type) [Field E] (r m : ℕ) :
    MvPolynomial (Fin m) (FractionRing (MvPolynomial (Fin r × Fin m) E)) →+*
      FractionRing (MvPolynomial (Fin (r+1) × Fin m) E) :=
  MvPolynomial.eval₂Hom (firstRowsFieldEmbedding E r m)
    (fun j => algebraMap (MvPolynomial (Fin (r+1) × Fin m) E) _ (MvPolynomial.X (Fin.last r,j)))

end APSCounting893.Main
end Component_53

section Component_54
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

lemma firstRowsFieldEmbedding_genericLinearValues {E : Type} [Field E] {r m : ℕ}
    (f : Fin m → E) (i : Fin r) :
    firstRowsFieldEmbedding E r m
      (algebraMap _ (FractionRing (MvPolynomial (Fin r × Fin m) E)) (genericLinearValues f i)) =
      algebraMap _ (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
        (genericLinearValues f (Fin.castLE (Nat.le_succ r) i)) := by
  rw [firstRowsFieldEmbedding_map]
  congr 1
  simp [genericLinearValues,firstRowsIndex]

lemma firstRowsFieldEmbedding_C {E : Type} [Field E] (r m : ℕ) (a : E) :
    firstRowsFieldEmbedding E r m
      (algebraMap (MvPolynomial (Fin r × Fin m) E) (FractionRing (MvPolynomial (Fin r × Fin m) E)) (MvPolynomial.C a)) =
      algebraMap (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)) (MvPolynomial.C a) := by
  rw [firstRowsFieldEmbedding_map,MvPolynomial.rename_C]

lemma lastRowPolynomialEmbedding_C {E : Type} [Field E] (r m : ℕ)
    (a : FractionRing (MvPolynomial (Fin r × Fin m) E)) :
    lastRowPolynomialEmbedding E r m (MvPolynomial.C a) = firstRowsFieldEmbedding E r m a :=
  MvPolynomial.eval₂Hom_C _ _ _

lemma lastRowPolynomialEmbedding_X {E : Type} [Field E] (r m : ℕ) (j : Fin m) :
    lastRowPolynomialEmbedding E r m (MvPolynomial.X j) =
      algebraMap (MvPolynomial (Fin (r+1) × Fin m) E) _ (MvPolynomial.X (Fin.last r,j)) :=
  MvPolynomial.eval₂Hom_X' _ _ _

end APSCounting893.Main
end Component_54

section Component_55
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma exists_incidence_relation_last_row_bound {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) K,
      q ≠ 0 ∧ rowDegree (Fin.last r) q ≤ d^r ∧ genericIncidenceChartHom K v q = 0 := by
  classical
  let E := FractionRing (MvPolynomial (Fin r) K)
  let S0 := MvPolynomial (Fin r × Fin m) E
  let T0 := FractionRing S0
  let S := MvPolynomial (Fin (r+1) × Fin m) E
  let T := FractionRing S
  let z := genericFirstRowGenerators v
  let L := IntermediateField.adjoin K (Set.range z)
  obtain ⟨hfinite,hdegree⟩ := generic_first_row_field_degree Q hQ P v hP g hg d hd hdQ hdP
  letI : Module.Finite L T0 := hfinite
  let f : Fin m → T0 := fun i => algebraMap S0 T0 (MvPolynomial.C (v i))
  obtain ⟨p,hpn,hpd,hvan⟩ := norm_relation_over_generators (K := K) z f
  let q := incidenceFlatten (K := K) r m p
  have hqn : q ≠ 0 := by
    simpa only [map_zero] using (incidenceFlatten_injective (K := K) r m).ne hpn
  refine ⟨q,hqn,(incidenceFlatten_last_row_degree r m p).trans (hpd.trans hdegree),?_⟩
  let U := MvPolynomial (Fin m) T0
  let phi : U →+* T := lastRowPolynomialEmbedding E r m
  let c : (Fin r × Fin m) ⊕ Fin r → T := Sum.elim
    (fun a => algebraMap S T (MvPolynomial.X (Fin.castLE (Nat.le_succ r) a.1,a.2)))
    (fun i => algebraMap S T (genericLinearValues v (Fin.castLE (Nat.le_succ r) i)))
  let x : Fin (m+1) → U := Fin.cons (∑ j, MvPolynomial.X j * MvPolynomial.C (f j)) MvPolynomial.X
  let y : Fin (m+1) → T := Fin.cons (algebraMap S T (genericLinearValues v (Fin.last r)))
    (fun j => algebraMap S T (MvPolynomial.X (Fin.last r,j)))
  have hc : phi.comp ((algebraMap T0 U).comp (MvPolynomial.aeval (R := K) z).toRingHom) =
      (MvPolynomial.aeval (R := K) c).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change phi (MvPolynomial.C (MvPolynomial.aeval (R := K) z (MvPolynomial.C k))) = MvPolynomial.aeval (R := K) c (MvPolynomial.C k)
      rw [MvPolynomial.aeval_C,MvPolynomial.aeval_C]
      change lastRowPolynomialEmbedding E r m (MvPolynomial.C (algebraMap K T0 k)) = algebraMap K T k
      rw [lastRowPolynomialEmbedding_C]
      change firstRowsFieldEmbedding E r m (algebraMap S0 T0 (MvPolynomial.C (algebraMap K E k))) = _
      rw [firstRowsFieldEmbedding_C]
      rfl
    · intro i
      change phi (MvPolynomial.C (MvPolynomial.aeval (R := K) z (MvPolynomial.X i))) = MvPolynomial.aeval (R := K) c (MvPolynomial.X i)
      rw [MvPolynomial.aeval_X,MvPolynomial.aeval_X]
      change lastRowPolynomialEmbedding E r m (MvPolynomial.C (z i)) = c i
      rw [lastRowPolynomialEmbedding_C]
      cases i with
      | inl a =>
        change firstRowsFieldEmbedding E r m (algebraMap S0 T0 (MvPolynomial.X a)) = _
        rw [firstRowsFieldEmbedding_map,MvPolynomial.rename_X]
        rfl
      | inr i => exact firstRowsFieldEmbedding_genericLinearValues v i
  have hy : (fun i => phi (x i)) = y := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change phi (∑ j, MvPolynomial.X j*MvPolynomial.C (f j)) = algebraMap S T (genericLinearValues v (Fin.last r))
      rw [map_sum]
      simp only [map_mul]
      change (∑ j, lastRowPolynomialEmbedding E r m (MvPolynomial.X j) *
        lastRowPolynomialEmbedding E r m (MvPolynomial.C (algebraMap S0 T0 (MvPolynomial.C (v j))))) = _
      simp only [lastRowPolynomialEmbedding_X,lastRowPolynomialEmbedding_C,firstRowsFieldEmbedding_C]
      simp only [genericLinearValues,map_sum,map_mul]
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (fun a => algebraMap S T (MvPolynomial.X (Fin.last r,j))*a)
        (firstRowsFieldEmbedding_C r m (v j))
    · exact lastRowPolynomialEmbedding_X r m j
  have hv' := congrArg phi hvan
  change phi (MvPolynomial.eval₂Hom ((algebraMap T0 U).comp (MvPolynomial.aeval (R := K) z).toRingHom) x p) = 0 at hv'
  rw [MvPolynomial.map_eval₂Hom,hc,hy] at hv'
  exact (incidenceFlatten_chart_evaluation v p).trans hv'

end APSCounting893.Main
end Component_55

section Component_56
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

lemma algebraicIndependent_unit_scaling {K E σ : Type} [CommRing K] [CommRing E] [Algebra K E]
    (v : σ → E) (hv : AlgebraicIndependent K v) (u : σ → Kˣ) :
    AlgebraicIndependent K (fun i => (u i : K) • v i) := by
  let f : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (u i : K)*MvPolynomial.X i)
  let g : MvPolynomial σ K →ₐ[K] MvPolynomial σ K :=
    MvPolynomial.aeval (fun i => MvPolynomial.C (((u i)⁻¹ : Kˣ) : K)*MvPolynomial.X i)
  have hgf : g.comp f = AlgHom.id K (MvPolynomial σ K) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply,AlgHom.id_apply]
    dsimp only [f,g]
    rw [MvPolynomial.aeval_X,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X]
    change MvPolynomial.C (u i : K) * (MvPolynomial.C (((u i)⁻¹ : Kˣ) : K)*MvPolynomial.X i) = MvPolynomial.X i
    rw [← mul_assoc,← map_mul]
    simp
  have hfi : Function.Injective f := by
    have hleft : Function.LeftInverse g f := by
      intro p
      exact AlgHom.congr_fun hgf p
    exact hleft.injective
  have hcomp : MvPolynomial.aeval (fun i => (u i : K) • v i) = (MvPolynomial.aeval v).comp f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply]
    dsimp only [f]
    rw [MvPolynomial.aeval_X,MvPolynomial.aeval_X,map_mul,MvPolynomial.aeval_C,MvPolynomial.aeval_X]
    exact Algebra.smul_def _ _
  change Function.Injective (MvPolynomial.aeval _)
  rw [hcomp]
  exact (show Function.Injective (MvPolynomial.aeval v) from hv).comp hfi

end APSCounting893.Main
end Component_56

section Component_57
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def incidenceChartIndex (r m : ℕ) :
    Fin r ⊕ (Fin (r+1) × Fin m) → Fin (r+1) × Fin (m+1) :=
  Sum.elim (fun i => (Fin.castLE (Nat.le_succ r) i,0)) (fun a => (a.1,a.2.succ))

lemma incidenceChartIndex_injective (r m : ℕ) : Function.Injective (incidenceChartIndex r m) := by
  intro a b h
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Fin.ext
      exact congrArg (fun x => x.1.val) h
    | inr b => exact (Fin.succ_ne_zero b.2 (congrArg Prod.snd h).symm).elim
  | inr a =>
    cases b with
    | inl b => exact (Fin.succ_ne_zero a.2 (congrArg Prod.snd h)).elim
    | inr b =>
      apply congrArg Sum.inr
      change (a.1,a.2.succ)=(b.1,b.2.succ) at h
      have h1 := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.1) h
      have h2 := congrArg (fun x : Fin (r+1) × Fin (m+1) => x.2) h
      exact Prod.ext h1 (Fin.succ_injective _ h2)

lemma incidenceChartIndex_ne_last (r m : ℕ) (a : Fin r ⊕ (Fin (r+1) × Fin m)) :
    incidenceChartIndex r m a ≠ (Fin.last r,0) := by
  intro h
  cases a with
  | inl i =>
    have hh := congrArg (fun x => x.1.val) h
    change i.val=r at hh
    exact (Nat.ne_of_lt i.isLt) hh
  | inr a => exact Fin.succ_ne_zero a.2 (congrArg Prod.snd h)

noncomputable def incidenceChartComplementEquiv (r m : ℕ) :
    (Fin r ⊕ (Fin (r+1) × Fin m)) ≃
      {a : Fin (r+1) × Fin (m+1) // a ≠ (Fin.last r,0)} :=
  Equiv.ofBijective (fun a => ⟨incidenceChartIndex r m a,incidenceChartIndex_ne_last r m a⟩) (by
    constructor
    · intro a b h
      exact incidenceChartIndex_injective r m (congrArg Subtype.val h)
    · intro a
      classical
      obtain ⟨⟨i,j⟩,ha⟩ := a
      revert ha
      refine Fin.cases ?_ (fun j => ?_) j
      · intro ha
        have hi : i.val < r := by
          by_contra hn
          have heq : i=Fin.last r := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
          exact ha (Prod.ext heq rfl)
        refine ⟨Sum.inl ⟨i.val,hi⟩,?_⟩
        exact Subtype.ext (Prod.ext (Fin.ext rfl) rfl)
      · intro ha
        exact ⟨Sum.inr (i,j),rfl⟩)

lemma genericIncidenceChartValues_index {E : Type} [Field E] {r m : ℕ}
    (f : Fin m → E) (a : Fin r ⊕ (Fin (r+1) × Fin m)) :
    genericIncidenceChartValues (r := r) f (incidenceChartIndex r m a) =
      Sum.elim (fun i : Fin r => -algebraMap _ (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
        (genericLinearValues f (Fin.castLE (Nat.le_succ r) i)))
      (fun a : Fin (r+1) × Fin m => algebraMap (MvPolynomial (Fin (r+1) × Fin m) E)
        (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)) (MvPolynomial.X a)) a := by
  cases a <;> simp [incidenceChartIndex,genericIncidenceChartValues]

lemma generic_incidence_complement_independent {K E : Type} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra.EssFiniteType K E] {r m : ℕ}
    (f : Fin m → E) (g : Fin r → Fin m) (hg : AlgebraicIndependent K (f ∘ g)) :
    AlgebraicIndependent K (fun a : {a : Fin (r+1) × Fin (m+1) // a ≠ (Fin.last r,0)} =>
      genericIncidenceChartValues (r := r) f a.val) := by
  classical
  have hh := generic_incidence_selected_independent f g hg
  let u : Fin r ⊕ (Fin (r+1) × Fin m) → Kˣ := Sum.elim (fun _ => -1) (fun _ => 1)
  have hs := algebraicIndependent_unit_scaling _ hh u
  have hs' := hs.comp (incidenceChartComplementEquiv r m).symm (incidenceChartComplementEquiv r m).symm.injective
  convert hs' using 1
  funext a
  have hi := genericIncidenceChartValues_index f ((incidenceChartComplementEquiv r m).symm a)
  have he : incidenceChartIndex r m ((incidenceChartComplementEquiv r m).symm a) = a.val :=
    congrArg Subtype.val ((incidenceChartComplementEquiv r m).apply_symm_apply a)
  rw [he] at hi
  rw [hi]
  cases hcase : (incidenceChartComplementEquiv r m).symm a <;> simp [u,hcase]

end APSCounting893.Main
end Component_57

section Component_58
set_option autoImplicit false
set_option maxHeartbeats 300000
namespace APSCounting893.Main
lemma polynomialFraction_trdeg (K σ : Type) [Field K] :
    Algebra.trdeg K (FractionRing (MvPolynomial σ K)) = Cardinal.lift (Cardinal.mk σ) := by
  let P := MvPolynomial σ K
  let E := FractionRing P
  letI : Algebra.IsAlgebraic P E := IsLocalization.isAlgebraic E (nonZeroDivisors P)
  have heq := trdeg_add_eq K P (A := E)
  have hz : Algebra.trdeg P E = 0 := trdeg_eq_zero
  rw [hz,add_zero,MvPolynomial.trdeg_of_isDomain] at heq
  exact heq.symm
end APSCounting893.Main
end Component_58

section Component_59
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.algebraMvPolynomial
open MvPolynomial
namespace APSCounting893.Main

lemma generic_incidence_kernel_principal {K E : Type} [Field K] [CharZero K] [Field E]
    [Algebra K E] [Algebra.EssFiniteType K E] {r m : ℕ}
    (hE : Algebra.trdeg K E = (r : Cardinal))
    (f : Fin m → E) (g : Fin r → Fin m) (hg : AlgebraicIndependent K (f ∘ g)) :
    let I := RingHom.ker (genericIncidenceChartHom K (r := r) f).toRingHom
    I ≠ ⊥ ∧ I.IsPrincipal := by
  classical
  intro I
  haveI : I.IsPrime := RingHom.ker_isPrime _
  have hcontract : I.comap (MvPolynomial.rename
      (Subtype.val : {a : Fin (r+1) × Fin (m+1) // a ≠ (Fin.last r,0)} → _)) = ⊥ := by
    ext p
    change MvPolynomial.aeval (genericIncidenceChartValues f) (MvPolynomial.rename Subtype.val p) = 0 ↔ p=0
    rw [MvPolynomial.aeval_rename]
    constructor
    · exact (generic_incidence_complement_independent f g hg).eq_zero_of_aeval_eq_zero p
    · rintro rfl; exact map_zero _
  refine ⟨?_,mv_prime_principal_of_contract_complement_zero (Fin.last r,0) I hcontract⟩
  intro hI
  have hind : AlgebraicIndependent K (genericIncidenceChartValues (r := r) f) :=
    (RingHom.injective_iff_ker_eq_bot _).mpr hI
  have hh := hind.cardinalMk_le_trdeg
  have htr := trdeg_add_eq K E (A := FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
  rw [hE,polynomialFraction_trdeg] at htr
  rw [← htr] at hh
  simp only [Cardinal.mk_fintype,Fintype.card_prod,Fintype.card_fin,Cardinal.lift_natCast] at hh
  have hn : (r+1)*(m+1) ≤ r+(r+1)*m := by exact_mod_cast hh
  nlinarith

end APSCounting893.Main
end Component_59

section Component_60
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
open MvPolynomial
namespace APSCounting893.Main

noncomputable def genericIncidencePolynomialValues {E : Type} [Field E] {r m : ℕ} (f : Fin m → E) :
    Fin (r+1) × Fin (m+1) → MvPolynomial (Fin (r+1) × Fin m) E :=
  fun a => Fin.cases (-genericLinearValues f a.1) (fun j => MvPolynomial.X (a.1,j)) a.2

noncomputable def genericIncidencePolynomialHom (K : Type) {E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) :
    MvPolynomial (Fin (r+1) × Fin (m+1)) K →ₐ[K] MvPolynomial (Fin (r+1) × Fin m) E :=
  MvPolynomial.aeval (genericIncidencePolynomialValues f)

lemma genericIncidenceChartHom_eq_map {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (p : MvPolynomial (Fin (r+1) × Fin (m+1)) K) :
    genericIncidenceChartHom K f p = algebraMap _ (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E))
      (genericIncidencePolynomialHom K f p) := by
  have heq : genericIncidenceChartHom K f =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin (r+1) × Fin m) E) _).comp (genericIncidencePolynomialHom K f) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [genericIncidenceChartHom,genericIncidencePolynomialHom,AlgHom.comp_apply,MvPolynomial.aeval_X]
    rcases a with ⟨i,j⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [genericIncidenceChartValues,genericIncidencePolynomialValues]
    · rfl
  exact AlgHom.congr_fun heq p

lemma genericIncidencePolynomialHom_rename_rows {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (e : Fin (r+1) ≃ Fin (r+1))
    (p : MvPolynomial (Fin (r+1) × Fin (m+1)) K) :
    genericIncidencePolynomialHom K f (MvPolynomial.rename (fun a => (e a.1,a.2)) p) =
      MvPolynomial.rename (fun a => (e a.1,a.2)) (genericIncidencePolynomialHom K f p) := by
  let u : Fin (r+1) × Fin (m+1) → Fin (r+1) × Fin (m+1) := fun a => (e a.1,a.2)
  let v : Fin (r+1) × Fin m → Fin (r+1) × Fin m := fun a => (e a.1,a.2)
  have heq : (genericIncidencePolynomialHom K f).comp (MvPolynomial.rename u) =
      ((MvPolynomial.rename v).restrictScalars K).comp (genericIncidencePolynomialHom K f) := by
    apply MvPolynomial.algHom_ext
    intro a
    simp only [AlgHom.comp_apply,MvPolynomial.rename_X,genericIncidencePolynomialHom,MvPolynomial.aeval_X]
    rcases a with ⟨i,j⟩
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [genericIncidencePolynomialValues,genericLinearValues,u,v]
    · simp [genericIncidencePolynomialValues,u,v]
  exact AlgHom.congr_fun heq p

lemma generic_incidence_kernel_row_invariant {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (e : Fin (r+1) ≃ Fin (r+1))
    (p : MvPolynomial (Fin (r+1) × Fin (m+1)) K)
    (hp : genericIncidenceChartHom K f p = 0) :
    genericIncidenceChartHom K f (MvPolynomial.rename (fun a => (e a.1,a.2)) p) = 0 := by
  rw [genericIncidenceChartHom_eq_map] at hp ⊢
  have hz : genericIncidencePolynomialHom K f p = 0 :=
    (IsFractionRing.injective (MvPolynomial (Fin (r+1) × Fin m) E) (FractionRing (MvPolynomial (Fin (r+1) × Fin m) E)))
      (by simpa only [map_zero] using hp)
  rw [genericIncidencePolynomialHom_rename_rows,hz,map_zero,map_zero]

end APSCounting893.Main
end Component_60

section Component_61
set_option autoImplicit false
set_option maxHeartbeats 500000
open MvPolynomial
namespace APSCounting893.Main

lemma incidence_generator_totalDegree_bound {K E : Type} [Field K] [Field E] [Algebra K E]
    {r m : ℕ} (f : Fin m → E) (q : MvPolynomial (Fin (r+1) × Fin (m+1)) K)
    (hq : q ≠ 0)
    (hgen : RingHom.ker (genericIncidenceChartHom K f).toRingHom = Ideal.span {q})
    (d : ℕ) (hd : rowDegree (Fin.last r) q ≤ d) : q.totalDegree ≤ (r+1)*d := by
  classical
  suffices hrows : ∀ i, rowDegree i q ≤ d by
    simpa only [Fintype.card_fin] using totalDegree_le_rows_bound q d hrows
  intro i
  let e : Fin (r+1) ≃ Fin (r+1) := Equiv.swap i (Fin.last r)
  have hqmem : genericIncidenceChartHom K f q = 0 := by
    change q ∈ RingHom.ker (genericIncidenceChartHom K f).toRingHom
    rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton q)
  have hmem := generic_incidence_kernel_row_invariant f e q hqmem
  have hdiv : q ∣ MvPolynomial.rename (fun a : Fin (r+1) × Fin (m+1) => (e a.1,a.2)) q := by
    apply Ideal.mem_span_singleton.mp
    rw [← hgen]
    exact hmem
  have hren : MvPolynomial.rename (fun a : Fin (r+1) × Fin (m+1) => (e a.1,a.2)) q ≠ 0 := by
    have hi : Function.Injective (fun a : Fin (r+1) × Fin (m+1) => (e a.1,a.2)) := by
      intro a b h
      have h1 := congrArg (fun a : Fin (r+1) × Fin (m+1) => a.1) h
      have h2 := congrArg (fun a : Fin (r+1) × Fin (m+1) => a.2) h
      exact Prod.ext (e.injective h1) h2
    simpa only [map_zero] using (MvPolynomial.rename_injective _ hi).ne hq
  have hh := rowDegree_le_of_dvd i hdiv hren
  have hrow := rowDegree_rename_rows e (Fin.last r) q
  have hei : e (Fin.last r)=i := by simp [e]
  rw [hei] at hrow
  exact hh.trans (hrow.le.trans hd)

end APSCounting893.Main
end Component_61

section Component_62
set_option autoImplicit false
set_option maxHeartbeats 800000
open MvPolynomial
namespace APSCounting893.Main

lemma exists_rational_incidence_relation_bounded {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) K,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*d^r ∧ genericIncidenceChartHom K v q = 0 := by
  classical
  let E := FractionRing (MvPolynomial (Fin r) K)
  obtain ⟨b,hbn,hbd,hbv⟩ := exists_incidence_relation_last_row_bound Q hQ P v hP g hg d hd hdQ hdP
  obtain ⟨hI,hprincipal⟩ := generic_incidence_kernel_principal (rationalFunction_trdeg K r) v g hg
  obtain ⟨q,hq⟩ := hprincipal
  change RingHom.ker (genericIncidenceChartHom K v).toRingHom = Ideal.span {q} at hq
  have hqn : q ≠ 0 := by
    intro hz
    apply hI
    rw [hq,hz]
    simp
  have hqv : genericIncidenceChartHom K v q = 0 := by
    change q ∈ RingHom.ker (genericIncidenceChartHom K v).toRingHom
    rw [hq]
    exact Ideal.subset_span (Set.mem_singleton q)
  have hdiv : q ∣ b := by
    apply Ideal.mem_span_singleton.mp
    rw [← hq]
    exact hbv
  have hrow := (rowDegree_le_of_dvd (Fin.last r) hdiv hbn).trans hbd
  exact ⟨q,hqn,incidence_generator_totalDegree_bound v q hqn hq (d^r) hrow,hqv⟩

end APSCounting893.Main
end Component_62

open APSCounting893.Main
open MvPolynomial
theorem solution {K : Type} [Field K] [CharZero K] {r m : ℕ}
    (Q : MvPolynomial (Fin r) K) (hQ : Q ≠ 0)
    (P : Fin m → MvPolynomial (Fin r) K)
    (v : Fin m → FractionRing (MvPolynomial (Fin r) K))
    (hP : ∀ i, algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) (P i) =
      algebraMap _ (FractionRing (MvPolynomial (Fin r) K)) Q * v i)
    (g : Fin r → Fin m) (hg : AlgebraicIndependent K (v ∘ g))
    (d : ℕ) (hd : 0 < d) (hdQ : Q.totalDegree ≤ d) (hdP : ∀ i, (P i).totalDegree ≤ d) :
    ∃ q : MvPolynomial (Fin (r+1) × Fin (m+1)) K,
      q ≠ 0 ∧ q.totalDegree ≤ (r+1)*d^r ∧ (let E := FractionRing (MvPolynomial (Fin r) K)
       let S := MvPolynomial (Fin (r+1) × Fin m) E
       MvPolynomial.aeval (R := K) (S₁ := FractionRing S) (fun a : Fin (r+1) × Fin (m+1) =>
         Fin.cases (-algebraMap S (FractionRing S) (∑ j : Fin m, MvPolynomial.X (a.1,j)*MvPolynomial.C (v j)))
           (fun j => algebraMap S (FractionRing S) (MvPolynomial.X (a.1,j))) a.2) q = 0) := by
  exact exists_rational_incidence_relation_bounded Q hQ P v hP g hg d hd hdQ hdP
