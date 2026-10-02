-- Prove2me | Definitions.Def_Yukon_6008ce847bd1d9756f7e9c8c
-- name    : Yukon_6008ce847bd1d9756f7e9c8c
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:44:43.839765+00:00
-- url     : https://prove2.me/theorems/2d752459-17b0-4817-948a-7c870c7c527e
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberProjection6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberProjection6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberProjection6811.lean
--
--   yukon-proof-operation:foundation-direct-c68704064ef556fe4a2428f0bc07ea2b340efb0b0067f3385e3dff9fc72d8285
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWRiMDQ0Nzk3YjJlN2U5YzE2ZDM0YWU5ZDcyNDU5NTNhZTZiYjk4NmE0ZTljMTIzYTRhMzk4OTNjZGI1NjFhYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWM2ODcwNDA2NGVmNTU2ZmU0YTI0MjhmMGJjMDdlYTJiMzQwZWZiMGIwMDY3ZjMzODVlM2RmZjlmYzcyZDgyODUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl82MDA4Y2U4NDdiZDFkOTc1NmY3ZTljOGMiLCJ2IjoyfQ]

import Definitions.Def_Yukon_727fafb6cbdbcd7b2f82f2c7











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Source-sensitive projection degrees on a moving fiber. Generic embedding
points supply isolation in the order required by the compiled source count.
No interchange of algebraic closures or presumed degree budget is used.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberProjection6811
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN072 RCN076 RCN084 RCN095 RCN134 RCN136
open RCN207 RCN208 RCN237 RCN264 RCN313 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberIsolatedZeros6811
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000

variable {K Ω E : Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProjection6811.instDecidableEq_proximityPrize : DecidableEq Ω := Classical.decEq Ω
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberProjection6811.instDecidableEq_proximityPrize_1 : DecidableEq E := Classical.decEq E

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E]
  [IsScalarTower Ω (RatFunc Ω) E] in
public theorem scalar_surface (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) :
    scalarPolynomialMap Ω E (surfaceMap phi F) =
      surfaceMap ((algebraMap Ω E).comp phi) F := by
  simp only [scalarPolynomialMap,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

public theorem filtered_zero {R : Type*} [CommRing R] (F H G : R) :
    filteredCut 0 (fun _ : Fin 1 => F) H G = F := by
  simp [filteredCut]

omit [IsAlgClosed Ω] in
theorem sum_separable_projection_degrees {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (carrier : MvPolynomial (Fin 3) Ω) (p q : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (ell : MvPolynomial (Fin 3) Ω) (hell : PolynomialInFlag q ell)
    (c : ℕ) [CharP E c]
    (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff))
    (hold : Function.Injective old)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) =
      coordinateEvaluation Ω (old i).1 ell) :
    (k+1)*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) := by
  classical
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  let L := surfaceMap phi (asS P).leadingCoeff
  let R := H*L
  let M := movingEquation H G Q A target
  have hderiv : H ∈ Ideal.span
      ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set (MvPolynomial (Fin 3) Ω)) := by
    let carrierIdeal := Ideal.span
      ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set (MvPolynomial (Fin 3) Ω))
    have hcar : carrier ∈ carrierIdeal := Ideal.subset_span (by simp)
    have hdc : MvPolynomial.pderiv (1 : Fin 3) carrier ∈ carrierIdeal := Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩ := hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∈ carrierIdeal
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact carrierIdeal.add_mem (carrierIdeal.mul_mem_right b hdc)
      (carrierIdeal.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) b) hcar)
  let mu := scalarPolynomialMap Ω E
  let phiE := (algebraMap Ω E).comp phi
  let prime := fun i => (old i).1
  letI : ∀ i, Algebra (RatFunc Ω) (CoordinateField Ω (prime i)) :=
    fun i => (projection i).embedding.toRingHom.toAlgebra
  letI : ∀ i, IsScalarTower Ω (RatFunc Ω) (CoordinateField Ω (prime i)) :=
    fun i => IsScalarTower.of_algebraMap_eq (fun a => ((projection i).embedding.commutes a).symm)
  letI : ∀ i, FiniteDimensional (RatFunc Ω) (CoordinateField Ω (prime i)) := fun i => (projection i).finite
  letI : ∀ i, Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (prime i)) := fun i => (projection i).separable
  let points := genericFiberPoints (B := RatFunc Ω) (L := E) prime
  let t := algebraMap (RatFunc Ω) E (RCN202.rationalVariable Ω)
  let N := MvPolynomial.C t-mu ell
  have hprime : Function.Injective prime := by
    intro i j hij
    exact hold (Subtype.ext hij)
  have hNflag : PolynomialInFlag q N :=
    inFlag_sub_poly (inFlag_const _ _) (inFlag_map _ hell)
  have hmuM : mu M = movingEquation (surfaceMap phiE (polyH K F))
      (surfaceMap phiE (polyG K F)) (mu Q) (mu A) (algebraMap Ω E target) := by
    simp only [M,movingEquation,map_sub,map_mul]
    rw [show mu H = surfaceMap phiE (polyH K F) from scalar_surface phi _,
      show mu G = surfaceMap phiE (polyG K F) from scalar_surface phi _]
    simp only [mu,scalarPolynomialMap,MvPolynomial.map_C]
  have certificate (i : ι) (f : CoordinateField Ω (prime i) →ₐ[RatFunc Ω] E) :
      let x := embeddingPoint (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (mu M) = 0 ∧ MvPolynomial.eval x (mu R) ≠ 0 ∧
      IsolatedPoint (mu carrier) N (mu M) x := by
    let C0 : RegularComponent Ω carrier (filteredCut 0 (fun _ : Fin 1 => M) R 0) R :=
      ⟨(old i).1,by simpa only [filtered_zero] using (old i).2⟩
    letI : Algebra (RatFunc Ω) (CoordinateField Ω C0.1) :=
      (projection i).embedding.toRingHom.toAlgebra
    have hj : algebraMap (RatFunc Ω) (CoordinateField Ω C0.1) (RCN202.rationalVariable Ω) =
        movingValue C0.1 R 0 ell 1 := by
      change SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) = _
      simpa only [movingValue,map_one,map_zero,mul_zero,zero_div,add_zero] using hvalue i
    have hone : (1 : MvPolynomial (Fin 3) Ω) ∉ C0.1 := by
      intro h
      have hz := (SecondJetComponentRoots.evaluation_zero_iff C0.1 1).mpr h
      exact one_ne_zero (by simpa only [map_one] using hz)
    have hc := RCN202.embedding_point_certificate carrier R 0 ell 1 0
      (fun _ : Fin 1 => M) C0 hj hone f
    have hc' :
        let x := embeddingPoint (prime i) (f.restrictScalars Ω)
        MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x (mu R*N) = 0 ∧
        MvPolynomial.eval x (mu M) = 0 ∧ MvPolynomial.eval x (mu R) ≠ 0 ∧
        IsolatedPoint (mu carrier) (mu R*N) (mu M) x := by
      simpa only [map_zero,map_one,movingEquation,eliminatedCut,filtered_zero,
        mul_zero,sub_zero,mul_one,MvPolynomial.aeval_eq_eval] using hc
    dsimp only at hc' ⊢
    have hn : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) N = 0 :=
      (mul_eq_zero.mp (by simpa only [map_mul] using hc'.2.1)).resolve_left hc'.2.2.2.1
    refine ⟨hc'.1,hn,hc'.2.2.1,hc'.2.2.2.1,?_⟩
    intro D hD hnot hp hF hN
    exact hc'.2.2.2.2 D hD hnot hp hF (D.mul_mem_left (mu R) hN)
  have hpoints : ∀ x ∈ points,
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (mu M) = 0 ∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)) ≠ 0 ∧
      MvPolynomial.eval x (surfaceMap phiE (asS P).leadingCoeff) ≠ 0 ∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) (mu carrier)) ≠ 0 := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hc := certificate i f
    have hRne := hc.2.2.2.1
    have hHL : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0 ∧
        MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) (mu L) ≠ 0 := by
      simpa only [R,map_mul,mul_ne_zero_iff] using hRne
    have hHne : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)) ≠ 0 := by simpa only [H,mu,scalar_surface,phiE] using hHL.1
    have hLne : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (asS P).leadingCoeff) ≠ 0 := by simpa only [L,mu,scalar_surface,phiE] using hHL.2
    have hd := map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)))
      (mu carrier) (mu H) (scalar_derivative_span carrier H hderiv) hc.1 hHL.1
    exact ⟨hc.1,hc.2.1,hc.2.2.1,hHne,hLne,hd⟩
  have hiso : ∀ x ∈ points, IsolatedPoint (mu carrier) N (mu M) x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  have hcar : mu carrier ∣ surfaceMap phiE F := by
    simpa only [mu,scalar_surface,phiE] using map_dvd mu hcarrierF
  have hmu : Function.Injective mu := MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne : mu carrier ≠ 0 := fun hz => hcarrier (hmu (by simpa only [map_zero] using hz))
  rw [hmuM] at hpoints hiso
  have hc := isolated_moving_points_scaled phiE F (mu carrier) N p q hne hcar
    (inFlag_map _ hflag) hNflag c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact
    (mu Q) (mu A) (algebraMap Ω E target) (inFlag_map _ hQ) (inFlag_map _ hA) points hpoints hiso
  have hcard := genericFiberPoints_card (B := RatFunc Ω) (L := E) prime hprime
  simpa only [points,hcard,SeparableCoordinate.degree,prime] using hc

omit [IsAlgClosed Ω] in
theorem sum_coordinate_projection_degrees {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (carrier : MvPolynomial (Fin 3) Ω) (p q : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (ell : MvPolynomial (Fin 3) Ω) (hell : PolynomialInFlag q ell)
    (c : ℕ) [CharP E c]
    (hdeg : p.zOnly+p.yz+p.all < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*surfaceMap phi (asS P).leadingCoeff))
    (hold : Function.Injective old)
    (projection : ∀ i, Coordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, coordinateValue Ω (CoordinateField Ω (old i).1) (projection i) =
      coordinateEvaluation Ω (old i).1 ell) :
    (k+1)*(∑ i, coordinateDegree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) := by
  classical
  let Alive : Set ι := {i | ∃ C, projection i = Sum.inr C}
  let sep := fun i : Alive => Classical.choose i.2
  have hsep (i : Alive) : projection i.1 = Sum.inr (sep i) := Classical.choose_spec i.2
  let old0 := fun i : Alive => old i.1
  have hi0 : Function.Injective old0 := by
    intro i j h
    exact Subtype.ext (hold h)
  have hv0 (i : Alive) :
      SeparableCoordinate.value Ω (CoordinateField Ω (old0 i).1) (sep i) =
        coordinateEvaluation Ω (old0 i).1 ell := by
    have h := hvalue i.1
    rw [hsep i] at h
    exact h
  have hsum : (∑ i, coordinateDegree Ω (CoordinateField Ω (old i).1) (projection i)) =
      ∑ i : Alive, SeparableCoordinate.degree Ω (CoordinateField Ω (old0 i).1) (sep i) := by
    apply Finset.sum_congr_set Alive
      (fun i => coordinateDegree Ω (CoordinateField Ω (old i).1) (projection i))
      (fun i => SeparableCoordinate.degree Ω (CoordinateField Ω (old0 i).1) (sep i))
    · intro i hi
      simp only [hsep ⟨i,hi⟩,coordinateDegree,Sum.elim_inr,old0]
    · intro i hi
      cases hp : projection i with
      | inl C => simp only [coordinateDegree,Sum.elim_inl]
      | inr C => exact (hi ⟨C,hp⟩).elim
  rw [hsum]
  exact sum_separable_projection_degrees (E := E) phi F carrier p q hcarrier hcarrierF hflag ell hell
    c hdeg hmix P B U T s k n0 hS hP hBU hUT hdn hB hn hdiv h2 hfact Q A target hQ hA
    old0 hi0 sep hv0





end
end ProximityPrize.SubmissionLower.MovingFiberProjection6811


