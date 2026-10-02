-- Prove2me | Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
-- name    : Yukon_ef32f3d6934bd47f231d0d68
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:16:46.725705+00:00
-- url     : https://prove2.me/theorems/90ea1e01-bdb3-4f3c-9fc2-bd44c41a3cac
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberThreeSources6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberThreeSources6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberThreeSources6811.lean
--
--   yukon-proof-operation:foundation-direct-5668e9bccc7143ce0738ddcd514cef53ad3697cb398cfc12770e859419af8720
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMzIwMDg5N2U0M2YyZDFjZWY2MDgxZjlhMzIxYzY2ZGFmMTBkYWJlYTJmNTBhNWIyY2M1Zjc4NWJlNWQ4NDUwYiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTU2NjhlOWJjY2M3MTQzY2UwNzM4ZGRjZDUxNGNlZjUzYWQzNjk3Y2IzOThjZmMxMjc3MGU4NTk0MTlhZjg3MjAiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9lZjMyZjNkNjkzNGJkNDdmMjMxZDBkNjgiLCJ2IjoyfQ]

import Definitions.Def_Yukon_1a160610cffff87fd04d9299












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Three actual source polynomials, one native component family. The record
below contains only the existing source support/divisibility data, not any
desired projection or zero-count inequality. -/
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
open scoped Classical BigOperators
open RCN002 RCN037 RCN039 RCN042 RCN046 RCN071 RCN076 RCN084 RCN095 RCN136 RCN207 RCN237 RCN264 RCN313 RCN340 RCN341 RCN344
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberNativeBudget6811 MovingFiberProjection6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 60000
set_option maxRecDepth 50000
variable {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberThreeSources6811.instDecidableEq_proximityPrize : DecidableEq Ω := Classical.decEq Ω
local notation "Poly3" => MvPolynomial (Fin 3) Ω

structure Source (F : MvPolynomial (Fin 4) K) where
  P : Poly (K := K)
  B : ℕ
  U : ℕ
  T : ℕ
  s : ℕ
  k : ℕ
  n0 : ℕ
  hS : ∀ e ∈ P.support, e 1 ≤ s
  hshape : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T
  hBU : B ≤ U
  hUT : U ≤ T
  hdn : k+1 ≤ n0
  hB : 2*(n0-(k+1)) ≤ B
  hn : n0 ≤ (asS P).natDegree
  hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j

def Source.d {F : MvPolynomial (Fin 4) K} (S : Source F) : ℕ := S.k+1
def Source.flag {F : MvPolynomial (Fin 4) K} (S : Source F) : FlagDegree :=
  SecondJetRelaxedFlag.budgetFlag S.B S.U S.T S.d S.n0
def Source.leading {F : MvPolynomial (Fin 4) K} (S : Source F) (phi : Polynomial K →+* Ω) : Poly3 :=
  surfaceMap phi (asS S.P).leadingCoeff
def direction : Fin 3 → FlagDegree := ![unitZFlag,unitYZFlag,unitAllFlag]
def weight (W : FlagDegree) : Fin 3 → ℕ := ![W.zOnly,W.yz,W.all]

theorem pure_cut_three_sources
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : Poly3) (p q W : FlagDegree)
    (hcarrier : Irreducible carrier) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) carrier ≠ 0)
    (hproper : ¬ carrier ∣ movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
    (hNflag : PolynomialInFlag q (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (base : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi), SeparableLiteralCoordinate C.1)
    (hY : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi), LiteralProjectionGate C 0)
    (hZ : ∀ C : RegularComponent Ω carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target)
      (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi), LiteralProjectionGate C 2)
    (cut : Poly3) (hcut : PolynomialInFlag W cut) (points : Finset (Fin 3 → Ω))
    (hpoints : ∀ x ∈ points, MvPolynomial.eval x carrier = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x) :
    D*points.card ≤ ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag := by
  classical
  let H := surfaceMap phi (polyH K F)
  let N := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R := H*∏ j, (source j).leading phi
  let Family := RegularComponent Ω carrier N R
  obtain ⟨unit,a,b,hzv,hyv,hav⟩ := exists_common_native_unit p q base hY hZ hderiv hcarrier hproper hflag hNflag
  let ell : Fin 3 → Poly3 := ![linearZ,linearU a,linearA b a]
  let projection : (j : Fin 3) → (C : Family) → Coordinate Ω (CoordinateField Ω C.1) :=
    ![unit.zProjection,unit.yzProjection,unit.allProjection]
  have hell (j : Fin 3) : PolynomialInFlag (direction j) (ell j) := by
    fin_cases j
    · exact linearZ_flag
    · exact linearU_flag a
    · exact linearA_flag b a
  have hvalue (j : Fin 3) (C : Family) :
      coordinateValue Ω (CoordinateField Ω C.1) (projection j C) = coordinateEvaluation Ω C.1 (ell j) := by
    fin_cases j
    · exact hzv C
    · exact hyv C
    · exact hav C
  have hH (C : Family) : H ∉ C.1 := by
    intro h
    exact regularComponent_H_not_mem Ω carrier N R C
      (C.1.mul_mem_right (∏ j, (source j).leading phi) h)
  have hL (j : Fin 3) (C : Family) : (source j).leading phi ∉ C.1 := by
    intro h
    have hd : (source j).leading phi ∣ R :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun j => (source j).leading phi) (Finset.mem_univ j)) H
    exact regularComponent_H_not_mem Ω carrier N R C (C.1.mem_of_dvd hd h)
  let forget (j : Fin 3) (C : Family) : RegularComponent Ω carrier N (H*(source j).leading phi) :=
    ⟨C.1,(mem_regularComponents Ω).mpr ⟨regularComponent_mem Ω carrier N R C,by
      intro h
      exact ((inferInstance : C.1.IsPrime).mem_or_mem h).elim (hH C) (hL j C)⟩⟩
  have hinj (j : Fin 3) : Function.Injective (forget j) := by
    intro C C' h
    have hh := congrArg (fun C0 : RegularComponent Ω carrier N (H*(source j).leading phi) => C0.1) h
    exact Subtype.ext hh
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : Algebra Ω Ext := ((algebraMap (RatFunc Ω) Ext).comp (algebraMap Ω (RatFunc Ω))).toAlgebra
  letI : SMul (RatFunc Ω) Ext := (inferInstance : Algebra (RatFunc Ω) Ext).toSMul
  letI : SMul Ω Ext := (inferInstance : Algebra Ω Ext).toSMul
  letI : IsScalarTower Ω (RatFunc Ω) Ext := by
    constructor
    intro a b x
    simp only [Algebra.smul_def,map_mul]
    exact mul_assoc _ _ _
  letI : CharP Ext c := by infer_instance
  have h2e : (2 : Ext) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hproj (j : Fin 3) :
      (source j).d*(∑ C : Family, coordinateDegree Ω (CoordinateField Ω C.1) (projection j C)) ≤
        flagMixed p (direction j) (source j).flag := by
    have hfe : ((source j).k.factorial : Ext) ≠ 0 := by
      simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
    have hdirection : (direction j).zOnly+(direction j).yz+(direction j).all = 1 := by fin_cases j <;> rfl
    exact sum_coordinate_projection_degrees (E := Ext) phi F carrier p (direction j) hcarrier.ne_zero hcarrierF hflag
      (ell j) (hell j) c (by omega) (by rw [hdirection,mul_one]; exact hunit)
      (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k (source j).n0
      (source j).hS (source j).hshape (source j).hBU (source j).hUT (source j).hdn (source j).hB
      (source j).hn (source j).hdiv h2e hfe Q A target hQ hA (forget j) (hinj j) (projection j) (hvalue j)
  have hscaled (j : Fin 3) :
      D*(∑ C : Family, coordinateDegree Ω (CoordinateField Ω C.1) (projection j C)) ≤
        (D/(source j).d)*flagMixed p (direction j) (source j).flag := by
    have h := Nat.mul_le_mul_left (D/(source j).d) (hproj j)
    simpa only [← Nat.mul_assoc,Nat.div_mul_cancel (hD j)] using h
  let budget := unit.toPrimeFlagBudgetFamily
  have hcard : points.card ≤ ∑ C : Family, budget.weightedCost W C := by
    apply (card_le_sum_componentSeeds Ω carrier N R points id
      (fun x hx => (hpoints x hx).1) (fun x hx => (hpoints x hx).2.1)
      (fun x hx => (hpoints x hx).2.2.1)).trans
    apply Finset.sum_le_sum
    intro C _
    by_cases he : (componentSeeds Ω carrier N R points id C).Nonempty
    · obtain ⟨x,hx⟩ := he
      have hxS := componentSeeds_subset Ω carrier N R points id C hx
      have hxC := componentSeeds_on_prime Ω carrier N R points id C x hx
      apply (budget.primeBudget C).zero_le W cut hcut
        (hisolated x hxS C.1 inferInstance (regularComponent_ne_point Ω carrier N R C)
          hxC (regularComponent_G_mem Ω carrier N R C) (regularComponent_T_mem Ω carrier N R C))
      · intro y hy
        exact componentSeeds_on_prime Ω carrier N R points id C y hy
      · intro y hy
        exact (hpoints y (componentSeeds_subset Ω carrier N R points id C hy)).2.2.2
    · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.zero_le]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
    Nat.mul_le_mul_left (weight W j) (hscaled j))
  have hb : D*(∑ C : Family, budget.weightedCost W C) ≤
      ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag := by
    have hl : D*(∑ C : Family, budget.weightedCost W C) =
        ∑ j : Fin 3, weight W j*(D*∑ C : Family, coordinateDegree Ω (CoordinateField Ω C.1) (projection j C)) := by
      simp only [Fin.sum_univ_three,projection,weight,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
        Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Matrix.cons_val_succ,
        budget,PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
        AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget,
        Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    have hr : (∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag) =
        ∑ j : Fin 3, weight W j*((D/(source j).d)*flagMixed p (direction j) (source j).flag) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hl,hr]
    exact hs
  exact (Nat.mul_le_mul_left D hcard).trans hb

theorem isolated_pure_cut_three_sources
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : Poly3) (p q W : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (c : ℕ) [CharP Ω c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all) < c)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (Q A : Poly3) (target : Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (hNflag : PolynomialInFlag q (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target))
    (cut : Poly3) (hcut : PolynomialInFlag W cut) (points : Finset (Fin 3 → Ω))
    (hpoints : ∀ x ∈ points, MvPolynomial.eval x carrier = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)*∏ j, (source j).leading phi) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier
      (movingEquation (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A target) cut x) :
    D*points.card ≤ ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed p (direction j) (source j).flag := by
  classical
  let H := surfaceMap phi (polyH K F)
  let N := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let R := H*∏ j, (source j).leading phi
  have hdeg : p.zOnly+p.yz+p.all < c := by omega
  have hderiv : H ∈ Ideal.span ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set Poly3) := by
    let I := Ideal.span ({carrier,MvPolynomial.pderiv (1 : Fin 3) carrier} : Set Poly3)
    have hc : carrier ∈ I := Ideal.subset_span (by simp)
    have hd : MvPolynomial.pderiv (1 : Fin 3) carrier ∈ I := Ideal.subset_span (by simp)
    obtain ⟨b,hb⟩ := hcarrierF
    change surfaceMap phi (MvPolynomial.pderiv (2 : Fin 4) F) ∈ I
    rw [← RCN267.surfaceMap_pderiv_R,hb,MvPolynomial.pderiv_mul]
    exact I.add_mem (I.mul_mem_right b hd) (I.mul_mem_right (MvPolynomial.pderiv (1 : Fin 3) b) hc)
  have hcover : ∀ x ∈ points, ∃ g : ↥(activeFactors carrier N), MvPolynomial.eval x g.1 = 0 := by
    intro x hx
    have hp := hpoints x hx
    have hh : MvPolynomial.eval x H ≠ 0 := by
      have hr : MvPolynomial.eval x H * MvPolynomial.eval x (∏ j, (source j).leading phi) ≠ 0 := by
        simpa only [map_mul] using hp.2.2.1
      exact (mul_ne_zero_iff.mp hr).1
    exact exists_active_factor_of_isolated carrier N cut R hcarrier x hp.1 hp.2.2.2 hp.2.2.1
      (map_pderiv_ne_zero_of_mem_span (MvPolynomial.eval x) carrier H hderiv hp.1 hh) (hisolated x hx)
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g : ↥(activeFactors carrier N)) : Finset (Fin 3 → Ω) :=
    points.filter (fun x => MvPolynomial.eval x g.1 = (0:Ω))
  have hcoverage : points ⊆ Finset.univ.biUnion S := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g : ↥(activeFactors carrier N)) :
      D*(S g).card ≤ ∑ j : Fin 3, weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (direction j) (source j).flag := by
    have hg := activeFactors_spec carrier N g
    have hgtotal : (exactFlag g.1).zOnly+(exactFlag g.1).yz+(exactFlag g.1).all ≤
        p.zOnly+p.yz+p.all := by
      rw [(exactFlag_cumulative g.1).2.2]
      exact (weightedTotalDegree_le_of_dvd_fin3 flagTotalWeights g.1 carrier hg.2.1 hcarrier).trans
        (inFlag_weight_caps carrier p hflag).2.2
    apply pure_cut_three_sources phi F source D hD g.1 (exactFlag g.1) q W hg.1
      (dvd_trans hg.2.1 hcarrierF) (polynomialIn_exactFlag g.1) c (by omega) h2 hfact
      Q A target hQ hA hg.2.2.2 hg.2.2.1 hNflag (base g) (hY g) (hZ g) cut hcut (S g)
    · intro x hx
      have hs := Finset.mem_filter.mp hx
      have hp := hpoints x hs.1
      exact ⟨hs.2,hp.2.1,hp.2.2.1,hp.2.2.2⟩
    · intro x hx J hj hnot hpoint hG hN
      exact hisolated x (Finset.mem_filter.mp hx).1 J hj hnot hpoint (J.mem_of_dvd hg.2.1 hG) hN
  calc
    D*points.card ≤ D*∑ g : ↥(activeFactors carrier N), (S g).card :=
      Nat.mul_le_mul_left _ ((Finset.card_le_card hcoverage).trans Finset.card_biUnion_le)
    _ = ∑ g : ↥(activeFactors carrier N), D*(S g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : ↥(activeFactors carrier N), ∑ j : Fin 3,
        weight W j*(D/(source j).d)*flagMixed (exactFlag g.1) (direction j) (source j).flag :=
      Finset.sum_le_sum (fun g _ => hcount g)
    _ = ∑ j : Fin 3, weight W j*(D/(source j).d)*
        ∑ g : ↥(activeFactors carrier N), flagMixed (exactFlag g.1) (direction j) (source j).flag := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => Nat.mul_le_mul_left _
      (activeFactors_mixed_sum_le carrier N hcarrier p (direction j) (source j).flag hflag))





end
end ProximityPrize.SubmissionLower.MovingFiberThreeSources6811


