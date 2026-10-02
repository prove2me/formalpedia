-- Prove2me | Definitions.Def_Yukon_ca6ef1ca29b9483e7b8d8f20
-- name    : Yukon_ca6ef1ca29b9483e7b8d8f20
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T06:34:15.540699+00:00
-- url     : https://prove2.me/theorems/73468f43-d668-45a6-bcb5-9e4c57775048
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberDegreeSum6811.lean
--
--   yukon-proof-operation:foundation-direct-90f5fc4accd2bd7d274ca456831a1519ba757f0c1cc452ff12db9ee1b5174465
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNjIxOGE5MmEzMWNkMDBkMzEzYmYzYmNlNDg2MWQ1N2U5ZTM1YThlODJlZjQ3YjFkZDRjN2ZjMmMwYTQyYWQ2OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTkwZjVmYzRhY2NkMmJkN2QyNzRjYTQ1NjgzMWExNTE5YmE3NTdmMGMxY2M0NTJmZjEyZGI5ZWUxYjUxNzQ0NjUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jYTZlZjFjYTI5Yjk0ODNlN2I4ZDhmMjAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Return from a generic moving fiber to the actual sum of moving degrees.
Use the repository's existing filtered-cut representation and clearing flag.
No multiplicity-weighted moving-degree estimate is required.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811
open scoped Classical BigOperators
open RCN002 RCN005 RCN006 RCN007 RCN046 RCN072 RCN084 RCN095 RCN134 RCN136 RCN202
open RCN199 RCN200 RCN207 RCN208 RCN209 RCN237 RCN264 RCN313 RCN341 RCN344
open SecondJetCoefficients MovingFiberThreeSources6811
noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000
set_option maxRecDepth 50000
variable {K Ω E : Type} [Field K] [Field Ω] [Field E] [IsAlgClosed Ω] [IsAlgClosed E]
  [Algebra Ω E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811.instDecidableEq_proximityPrize : DecidableEq Ω := Classical.decEq Ω
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811.instDecidableEq_proximityPrize_1 : DecidableEq E := Classical.decEq E

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
public theorem scalar_surface (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K) :
    scalarPolynomialMap Ω E (surfaceMap phi F) = surfaceMap ((algebraMap Ω E).comp phi) F := by
  simp only [scalarPolynomialMap,surfaceMap,RingHom.comp_apply,MvPolynomial.map_map]

omit [IsAlgClosed Ω] [IsAlgClosed E] [Algebra (RatFunc Ω) E] [IsScalarTower Ω (RatFunc Ω) E] in
public theorem eval_embedding (C : Ideal (MvPolynomial (Fin 3) Ω)) [C.IsPrime]
    (f : CoordinateField Ω C →ₐ[Ω] E) (F : MvPolynomial (Fin 3) Ω) :
    MvPolynomial.eval (embeddingPoint C f) (scalarPolynomialMap Ω E F) = f (coordinateEvaluation Ω C F) := by
  have h := AlgHom.congr_fun (embeddingPoint_aeval C f) F
  change MvPolynomial.eval (embeddingPoint C f) (MvPolynomial.map (algebraMap Ω E) F) = _
  rw [MvPolynomial.eval_map]
  exact h

theorem sum_moving_degrees_three_sources {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : MvPolynomial (Fin 3) Ω) (p : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (a b s n : ℕ) (center : FlagDegree)
    (coeff : Fin (n+1) → MvPolynomial (Fin 3) Ω) (coeffFlag : Fin (n+1) → FlagDegree)
    (hHflag : PolynomialInFlag (⟨a,b+1,s+1⟩ : FlagDegree) (surfaceMap phi (polyH K F)))
    (hGflag : PolynomialInFlag (⟨a,b,s+3⟩ : FlagDegree) (surfaceMap phi (polyG K F)))
    (hcoeff : ∀ j, PolynomialInFlag (coeffFlag j) (coeff j))
    (hcoeffEq : ∀ j, coeffFlag j+(n-j.val) • (⟨a,b+1,s+1⟩ : FlagDegree)+
      j.val • (⟨a,b,s+3⟩ : FlagDegree) = center+n • (⟨2*a,2*b+1,2*s+3⟩ : FlagDegree))
    (c : ℕ) [CharP E c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < c)
    (h2 : (2 : E) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier
      (filteredCut n coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)))
    (hold : Function.Injective old)
    (hleading : ∀ i j, (source j).leading phi ∉ (old i).1)
    (hAnonzero : ∀ i, A ∉ (old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) =
      movingValue (old i).1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A) :
    D*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      ∑ j : Fin 3, weight (center+n • (⟨a,b+1,s+2⟩ : FlagDegree)) j*(D/(source j).d)*
        flagMixed p (direction j) (source j).flag := by
  classical
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
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
  let target := algebraMap (RatFunc Ω) E (rationalVariable Ω)
  let N := fiberEquation (E := E) H G Q A
  let cut := fiberCut (E := E) n coeff Q A
  let W := center+n • (⟨a,b+1,s+2⟩ : FlagDegree)
  have hi : Function.Injective prime := by
    intro i j h
    exact hold (Subtype.ext h)
  have certificate (i : ι) (f : CoordinateField Ω (prime i) →ₐ[RatFunc Ω] E) :
      let x := embeddingPoint (prime i) (f.restrictScalars Ω)
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.aeval x cut = 0 ∧ MvPolynomial.eval x (mu H*mu A) ≠ 0 ∧
      IsolatedPoint (mu carrier) N cut x := by
    letI : Algebra (RatFunc Ω) (CoordinateField Ω (old i).1) :=
      (projection i).embedding.toRingHom.toAlgebra
    have hj : algebraMap (RatFunc Ω) (CoordinateField Ω (old i).1) (rationalVariable Ω) =
        movingValue (old i).1 H G Q A := hvalue i
    exact RCN202.embedding_point_certificate carrier H G Q A n coeff (old i) hj (hAnonzero i) f
  have hpoints : ∀ x ∈ points,
      MvPolynomial.eval x (mu carrier) = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (surfaceMap phiE (polyH K F)*∏ j, (source j).leading phiE) ≠ 0 ∧
      MvPolynomial.aeval x cut = 0 := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    have hc := certificate i f
    have hHne : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω)) (mu H) ≠ 0 := by
      have hh := hc.2.2.2.1
      rw [map_mul] at hh
      exact (mul_ne_zero_iff.mp hh).1
    have hLne (j : Fin 3) : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        ((source j).leading phiE) ≠ 0 := by
      have he : (source j).leading phiE = mu ((source j).leading phi) := by
        exact (scalar_surface phi (asS (source j).P).leadingCoeff).symm
      rw [he,eval_embedding]
      intro hz
      exact hleading i j ((SecondJetComponentRoots.evaluation_zero_iff (prime i) _).mp
        ((map_eq_zero_iff f f.injective).mp hz))
    have hprod : (∏ j : Fin 3, MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        ((source j).leading phiE)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => hLne j)
    have hgate : MvPolynomial.eval (embeddingPoint (prime i) (f.restrictScalars Ω))
        (surfaceMap phiE (polyH K F)*∏ j, (source j).leading phiE) ≠ 0 := by
      rw [map_mul,map_prod]
      apply mul_ne_zero _ hprod
      simpa only [H,mu,scalar_surface,phiE] using hHne
    exact ⟨hc.1,hc.2.1,hgate,hc.2.2.1⟩
  have hiso : ∀ x ∈ points, IsolatedPoint (mu carrier) N cut x := by
    intro x hx
    obtain ⟨⟨i,f⟩,_,rfl⟩ := Finset.mem_image.mp hx
    exact (certificate i f).2.2.2.2
  obtain ⟨hNflag,hcutflag⟩ := RCN202.fiber_small_flags (E := E) a b s n center H G Q A coeff coeffFlag
    hHflag hGflag hQ hA hcoeff hcoeffEq
  have hN : N = movingEquation (surfaceMap phiE (polyH K F)) (surfaceMap phiE (polyG K F))
      (mu Q) (mu A) target := by
    dsimp only [N,fiberEquation]
    rw [show scalarPolynomialMap Ω E H = surfaceMap phiE (polyH K F) from scalar_surface phi _,
      show scalarPolynomialMap Ω E G = surfaceMap phiE (polyG K F) from scalar_surface phi _]
  have hcar : mu carrier ∣ surfaceMap phiE F := by
    simpa only [mu,scalar_surface,phiE] using map_dvd mu hcarrierF
  have hmu : Function.Injective mu := MvPolynomial.map_injective (algebraMap Ω E) (algebraMap Ω E).injective
  have hne : mu carrier ≠ 0 := fun hz => hcarrier (hmu (by simpa only [map_zero] using hz))
  have hNflag' : PolynomialInFlag (⟨a,b+1,s+3⟩ : FlagDegree)
      (movingEquation (surfaceMap phiE (polyH K F)) (surfaceMap phiE (polyG K F)) (mu Q) (mu A) target) := by
    change PolynomialInFlag (⟨a,b+1,s+3⟩ : FlagDegree) N at hNflag
    rwa [hN] at hNflag
  rw [hN] at hpoints hiso
  have hc := isolated_pure_cut_three_sources phiE F source D hD (mu carrier) p (⟨a,b+1,s+3⟩ : FlagDegree) W
    hne hcar (inFlag_map _ hflag) c hunit hmix h2 hfact (mu Q) (mu A) target
    (inFlag_map _ hQ) (inFlag_map _ hA) hNflag' cut hcutflag points hpoints hiso
  have hcard := genericFiberPoints_card (B := RatFunc Ω) (L := E) prime hi
  simpa only [points,hcard,SeparableCoordinate.degree,prime,W] using hc

theorem actual_first_tail_moving_degrees {ι : Type} [Fintype ι]
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hD : ∀ j, (source j).d ∣ D)
    (carrier : MvPolynomial (Fin 3) Ω) (p : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (a b s w : ℕ) (hw : 1 ≤ w)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : RCN234.wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : RCN234.wt ![0,1,1,1] F ≤ a+b+s+3)
    (c : ℕ) [CharP E c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < c)
    (h2 : (2 : E) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : E) ≠ 0)
    (Q A : MvPolynomial (Fin 3) Ω)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q) (hA : PolynomialInFlag unitYZFlag A)
    (old : ι → RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F)))
    (hold : Function.Injective old)
    (hleading : ∀ i j, (source j).leading phi ∉ (old i).1)
    (hAnonzero : ∀ i, A ∉ (old i).1)
    (projection : ∀ i, SeparableCoordinate Ω (CoordinateField Ω (old i).1))
    (hvalue : ∀ i, SeparableCoordinate.value Ω (CoordinateField Ω (old i).1) (projection i) =
      movingValue (old i).1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) Q A) :
    D*(∑ i, SeparableCoordinate.degree Ω (CoordinateField Ω (old i).1) (projection i)) ≤
      ∑ j : Fin 3, weight (RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)) j*(D/(source j).d)*
        flagMixed p (direction j) (source j).flag := by
  classical
  obtain ⟨coeff,flags,heq,hcoeff,hrel⟩ := RCN086.exists_filtered_certificate phi a b s F hR hYR hAll
    (w+1) (by omega) (RCN086.tailSelector (w+1)) 0 0 0
  have heq' : RCN086.globalTailCut phi F (w+1) =
      filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) := heq
  let old' : ι → RegularComponent Ω carrier
      (filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)) := fun i => ⟨(old i).1,by rw [← heq']; exact (old i).2⟩
  have hi : Function.Injective old' := by
    intro i j h
    have hh := congrArg (fun C : RegularComponent Ω carrier
      (filteredCut w coeff (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)))
      (surfaceMap phi (polyH K F)) => C.1) h
    exact hold (Subtype.ext hh)
  obtain ⟨hHflag,hGflag⟩ := RCN201.surfaceMap_HG_flags phi a b s F hR hYR hAll
  exact sum_moving_degrees_three_sources (E := E) phi F source D hD carrier p hcarrier hcarrierF hflag
    a b s w (RCN198.center a b s) coeff flags hHflag hGflag hcoeff hrel c hunit hmix h2 hfact
    Q A hQ hA old' hi hleading hAnonzero projection hvalue

theorem exists_first_tail_budget
    (phi : Polynomial K →+* Ω) (F : MvPolynomial (Fin 4) K)
    (source : Fin 3 → Source F) (D : ℕ) (hDpos : 0 < D) (hD : ∀ j, (source j).d ∣ D)
    (carrier : MvPolynomial (Fin 3) Ω) (p tailFlag : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier)
    (a b s w : ℕ) (hw : 1 ≤ w)
    (hR : F.degreeOf 2 ≤ s+2)
    (hYR : RCN234.wt ![0,1,1,0] F ≤ b+s+3)
    (hAll : RCN234.wt ![0,1,1,1] F ≤ a+b+s+3)
    (c : ℕ) [CharP E c] (hunit : 2*(p.zOnly+p.yz+p.all) < c)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(a+(b+1)+(s+3)) < c)
    (h2 : (2 : E) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : E) ≠ 0)
    (base : ∀ C : RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1))
      (surfaceMap phi (polyH K F)), SeparableLiteralCoordinate C.1)
    (unit : AdaptiveUnitProjectionFamily base p tailFlag)
    (active : Finset (RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F))))
    (hleading : ∀ C ∈ active, ∀ j, (source j).leading phi ∉ C.1) :
    ∃ budget : ∀ C : RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F)),
        MovingPoleBudget C.1 (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)),
      (∀ C : RegularComponent Ω carrier (RCN086.globalTailCut phi F (w+1)) (surfaceMap phi (polyH K F)),
        (budget C).zCost = unit.toPrimeFlagBudgetFamily.zCost C ∧
        (budget C).yzCost = unit.toPrimeFlagBudgetFamily.yzCost C ∧
        (budget C).allCost = unit.toPrimeFlagBudgetFamily.allCost C) ∧
      (∑ C ∈ active, (budget C).movingCost) ≤
        (∑ j : Fin 3, weight (RCN198.center a b s+w • (⟨a,b+1,s+2⟩ : FlagDegree)) j*(D/(source j).d)*
          flagMixed p (direction j) (source j).flag)/D := by
  classical
  let H := surfaceMap phi (polyH K F)
  let G := surfaceMap phi (polyG K F)
  let T := RCN086.globalTailCut phi F (w+1)
  obtain ⟨Q,A,J,hQ,hA,hJ⟩ := exists_separable_moving_coordinates carrier T H G base
  let budget := budgetOfProjections carrier T H G unit J (fun C v => (hJ C).2.2.1 v)
  refine ⟨budget,(fun _ => ⟨rfl,rfl,rfl⟩),?_⟩
  have hb := actual_first_tail_moving_degrees (E := E) phi F source D hD carrier p hcarrier hcarrierF hflag
    a b s w hw hR hYR hAll c hunit hmix h2 hfact Q A hQ hA
    (fun C : active => C.val) Subtype.val_injective
    (fun C j => hleading C.val C.property j)
    (fun C => (hJ C.val).1) (fun C => J C.val) (fun C => (hJ C.val).2.1)
  have hsum : (∑ C ∈ active, (budget C).movingCost) =
      ∑ C : active, SeparableCoordinate.degree Ω (CoordinateField Ω C.val.1) (J C.val) := by
    exact (Finset.sum_coe_sort active (fun C => (budget C).movingCost)).symm
  apply (Nat.le_div_iff_mul_le hDpos).mpr
  rw [hsum]
  simpa only [Nat.mul_comm] using hb







end
end ProximityPrize.SubmissionLower.MovingFiberDegreeSum6811


