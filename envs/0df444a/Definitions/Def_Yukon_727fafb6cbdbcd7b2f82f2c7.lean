-- Prove2me | Definitions.Def_Yukon_727fafb6cbdbcd7b2f82f2c7
-- name    : Yukon_727fafb6cbdbcd7b2f82f2c7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T05:26:04.856148+00:00
-- url     : https://prove2.me/theorems/35d80ccb-d5d0-4b1f-9799-89c13f650e99
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberIsolatedZeros6811.lean
--
--   yukon-proof-operation:foundation-direct-2daf3c38e087c1872252f6d6d1a0301cd4c9549de71420a945a2870b57852017
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzY3NDczNzFmNjAyOWIyNTBmM2E5ZTMxOTlhYjMwZjdhZjNmNjg0NjAwYTdmYTdmYjA3NjI0NGQ2ZGJmODkwMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTJkYWYzYzM4ZTA4N2MxODcyMjUyZjZkNmQxYTAzMDFjZDRjOTU0OWRlNzE0MjBhOTQ1YTI4NzBiNTc4NTIwMTciLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl83MjdmYWZiNmNiZGJjZDdiMmY4MmYyYzciLCJ2IjoyfQ]

import Definitions.Def_Yukon_21acd551a6a6c6a8cdb57951










































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The source-sensitive count on all components of an actual pure slice.
Component coverage, empty components, pure pole budgets, and the final mixed
budget are constructed here; no desired projection-degree bound is a premise.
-/
namespace ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN026 RCN039 RCN046 RCN084 RCN095
open RCN114 RCN136 RCN187 RCN204 RCN207 RCN237 RCN257 RCN264 RCN271 RCN313 RCN340 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open MovingFiberSourceZeros6811
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 50000
set_option synthInstance.maxHeartbeats 300000
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]
local instance  _root_.ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811.instDecidableEq_proximityPrize : DecidableEq E := Classical.decEq E
local notation "Poly3" => MvPolynomial (Fin 3) E

public theorem pure_flag_poles
    {G N R : Poly3} {p q : FlagDegree}
    {base : ∀ C : RegularComponent E G N R, SeparableLiteralCoordinate C.1}
    (U : AdaptiveUnitPoleBudget base p q) (C : RegularComponent E G N R)
    (V : FlagDegree) (W : Finset (Place E (CoordinateField E C.1))) :
    (∑ nu ∈ W, flagPole nu.val (coordinate E C.1) V) ≤
      (U.toPrimeFlagBudgetFamily.weightedCost V C : ℤ) := by
  have hz := U.zPole C W
  have hy := U.yzPole C W
  have ha := U.allPole C W
  simp only [exponentSetPoleWeight_unitZ] at hz
  simp only [exponentSetPoleWeight_unitYZ] at hy
  simp only [exponentSetPoleWeight_unitAll] at ha
  have h := add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hz (Int.natCast_nonneg V.zOnly))
    (mul_le_mul_of_nonneg_left hy (Int.natCast_nonneg V.yz)))
    (mul_le_mul_of_nonneg_left ha (Int.natCast_nonneg V.all))
  simpa only [flagPole,Finset.sum_add_distrib,← Finset.mul_sum,
    PrimeFlagBudgetFamily.weightedCost,AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,
    Nat.cast_add,Nat.cast_mul] using h

theorem isolated_moving_points_scaled
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (carrier N : Poly3) (p q : FlagDegree)
    (hcarrier : carrier ≠ 0) (hcarrierF : carrier ∣ surfaceMap phi F)
    (hflag : PolynomialInFlag p carrier) (hNflag : PolynomialInFlag q N)
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
    (Q A : Poly3) (target : E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) Q)
    (hA : PolynomialInFlag unitYZFlag A)
    (points : Finset (Fin 3 → E))
    (hpoints : ∀ x ∈ points,
      MvPolynomial.eval x carrier = 0 ∧ MvPolynomial.eval x N = 0 ∧
      MvPolynomial.eval x (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) = 0 ∧
      MvPolynomial.eval x (surfaceMap phi (polyH K F)) ≠ 0 ∧
      MvPolynomial.eval x (surfaceMap phi (asS P).leadingCoeff) ≠ 0 ∧
      MvPolynomial.eval x (MvPolynomial.pderiv (1 : Fin 3) carrier) ≠ 0)
    (hisolated : ∀ x ∈ points, IsolatedPoint carrier N
      (movingEquation (surfaceMap phi (polyH K F))
        (surfaceMap phi (polyG K F)) Q A target) x) :
    (k+1)*points.card ≤
      flagMixed p q (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0) := by
  classical
  let H := surfaceMap phi (polyH K F)
  let L := surfaceMap phi (asS P).leadingCoeff
  let R := H*L
  let M := movingEquation H (surfaceMap phi (polyG K F)) Q A target
  let V := SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0
  have hR : ∀ x ∈ points, MvPolynomial.eval x R ≠ 0 := by
    intro x hx
    simpa only [R,map_mul] using mul_ne_zero (hpoints x hx).2.2.2.1 (hpoints x hx).2.2.2.2.1
  have hcover : ∀ x ∈ points, ∃ g : ↥(activeFactors carrier N), MvPolynomial.eval x g.1 = 0 := by
    intro x hx
    exact exists_active_factor_of_isolated carrier N M R hcarrier x
      (hpoints x hx).1 (hpoints x hx).2.2.1 (hR x hx)
      (hpoints x hx).2.2.2.2.2 (hisolated x hx)
  obtain ⟨base,hY,hZ⟩ := exists_small_projection_data carrier N R hcarrier p q hflag hNflag c hdeg hmix
  let S (g : ↥(activeFactors carrier N)) : Finset (Fin 3 → E) :=
    points.filter (fun (x : Fin 3 → E) => MvPolynomial.eval x g.1 = (0:E))
  have hcoverage : points ⊆ Finset.univ.biUnion S := by
    intro x hx
    obtain ⟨g,hg⟩ := hcover x hx
    exact Finset.mem_biUnion.mpr ⟨g,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hx,hg⟩⟩
  have hcount (g : ↥(activeFactors carrier N)) :
      (k+1)*(S g).card ≤ flagMixed (exactFlag g.1) q V := by
    have hg := activeFactors_spec carrier N g
    obtain ⟨unit⟩ := exists_adaptiveUnitProjectionFamily_of_nested (exactFlag g.1) q
      (base g) (hY g) (hZ g) hg.2.2.2 hg.1 hg.2.2.1
      ((support_subset_flagSupport_iff _ _).mpr (polynomialIn_exactFlag g.1))
      ((support_subset_flagSupport_iff _ _).mpr hNflag)
    let budget := unit.toPrimeFlagBudgetFamily
    have hcard := card_le_sum_componentSeeds E g.1 N R (S g) id
      (fun x hx => (Finset.mem_filter.mp hx).2)
      (fun x hx => (hpoints x (Finset.mem_filter.mp hx).1).2.1)
      (fun x hx => hR x (Finset.mem_filter.mp hx).1)
    have hlocal (C : RegularComponent E g.1 N R) :
        (k+1)*(componentSeeds E g.1 N R (S g) id C).card ≤ budget.weightedCost V C := by
      by_cases he : (componentSeeds E g.1 N R (S g) id C).Nonempty
      · obtain ⟨x,hx⟩ := he
        have hxS := componentSeeds_subset E g.1 N R (S g) id C hx
        have hxpoints := (Finset.mem_filter.mp hxS).1
        have hxC := componentSeeds_on_prime E g.1 N R (S g) id C x hx
        have hcar : carrier ∈ C.1 := C.1.mem_of_dvd hg.2.1 (regularComponent_G_mem E g.1 N R C)
        have hF : surfaceMap phi F ∈ C.1 := C.1.mem_of_dvd hcarrierF hcar
        have hH : H ∉ C.1 := by
          intro hh
          exact regularComponent_H_not_mem E g.1 N R C (C.1.mul_mem_right L hh)
        have hL : L ∉ C.1 := by
          intro hl
          exact regularComponent_H_not_mem E g.1 N R C (C.1.mul_mem_left H hl)
        have hproper : M ∉ C.1 := hisolated x hxpoints C.1 inferInstance
          (regularComponent_ne_point E g.1 N R C) hxC hcar (regularComponent_T_mem E g.1 N R C)
        have hb := finite_moving_zeros_of_source phi F C.1 (base g C) P B U T s k n0
          hS hP hBU hUT hdn hB hn hF hH hL hdiv h2 hfact Q A target hQ hA hproper
          (budget.weightedCost V C) (fun W => pure_flag_poles unit.toAdaptiveUnitPoleBudget C V W)
        have hc := hb (componentSeeds E g.1 N R (S g) id C)
          (fun y hy => componentSeeds_on_prime E g.1 N R (S g) id C y hy)
          (fun y hy => (hpoints y (Finset.mem_filter.mp
            (componentSeeds_subset E g.1 N R (S g) id C hy)).1).2.2.2.1)
          (fun y hy => (hpoints y (Finset.mem_filter.mp
            (componentSeeds_subset E g.1 N R (S g) id C hy)).1).2.2.1)
        exact (Nat.mul_le_mul_left (k+1) hc).trans (by
          simpa only [Nat.mul_comm] using Nat.div_mul_le_self (budget.weightedCost V C) (k+1))
      · simp only [Finset.not_nonempty_iff_eq_empty.mp he,Finset.card_empty,Nat.mul_zero,Nat.zero_le]
    calc
      (k+1)*(S g).card ≤ (k+1)*∑ C : RegularComponent E g.1 N R,
          (componentSeeds E g.1 N R (S g) id C).card := Nat.mul_le_mul_left _ hcard
      _ = ∑ C : RegularComponent E g.1 N R,
          (k+1)*(componentSeeds E g.1 N R (S g) id C).card := Finset.mul_sum _ _ _
      _ ≤ ∑ C : RegularComponent E g.1 N R, budget.weightedCost V C := Finset.sum_le_sum (fun C _ => hlocal C)
      _ ≤ _ := budget.sum_weightedCost_le V
  have hc := (Finset.card_le_card hcoverage).trans Finset.card_biUnion_le
  calc
    (k+1)*points.card ≤ (k+1)*∑ g : ↥(activeFactors carrier N), (S g).card := Nat.mul_le_mul_left _ hc
    _ = ∑ g : ↥(activeFactors carrier N), (k+1)*(S g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : ↥(activeFactors carrier N), flagMixed (exactFlag g.1) q V := Finset.sum_le_sum (fun g _ => hcount g)
    _ ≤ _ := activeFactors_mixed_sum_le carrier N hcarrier p q V hflag



end
end ProximityPrize.SubmissionLower.MovingFiberIsolatedZeros6811


