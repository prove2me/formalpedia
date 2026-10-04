-- Prove2me | Definitions.Def_Yukon_c562ca1e602b3cc572e6a79f
-- name    : Yukon_c562ca1e602b3cc572e6a79f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T01:43:21.835476+00:00
-- url     : https://prove2.me/theorems/5dd8653e-f521-4c43-8c7f-96e36010ec22
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceProperSeedCount6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-deef7bd8f845c3ad02d66e5fb19e8a2ca16a6ab2bb72c7ba53ceca89cba1e96a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiOTkzMDRlNmRkNDRjMDVkZDA2YTUyOTVmOTlkNjI4YzllYjk4NWMzMzMxZTZiNDRlNGM5NWJhMmI2OTk1OTM5OSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtZGVlZjdiZDhmODQ1YzNhZDAyZDY2ZTVmYjE5ZThhMmNhMTZhNmFiMmJiNzJjN2JhNTNjZWNhODljYmExZTk2YSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2M1NjJjYTFlNjAyYjNjYzU3MmU2YTc5ZiIsInYiOjJ9]

import Definitions.Def_Yukon_19e17a49e4fd3320c0eef751


























































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! The proper-delay branch now has an actual seed cardinality bound.
The inputs come from LinearRoute, the stage's selected solutions, and its
local multiplicity dichotomy. Exceptional and persistent components are
not declared proper or silently included in this theorem. -/
namespace ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN042 RCN074 RCN086 RCN095 RCN121 RCN135 RCN136 RCN238 RCN243 RCN244 RCN264
open MovingSourceGammaProjections6814 MovingSourceLinearCycleFamily6814 MovingSourceProjectionFamily6814
open MovingSourceFrameZeroCount6814 MovingSourceReducedSeedTails6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceReducedRoutes6814

public theorem sum_weighted_three {A : Type} [Fintype A]
    (m z u v : A → ℕ) (a b c : ℕ) :
    (∑ i, m i*(a*z i+b*u i+c*v i))=
      a*(∑ i, m i*z i)+b*(∑ i, m i*u i)+c*(∑ i, m i*v i) := by
  simp only [Nat.mul_add,Finset.sum_add_distrib,Finset.mul_sum,Nat.mul_left_comm]

variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev stageSeeds (S : Stage K I Gamma x p flag errorCap stageSupport) (C : FirstTailComponent S) :=
  componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (regularitySurface (polynomialEmbedding K) S.F) Gamma
    (selectedPoint (polynomialEmbedding K) S.selected) C

theorem proper_component_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    {A : Type} [Fintype A] (component : A → FirstTailComponent S)
    (hz : ∀ a, Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (hgate : ∀ a,
      (letI := (elementEmbedding (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinate (GenericField K) (component a).1 2) (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1)) ∧
      (letI := (elementEmbedding (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinate (GenericField K) (component a).1 2) (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc (GenericField K)) (CoordinateField (GenericField K) (component a).1)))
    (D : GammaFrame (fun a => (component a).1) S.G) (a : A)
    (hH : surfaceMap (polynomialEmbedding K) (linearH J)∉(component a).1)
    (delay : ℕ) (hdelay : delay≤localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a))
    (hproper : globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∉(component a).1) :
    (stageSeeds S (component a)).card ≤
      localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)*
        frameFlagCost D hz a reducedDelayFlag := by
  classical
  let m := localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)
  let N := surfaceMap (polynomialEmbedding K)
    (numerators (linearH J) (linearG J) (RCN326.w+1+delay))
  let seeds := stageSeeds S (component a)
  let point := selectedPoint (polynomialEmbedding K) S.selected
  let points := seeds.image point
  have hN := reduced_delay_flag_of_route S.F J hroute m delay
    (one_le_localMultiplicity S hfirst (component a)) hdelay
  have hNproper := reduced_tail_proper_on_component S (component a) (linearH J) (linearG J)
    (RCN326.w+1+delay) (hroute.2.2.2.2 _).1 hH hproper
  have hpoints : ∀ v∈points, (component a).1≤RingHom.ker (MvPolynomial.aeval v).toRingHom := by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hv
    exact componentSeeds_on_prime (GenericField K) S.G _ _ Gamma point (component a) gamma hgamma
  have hzero : ∀ v∈points, MvPolynomial.aeval v N=0 := by
    intro v hv
    obtain ⟨gamma,hgamma,rfl⟩ := Finset.mem_image.mp hv
    have hGamma := componentSeeds_subset (GenericField K) S.G _ _ Gamma point (component a) hgamma
    exact reduced_selected_tail_zero S (linearH J) (linearG J) (RCN326.w+1+delay)
      (by omega) (hroute.2.2.2.2 _).1 gamma hGamma
  have hc := (frame_prime_budget D hz hgate a).zero_le (m • reducedDelayFlag) N hN hNproper
    points hpoints hzero
  have hcard : points.card=seeds.card := Finset.card_image_of_injective _
    (selectedPoint_injective (polynomialEmbedding K) S.selected)
  have hcost : frameFlagCost D hz a (m • reducedDelayFlag)=m*frameFlagCost D hz a reducedDelayFlag := by
    simp only [frameFlagCost,nsmul_zOnly,nsmul_yz,nsmul_all]
    ring
  rw [hcard,hcost] at hc
  exact hc

/-- The actual proper stratum of the original stage, without a conjectured
factor choice or a supplied cardinality bound. -/
abbrev ProperLinearComponent
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H : MvPolynomial (Fin 4) K) :=
  {C : FirstTailComponent S //
    Transcendental (GenericField K) (coordinate (GenericField K) C.1 2) ∧
    surfaceMap (polynomialEmbedding K) H∉C.1 ∧
    ∃ delay, 1≤delay ∧ delay≤localMultiplicity S (canonicalLocalDVRFamily S hfirst) C ∧
      globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1+delay)∉C.1}

/-- Sum the actual proper-component seed sets against ONE shared cycle. -/
theorem proper_linear_seeds_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G)
    (hsmall : flagMixed surfaceFlag reducedFirstFlag unitZFlag<p) :
    (∑ C : ProperLinearComponent S hfirst (linearH J), (stageSeeds S C.1).card) ≤
      flagMixed surfaceFlag reducedFirstFlag reducedDelayFlag := by
  classical
  let A := ProperLinearComponent S hfirst (linearH J)
  let component : A → FirstTailComponent S := Subtype.val
  let hz (a : A) := a.2.1
  by_cases hA : Nonempty A
  · let a0 : A := Classical.choice hA
    have hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J) := by
      intro hd
      exact a0.2.2.1 (a0.1.1.mem_of_dvd hd (regularComponent_G_mem (GenericField K) S.G _ _ a0.1))
    have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hH
    have hT := reducedFirstFlag_of_route S.F J hroute
    have gate (a : A) := reduced_gamma_gate S (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hproper
      surfaceFlag reducedFirstFlag hS hT hsmall a.1 (hz a)
    obtain ⟨D,hD⟩ := exists_reduced_cycle_family S hfirst (linearH J) (linearG J)
      (hroute.2.2.2.2 _).1 hH component Subtype.val_injective hz
      surfaceFlag reducedFirstFlag hS hT hsmall
    let m (a : A) := localMultiplicity S (canonicalLocalDVRFamily S hfirst) a.1
    have hcount (a : A) : (stageSeeds S a.1).card≤m a*frameFlagCost D hz a reducedDelayFlag := by
      obtain ⟨delay,-,hd,hproper⟩ := a.2.2.2
      exact proper_component_seed_count S hfirst J hroute component hz gate D a a.2.2.1 delay hd hproper
    calc
      _≤∑ a : A, m a*frameFlagCost D hz a reducedDelayFlag :=
        Finset.sum_le_sum (fun a _ => hcount a)
      _=reducedDelayFlag.zOnly*(∑ a : A, m a*frameCost D hz .z a)+
          reducedDelayFlag.yz*(∑ a : A, m a*frameCost D hz .u a)+
          reducedDelayFlag.all*(∑ a : A, m a*frameCost D hz .v a) := by
        exact sum_weighted_three m (frameCost D hz .z) (frameCost D hz .u) (frameCost D hz .v)
          reducedDelayFlag.zOnly reducedDelayFlag.yz reducedDelayFlag.all
      _≤reducedDelayFlag.zOnly*flagMixed surfaceFlag reducedFirstFlag unitZFlag+
          reducedDelayFlag.yz*flagMixed surfaceFlag reducedFirstFlag unitYZFlag+
          reducedDelayFlag.all*flagMixed surfaceFlag reducedFirstFlag unitAllFlag :=
        Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ (hD .z)) (Nat.mul_le_mul_left _ (hD .u)))
          (Nat.mul_le_mul_left _ (hD .v))
      _= _ := (flagMixed_projection_decomposition surfaceFlag reducedFirstFlag reducedDelayFlag).symm
  · letI : IsEmpty A := ⟨fun a => hA ⟨a⟩⟩
    change (∑ a : A, (stageSeeds S a.1).card)≤_
    simp

theorem checked_proper_linear_seed_count
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)] (hp : p=2130706433)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    (hS : PolynomialInFlag ⟨3504,45,12⟩ S.G) :
    (∑ C : ProperLinearComponent S hfirst (linearH J), (stageSeeds S C.1).card) ≤80004988562225019 := by
  have hsmall : flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitZFlag<p := by
    rw [hp]
    exact checked_gamma_budget.2
  have he : flagMixed ⟨3504,45,12⟩ reducedFirstFlag reducedDelayFlag=80004988562225019 := by decide +kernel
  exact (proper_linear_seeds_sum_le S hfirst J hroute ⟨3504,45,12⟩ hS hsmall).trans_eq he







end
end ProximityPrize.SubmissionLower.MovingSourceProperSeedCount6814


