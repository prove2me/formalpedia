-- Prove2me | Definitions.Def_Yukon_c71a73feb87d242e88d6b4dc
-- name    : Yukon_c71a73feb87d242e88d6b4dc
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T08:35:29.842423+00:00
-- url     : https://prove2.me/theorems/e721c902-9eff-45bd-96e5-db61ae433ad3
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceConstantSeeds6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-74c2d9139c36dbdb30856dddc617e142ed89f6932ba889b00727aef5b016dbba
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZGU5ZWExNDZiNjU0MjFlN2VkZDRmNzhlOTViNzU3MDk2ZTI2MWE4ZDMyYTdiNzY2ODhlN2ZmOTQyYmE5ODc0MyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtNzRjMmQ5MTM5YzM2ZGJkYjMwODU2ZGRkYzYxN2UxNDJlZDg5ZjY5MzJiYTg4OWIwMDcyN2FlZjViMDE2ZGJiYSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2M3MWE3M2ZlYjg3ZDI0MmU4OGQ2YjRkYyIsInYiOjJ9]

import Definitions.Def_Yukon_c562ca1e602b3cc572e6a79f























































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Constant-parameter components have at most one selected seed apiece.
Their number is charged once to the new coprime pair, without requiring
separability in either of the two remaining literal coordinates. -/
namespace ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators Classical
open RCN002 RCN022 RCN093 RCN095 RCN135 RCN136 RCN238 RCN243 RCN264
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceProperSeedCount6814 MovingSourceReducedGamma6814
open MovingSourceLinearFlow6814 MovingSourceReducedRoutes6814

theorem constant_parameter_seeds_le_one
    {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω]
    (phi : Polynomial K →+* Ω) (selected : K → Polynomial K) (seeds : Finset K)
    (P : Ideal (MvPolynomial (Fin 3) Ω)) [P.IsPrime]
    (hconstant : IsAlgebraic Ω (coordinate Ω P 2))
    (hon : ∀ gamma∈seeds, P≤RingHom.ker (MvPolynomial.aeval (selectedPoint phi selected gamma)).toRingHom) :
    seeds.card≤1 := by
  obtain ⟨c,hc⟩ := RCN370.eq_algebraMap_of_isAlgebraic Ω (CoordinateField Ω P) _ hconstant
  have hmem : MvPolynomial.X (2 : Fin 3)-MvPolynomial.C c∈P := by
    rw [←coordinateEvaluation_ker Ω P]
    change coordinateEvaluation Ω P (MvPolynomial.X 2-MvPolynomial.C c)=0
    rw [coordinateEvaluation_eq_aeval]
    simpa using sub_eq_zero.mpr hc.symm
  have hvalue (gamma : K) (hgamma : gamma∈seeds) : (phi.comp Polynomial.C) gamma=c := by
    have hh := hon gamma hgamma hmem
    change MvPolynomial.aeval (selectedPoint phi selected gamma)
      (MvPolynomial.X (2 : Fin 3)-MvPolynomial.C c)=0 at hh
    simpa only [map_sub,MvPolynomial.aeval_X,MvPolynomial.aeval_C,
      Algebra.algebraMap_self,RingHom.id_apply,selectedPoint_seed,sub_eq_zero] using hh
  apply Finset.card_le_one.mpr
  intro gamma hgamma eta heta
  exact (phi.comp Polynomial.C).injective ((hvalue gamma hgamma).trans (hvalue eta heta).symm)

/-- A nonconstant literal projection counts components by their positive
full field degrees. No separability hypothesis is introduced. -/
theorem card_primes_le_direction
    {Ω : Type} [Field Ω] {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hinj : Function.Injective P) (axis : Axis)
    (ht : ∀ a, Transcendental Ω
      (flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))))
    (F N : MvPolynomial (Fin 3) Ω) (hF : F≠0) (hN : N≠0) (hrel : IsRelPrime F N)
    (hFmem : ∀ a,F∈P a) (hNmem : ∀ a,N∈P a)
    (p q : FlagDegree) (hp : PolynomialInFlag p F) (hq : PolynomialInFlag q N) :
    Fintype.card A≤flagMixed p q axis.flag := by
  letI : ∀ a, Algebra (RatFunc Ω) (CoordinateField Ω (P a)) := fun a =>
    (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) 0 0 0 (MvPolynomial.X (axis.order 0))) (ht a)).toRingHom.toAlgebra
  have hb := finite_sum_prime_fields Ω axis 0 0 0 P hinj ht F N hF hN hrel hFmem hNmem p q hp hq
  calc
    Fintype.card A=∑ _ : A, 1 := by simp
    _≤∑ a : A, Module.finrank (RatFunc Ω) (CoordinateField Ω (P a)) := by
      apply Finset.sum_le_sum
      intro a _
      letI := hb.1 a
      exact Module.finrank_pos
    _≤_ := hb.2

theorem constant_prime_family_card_le
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Type} [Fintype A]
    (P : A → Ideal (MvPolynomial (Fin 3) Ω)) [∀ a,(P a).IsPrime]
    (hinj : Function.Injective P)
    (hnonpoint : ∀ a, ∀ v : Fin 3 → Ω, P a≠RingHom.ker (MvPolynomial.aeval v).toRingHom)
    (hconstant : ∀ a, IsAlgebraic Ω (coordinate Ω (P a) 2))
    (F N : MvPolynomial (Fin 3) Ω) (hF : F≠0) (hN : N≠0) (hrel : IsRelPrime F N)
    (hFmem : ∀ a,F∈P a) (hNmem : ∀ a,N∈P a)
    (p q : FlagDegree) (hp : PolynomialInFlag p F) (hq : PolynomialInFlag q N) :
    Fintype.card A≤flagMixed p q unitYZFlag+flagMixed p q unitAllFlag := by
  let activeY (a : A) := Transcendental Ω (coordinate Ω (P a) 0)
  have hr (a : A) (ha : ¬activeY a) : Transcendental Ω (coordinate Ω (P a) 1) := by
    obtain ⟨i,hi⟩ := exists_transcendental_coordinate_of_ne_point_kernel Ω (P a) (hnonpoint a)
    fin_cases i
    · exact False.elim (ha hi)
    · exact hi
    · exact False.elim (hi (hconstant a))
  have hycap : Fintype.card {a : A // activeY a}≤flagMixed p q unitYZFlag :=
    card_primes_le_direction (fun a : {a : A // activeY a} => P a.1)
      (fun a b h => Subtype.ext (hinj h)) .u
      (fun a => by simpa [Axis.order,RCN125.uOrder,affineU] using a.2)
      F N hF hN hrel (fun a => hFmem a.1) (fun a => hNmem a.1) p q hp hq
  have hrcap : Fintype.card {a : A // ¬activeY a}≤flagMixed p q unitAllFlag :=
    card_primes_le_direction (fun a : {a : A // ¬activeY a} => P a.1)
      (fun a b h => Subtype.ext (hinj h)) .v
      (fun a => by simpa [Axis.order,RCN125.vOrder,affineV] using hr a.1 a.2)
      F N hF hN hrel (fun a => hFmem a.1) (fun a => hNmem a.1) p q hp hq
  have hcomp := Fintype.card_subtype_compl activeY
  have hle : Fintype.card {a : A // activeY a}≤Fintype.card A :=
    Fintype.card_le_of_injective (fun a : {a : A // activeY a} => a.1) Subtype.val_injective
  omega

open RCN074 RCN086 RCN244
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

abbrev ConstantComponent (S : Stage K I Gamma x p flag errorCap stageSupport) :=
  {C : FirstTailComponent S // IsAlgebraic (GenericField K) (coordinate (GenericField K) C.1 2)}

theorem constant_seed_sum_le
    (S : Stage K I Gamma x p flag errorCap stageSupport) [Fact (Irreducible S.F)]
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (J : WholeSpaceCube6814.Poly (K:=K)) (hroute : LinearRoute S.F J)
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) (linearH J))
    (surfaceFlag : FlagDegree) (hS : PolynomialInFlag surfaceFlag S.G) :
    (∑ C : ConstantComponent S, (stageSeeds S C.1).card)≤
      flagMixed surfaceFlag reducedFirstFlag unitYZFlag+flagMixed surfaceFlag reducedFirstFlag unitAllFlag := by
  have hproper := reducedTail_proper S hfirst (linearH J) (linearG J) (hroute.2.2.2.2 _).1 hH
  have hcard := constant_prime_family_card_le (fun a : ConstantComponent S => a.1.1)
    (fun a b h => Subtype.ext (Subtype.ext h))
    (fun a => regularComponent_ne_point (GenericField K) S.G _ _ a.1) (fun a => a.2)
    S.G (MovingSourceReducedCycle6814.reducedTailSurface (linearH J) (linearG J)) S.irreducible_G.ne_zero
    (fun hz => hproper (hz ▸ dvd_zero _)) (S.irreducible_G.isRelPrime_iff_not_dvd.mpr hproper)
    (fun a => regularComponent_G_mem (GenericField K) S.G _ _ a.1)
    (fun a => reducedTail_mem_old_component S (linearH J) (linearG J) (hroute.2.2.2.2 _).1 a.1)
    surfaceFlag reducedFirstFlag hS (reducedFirstFlag_of_route S.F J hroute)
  calc
    _≤∑ _ : ConstantComponent S, 1 := by
      apply Finset.sum_le_sum
      intro a _
      exact constant_parameter_seeds_le_one (polynomialEmbedding K) S.selected _ a.1.1 a.2
        (fun gamma hgamma => componentSeeds_on_prime (GenericField K) S.G _ _ Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) a.1 gamma hgamma)
    _=Fintype.card (ConstantComponent S) := by simp
    _≤_ := hcard

theorem constant_checked_budget :
    flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitYZFlag+
      flagMixed ⟨3504,45,12⟩ reducedFirstFlag unitAllFlag=33131204085 := by decide +kernel





end
end ProximityPrize.SubmissionLower.MovingSourceConstantSeeds6814


