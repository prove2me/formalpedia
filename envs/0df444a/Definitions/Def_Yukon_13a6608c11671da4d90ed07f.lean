-- Prove2me | Definitions.Def_Yukon_13a6608c11671da4d90ed07f
-- name    : Yukon_13a6608c11671da4d90ed07f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T21:45:26.068336+00:00
-- url     : https://prove2.me/theorems/736fdd9f-0e8f-49c8-b2f3-c978aec2c0db
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeDirChain6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeDirChain6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeDirChain6814.lean
--
--   yukon-proof-operation:certificate-split-210bc66d8ea20ab9bbcff1667700b616cf2cb9466146ceb946fc315d7c321613
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiNDhhMTVkMzNjYzdlNWMxNzI4OWNjNjc3N2FkMTU1ZWVhMWQ1MDlmMzE1OTBmYTQ4MDA5ZDJlYWE5YjE2YjFhYSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTIxMGJjNjZkOGVhMjBhYjliYmNmZjE2Njc3MDBiNjE2Y2YyY2I5NDY2MTQ2Y2ViOTQ2ZmMzMTVkN2MzMjE2MTMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8xM2E2NjA4YzExNjcxZGE0ZDkwZWQwN2YiLCJ2IjoyfQ]

import Definitions.Def_Yukon_805f46d03627d566202e2c91
















































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# Per-direction H-free first cut: the counting chain

`MovingFiberFixedStage6814.stage_bound`, `MovingFiberRegularGeometry6814.regular_seed_bound` and
`MovingFiberProfile6814.count_of_interpolants` with the per-direction first cut: the stage
hypothesis is `HFreeDir6813.HFreeStageDir` (discharged by `hfree_stage_dir_of_gaps`) and the
numerator is `HFreeDir6813.numeratorDir` (`HFreeDirArith6814.numberDir` over the catalog).
The proofs are those of the originals with the names changed.
-/

namespace ProximityPrize.SubmissionLower.HFreeDirChain6814
noncomputable section

section FixedStage
open scoped Classical BigOperators
open RCN074 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instCharPGenericFieldOfNatNat : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {Gamma : Finset K} {x : I → K} {flag : FlagDegree}

theorem stage_bound_dir
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x 2130706433 80889 flag w (cellSupport t y r))
    (hnodes : S.nodes.card = 262144)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤ (S.agreementFiber gamma).card)
    (hbox : S.F ∈ globalCoefficientBox K D w t r)
    (hflag : flag.all ≤ r ∧ flag.yz+flag.all ≤ y ∧ flag.zOnly+flag.yz+flag.all ≤ t)
    (source : Fin 3 → Source S.F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : HFreeDir6813.HFreeStageDir S)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (hidentityAbs : scale*131073*80890*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w ≤
      50184*HFreeDir6813.numeratorDir source scale t y r flag) :
    Gamma.card ≤ HFreeDir6813.numeratorDir source scale t y r flag/scale := by
  have hflagChar : flag.yz+flag.all < 2130706433 ∧ flag.all < 2130706433 ∧
      flag.zOnly+flag.yz+flag.all < 2130706433 := by omega
  by_cases hTail : S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1)
  · have hTailNumerator := (globalTailCut_dvd_iff (polynomialEmbedding K)
      (polynomialEmbedding_injective K) S.F (w+1) S.G).mp hTail
    have hmixed := BoundaryTailGates.identity_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have hprovider := BoundaryTailIdentity.actual_identityCurveCountProvider S 181255
      (by simpa using hnodes) hagreement (by norm_num [w]) hTailNumerator D t r
      (by norm_num [w]) hDlow hDchar hbox hflagChar hmixed
    have hpositive : 1 ≤ identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      apply Lower80788.FixedStage.identity_positive
      have hp := S.y_dependent
      have hd := degreeOf_le_flag_total S.G flag S.flag_support 1
      omega
    have hinc := identity_surface_seed_bound S 181255 _ hprovider hagreement
      (by norm_num [w]) (by rw [hnodes]; norm_num) hpositive
    have hinc' : Gamma.card*50184 ≤ 131073*80890*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w := by
      simpa only [hnodes,w] using hinc
    have hnum : scale*Gamma.card ≤ HFreeDir6813.numeratorDir source scale t y r flag := by
      apply Nat.le_of_mul_le_mul_left (c := 50184) _ (by decide)
      calc
        50184*(scale*Gamma.card) = scale*(Gamma.card*50184) := by ring
        _ ≤ scale*(131073*80890*identityCurveDegree flag (cellA t y) (cellB y r) (cellS r) w) :=
          Nat.mul_le_mul_left _ hinc'
        _ ≤ _ := by simpa only [Nat.mul_assoc] using hidentityAbs
    exact (Nat.le_div_iff_mul_le hscale).mpr (by simpa only [Nat.mul_comm] using hnum)
  · have hmixed := BoundaryTailGates.reduced_gate flag t y r hr3 hr hy hry (by omega) hflag.1 hflag.2.1
    have htangent : ∀ C : FirstTailComponent S,
        (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
        (componentSeeds (GenericField K) S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
          (regularitySurface (polynomialEmbedding K) S.F) Gamma
          (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
          (80889+1)*(BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed).yzCost C := by
      intro C hall
      exact tangent_component_card_le S C hTail (BoundaryTailReduced.reducedBaseOrd S hTail hflagChar hmixed C)
        181255 D t r (by simpa using hnodes) hagreement (by norm_num [w]) (by norm_num [w])
        hDlow hDchar hbox (BoundaryTailReduced.reducedBudgetFamily S hTail hflagChar hmixed)
        (BoundaryTailReduced.reducedBudgetFamily_yzPositive S hTail hflagChar hmixed C) hall
        (BoundaryTailReduced.reducedBudgetFamily_yzPole S hTail hflagChar hmixed C)
    have hmov : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < 2130706433 := by
      have hm := Nat.mul_le_mul (show 2*(flag.zOnly+flag.yz+flag.all) ≤ 2*7501 by omega)
        (show t+1 ≤ 7502 by omega)
      omega
    exact HFreeDir6813.retained_stage_bound_dir t y r scale hr3 hry (by omega) S source hscale hscaleDiv hfree hTail
      hflagChar hmixed (by omega) hmov (by norm_num [w]) (by
        unfold cellNormal
        rw [BoundaryTailAlgebra.normalFlag_eq_cell t y r hr3 hry]
        simpa only [add_yz,nsmul_yz,unitAllFlag,mul_zero,add_zero] using
          hybridC1Gate_of_le t y r 80889 hry (by norm_num)) htangent h2 hfact hgood

end FixedStage

section RegularGeometry
open scoped Classical BigOperators
open RCN081 RCN084 RCN085 RCN086 RCN087 RCN095 RCN130 RCN135 RCN136 RCN137 RCN146 RCN156 RCN159
open RCN174 RCN198 RCN199 RCN206 RCN207 RCN221 RCN222 RCN234 RCN237 RCN238 RCN243 RCN244 RCN260 RCN263 RCN264
open RCN271 RCN275 RCN287 RCN312 RCN313 RCN319 RCN327 RCN330 RCN332 RCN334 RCN335 RCN336 RCN338 RCN339 RCN341
open LocatorHybridCells LocatorHybridCellsC1 LocatorHybridTailProvider LocatorHybridTransportC2
open BoundaryTailProvider MovingFiberThreeSources6811 MovingFiberRetainedStage6811
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000
variable {K I : Type} [Field K] [CharP K 2130706433]
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instDecidableEq_proximityPrize_2 : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instDecidableEq_proximityPrize_3 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instCharPGenericFieldOfNatNat_1 : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433

theorem regular_seed_bound_dir
    (D t y r scale : ℕ) (hDlow : 131072 ≤ D) (hDchar : D < 2130706433)
    (ht : t ≤ 7501) (hy : y ≤ 142) (hr : r ≤ 31)
    (hr3 : 3 ≤ r) (hry : r+2 ≤ y) (hyt : y+2 ≤ t)
    (F : MvPolynomial (Fin 4) K) (hF : Irreducible F) (hFR : 0 < F.degreeOf 2)
    (hbox : F ∈ globalCoefficientBox K D w t r)
    (hsupport : ResidualSupportData (cellSupport t y r) F)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (nodes : Finset I) (x u0 u1 : I → K) (hinj : Set.InjOn x nodes) (hnodes : nodes.card = 262144)
    (hdegree : ∀ gamma ∈ Gamma, (selected gamma).natDegree ≤ w)
    (hagreement : ∀ gamma ∈ Gamma, 181255 ≤
      (nodes.filter (fun i => (selected gamma).eval (x i) = u0 i+gamma*u1 i)).card)
    (hsolution : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma F = 0)
    (hregular : ∀ gamma ∈ Gamma, specialization K (selected gamma) gamma (MvPolynomial.pderiv (2 : Fin 4) F) ≠ 0)
    (hno : NoLargeSelectedPencil selected Gamma w 80889)
    (source : Fin 3 → Source F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : ∀ (G : Finset K) (fl : FlagDegree) (S : ResidualStage (polynomialEmbedding K) G x
      2130706433 80889 fl w (cellSupport t y r)), S.F = F → HFreeDir6813.HFreeStageDir S)
    (h2 : (2 : GenericField K) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : GenericField K) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0)
    (hidentity : ∀ f : FlagDegree, scale*131073*80890*identityCurveDegree f (cellA t y) (cellB y r) (cellS r) w ≤
      50184*HFreeDir6813.numeratorDir source scale t y r f) :
    scale*Gamma.card ≤ HFreeDir6813.numeratorDir source scale t y r (originalCumulativeFlag F) := by
  have hFRsmall : F.degreeOf 2 < 2130706433 := (degreeOf_R_le_of_mem_box F D w t r hbox).trans_lt (by omega)
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = y := by dsimp [cellB,cellS]; omega
  have hts : cellA t y+cellB y r+cellS r+3 = t := by dsimp [cellA,cellB,cellS]; omega
  have hcover := card_le_sum_geometricSeeds K F hF.ne_zero selected Gamma hsolution
  have hstage (g : GeometricFactor K F) :
      scale*(geometricSeeds K F selected Gamma g).card ≤
        HFreeDir6813.numeratorDir source scale t y r (geometricCumulativeFlag K g) := by
    let S0 := geometricResidualStageOfSupport K (cellSupport t y r) F hF hFR hFRsmall hsupport
      selected Gamma nodes x u0 u1 hinj hdegree hsolution hregular hno (by norm_num [w]) g
    let S := reflagResidualStage S0 (polynomialIn_surfaceCumulativeFlag g.1)
    have hsub := geometricSeeds_subset K F selected Gamma g
    have hag : ∀ gamma ∈ geometricSeeds K F selected Gamma g, 181255 ≤ (S.agreementFiber gamma).card :=
      fun gamma hgamma => hagreement gamma (hsub hgamma)
    have hf := geometricCumulativeFlag_le_support F hF.ne_zero hsupport g
    have hf' : (geometricCumulativeFlag K g).all ≤ r ∧
        (geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ y ∧
        (geometricCumulativeFlag K g).zOnly+(geometricCumulativeFlag K g).yz+(geometricCumulativeFlag K g).all ≤ t := by
      simpa only [cellSupport,RCN198.support,hs,hys,hts] using hf
    have hc := stage_bound_dir D t y r scale hDlow hDchar ht hy hr hr3 hry hyt
      S hnodes hag hbox hf' source hscale hscaleDiv (hfree _ _ S rfl) h2 hfact
      (fun gamma hgamma j => hgood gamma (hsub hgamma) j) (hidentity _)
    have hm := (Nat.le_div_iff_mul_le hscale).mp hc
    dsimp only [S,S0,reflagResidualStage,geometricResidualStageOfSupport] at hm
    simpa only [Nat.mul_comm,geometricCumulativeFlag] using hm
  have hb := geometricCumulativeFlag_budgets F hF.ne_zero
  calc
    scale*Gamma.card ≤ scale*∑ g : GeometricFactor K F, (geometricSeeds K F selected Gamma g).card :=
      Nat.mul_le_mul_left _ hcover
    _ = ∑ g : GeometricFactor K F, scale*(geometricSeeds K F selected Gamma g).card := Finset.mul_sum _ _ _
    _ ≤ ∑ g : GeometricFactor K F,
        HFreeDir6813.numeratorDir source scale t y r (geometricCumulativeFlag K g) :=
      Finset.sum_le_sum (fun g _ => hstage g)
    _ ≤ _ := HFreeDir6813.sum_numeratorDir_le source scale t y r (geometricCumulativeFlag K)
      (originalCumulativeFlag F) hb.1 hb.2.1 hb.2.2

end RegularGeometry

section Profile
open scoped Classical BigOperators
open MvPolynomial RCN095 RCN130 RCN135 RCN136 RCN146 RCN156 RCN174 RCN222 RCN234 RCN238 RCN243 RCN260 RCN319 RCN327
open LocatorHybridCells LocatorHybridCellsC1 BoundaryTailProvider
open MovingFiberRegularData6814 MovingFiberThreeSources6811 MovingFiberInterpolation6814 MovingFiberTotalAvoidance6814
open MovingFiberProfile6814 HFreeDirArith6814
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

variable {K I : Type} [Field K] [CharP K 2130706433] [Fintype I]
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instDecidableEq_proximityPrize_4 : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instDecidableEq_proximityPrize_5 : DecidableEq I := Classical.decEq I
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDirChain6814.instCharPGenericFieldOfNatNat_2 : CharP (GenericField K) 2130706433 := genericField_charP K 2130706433
variable {nodes : I ↪ K} {u0 u1 : I → K}

/-- `MovingFiberProfile6814.bound` with `numberDir`. -/
def boundDir (S : Data nodes u0 u1) (cfg : Fin 3 → Params) (scale : ℕ) : ℕ :=
  max (Finset.univ.sup (fun j : Fin 3 => helperCap S (cfg j)))
    (numberDir cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale +
      ∑ j : Fin 3, coefficientCap S (cfg j))

theorem count_of_interpolants_dir
    (S : Data nodes u0 u1) (hI : Fintype.card I = 262144)
    (cfg : Fin 3 → Params) (hc : ∀ j, (cfg j).WellFormed)
    (scale : ℕ) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(cfg j).d ∣ scale)
    (hfree : ∀ (G : Finset K) (fl : FlagDegree) (S' : RCN159.ResidualStage (polynomialEmbedding K) G
      ⇑nodes 2130706433 80889 fl w (cellSupport S.t S.y S.r)), S'.F = S.F →
      HFreeDir6813.HFreeStageDir S')
    (P : Fin 3 → SecondJetSupport.Poly (K := K))
    (hP : ∀ j, Interpolant (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 nodes u0 u1 (P j))
    (hL : ∀ j, (cfg j).L < wt residualTotalWeights S.F)
    (hHelperGates : ∀ j, S.PairGates ((cfg j).B+(cfg j).s*(S.r-1))
      ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)))
    (hCoefficientGates : ∀ j, S.PairGates (cfg j).B (cfg j).U (cfg j).L)
    (hidentity : ∀ f : FlagDegree, scale*131073*80890*
      identityCurveDegree f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w ≤
        50184*numberDir cfg scale S.t S.y S.r f) :
    S.seeds.card ≤ boundDir S cfg scale := by
  classical
  have hshape (j : Fin 3) : ∀ e ∈ (P j).support, 2*e 1+e 3 ≤ (cfg j).B ∧
      e 1+e 2+e 3 ≤ (cfg j).U ∧ e 1+e 2+e 3+e 4 ≤ (cfg j).L := by
    intro e he
    have h := (hP j).2.1 e he
    exact ⟨h.1,h.2.2.1,h.2.2.2.1⟩
  have hS (j : Fin 3) : ∀ e ∈ (P j).support, e 1 ≤ (cfg j).s := fun e he => ((hP j).2.1 e he).2.1
  have factorial (j : Fin 3) (d : ℕ) (hd : d ≤ (cfg j).s) : (d.factorial : K) ≠ 0 :=
    SecondJetOwnShape.factorial_ne d (hd.trans_lt (hc j).2.2.2.2.2.2.2)
  have alternatives (j : Fin 3) := helper_or_divisibility (P j) S.F
    (cfg j).m (cfg j).B (cfg j).s (cfg j).U (cfg j).L (cfg j).k (cfg j).n0 S.r S.y S.t
    nodes u0 u1 (hP j) S.irreducible (hL j) (hc j).1
    (by have := hc j; unfold Params.WellFormed at this; omega)
    (by have := hc j; unfold Params.WellFormed at this; omega)
    (hc j).2.2.2.1 (hc j).2.2.2.2.1
    (by have := S.rpos; omega) (by have := S.ry; omega) (by have := S.yt; omega)
    S.weights (factorial j)
  by_cases hall : ∀ j : Fin 3, (cfg j).n0 ≤ (SecondJetCoefficients.asS (P j)).natDegree ∧
      ∀ d ≤ (cfg j).k, S.F ∣ SecondJetClearedHelper.helper (P j) S.F ((cfg j).s-d) d
  · let source : Fin 3 → Source S.F := fun j => {
      P := P j, B := (cfg j).B, U := (cfg j).U, T := (cfg j).L,
      s := (cfg j).s, k := (cfg j).k, n0 := (cfg j).n0,
      hS := hS j, hshape := hshape j, hBU := (hc j).2.1,
      hUT := (hc j).2.2.1, hdn := (hc j).2.2.2.2.2.1,
      hB := (hc j).2.2.2.2.2.2.1, hn := (hall j).1, hdiv := (hall j).2 }
    let point := selectedPoint (polynomialEmbedding K) S.selected
    let LC := fun j : Fin 3 => surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS (P j)).leadingCoeff
    let Good := S.seeds.filter (fun gamma => ∀ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) ≠ 0)
    let Bad := fun j : Fin 3 => S.seeds.filter (fun gamma => MvPolynomial.eval (point gamma) (LC j) = 0)
    let SG := S.restrict Good (Finset.filter_subset _ _)
    have hnum (f : FlagDegree) : HFreeDir6813.numeratorDir source scale S.t S.y S.r f =
        numberDir cfg scale S.t S.y S.r f := rfl
    have h2 : (2 : GenericField K) ≠ 0 := SecondJetOwnShape.two_ne
    have hf (j : Fin 3) : ((source j).k.factorial : GenericField K) ≠ 0 :=
      SecondJetOwnShape.factorial_ne (cfg j).k (by
        have := hc j; unfold Params.WellFormed at this; omega)
    have hgood : ∀ gamma ∈ SG.seeds, ∀ j,
        MvPolynomial.eval (selectedPoint (polynomialEmbedding K) SG.selected gamma)
          ((source j).leading (polynomialEmbedding K)) ≠ 0 := by
      intro gamma hgamma j
      exact (Finset.mem_filter.mp hgamma).2 j
    have hid (f : FlagDegree) : scale*131073*80890*
        identityCurveDegree f (cellA S.t S.y) (cellB S.y S.r) (cellS S.r) w ≤
          50184*HFreeDir6813.numeratorDir source scale S.t S.y S.r f := by
      rw [hnum]
      exact hidentity f
    have hg := regular_seed_bound_dir
      SG.D SG.t SG.y SG.r scale SG.Dlow SG.Dchar SG.tbound SG.ybound SG.rbound SG.rpos SG.ry SG.yt
      SG.F SG.irreducible SG.rdegree SG.box SG.support SG.selected SG.seeds Finset.univ nodes u0 u1
      nodes.injective.injOn (by simpa only [Finset.card_univ] using hI)
      SG.degree SG.agreement SG.solution SG.regular SG.noPencil
      source hscale hscaleDiv hfree h2 hf hgood hid
    have hGood : Good.card ≤ numberDir cfg scale S.t S.y S.r (originalCumulativeFlag S.F)/scale := by
      apply (Nat.le_div_iff_mul_le hscale).mpr
      rw [← hnum]
      dsimp only [SG,Data.restrict] at hg
      simpa only [Nat.mul_comm] using hg
    have hBad (j : Fin 3) : (Bad j).card ≤ coefficientCap S (cfg j) := by
      let SB := S.restrict (Bad j) (Finset.filter_subset _ _)
      have hnot := SecondJetTotalAvoidance.leading_not_dvd (P j) (hP j).1 S.F (cfg j).L
        (fun e he => (hshape j e he).2.2) (hL j)
      have hrel : IsRelPrime SB.F (SecondJetCoefficients.asS (P j)).leadingCoeff :=
        S.irreducible.isRelPrime_iff_not_dvd.mpr hnot.2
      apply SB.proper_count_left hI _ (cfg j).B (cfg j).U (cfg j).L hrel
        (SecondJetPairBounds.leading_degree_caps (P j) (cfg j).B (cfg j).U (cfg j).L (hshape j))
        (hCoefficientGates j)
      intro gamma hgamma
      have hz : MvPolynomial.eval (point gamma) (LC j) = 0 := (Finset.mem_filter.mp hgamma).2
      change MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        (surfaceMap (polynomialEmbedding K) (SecondJetCoefficients.asS (P j)).leadingCoeff) = 0 at hz
      rw [selectedPoint_surface_evaluation] at hz
      dsimp only [SB,Data.restrict]
      exact (polynomialEmbedding_injective K) (by simpa only [map_zero] using hz)
    have hcover : S.seeds ⊆ Good ∪ Finset.univ.biUnion Bad := by
      intro gamma hgamma
      by_cases hg : ∀ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) ≠ 0
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hgamma,hg⟩)
      · have hex : ∃ j : Fin 3, MvPolynomial.eval (point gamma) (LC j) = 0 := by simpa only [not_forall,not_not] using hg
        obtain ⟨j,hj⟩ := hex
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hgamma,hj⟩⟩)
    have hcard : S.seeds.card ≤ Good.card+∑ j : Fin 3, (Bad j).card :=
      ((Finset.card_le_card hcover).trans (Finset.card_union_le _ _)).trans
        (Nat.add_le_add_left Finset.card_biUnion_le _)
    exact (hcard.trans (Nat.add_le_add hGood (Finset.sum_le_sum (fun j _ => hBad j)))).trans (le_max_right _ _)
  · obtain ⟨j,hj⟩ := not_forall.mp hall
    rcases alternatives j with ⟨Q,hrel,hw,hzero⟩ | hret
    · have hb := S.proper_count_left hI Q ((cfg j).B+(cfg j).s*(S.r-1))
        ((cfg j).U+(cfg j).s*(S.y-1)) ((cfg j).L+(cfg j).s*(S.t-1)) hrel
        (SecondJetPairBounds.degree_caps_of_weights Q _ _ _ hw) (hHelperGates j) (by
          intro gamma hgamma
          apply hzero (S.selected gamma) (S.degree gamma hgamma) gamma
            (Finset.univ.filter (fun i => (S.selected gamma).eval (nodes i) = u0 i+gamma*u1 i))
            (S.agreement gamma hgamma) _ (S.solution gamma hgamma)
          intro i hi
          simpa only [mul_comm] using (Finset.mem_filter.mp hi).2)
      exact (hb.trans (Finset.le_sup (f := fun j : Fin 3 => helperCap S (cfg j)) (Finset.mem_univ j))).trans (le_max_left _ _)
    · exact (hj hret).elim

end Profile

end
end ProximityPrize.SubmissionLower.HFreeDirChain6814


