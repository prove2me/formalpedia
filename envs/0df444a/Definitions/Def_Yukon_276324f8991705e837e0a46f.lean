-- Prove2me | Definitions.Def_Yukon_276324f8991705e837e0a46f
-- name    : Yukon_276324f8991705e837e0a46f
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T15:47:39.734666+00:00
-- url     : https://prove2.me/theorems/59feeaf2-dae8-4c36-aafe-4e20090cc8c5
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.HFreeDir6813.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.HFreeDir6813.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/HFreeDir6813.lean
--
--   yukon-proof-operation:certificate-split-46a1ef0a601869589578fa717501faeabce713496046f9cb9f9ff96edcbc224f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMWEwMzcxOGJiMTExNDU0YWZhNmZhODVkNTY2MDA3MDY0Njg1OTZkNDM4NWJjZDA2Y2FmMmVjMjNhNjRmMGNjZiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTQ2YTFlZjBhNjAxODY5NTg5NTc4ZmE3MTc1MDFmYWVhYmNlNzEzNDk2MDQ2ZjljYjlmOWZmOTZlZGNiYzIyNGYiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yNzYzMjRmODk5MTcwNWU4MzdlMGE0NmYiLCJ2IjoyfQ]

import Definitions.Def_Yukon_071b2a37055271dabd65e7ea

import Definitions.Def_Yukon_5afa23587d963dbc1134f9e0





















































































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-!
# H-free first cut, per slice direction

`HFreeInfLaw6813` refines the per-place law at infinity by direction: a slice of direction `d`
subtracts `(w+1) · flagPole (infCap d)` from the H-free budget.  Summing over `W ∪ {zeros of H}`,
where the zeros of `H` are bounded by its flag `⟨z,v,r-1⟩`, the X-flag of direction `d` becomes

  `hfreeFlagDir d r v z C0 = (w+1) • cuspFlag d r v z + 3 • C0`,

with `cuspFlag d = 2•⟨z,v,r-1⟩ - capFlag d`, i.e. `⟨2z,2v-3,2r-7⟩`, `⟨2z,2v,2r-7⟩`,
`⟨2z,2v-3,2r-4⟩` (at `r = 3` the unitAll part of the cap above `2r-2` moves to unitYZ, which is
weaker since `t ≤ P`).  This replaces `2(w+1)•⟨z,v,r-1⟩ + 3•C0` of `HFreeFirstSlice6812.hfreeFlag`.

The stage-level hypothesis `HFreeStageDir` is discharged by `hfree_stage_dir_of_gaps`, and
`retained_stage_bound_dir` charges the retained stage `numeratorDir`, whose first-cut term is
`Σ_j scale/3 · normal_j · flagMixed f (hfreeFirstDir t y r j) e_j`.
-/

namespace ProximityPrize.SubmissionLower.HFreeDir6813
open RCN057 (WeightBound)
open RCN204 (flagPole)
open RCN026 (Place)
open scoped Classical BigOperators WithZero
open RCN002 RCN005 RCN006 RCN007 RCN055 RCN074 RCN086 RCN095 RCN134 RCN135 RCN136
open RCN156 RCN208 RCN234 RCN244 RCN248 RCN313 RCN341
open SecondJetSupport SecondJetCoefficients SecondJetClearedHelper
open ActualFirstCutPole6807 HFreeFirstSlice6812
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 500000

section Flags
local notation "w" => RCN326.w

theorem flag_eq_iff (p q : FlagDegree) :
    p = q ↔ p.zOnly = q.zOnly ∧ p.yz = q.yz ∧ p.all = q.all := by
  cases p; cases q; simp

/-- The cusp flag of direction `d`, in half units. -/
def cuspFlag (d : Fin 3) (r v z : ℕ) : FlagDegree :=
  ![⟨2*z, 2*v-3-(7-2*r), 2*r-7⟩, ⟨2*z, 2*v-(7-2*r), 2*r-7⟩, ⟨2*z, 2*v-3, 2*r-4⟩] d

/-- The part of `infCap d` subtracted from `2•⟨z,v,r-1⟩` (all of it for `r ≥ 4`). -/
def capFlag (d : Fin 3) (r : ℕ) : FlagDegree :=
  ![⟨0, 3+(7-2*r), 5-(7-2*r)⟩, ⟨0, 7-2*r, 5-(7-2*r)⟩, ⟨0, 3, 2⟩] d

theorem cusp_add_cap (d : Fin 3) (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v) :
    cuspFlag d r v z + capFlag d r = 2 • (⟨z, v, r-1⟩ : FlagDegree) := by
  rw [flag_eq_iff]
  fin_cases d <;> simp [cuspFlag, capFlag] <;> omega

/-- `capFlag d r` is dominated by `infCap d` at every place, since `t ≤ P`. -/
theorem capFlag_pole_le {L : Type*} [Field L] (V : Valuation L (WithZero (Multiplicative ℤ)))
    (x : Fin 3 → L) (d : Fin 3) (r : ℕ) (hr : 3 ≤ r) :
    flagPole V x (capFlag d r) ≤ flagPole V x (HFree6812.infCap d) := by
  have h1 : 0 ≤ RCN187.poleOrder V (x 0) := le_max_left _ _
  have h2 := le_max_right (RCN187.poleOrder V (x 1))
    (max (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2)))
  have h3 := le_max_left (RCN187.poleOrder V (x 0)) (RCN187.poleOrder V (x 2))
  rcases (show r = 3 ∨ 7 - 2*r = 0 by omega) with rfl | h0
  · fin_cases d <;> simp [flagPole, capFlag, HFree6812.infCap] <;> omega
  · fin_cases d <;> simp [flagPole, capFlag, HFree6812.infCap, h0]

/-- The H-free first-cut flag of direction `d`. -/
def hfreeFlagDir (d : Fin 3) (r v z : ℕ) (C0 : FlagDegree) : FlagDegree :=
  (w+1) • cuspFlag d r v z + 3 • C0

end Flags

section Slice
local notation "w" => RCN326.w
variable {K E : Type} [Field K] [Field E] [IsAlgClosed E]

/-- **The H-free per-slice pole budget with a cap at infinity (hypothesis).**  As
`HFreeSliceBudget`, with `(w+1) · flagPole Cap` subtracted at every place; `Cap = 0` is
`HFreeSliceBudget`. -/
structure HFreeSliceBudgetCap (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime] (C0 Cap : FlagDegree) : Prop where
  pole_le : ∀ W : Finset (Place E (CoordinateField E C)),
    3 * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
    ∑ nu ∈ W, (((w+1 : ℕ) : ℤ) *
      (4*RCN064.movingPoleTarget C (surfaceMap phi (polyH K F)) (surfaceMap phi (polyG K F)) nu +
        2*RCN026.zeroOrder E (CoordinateField E C) nu
          (SecondJetComponentRoots.coefficientMap phi C (polyH K F)) -
        flagPole nu.val (coordinate E C) Cap) +
      3*flagPole nu.val (coordinate E C) C0)

/-- `hfree_source_pole_mass` per direction: the X-flag is `hfreeFlagDir d r v z C0`. -/
theorem hfree_source_pole_mass_dir
    (phi : Polynomial K →+* E) (F : MvPolynomial (Fin 4) K)
    (C : Ideal (MvPolynomial (Fin 3) E)) [C.IsPrime]
    (base : SeparableLiteralCoordinate C)
    (P : Poly (K := K)) (B U T s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ T)
    (hBU : B ≤ U) (hUT : U ≤ T) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hF : surfaceMap phi F ∈ C)
    (hH : surfaceMap phi (polyH K F) ∉ C)
    (hlead : surfaceMap phi (asS P).leadingCoeff ∉ C)
    (hdiv : ∀ j ≤ k, F ∣ helper P F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (d : Fin 3) (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights F (r : ℤ))
    (hYR : WeightBound residualYSWeights F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hbudget : HFreeSliceBudgetCap phi F C C0 (HFree6812.infCap d))
    (CX CV : ℕ)
    (hXbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C) (hfreeFlagDir d r v z C0)) ≤ (CX : ℤ))
    (hVbudget : ∀ W : Finset (Place E (CoordinateField E C)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E C)
        (SecondJetRelaxedFlag.budgetFlag B U T (k+1) n0)) ≤ (CV : ℤ))
    (W : Finset (Place E (CoordinateField E C))) :
    ((3*(k+1) : ℕ) : ℤ) * (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      ((k+1 : ℕ) : ℤ)*(CX : ℤ)+((4*(w+1) : ℕ) : ℤ)*(CV : ℤ) := by
  letI := polynomialBaseAlgebra E C base.index
  letI := rationalBaseAlgebra E C base.index base.transcendental
  letI := polynomialBaseScalarTower E C base.index
  letI := polynomialRationalScalarTower E C base.index base.transcendental
  letI := rationalBaseScalarTower E C base.index base.transcendental
  letI : FiniteDimensional (RatFunc E) (CoordinateField E C) := base.finite
  letI : Algebra.IsSeparable (RatFunc E) (CoordinateField E C) := base.separable
  let L := CoordinateField E C
  let ev := SecondJetComponentRoots.coefficientMap phi C
  let H := ev (polyH K F)
  let sigma := ev (polyG K F)/H
  let theta := fun nu : Place E L =>
    max (2*flagPole nu.val (coordinate E C) unitAllFlag)
      (flagPole nu.val (coordinate E C) unitYZFlag + RCN187.poleOrder nu.val sigma)
  let Hf : FlagDegree := ⟨z,v,r-1⟩
  have hHne : H ≠ 0 := by
    intro hz
    apply hH
    exact (SecondJetComponentRoots.evaluation_zero_iff C _).mp hz
  let Pl := RCN026.placesFor E L H hHne
  set W' := W ∪ Pl with hW'
  -- the moving mass on `W'`, exactly as in `actual_first_source_pole_mass`
  have hdeg := SecondJetComponentRoots.degree_retained phi C P hlead
  have hroot := SecondJetComponentRoots.roots_retained phi C P F s k hS
    hF hH hlead hdiv h2 hfact
  have hdegree : n0 ≤ (SecondJetComponentRoots.componentPolynomial phi C P).natDegree := by
    rw [hdeg.2]
    exact hn
  have hs := SecondJetRelaxedFlag.moving_bound
    (MvPolynomial.map (phi.comp Polynomial.C) P) (phi Polynomial.X)
    B U T (k+1) n0 hBU hUT hdn hB
    (SecondJetSurfaceMap.mapped_support_bounds _ P B U T hP)
    (coordinate E C) (SecondJetComponentRoots.componentPolynomial phi C P)
    (SecondJetComponentRoots.coefficients phi C P) hdeg.1 hdegree
    (RCN064.movingRatio C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F))/2) hroot (CV : ℤ) hVbudget W'
  have hsource : ((k+1 : ℕ) : ℤ)*(∑ nu ∈ W', theta nu) ≤ (CV : ℤ) := by
    simpa only [SecondJetPoleScaling.pole_half _ h2, theta, sigma, H, ev,
      SecondJetComponentRoots.coefficientMap, RCN064.movingRatio,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hs
  have htarget : (∑ nu ∈ W', RCN064.movingPoleTarget C (surfaceMap phi (polyH K F))
      (surfaceMap phi (polyG K F)) nu) = ∑ nu ∈ W', theta nu := by
    apply Finset.sum_congr rfl
    intro nu _
    simp only [theta, RCN204.flagPole_unitAll, RCN204.flagPole_unitYZ]
    rfl
  -- zeros of `H` are bounded by its poles, hence by its flag
  have hHF := (BoundaryTailAlgebra.boundary_surfaceMap_flags phi F r v z (by omega) (by omega)
    hR hYR hAll).1
  have hpoleH (nu : Place E L) :
      RCN346.poleOrder E L nu H ≤ flagPole nu.val (coordinate E C) Hf := by
    apply pole_le_of_value_le nu.val _ _ (RCN204.flagPole_nonneg _ _ _)
    have h := RCN204.valuation_eval_le_flag nu.val (algebraMap E L)
      (RCN344.constant_value_le_one E L nu) (coordinate E C) Hf _ hHF
    simpa only [H, ev, SecondJetComponentRoots.coefficientMap,
      coordinateEvaluation_eq_aeval, MvPolynomial.aeval_eq_eval₂Hom,
      RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using h
  have hzero : (∑ nu ∈ W', RCN026.zeroOrder E L nu H) ≤
      ∑ nu ∈ W', flagPole nu.val (coordinate E C) Hf := by
    have hout : ∀ nu ∈ W'.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H = 0 := by
      intro nu hnu
      have hno : RCN026.order E L nu H = 0 := by
        by_contra hne
        exact (Finset.mem_filter.mp hnu).2 (RCN026.placesFor_covers E L H hHne nu hne)
      simp only [RCN026.zeroOrder, hno, max_self]
    calc
      _ = (∑ nu ∈ W'.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H) +
          ∑ nu ∈ W'.filter (fun nu => nu ∉ Pl), RCN026.zeroOrder E L nu H :=
        (Finset.sum_filter_add_sum_filter_not W' _ _).symm
      _ = ∑ nu ∈ W'.filter (fun nu => nu ∈ Pl), RCN026.zeroOrder E L nu H := by
        rw [Finset.sum_eq_zero hout, add_zero]
      _ ≤ ∑ nu ∈ Pl, RCN026.zeroOrder E L nu H :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun nu hnu => (Finset.mem_filter.mp hnu).2)
          (fun nu _ _ => RCN026.zeroOrder_nonneg E L nu H)
      _ = ∑ nu ∈ Pl, RCN346.poleOrder E L nu H := RCN026.sum_placesFor_zero_eq_pole E L H hHne
      _ ≤ ∑ nu ∈ Pl, flagPole nu.val (coordinate E C) Hf := Finset.sum_le_sum (fun nu _ => hpoleH nu)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_right
          (fun nu _ _ => RCN204.flagPole_nonneg nu.val (coordinate E C) Hf)
  -- `2•flag(H) = cusp + cap`, and the cap is dominated by `infCap d`
  have hcusp : 2 * (∑ nu ∈ W', flagPole nu.val (coordinate E C) Hf) ≤
      (∑ nu ∈ W', flagPole nu.val (coordinate E C) (cuspFlag d r v z)) +
        ∑ nu ∈ W', flagPole nu.val (coordinate E C) (HFree6812.infCap d) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun nu _ => ?_
    have e1 := congrArg (flagPole nu.val (coordinate E C)) (cusp_add_cap d r v z hr hv)
    rw [RCN204.flagPole_add, RCN204.flagPole_nsmul] at e1
    have e2 := capFlag_pole_le nu.val (coordinate E C) d r hr
    push_cast at e1
    linarith
  have hX := hXbudget W'
  simp only [hfreeFlagDir, RCN204.flagPole_add, RCN204.flagPole_nsmul, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hX
  have hb := hbudget.pole_le W'
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hb
  rw [htarget] at hb
  have hWW : (∑ nu ∈ W, RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      ∑ nu ∈ W', RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1)) :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
      (fun nu _ _ => le_max_left _ _)
  push_cast at hb hsource hX ⊢
  have hk : (0 : ℤ) ≤ (k : ℤ)+1 := by positivity
  have hw : (0 : ℤ) ≤ (w : ℤ)+1 := by positivity
  have e0 := mul_le_mul_of_nonneg_left (show
    2 * (∑ nu ∈ W', RCN026.zeroOrder E L nu H) ≤
      (∑ nu ∈ W', flagPole nu.val (coordinate E C) (cuspFlag d r v z)) +
        ∑ nu ∈ W', flagPole nu.val (coordinate E C) (HFree6812.infCap d) by linarith) hw
  have hb' : 3 * (∑ nu ∈ W', RCN187.poleOrder nu.val
      (SecondJetComponentRoots.coefficientMap phi C (baseNumerator F (w-1)) /
        SecondJetComponentRoots.coefficientMap phi C (polyH K F)^(2*w-1))) ≤
      4 * ((w : ℤ)+1) * (∑ nu ∈ W', theta nu) + (CX : ℤ) := by
    nlinarith
  have e1 := mul_le_mul_of_nonneg_left hb' hk
  have e2 := mul_le_mul_of_nonneg_left hsource (mul_nonneg (by norm_num : (0 : ℤ) ≤ 4) hw)
  have e3 := mul_le_mul_of_nonneg_left hWW (mul_nonneg (by norm_num : (0 : ℤ) ≤ 3) hk)
  nlinarith

end Slice

section Stage
local notation "w" => RCN326.w
variable {K I E T : Type} [Field K] [Field E] [IsAlgClosed E]
  [Algebra (GenericField K) E]
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDir6813.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDir6813.instDecidableEq_proximityPrize_1 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] [CharP E p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}
local notation "Ω" => GenericField K
local notation "PE" => MvPolynomial (Fin 3) E
local notation "φE" => RingHom.comp (algebraMap (GenericField K) E) (polynomialEmbedding K)

/-- `first_cut_on_prime_slice_hfree` per direction. -/
theorem first_cut_on_prime_slice_hfree_dir [Fintype T] [Nonempty T]
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (old : T → FirstTailComponent S)
    (emb : ∀ i, CoordinateField Ω (old i).1 →ₐ[Ω] E)
    (hinj : Function.Injective (fun i => embeddingPoint (old i).1 (emb i)))
    (D : Ideal PE) [D.IsPrime] (sep : SeparableLiteralCoordinate D)
    (hpoint : ∀ i, D ≤ RingHom.ker
      (MvPolynomial.aeval (embeddingPoint (old i).1 (emb i)) : PE →ₐ[E] E).toRingHom)
    (hcarrier : scalarPolynomialMap Ω E S.G ∈ D)
    (hisolated : scalarPolynomialMap Ω E
      (globalTailCut (polynomialEmbedding K) S.F (w+1)) ∉ D)
    (P : Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hlead : ∀ i, surfaceMap (polynomialEmbedding K) (asS P).leadingCoeff ∉ (old i).1)
    (hdiv : ∀ j ≤ k, S.F ∣ helper P S.F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (d : Fin 3) (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree)
    (hbudget : surfaceMap φE S.F ∈ D → surfaceMap φE (polyH K S.F) ∉ D →
      HFreeSliceBudgetCap φE S.F D C0 (HFree6812.infCap d))
    (CX CV : ℕ)
    (hXbudget : ∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E D) (hfreeFlagDir d r v z C0)) ≤ (CX : ℤ))
    (hVbudget : ∀ W : Finset (Place E (CoordinateField E D)),
      (∑ nu ∈ W, flagPole nu.val (coordinate E D)
        (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0)) ≤ (CV : ℤ)) :
    3*(k+1) * (∑ i, localMultiplicity S (canonicalLocalDVRFamily S hproper) (old i)) ≤
      (k+1)*CX+4*(w+1)*CV := by
  apply ActualWeightedFirstSlice6807.first_cut_on_prime_slice_of S hproper old emb hinj D sep
    hpoint hcarrier hisolated (2*w-1) (3*(k+1)) ((k+1)*CX+4*(w+1)*CV)
  intro hFd hHd hnot W
  have hs := hfree_source_pole_mass_dir φE S.F D sep P B U L s k n0 hS hP hBU hUL hdn hB hn
    hFd hHd (hnot _ hlead) hdiv h2 hfact d r v z hr hv hR hYR hAll C0
    (hbudget hFd hHd) CX CV hXbudget hVbudget W
  simpa only [Nat.cast_add, Nat.cast_mul] using hs

variable [Algebra (RatFunc (GenericField K)) E]
  [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]

/-- The H-free hypothesis for one slice direction `ell` of direction index `d`: every prime slice
component `D ∋ F, T-ell` with `H ∉ D` carries an `HFreeSliceBudgetCap` with cap `infCap d`. -/
def HFreeChannelDir (F : MvPolynomial (Fin 4) K) (ell : MvPolynomial (Fin 3) Ω)
    (C0 : FlagDegree) (d : Fin 3) : Prop :=
  ∀ (D : Ideal PE) [D.IsPrime], SeparableLiteralCoordinate D →
    surfaceMap φE F ∈ D → GenericSlicePoints6807.sliceEquation (E := E) ell ∈ D →
    surfaceMap φE (polyH K F) ∉ D → HFreeSliceBudgetCap φE F D C0 (HFree6812.infCap d)

/-- The per-direction H-free slice charge `3(k+1) | (k+1)•hfreeFlagDir + 4(w+1)•V`. -/
theorem hfree_slice_charge_dir
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (ell : MvPolynomial (Fin 3) Ω)
    (P : Poly (K := K)) (B U L s k n0 : ℕ)
    (hS : ∀ e ∈ P.support, e 1 ≤ s)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧
      e 1+e 2+e 3+e 4 ≤ L)
    (hBU : B ≤ U) (hUL : U ≤ L) (hdn : k+1 ≤ n0)
    (hB : 2*(n0-(k+1)) ≤ B) (hn : n0 ≤ (asS P).natDegree)
    (hdiv : ∀ j ≤ k, S.F ∣ helper P S.F (s-j) j)
    (h2 : (2 : E) ≠ 0) (hfact : (k.factorial : E) ≠ 0)
    (d : Fin 3) (r v z : ℕ) (hr : 3 ≤ r) (hv : 2 ≤ v)
    (hR : WeightBound residualSWeights S.F (r : ℤ))
    (hYR : WeightBound residualYSWeights S.F ((r+v : ℕ) : ℤ))
    (hAll : WeightBound residualTotalWeights S.F ((r+v+z : ℕ) : ℤ))
    (C0 : FlagDegree) (hH : HFreeChannelDir (E := E) S.F ell C0 d) :
    ActiveSliceAssembly6807.SliceCharge (E := E) S hproper
      (fun C => surfaceMap (polynomialEmbedding K) (asS P).leadingCoeff ∉ C.1)
      (GenericSlicePoints6807.sliceEquation (E := E) ell) (3*(k+1)) (k+1) (4*(w+1))
      (hfreeFlagDir d r v z C0) (SecondJetRelaxedFlag.budgetFlag B U L (k+1) n0) :=
  fun _ _ _ old hlead emb hinj D _ sep hpt hcar hN hA CX CV hX hV =>
    first_cut_on_prime_slice_hfree_dir S hproper old emb hinj D sep hpt hcar hA
      P B U L s k n0 hS hP hBU hUL hdn hB hn hlead hdiv h2 hfact d r v z hr hv hR hYR hAll C0
      (fun hFd hHd => hH D sep hFd hN hHd) CX CV hX hV

end Stage

section Retained
open MovingFiberRetainedStage6811 CommonLinearChannels6807 LocatorHybridCells
open RCN046 RCN084 RCN085 RCN159 RCN198 RCN199 RCN206 RCN207 RCN237 RCN238 RCN243
open RCN263 RCN264 RCN271 RCN275 RCN287 RCN327 RCN330 RCN331 RCN332 RCN334 RCN336 RCN338 RCN339
open RCN340 RCN344
open LocatorHybridCellsC1 LocatorHybridTransportC2 LocatorHybridTailProvider
open BoundaryTailProvider MovingFiberThreeSources6811
variable {K I : Type} [Field K]
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDir6813.instDecidableEq_proximityPrize_2 : DecidableEq K := Classical.decEq K
local instance  _root_.ProximityPrize.SubmissionLower.HFreeDir6813.instDecidableEq_proximityPrize_3 : DecidableEq I := Classical.decEq I
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP K p] [CharP (GenericField K) p] {errorCap : ℕ}
local notation "Ω" => GenericField K

/-- The H-free hypothesis for a retained stage, per direction: `HFreeChannelDir` (with
`C0 = unitAll`) in each slice direction `j`, with cap `infCap j`. -/
def HFreeStageDir {t y r : ℕ}
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r)) :
    Prop :=
  ∀ hproper hflagChar hmixedRed (j : Fin 3),
    HFreeChannelDir (E := AlgebraicClosure (RatFunc Ω)) S.F
      (channel S hproper hflagChar hmixedRed j) unitAllFlag j

/-- H-free first-cut flag of the cell in direction `j`: `(w+1)•cuspFlag + 3•unitAll`. -/
def hfreeFirstDir (t y r : ℕ) (j : Fin 3) : FlagDegree :=
  hfreeFlagDir j r (y-r) (t-y) unitAllFlag

/-- The retained-stage numerator with the per-direction first cut:
direction `j` is charged `(scale/3)·normal_j·mix(f,first_j,e_j) + 4(w+1)(scale/3d_j)·normal_j·
mix(f,e_j,V_j)`, plus the unchanged moving term. -/
def numeratorDir {F : MvPolynomial (Fin 4) K} (source : Fin 3 → Source F)
    (scale t y r : ℕ) (flag : FlagDegree) : ℕ :=
  ∑ j : Fin 3, (scale/3*weight (cellNormal t y r) j*
      flagMixed flag (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j) +
    (4*(w+1)*weight (cellNormal t y r) j*(scale/(3*(source j).d))+
      65539*weight (rawFirstFlag t y r) j*(scale/(source j).d))*
      flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag)

theorem sum_numeratorDir_le {J : Type*} [Fintype J] {F : MvPolynomial (Fin 4) K}
    (source : Fin 3 → Source F) (scale t y r : ℕ) (flags : J → FlagDegree) (total : FlagDegree)
    (hs : (∑ i, (flags i).all) ≤ total.all)
    (hm : (∑ i, ((flags i).yz+(flags i).all)) ≤ total.yz+total.all)
    (ht : (∑ i, ((flags i).zOnly+(flags i).yz+(flags i).all)) ≤
      total.zOnly+total.yz+total.all) :
    (∑ i, numeratorDir source scale t y r (flags i)) ≤ numeratorDir source scale t y r total := by
  have hfirst (j : Fin 3) := RCN084.sum_flagMixed_le_of_cumulative flags total
    (hfreeFirstDir t y r j) (MovingFiberThreeSources6811.direction j) hs hm ht
  have hsource (j : Fin 3) := RCN084.sum_flagMixed_le_of_cumulative flags total
    (MovingFiberThreeSources6811.direction j) (source j).flag hs hm ht
  unfold numeratorDir
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ (hfirst j)) (Nat.mul_le_mul_left _ (hsource j))

/-- `flagMixed` is monotone in its second argument. -/
theorem flagMixed_mono_mid (f q q' g : FlagDegree) (hz : q.zOnly ≤ q'.zOnly) (hy : q.yz ≤ q'.yz)
    (ha : q.all ≤ q'.all) : flagMixed f q g ≤ flagMixed f q' g := by
  unfold flagMixed
  gcongr







theorem retained_stage_bound_dir
    (t y r scale : ℕ) (hr3 : 3 ≤ r) (hb : r+2 ≤ y) (hyt : y ≤ t)
    (S : ResidualStage (polynomialEmbedding K) Gamma x p errorCap flag w (cellSupport t y r))
    (source : Fin 3 → Source S.F) (hscale : 0 < scale) (hscaleDiv : ∀ j, 3*(source j).d ∣ scale)
    (hfree : HFreeStageDir S)
    (hproper : ¬ S.G ∣ globalTailCut (polynomialEmbedding K) S.F (w+1))
    (hflagChar : flag.yz+flag.all < p ∧ flag.all < p ∧ flag.zOnly+flag.yz+flag.all < p)
    (hmixedRed : flagMixed flag (cellFirstTail t y r) unitZFlag < p)
    (hlinear : 2*(flag.zOnly+flag.yz+flag.all) < p)
    (hmovingGate : 2*(flag.zOnly+flag.yz+flag.all)*(t+1) < p)
    (hchar : 2*(w-1) < p)
    (hgate : errorCap+1 ≤ (cellNormal t y r).yz)
    (htangent : ∀ C : FirstTailComponent S,
      (∀ delay, globalTailCut (polynomialEmbedding K) S.F (w+1+delay) ∈ C.1) →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card ≤
        (errorCap+1)*(BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed).yzCost C)
    (h2 : (2 : Ω) ≠ 0) (hfact : ∀ j, ((source j).k.factorial : Ω) ≠ 0)
    (hgood : ∀ gamma ∈ Gamma, ∀ j,
      MvPolynomial.eval (selectedPoint (polynomialEmbedding K) S.selected gamma)
        ((source j).leading (polynomialEmbedding K)) ≠ 0) :
    Gamma.card ≤ numeratorDir source scale t y r flag / scale := by
  classical
  let Ext := AlgebraicClosure (RatFunc Ω)
  letI : CharP Ext p := charP_of_injective_algebraMap (algebraMap Ω Ext).injective p
  have h2E : (2 : Ext) ≠ 0 := by
    simpa only [map_ofNat,map_zero] using (algebraMap Ω Ext).injective.ne h2
  have hfactE (j : Fin 3) : ((source j).k.factorial : Ext) ≠ 0 := by
    simpa only [map_natCast,map_zero] using (algebraMap Ω Ext).injective.ne (hfact j)
  let base := BoundaryTailReduced.reducedBaseOrd S hproper hflagChar hmixedRed
  let Uold := BoundaryTailReduced.reducedUnitFamily S hproper hflagChar hmixedRed
  let unit := unitFamilyOfCongruentCut (ordinary_sub_reducedFirstCut_dvd S) Uold base
  let Bfam := BoundaryTailReduced.reducedBudgetFamily S hproper hflagChar hmixedRed
  let common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed
  let active : Finset (FirstTailComponent S) := Finset.univ.filter
    (fun C => ∀ j : Fin 3, (source j).leading (polynomialEmbedding K) ∉ C.1)
  have hlead (C : active) (j : Fin 3) : (source j).leading (polynomialEmbedding K) ∉ C.val.1 :=
    (Finset.mem_filter.mp C.property).2 j
  have Hsupport : ResidualSupportData (cellSupport t y r) S.F :=
    ⟨S.surface_s_weight,S.surface_ys_weight,S.surface_total_weight⟩
  have hs : cellS r+2 = r := by dsimp [cellS]; omega
  have hys : cellB y r+cellS r+3 = r+(y-r) := by dsimp [cellB,cellS]; omega
  have htot : cellA t y+cellB y r+cellS r+3 = r+(y-r)+(t-y) := by
    dsimp [cellA,cellB,cellS]; omega
  have hR : WeightBound residualSWeights S.F (r : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualSWeights S.F ≤ r by
      simpa only [cellSupport,RCN198.support,hs] using Hsupport.s_weight)
  have hYR : WeightBound residualYSWeights S.F ((r+(y-r) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualYSWeights S.F ≤ r+(y-r) by
      simpa only [cellSupport,RCN198.support,hys] using Hsupport.ys_weight)
  have hAll : WeightBound residualTotalWeights S.F ((r+(y-r)+(t-y) : ℕ) : ℤ) := by
    apply Or.inr
    exact_mod_cast (show wt residualTotalWeights S.F ≤ r+(y-r)+(t-y) by
      simpa only [cellSupport,RCN198.support,htot] using Hsupport.total_weight)
  have hgates : 2*(flag.zOnly+flag.yz+flag.all)*(cellA t y+(cellB y r+1)+(cellS r+3)) < p := by
    have he : cellA t y+(cellB y r+1)+(cellS r+3) = t+1 := by dsimp [cellA,cellB,cellS]; omega
    simpa only [he] using hmovingGate
  have hdiv1 (j : Fin 3) : (source j).d ∣ scale := (Dvd.intro_left 3 rfl).trans (hscaleDiv j)
  obtain ⟨budget,hcost,hmoving⟩ := MovingFiberDegreeSum6811.exists_first_tail_budget (E := Ext)
    (polynomialEmbedding K) S.F source scale hscale hdiv1 S.G flag (cellFirstTail t y r)
    S.irreducible_G.ne_zero S.G_dvd_surface S.flag_support
    (cellA t y) (cellB y r) (cellS r) w (by norm_num [w])
    Hsupport.coordinate_bounds.2.1 Hsupport.ys_weight Hsupport.total_weight p hlinear hgates h2E
    hfactE base unit active (fun C hC j => (Finset.mem_filter.mp hC).2 j)
  have hcost' (C : FirstTailComponent S) :
      (budget C).zCost = Bfam.zCost C ∧ (budget C).yzCost = Bfam.yzCost C ∧
        (budget C).allCost = Bfam.allCost C := by
    obtain ⟨hz,hy,ha⟩ := hcost C
    obtain ⟨ez,ey,ea⟩ :=
      unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    exact ⟨hz.trans ez,hy.trans ey,ha.trans ea⟩
  have heq (f : FlagDegree) (C : FirstTailComponent S) :
      unit.toPrimeFlagBudgetFamily.weightedCost f C = Bfam.weightedCost f C := by
    obtain ⟨ez,ey,ea⟩ :=
      unitFamilyOfCongruentCut_costs (ordinary_sub_reducedFirstCut_dvd S) Uold base C
    change unit.toPrimeFlagBudgetFamily.zCost C = Bfam.zCost C at ez
    change unit.toPrimeFlagBudgetFamily.yzCost C = Bfam.yzCost C at ey
    change unit.toPrimeFlagBudgetFamily.allCost C = Bfam.allCost C at ea
    unfold PrimeFlagBudgetFamily.weightedCost
    rw [ez,ey,ea]
  let mu := fun C : FirstTailComponent S => localMultiplicity (loosenStageGeneral S)
    (canonicalLocalDVRFamily (loosenStageGeneral S) hproper) C
  let first := hfreeFirstDir t y r
  let normal := cellNormal t y r
  let projection : (j : Fin 3) → (C : FirstTailComponent S) →
      Coordinate Ω (CoordinateField Ω C.1) :=
    ![unit.zProjection,unit.yzProjection,unit.allProjection]
  let ell := channel S hproper hflagChar hmixedRed
  have hell (j : Fin 3) : PolynomialInFlag (MovingFiberThreeSources6811.direction j) (ell j) := by
    fin_cases j
    · exact linearZ_in_flag
    · exact linearU_in_flag _
    · exact linearA_in_flag _ _
  have hvalue (j : Fin 3) (C : FirstTailComponent S) :
      coordinateValue Ω (CoordinateField Ω C.1) (projection j C) =
        coordinateEvaluation Ω C.1 (ell j) := by
    fin_cases j
    · exact common_z_value unit C
    · exact common_u_value unit common C
    · exact common_a_value unit common C
  have hnormal (j : Fin 3) :
      scale*(∑ C : active, mu C.val*
        coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) ≤
      scale/3*flagMixed flag (first j) (MovingFiberThreeSources6811.direction j) +
        4*(w+1)*(scale/(3*(source j).d))*
          flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
    have hq : (MovingFiberThreeSources6811.direction j).zOnly+
        (MovingFiberThreeSources6811.direction j).yz+
        (MovingFiberThreeSources6811.direction j).all = 1 := by fin_cases j <;> rfl
    have h := ActualGenericChannel6807.first_cut_for_coordinate_channel (E := Ext)
      (loosenStageGeneral S) hproper (fun C : active => C.val) Subtype.val_injective
      (ell j) (MovingFiberThreeSources6811.direction j) (hell j)
      (fun C => projection j C.val) (fun C => hvalue j C.val)
      hflagChar.2.2 (by rw [hq,mul_one]; exact hlinear) _ (fun C => hlead C j)
      _ _ _ _ _ (hfree_slice_charge_dir (E := Ext) (loosenStageGeneral S) hproper
        (ell j) (source j).P (source j).B (source j).U (source j).T (source j).s (source j).k
        (source j).n0 (source j).hS (source j).hshape (source j).hBU (source j).hUT
        (source j).hdn (source j).hB (source j).hn (source j).hdiv h2E (hfactE j)
        j r (y-r) (t-y) hr3 (by omega) hR hYR hAll
        unitAllFlag (hfree hproper hflagChar hmixedRed j))
    have hexp : flagMixed flag (MovingFiberThreeSources6811.direction j)
        ((source j).d • first j+(4*(w+1)) • (source j).flag) =
        (source j).d*flagMixed flag (first j) (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag := by
      simp only [flagMixed,add_zOnly,add_yz,add_all,nsmul_zOnly,nsmul_yz,nsmul_all]
      ring
    change 3*(source j).d*(∑ C : active, mu C.val*
        coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) ≤
      flagMixed flag (MovingFiberThreeSources6811.direction j)
        ((source j).d • first j+(4*(w+1)) • (source j).flag) at h
    rw [hexp] at h
    obtain ⟨m,hm⟩ := hscaleDiv j
    have hd0 : 0 < 3*(source j).d := by simp only [Source.d]; omega
    have h3 : scale/3 = (source j).d*m := by
      rw [hm,Nat.mul_assoc,Nat.mul_div_cancel_left _ (by norm_num)]
    have h3d : scale/(3*(source j).d) = m := by rw [hm,Nat.mul_div_cancel_left _ hd0]
    rw [h3,h3d,hm]
    calc
      _ = m*(3*(source j).d*(∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val))) := by ring
      _ ≤ m*((source j).d*flagMixed flag (first j) (MovingFiberThreeSources6811.direction j) +
          4*(w+1)*flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) :=
        Nat.mul_le_mul_left m h
      _ = _ := by ring
  have hnormalSum : scale*(∑ C ∈ active, mu C*Bfam.weightedCost normal C) ≤
      ∑ j : Fin 3, (scale/3*weight normal j*
          flagMixed flag (first j) (MovingFiberThreeSources6811.direction j) +
        4*(w+1)*weight normal j*(scale/(3*(source j).d))*
          flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag) := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin 3))) =>
      Nat.mul_le_mul_left (weight normal j) (hnormal j))
    have hsum : (∑ C ∈ active, mu C*Bfam.weightedCost normal C) =
        ∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val := by
      calc
        _ = ∑ C ∈ active, mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C := by
          apply Finset.sum_congr rfl
          intro C _
          rw [heq]
        _ = _ := (Finset.sum_coe_sort active
          (fun C => mu C*unit.toPrimeFlagBudgetFamily.weightedCost normal C)).symm
    rw [hsum]
    have hl : scale*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        ∑ j : Fin 3, weight normal j*(scale*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (projection j C.val)) := by
      rw [Fin.sum_univ_three]
      change scale*(∑ C : active, mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val) =
        normal.zOnly*(scale*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
        normal.yz*(scale*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
        normal.all*(scale*∑ C : active, mu C.val*
          coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val))
      have hp (C : active) : mu C.val*unit.toPrimeFlagBudgetFamily.weightedCost normal C.val =
          normal.zOnly*(mu C.val*
            coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.zProjection C.val)) +
          normal.yz*(mu C.val*
            coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.yzProjection C.val)) +
          normal.all*(mu C.val*
            coordinateDegree Ω (CoordinateField Ω C.val.1) (unit.allProjection C.val)) := by
        simp only [PrimeFlagBudgetFamily.weightedCost,
          AdaptiveUnitProjectionFamily.toPrimeFlagBudgetFamily,
          AdaptiveUnitPoleBudget.toPrimeFlagBudgetFamily,
          AdaptiveUnitProjectionFamily.toAdaptiveUnitPoleBudget]
        ring
      simp_rw [hp]
      simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    rw [hl]
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    ring
  let moveNum := ∑ j : Fin 3, weight (rawFirstFlag t y r) j*(scale/(source j).d)*
    flagMixed flag (MovingFiberThreeSources6811.direction j) (source j).flag
  have hmovingScaled : scale*(∑ C ∈ active, (budget C).movingCost) ≤ moveNum := by
    exact (Nat.mul_le_mul_left scale hmoving).trans (by
      simpa only [moveNum,rawFirstFlag,Nat.mul_comm] using Nat.div_mul_le_self moveNum scale)
  have hjointScaled : scale*(∑ C ∈ active,
      (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost)) ≤
      numeratorDir source scale t y r flag := by
    have h := Nat.add_le_add hnormalSum (Nat.mul_le_mul_left 65539 hmovingScaled)
    convert h using 1
    · simp only [Finset.sum_add_distrib,← Finset.mul_sum]
      ring
    · simp only [numeratorDir,moveNum,first,normal,Nat.add_mul,Finset.sum_add_distrib,
        Finset.mul_sum,Nat.mul_assoc]
      ring
  have hjoint : (∑ C ∈ active, (mu C*Bfam.weightedCost normal C+65539*(budget C).movingCost)) ≤
      numeratorDir source scale t y r flag/scale := by
    apply (Nat.le_div_iff_mul_le hscale).mpr
    simpa only [Nat.mul_comm] using hjointScaled
  have hinactive : ∀ C : FirstTailComponent S, C ∉ active →
      (componentSeeds Ω S.G (globalTailCut (polynomialEmbedding K) S.F (w+1))
        (regularitySurface (polynomialEmbedding K) S.F) Gamma
        (selectedPoint (polynomialEmbedding K) S.selected) C).card = 0 := by
    intro C hC
    have hex : ∃ j : Fin 3, (source j).leading (polynomialEmbedding K) ∈ C.1 := by
      simpa only [active,Finset.mem_filter,Finset.mem_univ,true_and,not_forall,not_not] using hC
    obtain ⟨j,hj⟩ := hex
    exact SecondJetExceptionalComponents.component_empty_of_nonvanishing _ _ _
      ((source j).leading (polynomialEmbedding K)) Gamma _ C hj
      (fun gamma hgamma => hgood gamma hgamma j)
  obtain ⟨provider⟩ := BoundaryTailJointBudget6807.exists_provider_of_joint_curve_budget
    t y r hr3 hb hyt hchar S hproper (cellFirstTail t y r) Bfam base budget hcost'
    active (numeratorDir source scale t y r flag/scale) hinactive hjoint hgate htangent
  exact stage_card_le_divisorBound S provider

end Retained

section Discharge
open HFree6812 MovingFiberRetainedStage6811 CommonLinearChannels6807 LocatorHybridCells
open WithZero MvPolynomial
variable {K I : Type} [Field K] [CharP K 2130706433]
  {Gamma : Finset K} {x : I → K} {flag : FlagDegree} {errorCap : ℕ}
  [CharP (GenericField K) 2130706433]

omit [CharP (GenericField K) 2130706433] in
public theorem natCast_ne_zero_K {n : ℕ} (h0 : 0 < n) (hn : n < 2130706433) : (n : K) ≠ 0 := by
  intro h
  exact absurd (Nat.le_of_dvd h0 ((CharP.cast_eq_zero_iff K 2130706433 n).1 h)) (by omega)

omit [CharP (GenericField K) 2130706433] in
/-- One slice direction: `hfree_slice_budget_dir` fed by the two gaps. -/
public theorem channel_budget_dir {E : Type} [Field E] [IsAlgClosed E]
    [Algebra (GenericField K) E] [Algebra (RatFunc (GenericField K)) E]
    [IsScalarTower (GenericField K) (RatFunc (GenericField K)) E]
    (F : MvPolynomial (Fin 4) K) (N : ℕ)
    (hN : MvPolynomial.weightedTotalDegree ![0,1,1,1] F ≤ N)
    (hN9 : N ≤ 9678) (D : Ideal (MvPolynomial (Fin 3) E)) [D.IsPrime]
    (sep : SeparableLiteralCoordinate D) (hFD : surfaceMap (phiE K E) F ∈ D)
    (hHD : surfaceMap (phiE K E) (polyH K F) ∉ D) (d : Fin 3)
    (c : Fin 3 → GenericField K) (i : Fin 3) (hci : c i = 1) (q : Fin 3 → Polynomial K)
    (hqd : DirShape d q) (hq : ∀ m, polynomialEmbedding K (q m) = c m) (hq1 : i = 1 ∨ q 1 = 0)
    (hslice : MvPolynomial.C (sliceValue (GenericField K) E) -
      scalarPolynomialMap (GenericField K) E
        (∑ m, MvPolynomial.C (c m) * MvPolynomial.X m) ∈ D) :
    HFreeSliceBudgetCap (phiE K E) F D unitAllFlag (infCap d) := by
  have hNK : ∀ n : ℕ, 0 < n → n ≤ N → (n : K) ≠ 0 :=
    fun n h0 hn => natCast_ne_zero_K h0 (by omega)
  exact ⟨hfree_slice_budget_dir d F D sep hFD hHD c i hci q hqd hq hslice
    (by exact_mod_cast natCast_ne_zero_K (K := K) (n := 2) (by norm_num) (by norm_num))
    (hchar_gap F D sep hFD hHD c i hci hslice N hN hN9)
    (hdefer_gap F D hHD c i hci q hq hq1 hslice N hN hNK)⟩

/-- The per-direction H-free stage hypothesis, from `hfree_slice_budget_dir`, `hchar_gap` and
`hdefer_gap` (the same inputs as `hfree_stage_of_gaps`). -/
theorem hfree_stage_dir_of_gaps {t y r : ℕ}
    (S : RCN159.ResidualStage (polynomialEmbedding K) Gamma x 2130706433 errorCap flag RCN326.w
      (cellSupport t y r)) (htot : (cellSupport t y r).total ≤ 9678) : HFreeStageDir S := by
  intro hproper hflagChar hmixedRed j D _ sep hFD hsl hHD
  set common := ReducedCommonLinear6807.original_common S hproper hflagChar hmixedRed with hcommon
  obtain ⟨ql, hql⟩ :=
    ReducedCommonLinear6807.original_common_lam_poly S hproper hflagChar hmixedRed
  obtain ⟨qm, hqm⟩ :=
    ReducedCommonLinear6807.original_common_mu_poly S hproper hflagChar hmixedRed
  have go := channel_budget_dir S.F _ S.surface_total_weight htot D sep hFD hHD j
  fin_cases j
  · refine go ![0,0,1] 2 rfl ![0,0,1] (by simp [DirShape])
      (fun m => by fin_cases m <;> simp) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![0,0,1] : Fin 3 → GenericField K) m) * MvPolynomial.X m :
        MvPolynomial (Fin 3) (GenericField K)) = linearZ := by
      simp [linearZ, Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![1,0,common.lam] 0 rfl ![1,0,ql] (by simp [DirShape])
      (fun m => by fin_cases m <;> simp [hql, hcommon]) (Or.inr rfl) ?_
    have he : (∑ m, MvPolynomial.C ((![1,0,common.lam] : Fin 3 → GenericField K) m) *
        MvPolynomial.X m : MvPolynomial (Fin 3) (GenericField K)) = linearU common.lam := by
      simp [linearU, Fin.sum_univ_three]
    rw [he]; exact hsl
  · refine go ![common.mu,1,common.mu*common.lam] 1 rfl ![qm,1,qm*ql] trivial
      (fun m => by fin_cases m <;> simp [hql, hqm, hcommon]) (Or.inl rfl) ?_
    have he : (∑ m, MvPolynomial.C
        ((![common.mu,1,common.mu*common.lam] : Fin 3 → GenericField K) m) *
        MvPolynomial.X m : MvPolynomial (Fin 3) (GenericField K)) =
          linearA common.mu common.lam := by
      simp [linearA, Fin.sum_univ_three]; ring
    rw [he]; exact hsl

end Discharge

end
end ProximityPrize.SubmissionLower.HFreeDir6813


