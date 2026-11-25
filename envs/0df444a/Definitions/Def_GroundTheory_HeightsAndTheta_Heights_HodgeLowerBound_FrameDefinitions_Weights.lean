-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Weights
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-25T08:22:48.410797+00:00
-- url     : https://prove2.me/theorems/b9c87082-de67-4223-822f-3818d49891b6
-- title:
--   Weights
-- statement:
--   Definitions and structural lemmas for Weights, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/FrameDefinitions/Weights.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_HasCoverByOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_EqZeroOfIsIsoSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open ReciprocityTheory.AnForm.A (Mollifier)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
open GroundTheory.Heights₂.Heights.Regular (RegChartData BoundedPshData)
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Models
structure CxModel (P : Ideal (MRing ι)) (d : ℕ) where
  Xc : Type
  [top : TopologicalSpace Xc]
  [compact : CompactSpace Xc]
  [t2 : T2Space Xc]
  atlas : FinHolAtlas d Xc

  proj : ((Σ k, ι k) → ℂ) → Xc
  surj : ∀ x, ∃ z ∈ mcPts P, proj z = x
  fibre : ∀ z ∈ mcPts P, ∀ z' ∈ mcPts P, proj z = proj z' ↔
    ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z
  cont : ContinuousOn proj (mcPts P)
  sections : ∀ x, ∃ U : Set Xc, IsOpen U ∧ x ∈ U ∧ ∃ s : Xc → (Σ k, ι k) → ℂ,
    (∀ y ∈ U, s y ∈ mcPts P ∧ proj (s y) = y) ∧ ∀ p, atlas.HoloOn U fun y => s y p
attribute [instance] CxModel.top CxModel.compact CxModel.t2
variable {P : Ideal (MRing ι)} {d : ℕ}
structure LogLogRegularisationSetting (M : CxModel P d) (Xo : Set ((Σ k, ι k) → ℂ)) (A : HermLine ι) where

  ref : HermLine ι
  ref_deg : ref.a = A.a
  ref_smooth : IsSmoothHerm ref

  R : RegChartData M.atlas
  th_ref : ∀ x, ∀ y ∈ R.th.U x, ∃ U : Set M.Xc, IsOpen U ∧ y ∈ U ∧ U ⊆ R.th.U x ∧
    ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧
      (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
        ∀ y' ∈ U, R.th.φ x y' - Real.log (ref.h (s y')) = (G y').re
  Yo_sub : ∀ x ∈ R.Yo, ∃ z ∈ Xo ∩ mcPts P, M.proj z = x
  ph_eq : ∀ z ∈ Xo ∩ mcPts P, M.proj z ∈ R.Yo → R.ph (M.proj z) = Real.log (A.h z) - Real.log (ref.h z)
  ρ : Mollifier d
  η : Fin R.N → M.Xc → ℝ
  Cη : ℝ
  cutoff : R.IsCutoffFamily η Cη

  K : ℝ → ℝ

  e1 : ℝ → ℝ
  e1_ge : ∀ t, 0 < t → t ≤ e1 t
def LogLogRegularisationSetting.regWeight {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι}
    (S : LogLogRegularisationSetting M Xo A) (t : ℝ) : M.Xc → ℝ :=
  S.R.regularised S.ρ (S.K t) t (S.e1 t) S.η
def LogLogRegularisationSetting.regLine {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {A : HermLine ι}
    (S : LogLogRegularisationSetting M Xo A) (t : ℝ) : HermLine ι :=
  hermOfFun ι A.a fun z => S.ref.h z * Real.exp (S.regWeight t (M.proj z))
structure BoundedRegularisationSetting (M : CxModel P d) (Xo : Set ((Σ k, ι k) → ℂ)) (a : K → ℤ)
    (w : ((Σ k, ι k) → ℂ) → ℝ) where
  ref : HermLine ι
  ref_deg : ref.a = a
  ref_smooth : IsSmoothHerm ref

  B : BoundedPshData M.atlas
  th_ref : ∀ x, ∀ y ∈ B.th.U x, ∃ U : Set M.Xc, IsOpen U ∧ y ∈ U ∧ U ⊆ B.th.U x ∧
    ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y' ∈ U, s y' ∈ mcPts P ∧ M.proj (s y') = y') ∧
      (∀ p, M.atlas.HoloOn U fun y' => s y' p) ∧ ∃ G : M.Xc → ℂ, M.atlas.HoloOn U G ∧
        ∀ y' ∈ U, B.th.φ x y' - Real.log (ref.h (s y')) = (G y').re
  ph_eq : ∀ z ∈ Xo ∩ mcPts P, B.ph (M.proj z) = w z - Real.log (ref.h z)
  ρ : Mollifier d
  η : Fin B.N → M.Xc → ℝ
  Cη : ℝ
  cutoff : B.IsCutoffFamily η Cη
  e1 : ℝ → ℝ
  e1_ge : ∀ t, 0 < t → t ≤ e1 t
def BoundedRegularisationSetting.bregWeight {M : CxModel P d} {Xo : Set ((Σ k, ι k) → ℂ)} {a : K → ℤ}
    {w : ((Σ k, ι k) → ℂ) → ℝ} (S : BoundedRegularisationSetting M Xo a w) (t : ℝ) : M.Xc → ℝ :=
  S.B.regularised S.ρ t (S.e1 t) S.η
open Classical in

def smoothRep (P : Ideal (MRing ι)) (A : HermLine ι) : HermLine ι :=
  if h : ∃ A' : HermLine ι, A'.a = A.a ∧ IsSmoothHerm A' ∧ ∀ z ∈ mcPts P, A'.h z = A.h z then h.choose
  else A
end Models
variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]
  {D : ComponentData II Ψ K ι Ω E}
namespace ComponentData
def SB (D : ComponentData II Ψ K ι Ω E) (B : ℕ) : Finset ℕ := D.S.filter (· ≤ B)
open Classical in

def vertFactor (D : ComponentData II Ψ K ι Ω E) (p : ℕ) (z : (Σ k, ι k) → ℂ) : ℝ :=
  if hc : ∃ c : (k : K) → ι k, ∀ k, z ⟨k, c k⟩ ≠ 0 then
    ‖valAt D.y (aeval D.y (D.vnum p) / aeval D.y (D.vden p) * chartMono D.y hc.choose (-D.vdeg p)) z‖ *
      ‖zMono z hc.choose (D.vdeg p)‖
  else 1
end ComponentData
section Numbers
variable (H : HodgeData D)
abbrev XModel (D : ComponentData II Ψ K ι Ω E) : Type 1 := CxModel (mCoordIdeal D.y) D.n
def degMu : ℝ := geomDeg (mCoordIdeal D.y) (muLine H) D.n
def meanU {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂) : ℝ :=
  ptsIntegral (e := D.n) (mCoordIdeal D.y) (fun _ => phMu H) Cd.cuspWeight / degMu H
def cuspCorrected {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
    (z : (Σ k, ι k) → ℂ) : ℝ :=
  phMu H z + Cd.cuspWeight z
def muTwDeg (B : ℕ) : K → ℤ := H.aMu + ∑ p ∈ D.SB B, D.vdeg p
def muReg {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) (t : ℝ) : HermLine ι :=
  smoothRep (mCoordIdeal D.y)
    (hermOfFun ι (muTwDeg H B) fun z => (S.regLine t).h z * ∏ p ∈ D.SB B, D.vertFactor p z)
def arLimFun {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) (t : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) fun _ => muReg H S B t
def arLim {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) : ℝ :=
  limUnder (𝓝[>] 0) (arLimFun H S B)
def ArLimExists {M : XModel D} (S : LogLogRegularisationSetting M D.Xo (muLine H)) (B : ℕ) : Prop :=
  ∃ L, Tendsto (arLimFun H S B) (𝓝[>] 0) (𝓝 L)
variable {O abelian₂ : Type} [CommRing O] [AddCommGroup abelian₂] [Module O abelian₂] (Cd : CuspData D O abelian₂)
def MU {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorrected H Cd)) (B p q : ℕ) (t' : ℝ) :
    HermLine ι :=
  smoothRep (mCoordIdeal D.y)
    (hermOfFun ι ((q : ℤ) • muTwDeg H B + (p : ℤ) • D.a') fun z =>
      (S.ref.h z * Real.exp (S.bregWeight t' (M.proj z))) ^ q *
        (∏ p' ∈ D.SB B, D.vertFactor p' z) ^ q * D.A'.h z ^ p)
def topMU {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorrected H Cd)) (B p q : ℕ) (t' : ℝ) : ℝ :=
  II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => MU H Cd S B p q t') / (q : ℝ) ^ (D.n + 1)
def geomDegMU {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorrected H Cd)) (B p q : ℕ) (t' : ℝ) : ℝ :=
  geomDeg (mCoordIdeal D.y) (MU H Cd S B p q t') D.n / (q : ℝ) ^ D.n
def htMU {M : XModel D} (S : BoundedRegularisationSetting M D.Xo H.aMu (cuspCorrected H Cd)) (B p q : ℕ) (t' : ℝ)
    (W : Ideal (MRing ι)) : ℝ :=
  II K ι W 1 ![MU H Cd S B p q t'] / ((q : ℝ) * degC W)
end Numbers
end GroundTheory.Heights₂.Heights.LowerBoundFree


