-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_DetLineSmooth
-- name    : GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_DetLineSmooth
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:17:37.59873+00:00
-- url     : https://prove2.me/theorems/359106fe-e171-408a-9b56-c376622a702a
-- title:
--   Det Line Smooth
-- statement:
--   Definitions and structural lemmas for Det Line Smooth, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HodgeLowerBound/DetLineSmooth.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FlagComplexPointsOverX
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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine
open MvPolynomial Filter Topology Matrix ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
section Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def GenSmooth (P : Ideal (MRing ι)) : Prop :=
  ∀ hP : P.IsPrime, haveI := hP
    ∀ c : ∀ k, ι k, (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) →
      Algebra.Smooth ℚ (TensorProduct ℤ ℚ (chartRingZ (genPt P) c))
def IsSncProv (P : Ideal (MRing ι)) (Bd : Finset (Ideal (MRing ι))) (d : ℕ) : Prop :=
  ∀ T ⊆ Bd, T.Nonempty →
    (∀ Q ∈ (P ⊔ ⨆ B ∈ T, B).minimalPrimes, IsHorizontal Q → IsArithVar Q (d + 1 - T.card) ∧ GenSmooth Q) ∧
      IsReduced (TensorProduct ℤ ℚ (MRing ι ⧸ (P ⊔ ⨆ B ∈ T, B)))
end Geo
variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]
namespace ComponentData
structure Clauses (D : ComponentData Ψ K ι) : Prop where
  genSmooth : GenSmooth D.P
  snc : IsSncProv D.P D.Bd D.n
  bd_eq : ∀ B ∈ D.Bd, ∀ W ∈ divSupp D.P (D.bdEq B), IsHorizontal W →
    W ∈ D.Bd ∧ multAt (D.P ⊔ Ideal.span {D.bdEq B}) W = 1
  metric_herm : ∀ τ z, (D.metric τ z)ᴴ = D.metric τ z
  metric_homog : ∀ τ (c : K → ℂ) z, (∀ k, c k ≠ 0) →
    D.metric τ (fun p => c p.1 * z p) = ((∏ k, ‖c k‖ ^ (-2 * D.twist τ k) : ℝ) : ℂ) • D.metric τ z
  metric_pos : ∀ τ, ∀ z ∈ D.Xo, ∀ v : Fin D.N1 → ℂ, v ≠ 0 → (∀ a, ∑ l, evalC (D.what₂ τ a l) z * v l = 0) →
    0 < (star v ⬝ᵥ (D.metric τ z *ᵥ v)).re
  metric_smooth : ∀ τ, ∃ U : Set (Cone ι), IsOpen U ∧ D.Xo ⊆ U ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z (a b : Fin D.N1) => D.metric τ z a b) U
  metric_conj : ∀ τ z, D.metric τ (fun p => starRingEnd ℂ (z p)) = (D.metric τ z).map (starRingEnd ℂ)
  logBounds : ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ τ, ∀ z ∈ D.Xo, IsBlockUnit z →
    (∀ v : Fin D.N1 → ℂ, (∀ a, ∑ l, evalC (D.what₂ τ a l) z * v l = 0) →
      c / D.sncWeight z * ‖v‖ ^ 2 ≤ (star v ⬝ᵥ (D.metric τ z *ᵥ v)).re ∧
      (star v ⬝ᵥ (D.metric τ z *ᵥ v)).re ≤ C * ‖v‖ ^ 2) ∧
    ‖fderiv ℝ (fun z (a b : Fin D.N1) => D.metric τ z a b) z‖ ≤ C * Real.exp (D.sncWeight z / 2)
  hodge_mu : ∀ z ∈ D.Xo, ∀ (i : ι D.kMu) (r : ℂ) (g : Ψ → Matrix (Fin (D.N - D.j)) (Fin D.N1) ℂ),
    IsValAt D.P (D.muCoord i) z r → (∀ τ a l, IsValAt D.P (D.hodge τ a l) z (g τ a l)) →
    D.muLine.h z * (‖r‖ * ∏ τ, (((g τ).map (starRingEnd ℂ) * D.metric τ z * (g τ)ᵀ).det.re) ^ ((D.k0 : ℝ) / 2)) =
      ‖z ⟨D.kMu, i⟩‖
  hodge_det : ∀ τ, ∀ z ∈ D.Xo, ∀ (r : ℂ) (g : Matrix (Fin D.N) (Fin D.N1) ℂ),
    IsValAt D.P (D.detCoord τ) z r → (∀ a l, IsValAt D.P (D.basis τ a l) z (g a l)) →
    (D.detLine τ).h z * Real.sqrt ((g.map (starRingEnd ℂ) * D.metric τ z * gᵀ).det.re) = ‖r‖
  detLine_smooth : ∀ τ, IsSmoothHerm (D.detLine τ)
  muRef_smooth : IsSmoothHerm D.muRef ∧ IsConjInvariantH D.muRef
  ample_smooth : IsSmoothHerm D.ample ∧ IsConjInvariantH D.ample
  ample_pos : ∀ z ∈ mcPts D.P, ∀ w, IsConeTangent (Int.castRingHom ℂ) D.P z w → ¬ IsTorusDir z w →
    0 < leviForm (fun z => Real.log (D.ample.h z)) z w
  ample_ample : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsAmpleGeneric D.P D.ample ∧
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.IsAmpleOnFibres D.P D.ample.a
  lat : ∀ p ∈ D.S, ∀ τ r, IsSmoothHerm (D.latFl p τ r) ∧ IsConjInvariantH (D.latFl p τ r) ∧
    (∃ dn dd : K → ℕ, IsMultiHomog (D.latNum p τ r) dn ∧ IsMultiHomog (D.latDen p τ r) dd ∧
      ∀ k, (dn k : ℤ) - dd k = (D.latFl p τ r).a k) ∧
    D.latNum p τ r ∉ D.P ∧ D.latDen p τ r ∉ D.P ∧
    (∀ z ∈ mcPts D.P, (D.latFl p τ r).h z * ‖evalC (D.latDen p τ r) z‖ = ‖evalC (D.latNum p τ r) z‖) ∧
    ∀ W ∈ divSupp D.P (D.latNum p τ r) ∪ divSupp D.P (D.latDen p τ r), (IsHorizontal W ∨ charOf W ≠ p) →
      multAt (D.P ⊔ Ideal.span {D.latNum p τ r}) W = multAt (D.P ⊔ Ideal.span {D.latDen p τ r}) W
  cusp : ∀ I, IsTorusInv (D.cuspNorm I) ∧ ∀ z, 0 < D.cuspNorm I z
  cusp_psh : ∀ I, ∀ z ∈ D.Xo, ∀ w, IsConeTangent (Int.castRingHom ℂ) D.P z w →
    0 ≤ leviForm (fun z => Real.log (D.muLine.h z) / D.k0 - Real.log (D.cuspNorm I z)) z w
  reg_mu : IsRegSystem D.P D.Xo (fun z => Real.log (D.muRef.h z) / D.k0) (fun z => Real.log (D.ample.h z))
    D.sncWeight D.hodgeW D.regMu
  reg_cusp : IsRegSystemBdd D.P D.Xo (fun z => Real.log (D.muRef.h z) / D.k0) (fun z => Real.log (D.ample.h z))
    (fun z => D.hodgeW z + D.U z) D.regCusp
  reg_fl : ∀ τ r, IsRegSystem D.flagBundleIdeal D.flagComplexPointsOverX (fun w => Real.log ((fsLine (D.lineDeg τ r)).h w))
    (fun w => Real.log ((D.liftX D.ample).h w) +
      Real.log ((fsLine (Sum.elim (fun _ => 0) (fun _ => 1) : K ⊕ (Ψ × Fin (D.N - 1)) → ℤ)).h w))
    (fun w => D.sncWeight (D.xPart w)) (D.hodgeLineW τ r) (fun t => D.regFl t τ r)
def KBound (D : ComponentData Ψ K ι) (II : IntersectionSystem) : Prop :=
  ∀ W, IsAlgPt D.P W → -D.Kamp ≤ (RLine.single 1 D.ample).ht II W
end ComponentData
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.Nine


