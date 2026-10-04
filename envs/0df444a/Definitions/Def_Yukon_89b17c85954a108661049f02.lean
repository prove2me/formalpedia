-- Prove2me | Definitions.Def_Yukon_89b17c85954a108661049f02
-- name    : Yukon_89b17c85954a108661049f02
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T00:41:13.025013+00:00
-- url     : https://prove2.me/theorems/5cdc5d67-b227-4112-8c82-4aa7eafe9ee6
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingSourceLinearCycleFamily6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-727529de55cd6a562fde3842ddee908bbfe25350fa42994d51d8d15214e510e5
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMmRmMDQzZTBjMzk0YjM4OGUwM2Q4MWVjNzNkZWNjNjExMDM4OTgwMjM2MTI1MzFlYTYzMmQ4NTVhOTZjNGNlMCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtNzI3NTI5ZGU1NWNkNmE1NjJmZGUzODQyZGRlZTkwOGJiZmUyNTM1MGZhNDI5OTRkNTFkOGQxNTIxNGU1MTBlNSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzg5YjE3Yzg1OTU0YTEwODY2MTA0OWYwMiIsInYiOjJ9]

import Definitions.Def_Yukon_42e09cdac02be46bc4db2213



















































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Construct the projections and all three weighted degree bounds on the
actual gamma-nonconstant subfamily. This closes the shared first-tail
cycle, not the final seed count or its exceptional/persistent branches. -/
namespace ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open scoped BigOperators
open RCN002 RCN022 RCN042 RCN093 RCN095 RCN116 RCN117 RCN125
open MovingSourceProjectionFamily6814 MovingSourcePrimeFamily6814
open MovingSourceGammaProjections6814

section General
variable {Ω : Type} [Field Ω] [IsAlgClosed Ω]
variable {A : Type} [Fintype A]
variable {P : A → Ideal (MvPolynomial (Fin 3) Ω)} [∀ a,(P a).IsPrime]
variable {surface : MvPolynomial (Fin 3) Ω}

theorem frame_trans (D : GammaFrame P surface)
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2)) (axis : Axis) (a : A) :
    Transcendental Ω (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam)
      (MvPolynomial.X (axis.order 0))) := by
  cases axis with
  | z => simpa [Axis.order,zOrder] using hz a
  | u => simpa [Axis.order,uOrder] using D.uTranscendental a
  | v => simpa [Axis.order,vOrder] using D.vTranscendental a

theorem frame_gate (D : GammaFrame P surface)
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2))
    (hgate : ∀ a,
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
      (letI := (elementEmbedding Ω (CoordinateField Ω (P a)) (coordinate Ω (P a) 2)
        (hz a)).toRingHom.toAlgebra;
        Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))))
    (axis : Axis) (a : A)
    (ht : Transcendental Ω (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam)
      (MvPolynomial.X (axis.order 0)))) :
    (letI := (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
      ht).toRingHom.toAlgebra;
      FiniteDimensional (RatFunc Ω) (CoordinateField Ω (P a))) ∧
    (letI := (elementEmbedding Ω (CoordinateField Ω (P a))
      (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
      ht).toRingHom.toAlgebra;
      Algebra.IsSeparable (RatFunc Ω) (CoordinateField Ω (P a))) := by
  cases axis with
  | z =>
    have he := elementEmbedding_congr ht (hz a) (by simp [Axis.order,zOrder])
    rw [he]
    exact hgate a
  | u =>
    have he := elementEmbedding_congr ht (D.uTranscendental a) (by simp [Axis.order,uOrder])
    rw [he]
    exact ⟨D.uFinite a,D.uSeparable a⟩
  | v =>
    have he := elementEmbedding_congr ht (D.vTranscendental a) (by simp [Axis.order,vOrder])
    rw [he]
    exact ⟨D.vFinite a,D.vSeparable a⟩

def frameCost (D : GammaFrame P surface)
    (hz : ∀ a, Transcendental Ω (coordinate Ω (P a) 2)) (axis : Axis) (a : A) : ℕ :=
  letI := (elementEmbedding Ω (CoordinateField Ω (P a))
    (flagEvaluation Ω (P a) D.lam D.mu (D.mu*D.lam) (MvPolynomial.X (axis.order 0)))
    (frame_trans D hz axis a)).toRingHom.toAlgebra
  Module.finrank (RatFunc Ω) (CoordinateField Ω (P a))
end General

open RCN135 RCN136 RCN074 RCN086 RCN244 RCN245 RCN249 RCN313
open MovingSourceFlowNumerator6814 MovingSourceReducedCycle6814 MovingSourceReducedGamma6814
variable {K I : Type} [Field K]
variable {Gamma : Finset K} {x : I → K} {p : ℕ} {flag : FlagDegree}
  [CharP (GenericField K) p] {errorCap : ℕ}
  {stageSupport : RCN275.ResidualSupportParameters}

/-- The selected frame has all three weighted shared budgets, supplied by
the actual stage and denominator-change identity. Only the parameter
mixed degree must be below characteristic. -/
theorem exists_reduced_cycle_family
    (S : Stage K I Gamma x p flag errorCap stageSupport)
    (hfirst : ¬S.G∣globalTailCut (polynomialEmbedding K) S.F (RCN326.w+1))
    (H G : MvPolynomial (Fin 4) K)
    (hcross : S.F∣H^(2*(RCN326.w+1))*numerator K S.F (RCN326.w+1)-
      (polyH K S.F)^(2*(RCN326.w+1))*numerators H G (RCN326.w+1))
    (hH : ¬S.G∣surfaceMap (polynomialEmbedding K) H)
    {A : Type} [Fintype A] (component : A → FirstTailComponent S)
    (hinj : Function.Injective component)
    (hz : ∀ a, Transcendental (GenericField K) (coordinate (GenericField K) (component a).1 2))
    (surfaceFlag tailFlag : FlagDegree)
    (hS : RCN095.PolynomialInFlag surfaceFlag S.G)
    (hT : RCN095.PolynomialInFlag tailFlag (reducedTailSurface H G))
    (hsmall : flagMixed surfaceFlag tailFlag unitZFlag<p) :
    ∃ D : GammaFrame (fun a => (component a).1) S.G, ∀ axis : Axis,
      (∑ a, localMultiplicity S (canonicalLocalDVRFamily S hfirst) (component a)*frameCost D hz axis a) ≤
        flagMixed surfaceFlag tailFlag axis.flag := by
  classical
  have hproper := reducedTail_proper S hfirst H G hcross hH
  have hgate (a : A) := reduced_gamma_gate S H G hcross hproper surfaceFlag tailFlag hS hT hsmall
    (component a) (hz a)
  have hderiv := RCN315.residualStage_pderiv_one_ne_zero_of_support S
  obtain ⟨D⟩ := exists_gamma_frame (fun a => (component a).1) hz hgate S.G hderiv
  refine ⟨D,fun axis => ?_⟩
  let F : StageIndexedFlagFamily S A := {
    component := component, injective := hinj
    lam := D.lam, mu := D.mu, nu := D.mu*D.lam, order := axis.order
    ht := frame_trans D hz axis
    finite := fun a => (frame_gate D hz hgate axis a (frame_trans D hz axis a)).1
    generates := fun a => flag_generators_axis (GenericField K) (component a).1
      axis D.lam D.mu (D.mu*D.lam) (frame_trans D hz axis a)
    positive := by
      cases axis with
      | z => exact (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hderiv).2
      | u => exact (flag_u_z_outer_positive_of_pderiv D.lam D.mu S.G hderiv).1
      | v => exact flag_v_outer_positive_of_directional D.lam D.mu S.G D.directional }
  have hb := reduced_projection_sum_le S hfirst H G hcross hproper F
    (frame_gate D hz hgate axis) axis rfl surfaceFlag tailFlag hS hT
  have he (a : A) :
      RCN344.coordinateDegree (GenericField K) (CoordinateField (GenericField K) (component a).1)
        (coordinateOfGate
          (flagEvaluation (GenericField K) (component a).1 D.lam D.mu (D.mu*D.lam)
            (MvPolynomial.X (axis.order 0))) (frame_gate D hz hgate axis a))=frameCost D hz axis a :=
    coordinateOfGate_degree_of_transcendental _ _ (frame_trans D hz axis a)
  simpa only [F,he] using hb








end
end ProximityPrize.SubmissionLower.MovingSourceLinearCycleFamily6814


