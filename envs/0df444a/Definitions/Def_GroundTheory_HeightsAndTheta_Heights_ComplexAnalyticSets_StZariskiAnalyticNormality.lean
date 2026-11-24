-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StZariskiAnalyticNormality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:29:22.453914+00:00
-- url     : https://prove2.me/theorems/f808c99d-4582-41bd-9c8f-3c63ff2d74d9
-- title:
--   St Zariski Analytic Normality
-- statement:
--   Definitions and structural lemmas for St Zariski Analytic Normality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/StZariskiAnalyticNormality.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
noncomputable section
def holGerms {σ : Type} [Fintype σ] (w : σ → ℂ) : Subring (Germ (𝓝 w) ℂ) where
  carrier := {φ | ∃ f : (σ → ℂ) → ℂ, AnalyticAt ℂ f w ∧ (f : Germ (𝓝 w) ℂ) = φ}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, rfl⟩
  one_mem' := ⟨fun _ => 1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  zero_mem' := ⟨fun _ => 0, analyticAt_const, rfl⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, rfl⟩
theorem analyticAt_eval_polynomial {σ : Type} [Fintype σ] (w : σ → ℂ) (q : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun z : σ → ℂ => eval z q) w := by
  induction q using MvPolynomial.induction_on with
  | C a => simpa using (analyticAt_const : AnalyticAt ℂ (fun _ : σ → ℂ => a) w)
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hi : AnalyticAt ℂ (fun z : σ → ℂ => z i) w :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ => ℂ) i).analyticAt w
    simp only [map_mul, eval_X]
    exact hp.mul hi
def polyGerm {σ : Type} [Fintype σ] (w : σ → ℂ) : MvPolynomial σ ℂ →+* holGerms w :=
  ((Germ.coeRingHom (𝓝 w)).comp (RingHom.pi fun z : σ → ℂ => (MvPolynomial.eval z))).codRestrict
    (holGerms w) fun q => ⟨fun z => eval z q, analyticAt_eval_polynomial w q, rfl⟩
def ZariskiAnalyticNormality.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ),
    I.IsPrime → IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ I) → w ∈ zeroSetIn I →
      (I.map (polyGerm w)).IsPrime ∧ IsIntegrallyClosed (holGerms w ⧸ I.map (polyGerm w))
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


