-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
-- name    : CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:25.468521+00:00
-- url     : https://prove2.me/theorems/3ac59b2d-2943-4418-9aed-1a80f08f307a
-- title:
--   Hyp J
-- statement:
--   Definitions and structural lemmas for Hyp J, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/CountingDefinitions/AdelicEulerProducts/HypJ.lean

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SW
open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal
def hypJ {K : Type} [Zero K] [One K] {M : ℕ} (A : Matrix (Fin M) (Fin M) K) :
    Matrix (Fin (M + 2)) (Fin (M + 2)) K :=
  Matrix.of (Fin.cons (Fin.cons 0 (Fin.cons 1 (fun _ => 0)))
    (Fin.cons (Fin.cons 1 (Fin.cons 0 (fun _ => 0))) (fun i => Fin.cons 0 (Fin.cons 0 (A i)))))
def eOne (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 1) → K :=
  fun _ => Fin.cons 1 (fun _ => 0)
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
def box {d M n : ℕ} (b : Module.Basis (Fin d) F E) (N : ℕ) (r : ℝ) : Set (Fin n → Fin M → AF F ⊗[F] E) :=
  {X | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r}
def IsFlow (τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ) : Prop :=
  Continuous τ ∧ ∃ θ : ℝ →+* Ainf F, Continuous θ ∧
    ∀ x : ℝ, ((τ (Multiplicative.ofAdd x) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) =
      pairA F (θ (Real.exp x)) 1 ⊗ₜ[F] (1 : E)
def cntI (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (μ : Measure (HA (AF F) σ J))
    (𝓕 : Set (HA (AF F) σ J)) (S : Set (Fin n → Fin M → E))
    (Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ h in 𝓕, ∑' X : S, Φ (actW (AF F) σ J h⁻¹ (ratTup (AF F) (X : Fin n → Fin M → E))) ∂μ
end GlobalTheory.CompanionTheory.SW


