-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Statements
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Statements
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:54:07.845963+00:00
-- url     : https://prove2.me/theorems/1b060e59-da00-40bf-8980-c94530c67633
-- title:
--   Statements
-- statement:
--   Definitions and structural lemmas for Statements, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/Statements.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Examples
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def LatticeOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ S : Set (AddSubgroup W), S.Finite ∧
    ∀ La : AddSubgroup W, IsDIntegral h D La → ∃ L ∈ S, ∃ g : h.unitaryGroup, g • L = La
def LinePairOrbitsFinite.Statement [FiniteDimensional E W] (h : HermitianForm F E W) : Prop :=
  ∀ D : ℕ, ∃ S : Set (AddSubgroup W × Submodule E W), S.Finite ∧
    ∀ (La : AddSubgroup W) (l : Submodule E W), IsDIntegral h D La → IsIsotropicLine h l →
      ∃ p ∈ S, ∃ g : h.unitaryGroup,
        g • p.1 = La ∧ p.2.map ((g : W ≃ₗ[E] W) : W →ₗ[E] W) = l
def ArithmeticCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ) (La : AddSubgroup W),
    IsDIntegral h D La → ∃ FD : Set (archUnitary h v),
      IsFundamentalDomain (archLatticeGroup h v La) FD μ ∧ μ FD < ⊤
instance measurableSpace_unitaryPoints_adele (H : Matrix ι ι E) :
    MeasurableSpace (unitaryPoints F E H 𝔸[F]) :=
  borel _
instance borelSpace_unitaryPoints_adele (H : Matrix ι ι E) :
    BorelSpace (unitaryPoints F E H 𝔸[F]) :=
  ⟨rfl⟩
def AdelicCovolumeFinite.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (μ : Measure (unitaryPoints F E (gram h.toSesq v) 𝔸[F])) [μ.IsHaarMeasure],
    ∃ FD : Set (unitaryPoints F E (gram h.toSesq v) 𝔸[F]),
      IsFundamentalDomain (hermitianDiagonal h v).range FD μ ∧ μ FD < ⊤
def ScalingLaw.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
    (La : AddSubgroup W) (VV : Set W),
    IsDIntegral h D La → VV ⊆ La → (∀ x ∈ VV, x ≠ 0 ∧ h.toSesq x x = 0) →
    (∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV) →
    (∃ C : ℕ, ∀ x ∈ VV, lineIndex E La x ≤ C) →
    ∃ FD : Set (archUnitary h v), IsFundamentalDomain (archLatticeGroup h v La) FD μ ∧
      ∀ t : ℝ, 0 < t → massBelow M μ FD VV t < ⊤ ∧
        ∀ θ : ℝ, 0 < θ → massBelow M μ FD VV (θ * t) =
          ENNReal.ofReal (θ ^ (2 * finrank ℚ F * (finrank E W - 1))) * massBelow M μ FD VV t
def MahlerCompactness.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (t : ℝ), 0 < t →
    ∃ S : Set (AddSubgroup W), S.Finite ∧ ∃ K : Set (archUnitary h v), IsCompact K ∧
      ∀ (La : AddSubgroup W) (g : archUnitary h v), IsDIntegral h D La →
        (∀ x ∈ La, x ≠ 0 → t ≤ M.len (invApply g (vecAt v x))) →
        ∃ γ : h.unitaryGroup, γ • La ∈ S ∧ archEmbed h v γ * g ∈ K
def ShortVectorIsotropic.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (D : ℕ) (La : AddSubgroup W) (g : archUnitary h v) (x : W),
    IsDIntegral h D La → x ∈ La → M.len (invApply g (vecAt v x)) < 1 → h.toSesq x x = 0
def ShortestVectorIndex.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (r : ℝ),
    (∃ a : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ r) →
    ∀ (D : ℕ) (La : AddSubgroup W) (g : archUnitary h v) (x : W),
      IsDIntegral h D La → x ∈ La → x ≠ 0 →
      (∀ y ∈ La, y ≠ 0 → M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y))) →
      (lineIndex E La x : ℝ) ≤ (r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)
def UnfoldingIntegral.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (μ : Measure (archUnitary h v)) [μ.IsHaarMeasure] (D : ℕ)
    (La : AddSubgroup W) (x₀ : W), IsDIntegral h D La → x₀ ∈ La → x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∃ FD : Set (archUnitary h v), IsFundamentalDomain (vecStabGroup h v La x₀) FD μ ∧
      ∃ C : ℝ≥0∞, 0 < C ∧ C < ⊤ ∧ ∀ t : ℝ, 0 < t →
        μ (FD ∩ {g | M.len (invApply g (vecAt v x₀)) < t}) =
          C * ENNReal.ofReal (t ^ (2 * finrank ℚ F * (finrank E W - 1)))
def ParabolicDecomposition.Statement (h : HermitianForm F E W) (v : Basis ι E W) : Prop :=
  ∀ (M : Majorant h v) (x₀ : W), x₀ ≠ 0 → h.toSesq x₀ x₀ = 0 →
    ∀ g : archUnitary h v, ∃ p k : archUnitary h v, k ∈ M.stab ∧ g = p * k ∧
      ∀ w, ∃ c : ℂ, (((p : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ) *ᵥ vecAt v x₀ w) =
        c • vecAt v x₀ w
section Inhabitants
open GaussianPlane
end Inhabitants
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


