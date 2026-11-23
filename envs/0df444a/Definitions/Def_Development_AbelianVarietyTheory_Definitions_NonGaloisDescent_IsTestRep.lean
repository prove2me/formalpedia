-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:32:21.720835+00:00
-- url     : https://prove2.me/theorems/5fd1496e-eb9d-44fc-bfb4-ed0318643c9b
-- title:
--   Is Test Rep
-- statement:
--   Definitions and structural lemmas for Is Test Rep, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/IsTestRep.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
namespace GlobalTheory.JR
def fourB {V : Type} [MeasurableSpace V] (μ : Measure V) (B : V → V → ℂ) (f : V → ℂ) (y : V) : ℂ :=
  ∫ x, f x * B x y ∂μ
def SelfDual {V : Type} [AddCommGroup V] [TopologicalSpace V] [MeasurableSpace V] (μ : Measure V)
    (B : V → V → ℂ) : Prop :=
  μ.IsAddHaarMeasure ∧ ∀ f : V → ℂ, IsTest f → ∀ y, fourB μ B (fourB μ B f) y = f (-y)
def IsTestRep {G X : Type} [Group G] [TopologicalSpace X] (W : G → (X → ℂ) → X → ℂ) : Prop :=
  (∀ g f, IsTest f → IsTest (W g f)) ∧ (∀ f, IsTest f → W 1 f = f) ∧
    (∀ g h f, IsTest f → W (g * h) f = W g (W h f)) ∧
    ∀ g (c : ℂ) f f', IsTest f → IsTest f' → W g (c • f + f') = c • W g f + W g f'
def nS {k : Type} [CommRing k] (z : k) : SpecialLinearGroup (Fin 2) k := ⟨!![1, z; 0, 1], by simp [Matrix.det_fin_two]⟩
def mS {k : Type} [CommRing k] (s : kˣ) : SpecialLinearGroup (Fin 2) k :=
  ⟨!![(s : k), 0; 0, ((s⁻¹ : kˣ) : k)], by simp [Matrix.det_fin_two]⟩
def wS (k : Type) [CommRing k] : SpecialLinearGroup (Fin 2) k := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
structure Et (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] where
  K : Type
  L : Type
  [crK : CommRing K]
  [algK : Algebra F K]
  [finK : Module.Finite F K]
  [redK : IsReduced K]
  [topK : TopologicalSpace K]
  [mtK : IsModuleTopology F K]
  [trK : IsTopologicalRing K]
  [lcK : LocallyCompactSpace K]
  [mK : MeasurableSpace K]
  [bK : BorelSpace K]
  [crL : CommRing L]
  [stL : StarRing L]
  [algFL : Algebra F L]
  [algKL : Algebra K L]
  [algEL : Algebra E L]
  [twK : IsScalarTower F K L]
  [twE : IsScalarTower F E L]
  [topL : TopologicalSpace L]
  [mtL : IsModuleTopology F L]
  [mL : MeasurableSpace L]
  [bL : BorelSpace L]
  push : Algebra.IsPushout F E K L
  star_K : ∀ x : K, star (algebraMap K L x) = algebraMap K L x
  star_E : ∀ y : E, star (algebraMap E L y) = algebraMap E L (star y)
attribute [instance] Et.crK Et.algK Et.finK Et.redK Et.topK Et.mtK Et.trK Et.lcK Et.mK Et.bK Et.crL Et.stL Et.algFL
  Et.algKL Et.algEL Et.twK Et.twE Et.topL Et.mtL Et.mL Et.bL
namespace Et
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E)
def absK (t : A.K) : ℝ := by
  classical exact if h : IsUnit t then (distribHaarChar A.K h.unit : ℝ) else 0
def etaK (t : A.K) : ℂ := eta (Algebra.norm F t)
def psiK (ψ : AddChar F ℂ) (t : A.K) : ℂ := ψ (Algebra.trace F A.K t)
def NL (y : A.L) : A.K := Algebra.norm A.K y
def kerK (ψ : AddChar F ℂ) (y y' : A.K) : ℂ := A.psiK ψ (y * y')
def kerL (ψ : AddChar F ℂ) (x : A.K) (y' y : A.L) : ℂ := A.psiK ψ (x * Algebra.trace A.K A.L (star y' * y))
def orbK (μK : Measure A.K) (φ' : A.K × A.K → ℂ) (a : A.K) : ℂ :=
  ∫ t in {t : A.K | IsUnit t}, φ' (a * Ring.inverse t, t) * A.etaK t * ((A.absK t : ℂ))⁻¹ ∂μK
def fourK (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (p : A.K × A.K) : ℂ :=
  ∫ b', ∫ c', φ' (b', c') * A.psiK ψ (p.1 * c' + b' * p.2) ∂μK ∂μK
def orbL (ν : Measure (unitary A.L)) (φ : A.L → ℂ) (y₀ : A.L) : ℂ := ∫ t : unitary A.L, φ (t.1 * y₀) ∂ν
def IsNat (μK : Measure A.K) (μL : Measure A.L) (ν : Measure (unitary A.L)) : Prop :=
  ν.IsHaarMeasure ∧ ∀ (s : A.K → A.L), (∀ y : A.L, IsUnit y → A.NL (s (A.NL y)) = A.NL y) →
    ∀ h : A.L → ℂ, IsTest h → tsupport h ⊆ {y | IsUnit y} →
      ∫ y, h y * ((A.absK (A.NL y) : ℂ))⁻¹ ∂μL =
        ∫ a in {a : A.K | ∃ y : A.L, IsUnit y ∧ A.NL y = a}, A.orbL ν h (s a) * ((A.absK a : ℂ))⁻¹ ∂μK
structure Meas (ψ : AddChar F ℂ) where
  μK : Measure A.K
  μL : A.Kˣ → Measure A.L
  ν : Measure (unitary A.L)
  sdK : SelfDual μK (A.kerK ψ)
  sdL : ∀ x : A.Kˣ, SelfDual (μL x) (A.kerL ψ x)
  nat : A.IsNat μK (μL 1) ν
def IsWeil (ψ : AddChar F ℂ) (x : A.K) (ω : A.K → ℂ) (μ : Measure A.L) (γ : ℂ)
    (W : SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ) : Prop :=
  IsTestRep W ∧ ∀ φ, IsTest φ →
    (∀ z y, W (nS z) φ y = A.psiK ψ (z * x * A.NL y) * φ y) ∧
    (∀ (s : A.Kˣ) y, W (mS s) φ y = ω s * (A.absK s : ℂ) * φ ((s : A.K) • y)) ∧
    ∀ y, W (wS A.K) φ y = γ * fourB μ (A.kerL ψ x) φ y
def OK : Set A.K := {z | ∀ i, ‖(LinearMap.charpoly (Algebra.lmul F A.K z)).coeff i‖ ≤ 1}
def InI (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) : Prop :=
  (∃ U ∈ 𝓝 (0 : A.K), ∀ g k : SpecialLinearGroup (Fin 2) A.K,
      (∀ i j, ((k : Matrix (Fin 2) (Fin 2) A.K) - 1) i j ∈ U) → Φ (g * k) = Φ g) ∧
    ∀ z (s : A.Kˣ) g, Φ (nS z * mS s * g) = A.etaK s * (A.absK s : ℂ) * Φ g
def abelian₂ (μK : Measure A.K) (ψ : AddChar F ℂ) (a : A.K) (Φ : SpecialLinearGroup (Fin 2) A.K → ℂ) (c : F) : ℂ :=
  ∫ z in {z : A.K | c • z ∈ A.OK}, Φ (wS A.K * nS z) * A.psiK ψ (-(a * z)) ∂μK
def tilde (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (c u : A.K) : ℂ :=
  ∫ b, φ' (b, c) * A.psiK ψ (u * b) ∂μK
def jHyp (μK : Measure A.K) (ψ : AddChar F ℂ) (φ' : A.K × A.K → ℂ) (g : SpecialLinearGroup (Fin 2) A.K) : ℂ :=
  ∫ t, A.tilde μK ψ φ' (t * g 1 0) (t * g 1 1) * A.etaK t ∂μK
def IsIsom {r : ℕ} (x : A.K) (j : A.L ≃ₗ[E] (Fin r → E)) : Prop :=
  ∀ y y', star (j y) ⬝ᵥ j y' = Algebra.trace E A.L (algebraMap A.K A.L x * star y * y')
def IsReps (S : Set A.Kˣ) : Prop := ∀ a : A.Kˣ, ∃! x : A.Kˣ, x ∈ S ∧ ∃ y : A.L, IsUnit y ∧ (a : A.K) = x * A.NL y
def IsGen {r : ℕ} (τ : A.K) (p : Fin r → F) : Prop :=
  LinearIndependent F (fun i : Fin r => τ ^ (i : ℕ)) ∧ Module.finrank F A.K = r ∧
    τ ^ r + ∑ i, p i • τ ^ (i : ℕ) = 0
def invK {r : ℕ} (τ : A.K) (p : Fin r → F) (lam : F) (a : A.K) : Inv r F :=
  (p, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * a), lam)
end Et
def WeilField : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E), IsField A.K → IsField A.L → ∀ (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L),
    SelfDual μ (A.kerL ψ x) → ∀ ω : A.K → ℂ,
    (∀ s : A.Kˣ, ((∃ y, A.NL y = s) → ω s = 1) ∧ ((¬ ∃ y, A.NL y = s) → ω s = -1)) →
    ∃ γ W, A.IsWeil ψ x ω μ γ W
def WeilEt : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L),
    SelfDual μ (A.kerL ψ x) → ∃ γ W, A.IsWeil ψ x A.etaK μ γ W
def RankOne : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (m : A.Meas ψ) (S : Set A.Kˣ), A.IsReps S →
    ∀ (γ : A.Kˣ → ℂ) (W : A.Kˣ → SpecialLinearGroup (Fin 2) A.K → (A.L → ℂ) → A.L → ℂ),
    (∀ x ∈ S, A.IsWeil ψ x A.etaK (m.μL x) (γ x) (W x)) →
    ∀ (φ' : A.K × A.K → ℂ) (φ : A.Kˣ → A.L → ℂ) (κ : ℂ), IsTest φ' → (∀ x ∈ S, IsTest (φ x)) →
    (∀ x ∈ S, ∀ y : A.L, IsUnit y → κ * A.orbK m.μK φ' (x * A.NL y) = A.orbL m.ν (φ x) y) →
    ∀ x ∈ S, ∀ y : A.L, IsUnit y →
      κ * A.orbK m.μK (A.fourK m.μK ψ φ') (x * A.NL y) =
        γ x * A.orbL m.ν (fourB (m.μL x) (A.kerL ψ x) (φ x)) y
def GammaOne : Prop :=
  ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E]
    (A : Et F E) (ψ : AddChar F ℂ), IsStdChar ψ → ∀ (x : A.Kˣ) (μ : Measure A.L), SelfDual μ (A.kerL ψ x) →
    ∀ (ω : A.K → ℂ) (γ : ℂ) W, A.IsWeil ψ x ω μ γ W → ∀ (r : ℕ) (j : A.L ≃ₗ[E] (Fin r → E)), A.IsIsom x j → γ = 1
end GlobalTheory.JR


