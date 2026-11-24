-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SiegelReframe
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:57:01.882716+00:00
-- url     : https://prove2.me/theorems/43d6419e-905c-421d-91ac-7951a959efec
-- title:
--   Siegel Reframe
-- statement:
--   Definitions and structural lemmas for Siegel Reframe, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SiegelReframe.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory
open scoped Real ContDiff
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
abbrev Fl (g : ℕ) : Type := Fin g ⊕ Fin g → ℝ
def riem {g : ℕ} (x y : Fl g) : ℝ :=
  ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i))
def symp (g : ℕ) : Fl g [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := riem (v 0) (v 1)
  map_update_add' := by
    intro inst v i x y
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, add_mul, mul_add, Finset.sum_add_distrib] <;> ring
  map_update_smul' := by
    intro inst v i c x
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, ← Finset.sum_sub_distrib, Finset.mul_sum] <;>
      exact Finset.sum_congr rfl fun _ _ => by ring
  cont := by
    unfold riem
    fun_prop
  map_eq_zero_of_eq' := by
    intro v i j h hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simp only [riem, h01]
    exact Finset.sum_eq_zero fun _ _ => by ring
def stdLat (g : ℕ) : Submodule ℤ (Fl g) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g)))
def IsLat {g : ℕ} (M : Submodule ℤ (Fl g)) : Prop :=
  ∃ _ : DiscreteTopology M, IsZLattice ℝ M
def IsRatLat {g : ℕ} (M : Submodule ℤ (Fl g)) : Prop :=
  IsLat M ∧ ∀ l ∈ M, ∀ i, ∃ r : ℚ, l i = r
def wedgePow {T : Type*} [NormedAddCommGroup T] [NormedSpace ℝ T]
    (α : T [⋀^Fin 2]→L[ℝ] ℝ) (k : ℕ) (v : Fin k × Fin 2 → T) : ℝ :=
  (1 / 2 ^ k) * ∑ σ : Equiv.Perm (Fin k × Fin 2),
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, α ![v (σ (i, 0)), v (σ (i, 1))]
def herm {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) : ℂ :=
  (v ᵥ* ((τ.map Complex.im)⁻¹).map (fun t : ℝ => (t : ℂ))) ⬝ᵥ star w
def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : Fin g → ℂ :=
  (fun i => (x (Sum.inl i) : ℂ)) ᵥ* τ + fun i => (x (Sum.inr i) : ℂ)
def flatOf {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : Fl g :=
  Sum.elim ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹)
    ((fun i => (z i).re) - ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.re)
abbrev Sp (g : ℕ) : Type := Matrix.symplecticGroup (Fin g) ℝ
def Sp.mat {g : ℕ} (γ : Sp g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ := γ.1
def den {g : ℕ} (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  γ.mat.toBlocks₂₁.map (fun t : ℝ => (t : ℂ)) * τ + γ.mat.toBlocks₂₂.map (fun t : ℝ => (t : ℂ))
def moeb {g : ℕ} (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) * τ + γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ))) *
    (den γ τ)⁻¹
def latAct {g : ℕ} (M : Submodule ℤ (Fl g)) (γ : Sp g) : Submodule ℤ (Fl g) :=
  M.map ((Matrix.vecMulLinear (γ⁻¹).mat).restrictScalars ℤ)
section Family
abbrev Pt (E : Type) (g : ℕ) : Type := E × (Fin g → ℂ)
variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g : ℕ}
abbrev Form2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) : Type :=
  Pt E g [⋀^Fin 2]→L[ℝ] ℝ
def IsPeriodMap (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  IsOpen B ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) ∧ ∀ b ∈ B, IsSiegel (τ b)
def cov (B : Set E) (g : ℕ) : Set (Pt E g) := B ×ˢ Set.univ
def flat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Fl g := flatOf (τ P.1) P.2
def dflat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Pt E g →L[ℝ] Fl g :=
  fderiv ℝ (flat τ) P
def om0 (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Form2 E g :=
  (symp g).compContinuousLinearMap (dflat τ P)
def pull (f : Pt E g → Pt E' g) (α : Pt E' g → Form2 E' g) (P : Pt E g) : Form2 E g :=
  (α (f P)).compContinuousLinearMap (fderiv ℝ f P)
def transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : Pt E g :=
  (P.1, P.2 + per (τ P.1) x)
def mulN (n : ℤ) (P : Pt E g) : Pt E g := (P.1, n • P.2)
def zeroSec (g : ℕ) (b : E) : Pt E g := (b, 0)
def reframe (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (P : Pt E g) : Pt E g :=
  (P.1, P.2 ᵥ* (den γ (τ P.1))⁻¹)
def ddc (u : Pt E g → ℝ) (P v w : Pt E g) : ℝ :=
  (1 / (4 * π)) * (fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • v)) P w -
    fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • w)) P v)
def fibreInt (τ : E → Matrix (Fin g) (Fin g) ℂ) (α : Pt E g → Form2 E g) (b : E) : ℝ :=
  ∫ z in per (τ b) '' Set.Icc (0 : Fl g) 1,
    wedgePow (α (b, z)) g (fun k => ((0 : E),
      Pi.single k.1 (if k.2 = 0 then (1 : ℂ) else Complex.I))) / (g.factorial : ℝ)
def FlatFormProps (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=

  (∀ b ∈ B, (∀ x, flatOf (τ b) (per (τ b) x) = x) ∧ ∀ z, per (τ b) (flatOf (τ b) z) = z) ∧
  AnalyticOnNhd ℝ (flat τ) (cov B g) ∧
  AnalyticOnNhd ℝ (fun Q : E × Fl g => per (τ Q.1) Q.2) (B ×ˢ Set.univ) ∧

  (∀ γ : Sp g, IsPeriodMap B (fun b => moeb γ (τ b)) ∧ (∀ b ∈ B, IsUnit (den γ (τ b))) ∧
    DifferentiableOn ℂ (reframe τ γ) (cov B g) ∧
    ∀ P ∈ cov B g, flat (fun b => moeb γ (τ b)) (reframe τ γ P) = flat τ P ᵥ* (γ⁻¹).mat ∧
      pull (reframe τ γ) (om0 fun b => moeb γ (τ b)) P = om0 τ P) ∧

  ContDiffOn ℝ ∞ (om0 τ) (cov B g) ∧
  (∀ P ∈ cov B g, extDeriv (om0 τ) P = 0) ∧

  (∀ P ∈ cov B g, ∀ v w : Pt E g, om0 τ P ![Complex.I • v, Complex.I • w] = om0 τ P ![v, w]) ∧

  (∀ P ∈ cov B g, ∀ v w : Fin g → ℂ, om0 τ P ![(0, v), (0, w)] = -(herm (τ P.1) v w).im) ∧
  (∀ P ∈ cov B g, ∀ v : Fin g → ℂ, v ≠ 0 → 0 < om0 τ P ![(0, v), (0, Complex.I • v)]) ∧

  (∀ n : ℤ, ∀ P ∈ cov B g, pull (mulN n) (om0 τ) P = ((n : ℝ) ^ 2) • om0 τ P) ∧
  (∀ b ∈ B, (om0 τ (zeroSec g b)).compContinuousLinearMap (fderiv ℝ (zeroSec g) b) = 0) ∧
  (∀ P ∈ cov B g, ∀ v, wedgePow (om0 τ P) (g + 1) v = 0) ∧
  (∀ b ∈ B, fibreInt τ (om0 τ) b = 1) ∧

  (∀ x : Fl g, DifferentiableOn ℂ (transl τ x) (cov B g) ∧
    ∀ P ∈ cov B g, pull (transl τ x) (om0 τ) P = om0 τ P) ∧

  (∀ P ∈ cov B g, ∀ v : Pt E g,
    (∀ w : Fin g → ℂ, om0 τ P ![v, (0, w)] = 0) ↔ dflat τ P v = 0) ∧
  (∀ P ∈ cov B g, (∀ v : Pt E g, dflat τ P v = 0 → dflat τ P (Complex.I • v) = 0) ∧
    ∀ u : E, ∃! w : Fin g → ℂ, dflat τ P (u, w) = 0)
def IsFactor (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  (∀ l ∈ M, DifferentiableOn ℂ (j l) (cov B g) ∧ ∀ P ∈ cov B g, j l P ≠ 0) ∧
  ∀ l ∈ M, ∀ l' ∈ M, ∀ P ∈ cov B g, j (l + l') P = j l (transl τ l' P) * j l' P
def IsMetric (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (cov B g) ∧ (∀ P ∈ cov B g, 0 < h P) ∧
  ∀ l ∈ M, ∀ P ∈ cov B g, h (transl τ l P) * ‖j l P‖ ^ 2 = h P
def ChernIsFlat (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) : Prop :=
  ∀ P ∈ cov B g, ∀ v w : Pt E g, -ddc (fun Q => Real.log (h Q)) P v w = om0 τ P ![v, w]
def IsBundleIso (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j j' : Fl g → Pt E g → ℂ) (φ : Pt E g → ℂ) : Prop :=
  DifferentiableOn ℂ φ (cov B g) ∧ (∀ P ∈ cov B g, φ P ≠ 0) ∧
  ∀ l ∈ M, ∀ P ∈ cov B g, φ (transl τ l P) * j l P = j' l P * φ P
def IsIsometry (B : Set E) (h h' : Pt E g → ℝ) (φ : Pt E g → ℂ) : Prop :=
  ∀ P ∈ cov B g, h' P * ‖φ P‖ ^ 2 = h P
def mulPullFactor (n : ℤ) (j : Fl g → Pt E g → ℂ) (l : Fl g) (P : Pt E g) : ℂ :=
  j (n • l) (mulN n P)
def translPullFactor (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (j : Fl g → Pt E g → ℂ)
    (l : Fl g) (P : Pt E g) : ℂ :=
  j l (transl τ x P)
def InducesPolarisation (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  ∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ,
    (∀ l ∈ M, Differentiable ℂ (f l) ∧ ∀ z, j l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧
    ∀ l ∈ M, ∀ l' ∈ M, ∀ z,
      f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = (riem l l' : ℂ)
def IsRigidification (B : Set E) (r : E → ℂ) : Prop :=
  DifferentiableOn ℂ r B ∧ ∀ b ∈ B, r b ≠ 0
def IsCubicalMetric (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (j : Fl g → Pt E g → ℂ)
    (r : E → ℂ) (h : Pt E g → ℝ) : Prop :=
  IsMetric B τ (stdLat g) j h ∧ ChernIsFlat B τ h ∧ ∀ b ∈ B, h (zeroSec g b) * ‖r b‖ ^ 2 = 1
def IsSquareIso (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (j : Fl g → Pt E g → ℂ)
    (r : E → ℂ) (n : ℤ) (φ : Pt E g → ℂ) : Prop :=
  IsBundleIso B τ (stdLat g) (mulPullFactor n j) (fun l P => j l P ^ (n.natAbs ^ 2)) φ ∧
  ∀ b ∈ B, φ (zeroSec g b) * r b = r b ^ (n.natAbs ^ 2)
def CubicalMetricProps (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  ∀ (j : Fl g → Pt E g → ℂ) (r : E → ℂ), IsFactor B τ (stdLat g) j →
    (∃ ι, IsBundleIso B τ (stdLat g) (mulPullFactor (-1) j) j ι) → IsRigidification B r →
    InducesPolarisation B τ (stdLat g) j →
    (∃ h, IsCubicalMetric B τ j r h) ∧
    (∀ h h', IsCubicalMetric B τ j r h → IsCubicalMetric B τ j r h' →
      Set.EqOn h h' (cov B g)) ∧
    ∀ n : ℤ, (∃ φ, IsSquareIso B τ j r n φ) ∧
      ∀ h φ, IsCubicalMetric B τ j r h → IsSquareIso B τ j r n φ →
        IsIsometry B (fun P => h (mulN n P)) (fun P => h P ^ (n.natAbs ^ 2)) φ
def RigidityProps (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  SimplyConnectedSpace B → ∀ M : Submodule ℤ (Fl g), IsLat M →
    (∀ l ∈ M, ∀ l' ∈ M, ∃ k : ℤ, riem l l' = k) →
    ∀ (j₁ j₂ : Fl g → Pt E g → ℂ) (h₁ h₂ : Pt E g → ℝ),
      IsFactor B τ M j₁ → IsMetric B τ M j₁ h₁ → ChernIsFlat B τ h₁ →
      IsFactor B τ M j₂ → IsMetric B τ M j₂ h₂ → ChernIsFlat B τ h₂ →
      ∃ (x : Fl g) (φ : Pt E g → ℂ), IsBundleIso B τ M j₂ (translPullFactor τ x j₁) φ ∧
        IsIsometry B h₂ (fun P => h₁ (transl τ x P)) φ
def SameOrbit (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g)) (P Q : Pt E g) : Prop :=
  ∃ l ∈ M, Q = transl τ l P
end Family
def symMat (g : ℕ) : Submodule ℂ (Fin g → Fin g → ℂ) where
  carrier := {A | ∀ i j, A i j = A j i}
  add_mem' := fun {A B} hA hB i j => by simp [hA i j, hB i j]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c A hA i j => by simp [hA i j]
def tauU {g : ℕ} (s : symMat g) : Matrix (Fin g) (Fin g) ℂ := Matrix.of s.1
def siegel (g : ℕ) : Set (symMat g) := {s | IsSiegel (tauU s)}
def symPart {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : symMat g :=
  ⟨fun i j => (A i j + A j i) / 2, fun i j => by simp only [add_comm]⟩
def actU {g : ℕ} (γ : Sp g) (P : Pt (symMat g) g) : Pt (symMat g) g :=
  (symPart (moeb γ (tauU P.1)), P.2 ᵥ* (den γ (tauU P.1))⁻¹)
def UniversalProps (g : ℕ) : Prop :=
  IsPeriodMap (siegel g) tauU ∧ SimplyConnectedSpace (siegel g) ∧
  (∀ P ∈ cov (siegel g) g, actU 1 P = P) ∧
  (∀ γ γ' : Sp g, ∀ P ∈ cov (siegel g) g, actU (γ * γ') P = actU γ (actU γ' P)) ∧
  (∀ γ : Sp g, Set.BijOn (actU γ) (cov (siegel g) g) (cov (siegel g) g) ∧
    DifferentiableOn ℂ (actU γ) (cov (siegel g) g) ∧
    (∀ P ∈ cov (siegel g) g, IsUnit (den γ (tauU P.1)) ∧
      tauU (actU γ P).1 = moeb γ (tauU P.1) ∧
      flat tauU (actU γ P) = flat tauU P ᵥ* (γ⁻¹).mat ∧
      pull (actU γ) (om0 tauU) P = om0 tauU P ∧
      (P.2 = 0 → (actU γ P).2 = 0)) ∧
    ((∀ i k, ∃ r : ℚ, γ.mat i k = r) → ∀ M : Submodule ℤ (Fl g), IsRatLat M →
      IsRatLat (latAct M γ) ∧ ∀ P ∈ cov (siegel g) g, ∀ Q ∈ cov (siegel g) g,
        SameOrbit tauU M P Q ↔ SameOrbit tauU (latAct M γ) (actU γ P) (actU γ Q))) ∧
  ∃ j h, IsFactor (siegel g) tauU (stdLat g) j ∧ IsMetric (siegel g) tauU (stdLat g) j h ∧
    ChernIsFlat (siegel g) tauU h
def FlatCubical : Prop :=
  ∀ g : ℕ,
    (∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
      (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ), IsPeriodMap B τ →
      FlatFormProps B τ ∧ CubicalMetricProps B τ ∧ RigidityProps B τ) ∧
    UniversalProps g
def thetaExp {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (l : Fl g) (z : Fin g → ℂ) : ℂ :=
  -(((fun i => (l (Sum.inl i) : ℂ)) ᵥ* τ) ⬝ᵥ fun i => (l (Sum.inl i) : ℂ)) / 2 -
    (fun i => (l (Sum.inl i) : ℂ)) ⬝ᵥ z
end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe


