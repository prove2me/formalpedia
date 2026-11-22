-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:03:12.184417+00:00
-- url     : https://prove2.me/theorems/47fb3bb7-1133-4196-9afc-5b4fdb951fd3
-- title:
--   Stationary Phase Model
-- statement:
--   Definitions and structural lemmas for Stationary Phase Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/StationaryPhaseModel.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
section PartD0
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
def Sym {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : Set E) (w : E → ℝ) (m : ℤ) (N : ℕ) (K : ℝ) (f : E → F) : Prop :=
  ContDiff ℝ N f ∧ ∀ x ∈ A, ∀ i : ℕ, i ≤ N → ‖iteratedFDeriv ℝ i f x‖ ≤ K * w x ^ (m - (i : ℤ))
def wt {E : Type*} [NormedAddCommGroup E] (σ : ℝ) (x : E) : ℝ := ‖x‖ + σ
def osc {E : Type*} (φ : E → ℝ) (τ : ℝ) (x : E) : ℂ := Complex.exp (Complex.I * ((φ x / τ : ℝ) : ℂ))
def dirv {d : ℕ} (l : Fin d × Bool) : Fin d → ℂ := Pi.single l.1 (if l.2 then Complex.I else 1)
def cutB (d : ℕ) (ρ : ℝ) (x : Fin d → ℂ) : ℝ :=
  if h : 0 < ρ then (⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩ : ContDiffBump (0 : Fin d → ℂ)) x else 0
def quad {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : E → ℝ) (x : E) : ℝ :=
  φ 0 + (1 / 2) * fderiv ℝ (fderiv ℝ φ) 0 x x
end
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartD0
section PartA
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
section SymCalc
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {A : Set E} {w : E → ℝ} {m m₁ m₂ : ℤ} {N : ℕ} {K K₁ K₂ : ℝ}
theorem A_const_nonneg {f : E → F} (hw : ∀ x ∈ A, 0 < w x) (h : Sym A w m N K f) {x : E} (hx : x ∈ A) :
    0 ≤ K := by
  have h0 := h.2 x hx 0 (Nat.zero_le _)
  have hp : 0 < w x ^ (m - ((0 : ℕ) : ℤ)) := zpow_pos (hw x hx) _
  by_contra hK
  push Not at hK
  have : K * w x ^ (m - ((0 : ℕ) : ℤ)) < 0 := mul_neg_of_neg_of_pos hK hp
  linarith [norm_nonneg (iteratedFDeriv ℝ 0 f x)]
theorem Sym.smul {f : E → ℝ} {g : E → F} (hw : ∀ x ∈ A, 0 < w x) (hf : Sym A w m₁ N K₁ f)
    (hg : Sym A w m₂ N K₂ g) : Sym A w (m₁ + m₂) N (2 ^ N * K₁ * K₂) (fun x => f x • g x) := by
  refine ⟨hf.1.smul hg.1, fun x hx n hn => ?_⟩
  have hK₁ := A_const_nonneg hw hf hx
  have hK₂ := A_const_nonneg hw hg hx
  have hwx := hw x hx
  refine (norm_iteratedFDeriv_smul_le hf.1 hg.1 x (by exact_mod_cast hn)).trans ?_
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖ ≤
        (n.choose i : ℝ) * (K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ))) := by
    intro i hi
    have hin : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have h1 := hf.2 x hx i (hin.trans hn)
    have h2 := hg.2 x hx (n - i) ((Nat.sub_le _ _).trans hn)
    have h3 : w x ^ (m₁ - (i : ℤ)) * w x ^ (m₂ - ((n - i : ℕ) : ℤ)) = w x ^ (m₁ + m₂ - (n : ℤ)) := by
      rw [← zpow_add₀ hwx.ne']
      congr 1
      push_cast [hin]
      ring
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    calc ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n - i) g x‖
        ≤ (K₁ * w x ^ (m₁ - (i : ℤ))) * (K₂ * w x ^ (m₂ - ((n - i : ℕ) : ℤ))) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)) := by rw [← h3]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hs : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = 2 ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  rw [hs]
  have hpos : 0 ≤ K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)) :=
    mul_nonneg (mul_nonneg hK₁ hK₂) (zpow_pos hwx _).le
  calc (2 : ℝ) ^ n * (K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)))
      ≤ 2 ^ N * (K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ))) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hpos
    _ = 2 ^ N * K₁ * K₂ * w x ^ (m₁ + m₂ - (n : ℤ)) := by ring
theorem Sym.mul {f g : E → ℝ} (hw : ∀ x ∈ A, 0 < w x) (hf : Sym A w m₁ N K₁ f)
    (hg : Sym A w m₂ N K₂ g) : Sym A w (m₁ + m₂) N (2 ^ N * K₁ * K₂) (fun x => f x * g x) := by
  simpa only [smul_eq_mul] using Sym.smul hw hf hg
theorem Sym.fderiv {f : E → F} (hf : Sym A w m (N + 1) K f) : Sym A w (m - 1) N K (fderiv ℝ f) := by
  refine ⟨hf.1.fderiv_right (by norm_cast), fun x hx i hi => ?_⟩
  rw [norm_iteratedFDeriv_fderiv]
  have h := hf.2 x hx (i + 1) (Nat.succ_le_succ hi)
  have e : m - ((i + 1 : ℕ) : ℤ) = m - 1 - (i : ℤ) := by push_cast; ring
  rwa [e] at h
end SymCalc
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartA
section PartB
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
section IBP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
end IBP
section Step
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
end Step
section Reduce
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
end Reduce
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartB
section PartC
open MeasureTheory Filter Topology Metric
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
section Holo
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
end Holo
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartC
section PartD
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
def D_nsq (d : ℕ) (x : Fin d → ℂ) : ℝ := ∑ k, ‖x k‖ ^ 2
def D_gau (d : ℕ) (δ : ℝ) (x : Fin d → ℂ) : ℝ := Real.exp (-δ * ∑ k, ‖x k‖ ^ 2)
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
end
def D_phi (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x : Fin d → ℂ) : ℝ := (c * (x ⬝ᵥ (H *ᵥ x)) / 2).re
def D_bil (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) : (Fin d → ℂ) →ₗ[ℝ] (Fin d → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x v => (c * (v ⬝ᵥ (H *ᵥ x))).re)
    (fun x x' v => by simp [Matrix.mulVec_add, dotProduct_add, mul_add])
    (fun r x v => by
      rw [Matrix.mulVec_smul, dotProduct_smul, Complex.real_smul, smul_eq_mul, ← Complex.re_ofReal_mul]
      congr 1; ring)
    (fun x v v' => by simp [add_dotProduct, mul_add])
    (fun r x v => by
      rw [smul_dotProduct, Complex.real_smul, smul_eq_mul, ← Complex.re_ofReal_mul]
      congr 1; ring)
theorem D_bil_apply (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (x v : Fin d → ℂ) :
    D_bil d c H x v = (c * (v ⬝ᵥ (H *ᵥ x))).re := rfl
theorem D_mulVec_le (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ) {Γ : ℝ} (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x : Fin d → ℂ)
    (k : Fin d) : ‖(H *ᵥ x) k‖ ≤ d * Γ * ‖x‖ := by
  unfold Matrix.mulVec dotProduct
  calc ‖∑ j, H k j * x j‖ ≤ ∑ j, ‖H k j * x j‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, Γ * ‖x‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hH k j) (norm_le_pi_norm x j) (norm_nonneg _) ((norm_nonneg _).trans (hH k j))
    _ = d * Γ * ‖x‖ := by simp; ring
theorem D_bil_bound (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) {Γ : ℝ}
    (hH : ∀ i j, ‖H i j‖ ≤ Γ) (x v : Fin d → ℂ) :
    ‖D_bil d c H x v‖ ≤ (‖c‖ * (d * (d * Γ))) * ‖x‖ * ‖v‖ := by
  rw [D_bil_apply, Real.norm_eq_abs]
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul]
  have h1 : ‖v ⬝ᵥ (H *ᵥ x)‖ ≤ d * (‖v‖ * (d * Γ * ‖x‖)) := by
    unfold dotProduct
    calc ‖∑ k, v k * (H *ᵥ x) k‖ ≤ ∑ k, ‖v k * (H *ᵥ x) k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin d, ‖v‖ * (d * Γ * ‖x‖) := by
          refine Finset.sum_le_sum fun k _ => ?_
          rw [norm_mul]
          exact mul_le_mul (norm_le_pi_norm v k) (D_mulVec_le d H hH x k) (norm_nonneg _) (norm_nonneg _)
      _ = d * (‖v‖ * (d * Γ * ‖x‖)) := by simp
  calc ‖c‖ * ‖v ⬝ᵥ (H *ᵥ x)‖ ≤ ‖c‖ * (d * (‖v‖ * (d * Γ * ‖x‖))) := by gcongr
    _ = _ := by ring
def D_bilC (d : ℕ) (c : ℂ) (H : Matrix (Fin d) (Fin d) ℂ) (Γ : ℝ) (_hΓ : 0 ≤ Γ) (hH : ∀ i j, ‖H i j‖ ≤ Γ) :
    (Fin d → ℂ) →L[ℝ] (Fin d → ℂ) →L[ℝ] ℝ :=
  (D_bil d c H).mkContinuous₂ (‖c‖ * (d * (d * Γ))) (D_bil_bound d c H hH)
end
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartD
section PartE
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
section TaylorInS
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
end TaylorInS
section ECut
variable {d : ℕ} {ρ : ℝ}
noncomputable def E_bump (d : ℕ) (ρ : ℝ) (h : 0 < ρ) : ContDiffBump (0 : Fin d → ℂ) :=
  ⟨ρ / 2, ρ, half_pos h, half_lt_self h⟩
end ECut
section EQuad
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end EQuad
section EP
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
noncomputable def E_P (φ : E → ℝ) (x : E) : ℝ := φ x - quad φ x
noncomputable def E_Pe (φ : E → ℝ) (x : E) : ℝ := (1 / 2 : ℝ) * (E_P φ x + E_P φ (-x))
end EP
section EP2
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end EP2
section EPhase
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
end EPhase
section EEst
def E_OB (d q : ℕ) (β : ℂ) (Γ c₁ C : ℝ) : Prop :=
  ∀ (A : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ →
      ContDiff ℝ (d + 2 + q : ℕ) φ →
      Sym A (wt (Real.sqrt τ)) 1 (d + 1 + q) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ),
        0 ≤ K → HasCompactSupport b → tsupport b ⊆ A →
        Sym A (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b →
        ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q)
structure E_Phase (d : ℕ) (r Γ c₁ : ℝ) (φ : (Fin d → ℂ) → ℝ) : Prop where
  smooth : ContDiff ℝ (d + 6 : ℕ) φ
  bd : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ
  crit : fderiv ℝ φ 0 = 0
  low : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ : ℝ} {φ : (Fin d → ℂ) → ℝ}
end EEst
section EAmp
variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
noncomputable def constantAmplitude (d : ℕ) (ρ : ℝ) (a₀ : V) (x : Fin d → ℂ) : V := cutB d ρ x • a₀
noncomputable def linearAmplitude (d : ℕ) (ρ : ℝ) (ℓ : (Fin d → ℂ) →L[ℝ] V) (x : Fin d → ℂ) : V := cutB d ρ x • ℓ x
noncomputable def modelAmplitude (d : ℕ) (ρ : ℝ) (a₀ : V) (ℓ : (Fin d → ℂ) →L[ℝ] V) (x : Fin d → ℂ) : V :=
  cutB d ρ x • (a₀ + ℓ x)
end EAmp
section ETerms
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}
end ETerms
section EFinal
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
noncomputable def E_u (d : ℕ) (ρ : ℝ) (a : (Fin d → ℂ) → V) (x : Fin d → ℂ) : V :=
  a x - modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x
end EFinal
section ECore
end ECore
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartE
section PartF
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable def realPartMulCLM (c : ℂ) : ℂ →L[ℝ] ℝ := Complex.reCLM.comp (ContinuousLinearMap.mul ℝ ℂ c)
section Holo
variable {d : ℕ} {r : ℝ} {g : (Fin d → ℂ) → ℂ}
variable {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
end Holo
section Holo2
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
end Holo2
section Phase
noncomputable def F_bump (d : ℕ) (r : ℝ) (x : Fin d → ℂ) : ℝ :=
  if h : 0 < r then (⟨5 * r / 4, 3 * r / 2, by positivity, by linarith⟩ : ContDiffBump (0 : Fin d → ℂ)) x else 0
noncomputable def F_phi (d : ℕ) (r : ℝ) (c : ℂ) (g : (Fin d → ℂ) → ℂ) (x : Fin d → ℂ) : ℝ :=
  F_bump d r x * (c * g x).re
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ}
end Phase
section Final
variable {d : ℕ} {r Λ : ℝ} {g : (Fin d → ℂ) → ℂ} {dg : (Fin d → ℂ) → Fin d → ℂ} {H : Matrix (Fin d) (Fin d) ℂ}
noncomputable def F_c (β t : ℂ) : ℂ := β * (‖t‖ : ℂ) / t
end Final
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
end PartF


