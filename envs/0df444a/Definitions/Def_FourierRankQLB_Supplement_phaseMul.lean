-- Prove2me | Definitions.Def_FourierRankQLB_Supplement_phaseMul
-- name    : FourierRankQLB_Supplement_phaseMul
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:12:28.638453+00:00
-- url     : https://prove2.me/theorems/2900f068-1c88-4488-83b0-e33f108dda91
-- title:
--   Phase multiplication $\psi(y) \mapsto e^{i\theta(y)}\psi(y)$ on $L^2(Y,\nu)\otimes W$
-- statement:
--   Let $(Y,\nu)$ be a measure space of query labels and $W$ a complex Hilbert space (the algorithm's workspace). The phase-model register is $L^2(Y,\nu)\otimes W$, realized as the Bochner space $L^2(Y,\nu;W)$ of square-integrable $W$-valued wavefunctions. For a measurable real phase $\theta : Y \to \mathbb R$, the **phase multiplication** is the operator
--
--   $$
--   (P_\theta\psi)(y) = e^{i\theta(y)}\,\psi(y).
--   $$
--
--   It is unitary, with inverse $P_{-\theta}$.
--
--   Both phase oracles of the paper, the matrix phase oracle (11) and the gradient phase oracle (58), are phase multiplications for a specific phase.
--
--   **Formalization Note** The operator is constructed as a linear isometric equivalence of $L^2(Y,\nu;W)$; its pointwise formula holds almost everywhere. The workspace $W$ is untouched; there is no answer bit (unlike the membership register of the base mission).
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Eq. (11), p.15; Eq. (58), p.33; Remark 3.6, p.20

import Mathlib

open MeasureTheory

namespace FourierRankQLB

namespace Supplement

/-- The pointwise action `ψ ↦ (y ↦ e^{i θ(y)} ψ(y))` of a phase multiplication on a wavefunction. -/
noncomputable def phaseFun {Y : Type} (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (θ : Y → ℝ) (ψ : Y → W) (y : Y) : W :=
  Complex.exp ((θ y : ℂ) * Complex.I) • ψ y

theorem norm_phaseFun {Y : Type} (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (θ : Y → ℝ) (ψ : Y → W) (y : Y) : ‖phaseFun W θ ψ y‖ = ‖ψ y‖ := by
  simp [phaseFun, norm_smul, Complex.norm_exp_ofReal_mul_I]

theorem phaseFun_neg_phaseFun {Y : Type} (W : Type) [NormedAddCommGroup W]
    [InnerProductSpace ℂ W] (θ : Y → ℝ) (ψ : Y → W) (y : Y) :
    phaseFun W (fun y => -θ y) (phaseFun W θ ψ) y = ψ y := by
  simp only [phaseFun, smul_smul, ← Complex.exp_add]
  simp

theorem memLp_phaseFun {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {θ : Y → ℝ} (hθ : Measurable θ)
    {ψ : Y → W} (hψ : MemLp ψ 2 ν) : MemLp (phaseFun W θ ψ) 2 ν := by
  refine hψ.congr_norm ?_ (ae_of_all _ fun y => (norm_phaseFun W θ ψ y).symm)
  have h1 : Measurable fun y => Complex.exp ((θ y : ℂ) * Complex.I) :=
    Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp hθ).mul_const _)
  exact h1.aestronglyMeasurable.smul hψ.1

/-- Phase multiplication as a linear map on `L²(Y, ν; W)`. -/
noncomputable def phaseLin {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (θ : Y → ℝ) (hθ : Measurable θ) :
    Lp W 2 ν →ₗ[ℂ] Lp W 2 ν where
  toFun ψ := (memLp_phaseFun ν W hθ (Lp.memLp ψ)).toLp _
  map_add' ψ φ := by
    refine Lp.ext ?_
    filter_upwards [(memLp_phaseFun ν W hθ (Lp.memLp (ψ + φ))).coeFn_toLp,
      Lp.coeFn_add ((memLp_phaseFun ν W hθ (Lp.memLp ψ)).toLp _)
        ((memLp_phaseFun ν W hθ (Lp.memLp φ)).toLp _),
      (memLp_phaseFun ν W hθ (Lp.memLp ψ)).coeFn_toLp,
      (memLp_phaseFun ν W hθ (Lp.memLp φ)).coeFn_toLp, Lp.coeFn_add ψ φ] with y h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4]
    simp only [phaseFun, h5, Pi.add_apply, smul_add]
  map_smul' c ψ := by
    refine Lp.ext ?_
    filter_upwards [(memLp_phaseFun ν W hθ (Lp.memLp (c • ψ))).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_phaseFun ν W hθ (Lp.memLp ψ)).toLp _),
      (memLp_phaseFun ν W hθ (Lp.memLp ψ)).coeFn_toLp, Lp.coeFn_smul c ψ] with y h1 h2 h3 h4
    rw [h1]
    simp only [RingHom.id_apply]
    rw [h2, Pi.smul_apply, h3]
    simp only [phaseFun, h4, Pi.smul_apply, smul_comm c]

theorem coeFn_phaseLin {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (θ : Y → ℝ) (hθ : Measurable θ)
    (ψ : Lp W 2 ν) : (phaseLin ν W θ hθ ψ : Y → W) =ᵐ[ν] phaseFun W θ ψ :=
  (memLp_phaseFun ν W hθ (Lp.memLp ψ)).coeFn_toLp

theorem phaseLin_inv {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (θ θ' : Y → ℝ) (hθ : Measurable θ)
    (hθ' : Measurable θ') (h : ∀ y, θ' y = -θ y) (ψ : Lp W 2 ν) :
    phaseLin ν W θ' hθ' (phaseLin ν W θ hθ ψ) = ψ := by
  refine Lp.ext ?_
  have h1 := coeFn_phaseLin ν W θ' hθ' (phaseLin ν W θ hθ ψ)
  have h2 := coeFn_phaseLin ν W θ hθ ψ
  filter_upwards [h1, h2] with y h1 h2
  rw [h1]
  simp only [phaseFun, h2, smul_smul, ← Complex.exp_add, h]
  simp

/-- The phase multiplication `(P_θ ψ)(y) = e^{i θ(y)} ψ(y)` on `L²(Y, ν) ⊗ W = L²(Y, ν; W)`, for a
measurable phase `θ : Y → ℝ`, as a unitary.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Eq. (11), p. 15 (matrix phase oracle), Eq. (58), p. 33 (gradient phase oracle), Remark 3.6, p. 20.

**Formalization Note.** The register is the Bochner space `L²(Y, ν; W)` for a label space `(Y, ν)`
and any complex Hilbert workspace `W`, on which the phase acts only through the label. The inverse
is the phase multiplication by `-θ`. -/
noncomputable def phaseMul {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (θ : Y → ℝ) (hθ : Measurable θ) :
    Lp W 2 ν ≃ₗᵢ[ℂ] Lp W 2 ν :=
  { (LinearEquiv.ofLinearMap (phaseLin ν W θ hθ) (phaseLin ν W (fun y => -θ y) hθ.neg)
      (LinearMap.ext fun ψ => phaseLin_inv ν W _ _ hθ.neg hθ (fun y => (neg_neg _).symm) ψ)
      (LinearMap.ext fun ψ => phaseLin_inv ν W _ _ hθ hθ.neg (fun _ => rfl) ψ) :
        Lp W 2 ν ≃ₗ[ℂ] Lp W 2 ν) with
    norm_map' := fun ψ => by
      change ‖(memLp_phaseFun ν W hθ (Lp.memLp ψ)).toLp _‖ = ‖ψ‖
      rw [Lp.norm_toLp, Lp.norm_def]
      congr 1
      exact eLpNorm_congr_norm_ae (ae_of_all _ fun y => norm_phaseFun W θ ψ y) }

/-- Pointwise formula: `P_θ ψ = e^{i θ} ψ` almost everywhere. -/
theorem coeFn_phaseMul {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (θ : Y → ℝ) (hθ : Measurable θ)
    (ψ : Lp W 2 ν) :
    (phaseMul ν W θ hθ ψ : Y → W) =ᵐ[ν] fun y => Complex.exp ((θ y : ℂ) * Complex.I) • ψ y :=
  coeFn_phaseLin ν W θ hθ ψ

end Supplement

end FourierRankQLB


