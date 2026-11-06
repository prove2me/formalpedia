-- Prove2me | Definitions.Def_FourierRankQLB_flipOn
-- name    : FourierRankQLB_flipOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:39:30.910187+00:00
-- url     : https://prove2.me/theorems/5fa75536-cf22-4efd-ad50-252125f3b8a0
-- title:
--   The coherent membership oracle of a measurable set of labels
-- statement:
--   For a measurable set $S\subseteq Y$ of labels, the unitary on $L^2(Y,\nu)\otimes\mathbb C^2\otimes W$ acting as
--   $$
--   |y\rangle|b\rangle\mapsto|y\rangle|b\oplus\mathbf 1[y\in S]\rangle .
--   $$
--   On a wavefunction $\Psi$ it flips the answer bit of $\Psi(y)$ for $y\in S$ and leaves $\Psi(y)$ alone otherwise.
--
--   Both the grid oracle of Definition 2.2 and the continuous oracle of Appendix A are instances.
--
--   **Formalization Note** The module constructs the operator as a linear isometric equivalence, with its helper `flipFun`.
-- source:
--   Augustino et al., Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank, arXiv:2609.09035, Definition 2.2, Eq. (6), p.14 and Appendix A, p.50

import Mathlib
import Definitions.Def_FourierRankQLB_QReg
import Definitions.Def_FourierRankQLB_swapBit

open MeasureTheory

namespace FourierRankQLB

open scoped Classical in
/-- The pointwise action of the oracle on a wavefunction: flip the answer bit at the labels in `S`. -/
noncomputable def flipFun {Y : Type} (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (S : Set Y) (Ψ : Y → PiLp 2 fun _ : Bool => W) (y : Y) : PiLp 2 fun _ : Bool => W :=
  if y ∈ S then swapBit W (Ψ y) else Ψ y

theorem norm_flipFun {Y : Type} (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (S : Set Y) (Ψ : Y → PiLp 2 fun _ : Bool => W) (y : Y) : ‖flipFun W S Ψ y‖ = ‖Ψ y‖ := by
  unfold flipFun
  split_ifs <;> simp

theorem flipFun_flipFun {Y : Type} (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (S : Set Y) (Ψ : Y → PiLp 2 fun _ : Bool => W) (y : Y) :
    flipFun W S (flipFun W S Ψ) y = Ψ y := by
  unfold flipFun
  split_ifs <;> simp [swapBit_swapBit]

theorem memLp_flipFun {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] {S : Set Y} (hS : MeasurableSet S)
    {Ψ : Y → PiLp 2 fun _ : Bool => W} (hΨ : MemLp Ψ 2 ν) : MemLp (flipFun W S Ψ) 2 ν := by
  refine hΨ.congr_norm ?_ (ae_of_all _ fun y => (norm_flipFun W S Ψ y).symm)
  have h1 : AEStronglyMeasurable (fun y => swapBit W (Ψ y)) ν :=
    (swapBit W).continuous.comp_aestronglyMeasurable hΨ.1
  classical
  have h2 := AEStronglyMeasurable.piecewise hS h1.restrict hΨ.1.restrict
  have : flipFun W S Ψ = S.piecewise (fun y => swapBit W (Ψ y)) Ψ := by
    funext y
    simp only [flipFun, Set.piecewise]
  rwa [this]

/-- The membership oracle `|y⟩|b⟩ ↦ |y⟩|b ⊕ 1[y ∈ S]⟩` on `L²(Y, ν) ⊗ ℂ² ⊗ W`, for a measurable set of
labels `S`, as a unitary.

Augustino et al., *Near-Optimal Quantum Lower Bounds for Convex Optimization via Fourier Rank*, arXiv:2609.09035, Definition 2.2, Eq. (6), p. 14 and Appendix A, p. 50.

**Formalization Note.** It acts on wavefunctions: `(flipOn S Ψ)(y)` is the flip of `Ψ(y)` when
`y ∈ S` and `Ψ(y)` otherwise. The workspace `W` is left alone. -/
noncomputable def flipOn {Y : Type} [MeasurableSpace Y] (ν : Measure Y) (W : Type)
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] (S : Set Y) (hS : MeasurableSet S) :
    QReg ν W ≃ₗᵢ[ℂ] QReg ν W :=
  have hmem : ∀ Ψ : QReg ν W, MemLp (flipFun W S Ψ) 2 ν := fun Ψ =>
    memLp_flipFun ν W hS (Lp.memLp Ψ)
  have hcongr : ∀ {f g : Y → PiLp 2 fun _ : Bool => W}, f =ᵐ[ν] g →
      flipFun W S f =ᵐ[ν] flipFun W S g := fun {f g} h => by
    filter_upwards [h] with y hy
    simp only [flipFun, hy]
  let L : QReg ν W →ₗ[ℂ] QReg ν W :=
    { toFun := fun Ψ => (hmem Ψ).toLp _
      map_add' := fun Ψ Φ => by
        refine Lp.ext ?_
        filter_upwards [(hmem (Ψ + Φ)).coeFn_toLp, Lp.coeFn_add ((hmem Ψ).toLp _) ((hmem Φ).toLp _),
          (hmem Ψ).coeFn_toLp, (hmem Φ).coeFn_toLp, Lp.coeFn_add Ψ Φ] with y h1 h2 h3 h4 h5
        rw [h1, h2, Pi.add_apply, h3, h4]
        simp only [flipFun, h5, Pi.add_apply]
        split_ifs <;> simp
      map_smul' := fun c Ψ => by
        refine Lp.ext ?_
        filter_upwards [(hmem (c • Ψ)).coeFn_toLp, Lp.coeFn_smul c ((hmem Ψ).toLp _),
          (hmem Ψ).coeFn_toLp, Lp.coeFn_smul c Ψ] with y h1 h2 h3 h4
        rw [h1]
        simp only [RingHom.id_apply]
        rw [h2, Pi.smul_apply, h3]
        simp only [flipFun, h4, Pi.smul_apply]
        split_ifs <;> simp }
  have hinv : Function.Involutive L := fun Ψ => by
    refine Lp.ext ?_
    have h1 : (L (L Ψ) : Y → _) =ᵐ[ν] flipFun W S (L Ψ) := (hmem (L Ψ)).coeFn_toLp
    have h2 : flipFun W S (L Ψ) =ᵐ[ν] flipFun W S (flipFun W S Ψ) :=
      hcongr (hmem Ψ).coeFn_toLp
    filter_upwards [h1, h2] with y h1 h2
    rw [h1, h2, flipFun_flipFun]
  { LinearEquiv.ofInvolutive L hinv with
    norm_map' := fun Ψ => by
      change ‖(hmem Ψ).toLp _‖ = ‖Ψ‖
      rw [Lp.norm_toLp, Lp.norm_def]
      congr 1
      exact eLpNorm_congr_norm_ae (ae_of_all _ fun y => norm_flipFun W S Ψ y) }

end FourierRankQLB


