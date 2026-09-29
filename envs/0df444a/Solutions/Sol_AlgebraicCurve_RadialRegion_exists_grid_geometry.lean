-- Prove2me | solution 1 for AlgebraicCurve.RadialRegion.exists_grid_geometry
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.4153+00:00
-- url     : https://prove2.me/submissions/34e552d2-2252-5dc9-9098-d41257738a00

import Mathlib
import Definitions.Def_AlgebraicCurve_CellDissection
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_across_edge
import Theorems.Thm_AlgebraicCurve_RadialRegion_exists_reparam_same_side
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicCurve_RadialRegion_exists_grid_geometry

set_option Elab.async false

section Part_D1GridData

set_option autoImplicit false

open AlgebraicCurve Set
open scoped Real

namespace PlanarRegions

abbrev RectClauses (x₀ x₁ y₀ y₁ : ℝ) (p : ℂ) (yL : ℝ) (_hx₀ : x₀ < p.re) (_hx₁ : p.re < x₁) (_hy₀ : y₀ < p.im) (_hy₁ : p.im < y₁) (_hL₀ : y₀ < yL) (_hL₁ : yL < y₁) (R : RadialRegion) : Prop :=
  R.q = p ∧ R.N = 6 ∧
  R.K = {z : ℂ | z.re ∈ Icc x₀ x₁ ∧ z.im ∈ Icc y₀ y₁} ∧
  R.Kint = {z : ℂ | z.re ∈ Ioo x₀ x₁ ∧ z.im ∈ Ioo y₀ y₁} ∧
  (∀ k : Fin R.N, k.val = 0 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc p.im y₁}) ∧
  (∀ k : Fin R.N, k.val = 1 → R.arcSet k = {z : ℂ | z.im = y₁ ∧ z.re ∈ Icc x₀ x₁}) ∧
  (∀ k : Fin R.N, k.val = 2 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc yL y₁}) ∧
  (∀ k : Fin R.N, k.val = 3 → R.arcSet k = {z : ℂ | z.re = x₀ ∧ z.im ∈ Icc y₀ yL}) ∧
  (∀ k : Fin R.N, k.val = 4 → R.arcSet k = {z : ℂ | z.im = y₀ ∧ z.re ∈ Icc x₀ x₁}) ∧
  (∀ k : Fin R.N, k.val = 5 → R.arcSet k = {z : ℂ | z.re = x₁ ∧ z.im ∈ Icc y₀ p.im}) ∧
  (∀ k : Fin (R.N + 1), k.val = 0 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 1 → R.loop (R.φs k) = ⟨x₁, y₁⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 2 → R.loop (R.φs k) = ⟨x₀, y₁⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 3 → R.loop (R.φs k) = ⟨x₀, yL⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 4 → R.loop (R.φs k) = ⟨x₀, y₀⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 5 → R.loop (R.φs k) = ⟨x₁, y₀⟩) ∧
  (∀ k : Fin (R.N + 1), k.val = 6 → R.loop (R.φs k) = ⟨x₁, p.im⟩) ∧
  (∀ k : Fin R.N, k.val = 0 ∨ k.val = 5 →
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (x₁ - p.re))⁻¹)) ∧
  (∀ k : Fin R.N, k.val = 1 → ∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (y₁ - p.im))⁻¹) ∧
  (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 →
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (p.re - x₀))⁻¹)) ∧
  (∀ k : Fin R.N, k.val = 4 → ∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (p.im - y₀))⁻¹) ∧
  (∀ k : Fin R.N, k.val = 0 → R.arcIcc k ⊆ Ico 0 (π / 2)) ∧
  (∀ k : Fin R.N, k.val = 1 → R.arcIcc k ⊆ Ioo 0 π) ∧
  (∀ k : Fin R.N, k.val = 2 ∨ k.val = 3 → R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
  (∀ k : Fin R.N, k.val = 4 → R.arcIcc k ⊆ Ioo π (2 * π)) ∧
  (∀ k : Fin R.N, k.val = 5 → R.arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
  (∀ z ∈ R.K, z ∉ R.Kint →
  R.loop (if Complex.arg (z - p) < 0 then Complex.arg (z - p) + 2 * π else Complex.arg (z - p))
  = z) ∧
  (∀ (k : Fin R.N) (t₁ t₂ : ℝ), t₁ ∈ R.arcIcc k → t₂ ∈ R.arcIcc k → t₁ ≤ t₂ →
  R.loop '' Icc t₁ t₂ = segment ℝ (R.loop t₁) (R.loop t₂))

abbrev WindowClauses (o hm : ℝ) (_hhm : 0 < hm) (jlo jhi klo khi : ℤ) (_hj : jlo ≤ jhi) (_hk : klo ≤ khi) (cy : ℤ × ℤ → ℝ) (_hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < cy p ∧ cy p < o + (p.2 + 1) * hm) (_hx₀ : o + jlo * hm < 0) (_hx₁ : 0 < o + (jhi + 1) * hm) (_hy₀ : o + klo * hm < 0) (_hy₁ : 0 < o + (khi + 1) * hm) (_hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → cy (jhi, k) = 0) (R : RadialRegion) : Prop :=
  R.q = 0 ∧
  R.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
  z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
  R.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
  z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
  R.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
  (∀ k k' : Fin R.N, R.arcSet k = R.arcSet k' → k = k') ∧
  (∀ k : Fin R.N,
  (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
  R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo π (2 * π)) ∨
  (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
  R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
  z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
  R.arcIcc k ⊆ Ioo 0 π) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))} ∧
  R.loop (R.φs k.castSucc) = ⟨o + jlo * hm, cy (jlo, k₀)⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
  R.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
  (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
  (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
  z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)} ∧
  R.loop (R.φs k.castSucc) = ⟨o + (jhi + 1) * hm, cy (jhi, k₀)⟩ ∧
  R.loop (R.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
  (∀ t ∈ R.arcIcc k, R.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
  (R.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨ R.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
  (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.im = o + klo * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
  (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧ z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (cy (jlo, k₀)) (o + (k₀ + 1) * hm)}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jlo, k₀))}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧ z.im ∈ Icc (o + k₀ * hm) (cy (jhi, k₀))}) ∧
  (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin R.N,
  R.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
  z.im ∈ Icc (cy (jhi, k₀)) (o + (k₀ + 1) * hm)})

structure GridData where
  o : ℝ
  hm : ℝ
  hhm : 0 < hm
  jlo : ℤ
  jhi : ℤ
  klo : ℤ
  khi : ℤ
  hjlt : jlo + 1 < jhi
  hklt : klo + 1 < khi
  ctr : ℤ × ℤ → ℂ
  hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
    (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)
  hzero : (o + jlo * hm < 0 ∧ 0 < o + (jhi + 1) * hm) ∧ (o + klo * hm < 0 ∧
    0 < o + (khi + 1) * hm)
  hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0
  base : ℤ × ℤ → RadialRegion
  hbase : ∀ p : ℤ × ℤ,
      (base p).q = ctr p ∧ (base p).N = 6 ∧
      (base p).K = {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (base p).Kint = {z : ℂ | z.re ∈ Ioo (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Ioo (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (ctr p).im (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcSet k = {z : ℂ | z.im = (o + (p.2 + 1) * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 2 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)
          (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 3 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)}) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcSet k = {z : ℂ | z.im = (o + p.2 * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (ctr p).im}) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 0 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 1 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 2 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 3 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (if p.1 = jlo then (ctr p).im else (ctr
          (p.1 - 1, p.2)).im)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 4 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 5 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 6 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin (base p).N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.cos t / ((o + (p.1 + 1) * hm) - (ctr p).re))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 1 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.sin t / ((o + (p.2 + 1) * hm) - (ctr p).im))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.cos t / ((ctr p).re - (o + p.1 * hm)))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 4 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.sin t / ((ctr p).im - (o + p.2 * hm)))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 → (base p).arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ (base p).K, z ∉ (base p).Kint →
        (base p).loop (if Complex.arg (z - ctr p) < 0 then Complex.arg
          (z - ctr p) + 2 * π else Complex.arg (z - ctr p))
          = z) ∧
      (∀ (k : Fin (base p).N) (t₁ t₂ : ℝ), t₁ ∈ (base p).arcIcc k → t₂ ∈ (base p).arcIcc k →
        t₁ ≤ t₂ →
        (base p).loop '' Icc t₁ t₂ = segment ℝ ((base p).loop t₁) ((base p).loop t₂))
  winReg : RadialRegion
  hwin :
      winReg.q = 0 ∧
      winReg.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin winReg.N, winReg.arcSet k = winReg.arcSet k' → k = k') ∧
      (∀ k : Fin winReg.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)})

namespace GridData

variable (M : GridData)

def sx (p : ℤ × ℤ) : ℝ := M.o + p.1 * M.hm
def sx' (p : ℤ × ℤ) : ℝ := M.o + (p.1 + 1) * M.hm
def sy (p : ℤ × ℤ) : ℝ := M.o + p.2 * M.hm
def sy' (p : ℤ × ℤ) : ℝ := M.o + (p.2 + 1) * M.hm

theorem ctr_mem (p : ℤ × ℤ) :
    (M.sx p < (M.ctr p).re ∧ (M.ctr p).re < M.sx' p) ∧
      (M.sy p < (M.ctr p).im ∧ (M.ctr p).im < M.sy' p) :=
  M.hctr p

noncomputable def yL (p : ℤ × ℤ) : ℝ :=
  if p.1 = M.jlo then (M.ctr p).im else (M.ctr (p.1 - 1, p.2)).im

theorem yL_mem (p : ℤ × ℤ) : M.sy p < M.yL p ∧ M.yL p < M.sy' p := by
  unfold yL
  split_ifs
  · exact (M.ctr_mem p).2
  · have h := (M.ctr_mem (p.1 - 1, p.2)).2
    exact h

def cy (p : ℤ × ℤ) : ℝ := (M.ctr p).im

theorem cy_mem (p : ℤ × ℤ) : M.o + p.2 * M.hm < M.cy p ∧ M.cy p < M.o + (p.2 + 1) * M.hm :=
  (M.ctr_mem p).2

theorem zero_mem_window :
    (M.sx (M.jlo, M.klo) < 0 ∧ 0 < M.sx' (M.jhi, M.khi)) ∧
      (M.sy (M.jlo, M.klo) < 0 ∧ 0 < M.sy' (M.jhi, M.khi)) :=
  M.hzero

theorem cy_zero : ∀ k : ℤ, M.o + k * M.hm < 0 → 0 < M.o + (k + 1) * M.hm → M.cy (M.jhi, k) = 0 :=
  fun k h1 h2 => M.hcy0 k h1 h2

theorem jlo_le_jhi : M.jlo ≤ M.jhi := by have := M.hjlt; omega
theorem klo_le_khi : M.klo ≤ M.khi := by have := M.hklt; omega

theorem base_spec (p : ℤ × ℤ) :
    RectClauses (M.sx p) (M.sx' p) (M.sy p) (M.sy' p) (M.ctr p) (M.yL p)
      (M.ctr_mem p).1.1 (M.ctr_mem p).1.2 (M.ctr_mem p).2.1 (M.ctr_mem p).2.2
      (M.yL_mem p).1 (M.yL_mem p).2 (M.base p) :=
  M.hbase p

theorem base_q (p : ℤ × ℤ) : (M.base p).q = M.ctr p := (M.base_spec p).1
theorem base_N (p : ℤ × ℤ) : (M.base p).N = 6 := (M.base_spec p).2.1

theorem winReg_spec :
    WindowClauses M.o M.hm M.hhm M.jlo M.jhi M.klo M.khi M.jlo_le_jhi M.klo_le_khi M.cy M.cy_mem
      M.zero_mem_window.1.1 M.zero_mem_window.1.2 M.zero_mem_window.2.1 M.zero_mem_window.2.2
      M.cy_zero M.winReg :=
  M.hwin

theorem winReg_q : M.winReg.q = 0 := M.winReg_spec.1
theorem winReg_Kint : M.winReg.Kint =
    {z : ℂ | z.re ∈ Ioo (M.sx (M.jlo, M.klo)) (M.sx' (M.jhi, M.khi)) ∧
      z.im ∈ Ioo (M.sy (M.jlo, M.klo)) (M.sy' (M.jhi, M.khi))} := M.winReg_spec.2.2.1
theorem winReg_N :
    M.winReg.N = 2 * (M.jhi - M.jlo + 1).toNat + 4 * (M.khi - M.klo + 1).toNat :=
  M.winReg_spec.2.2.2.1
theorem two_le_winReg_N : 2 ≤ M.winReg.N := by
  rw [winReg_N]
  have := M.hjlt
  omega

end GridData

end PlanarRegions

end Part_D1GridData

section Part_D1SideId

set_option autoImplicit false

open AlgebraicCurve Set
open scoped Real

namespace SideIdentity

def IsSquare (o hm : ℝ) (j k : ℤ) (c : ℂ) (yL : ℝ) (R : RadialRegion) : Prop :=
  ∃ (hx₀ : o + j*hm < c.re) (hx₁ : c.re < o + (j+1)*hm) (hy₀ : o + k*hm < c.im) (hy₁ : c.im < o + (k+1)*hm)
    (hL₀ : o + k*hm < yL) (hL₁ : yL < o + (k+1)*hm), PlanarRegions.RectClauses (o + j*hm) (o + (j+1)*hm) (o + k*hm) (o + (k+1)*hm) c yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ R

def vseg (x lo hi : ℝ) : Set ℂ := {z : ℂ | z.re = x ∧ z.im ∈ Icc lo hi}

def hseg (y lo hi : ℝ) : Set ℂ := {z : ℂ | z.im = y ∧ z.re ∈ Icc lo hi}

theorem mk_mem_vseg {x lo hi a b : ℝ} : (⟨a, b⟩ : ℂ) ∈ vseg x lo hi ↔ a = x ∧ lo ≤ b ∧ b ≤ hi :=
  Iff.rfl

theorem mk_mem_hseg {y lo hi a b : ℝ} : (⟨a, b⟩ : ℂ) ∈ hseg y lo hi ↔ b = y ∧ lo ≤ a ∧ a ≤ hi :=
  Iff.rfl

theorem vseg_eq_vseg {x lo hi x' lo' hi' : ℝ} (hlt : lo < hi) (h : vseg x lo hi = vseg x' lo' hi') :
    x = x' ∧ lo = lo' ∧ hi = hi' := by
  have h₁ : (⟨x, lo⟩ : ℂ) ∈ vseg x' lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨x, hi⟩ : ℂ) ∈ vseg x' lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, hlt.le, le_rfl⟩
  obtain ⟨e₁, e₂, e₃⟩ := mk_mem_vseg.1 h₁
  obtain ⟨-, -, e₅⟩ := mk_mem_vseg.1 h₂
  have hle' : lo' ≤ hi' := e₂.trans e₃
  have h₃ : (⟨x', lo'⟩ : ℂ) ∈ vseg x lo hi := by
    rw [h]; exact mk_mem_vseg.2 ⟨rfl, le_rfl, hle'⟩
  have h₄ : (⟨x', hi'⟩ : ℂ) ∈ vseg x lo hi := by
    rw [h]; exact mk_mem_vseg.2 ⟨rfl, hle', le_rfl⟩
  obtain ⟨-, e₆, -⟩ := mk_mem_vseg.1 h₃
  obtain ⟨-, -, e₇⟩ := mk_mem_vseg.1 h₄
  exact ⟨e₁, le_antisymm e₆ e₂, le_antisymm e₅ e₇⟩

theorem hseg_eq_hseg {y lo hi y' lo' hi' : ℝ} (hlt : lo < hi) (h : hseg y lo hi = hseg y' lo' hi') :
    y = y' ∧ lo = lo' ∧ hi = hi' := by
  have h₁ : (⟨lo, y⟩ : ℂ) ∈ hseg y' lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨hi, y⟩ : ℂ) ∈ hseg y' lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, hlt.le, le_rfl⟩
  obtain ⟨e₁, e₂, e₃⟩ := mk_mem_hseg.1 h₁
  obtain ⟨-, -, e₅⟩ := mk_mem_hseg.1 h₂
  have hle' : lo' ≤ hi' := e₂.trans e₃
  have h₃ : (⟨lo', y'⟩ : ℂ) ∈ hseg y lo hi := by
    rw [h]; exact mk_mem_hseg.2 ⟨rfl, le_rfl, hle'⟩
  have h₄ : (⟨hi', y'⟩ : ℂ) ∈ hseg y lo hi := by
    rw [h]; exact mk_mem_hseg.2 ⟨rfl, hle', le_rfl⟩
  obtain ⟨-, e₆, -⟩ := mk_mem_hseg.1 h₃
  obtain ⟨-, -, e₇⟩ := mk_mem_hseg.1 h₄
  exact ⟨e₁, le_antisymm e₆ e₂, le_antisymm e₅ e₇⟩

theorem vseg_ne_hseg {x lo hi y lo' hi' : ℝ} (hlt : lo < hi) : vseg x lo hi ≠ hseg y lo' hi' := by
  intro h
  have h₁ : (⟨x, lo⟩ : ℂ) ∈ hseg y lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨x, hi⟩ : ℂ) ∈ hseg y lo' hi' := by
    rw [← h]; exact mk_mem_vseg.2 ⟨rfl, hlt.le, le_rfl⟩
  exact hlt.ne ((mk_mem_hseg.1 h₁).1.trans (mk_mem_hseg.1 h₂).1.symm)

theorem hseg_ne_vseg {y lo hi x lo' hi' : ℝ} (hlt : lo < hi) : hseg y lo hi ≠ vseg x lo' hi' := by
  intro h
  have h₁ : (⟨lo, y⟩ : ℂ) ∈ vseg x lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, le_rfl, hlt.le⟩
  have h₂ : (⟨hi, y⟩ : ℂ) ∈ vseg x lo' hi' := by
    rw [← h]; exact mk_mem_hseg.2 ⟨rfl, hlt.le, le_rfl⟩
  exact hlt.ne ((mk_mem_vseg.1 h₁).1.trans (mk_mem_vseg.1 h₂).1.symm)

theorem eq_of_grid (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {s t : ℝ} (h : o + s * hm = o + t * hm) : s = t := by
  have h' : s * hm = t * hm := by linarith
  exact mul_right_cancel₀ hhm.ne' h'

theorem lt_of_grid (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {s t : ℝ} (h : o + s * hm < o + t * hm) : s < t := by
  have h' : s * hm < t * hm := by linarith
  exact lt_of_mul_lt_mul_right h' hhm.le

theorem int_eq_of_grid₀₀ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm = o + n * hm) :
    m = n := by
  exact_mod_cast eq_of_grid o hhm h

theorem int_eq_of_grid₀₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm = o + (n + 1) * hm) :
    m = n + 1 := by
  exact_mod_cast eq_of_grid o hhm h

theorem int_eq_of_grid₁₀ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + (m + 1) * hm = o + n * hm) :
    m + 1 = n := by
  exact_mod_cast eq_of_grid o hhm h

theorem int_eq_of_grid₁₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ)
    (h : o + (m + 1) * hm = o + (n + 1) * hm) : m = n := by
  have h' := eq_of_grid o hhm h
  have h'' : (m : ℝ) = n := by linarith
  exact_mod_cast h''

theorem int_lt_of_grid₀₀ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm < o + n * hm) :
    m < n := by
  exact_mod_cast lt_of_grid o hhm h

theorem int_lt_of_grid₀₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ) (h : o + m * hm < o + (n + 1) * hm) :
    m < n + 1 := by
  exact_mod_cast lt_of_grid o hhm h

theorem int_lt_of_grid₁₁ (o : ℝ) {hm : ℝ} (hhm : 0 < hm) (m n : ℤ)
    (h : o + (m + 1) * hm < o + (n + 1) * hm) : m < n := by
  have h' := lt_of_grid o hhm h
  have h'' : (m : ℝ) < n := by linarith
  exact_mod_cast h''

structure ArcData (R : RadialRegion) (x₀ x₁ y₀ y₁ yc yL : ℝ) : Prop where
  hx : x₀ < x₁
  hc₀ : y₀ < yc
  hc₁ : yc < y₁
  hL₀ : y₀ < yL
  hL₁ : yL < y₁
  hN : R.N = 6
  arc0 : ∀ a : Fin R.N, a.val = 0 → R.arcSet a = vseg x₁ yc y₁
  arc1 : ∀ a : Fin R.N, a.val = 1 → R.arcSet a = hseg y₁ x₀ x₁
  arc2 : ∀ a : Fin R.N, a.val = 2 → R.arcSet a = vseg x₀ yL y₁
  arc3 : ∀ a : Fin R.N, a.val = 3 → R.arcSet a = vseg x₀ y₀ yL
  arc4 : ∀ a : Fin R.N, a.val = 4 → R.arcSet a = hseg y₀ x₀ x₁
  arc5 : ∀ a : Fin R.N, a.val = 5 → R.arcSet a = vseg x₁ y₀ yc

theorem arcData_of_rectClauses {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {yL : ℝ} {hx₀ : x₀ < p.re} {hx₁ : p.re < x₁}
    {hy₀ : y₀ < p.im} {hy₁ : p.im < y₁} {hL₀ : y₀ < yL} {hL₁ : yL < y₁} {R : RadialRegion}
    (h : PlanarRegions.RectClauses x₀ x₁ y₀ y₁ p yL hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ R) : ArcData R x₀ x₁ y₀ y₁ p.im yL := by
  obtain ⟨-, hN, -, -, h0, h1, h2, h3, h4, h5, -⟩ := h
  exact ⟨hx₀.trans hx₁, hy₀, hy₁, hL₀, hL₁, hN, h0, h1, h2, h3, h4, h5⟩

theorem arcData_of_isSquare {o hm : ℝ} {j k : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm j k c yL R) :
    ArcData R (o + j * hm) (o + (j + 1) * hm) (o + k * hm) (o + (k + 1) * hm) c.im yL := by
  obtain ⟨_, _, _, _, _, _, hc⟩ := h
  exact arcData_of_rectClauses hc

namespace ArcData p2m_export "SideIdentity.ArcData" "right_pair'" end ArcData

theorem ArcData.arcSet_cases {R : RadialRegion} {x₀ x₁ y₀ y₁ yc yL : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (a : Fin R.N) :
    (a.val = 0 ∧ R.arcSet a = vseg x₁ yc y₁) ∨ (a.val = 1 ∧ R.arcSet a = hseg y₁ x₀ x₁) ∨
    (a.val = 2 ∧ R.arcSet a = vseg x₀ yL y₁) ∨ (a.val = 3 ∧ R.arcSet a = vseg x₀ y₀ yL) ∨
    (a.val = 4 ∧ R.arcSet a = hseg y₀ x₀ x₁) ∨ (a.val = 5 ∧ R.arcSet a = vseg x₁ y₀ yc) := by
  have hN := D.hN
  have hlt := a.isLt
  rcases (by omega : a.val = 0 ∨ a.val = 1 ∨ a.val = 2 ∨ a.val = 3 ∨ a.val = 4 ∨ a.val = 5) with
    h | h | h | h | h | h
  · exact Or.inl ⟨h, D.arc0 a h⟩
  · exact Or.inr (Or.inl ⟨h, D.arc1 a h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨h, D.arc2 a h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h, D.arc3 a h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h, D.arc4 a h⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h, D.arc5 a h⟩))))

theorem ArcData.arcSet_injective {R : RadialRegion} {x₀ x₁ y₀ y₁ yc yL : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) : ∀ a a' : Fin R.N, R.arcSet a = R.arcSet a' → a = a' := by
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hy := D.hc₀.trans D.hc₁
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | exact Fin.ext (by omega)
    | exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg (by assumption))
    | refine (vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))
    | exact absurd _e₂ (ne_of_gt (by assumption))

theorem ArcData.right_eq₀₂ {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₁ : y₁' = y₁) (hL : yL' = yc)
    (a : Fin R.N) (ha : a.val = 0) (a' : Fin R'.N) (ha' : a'.val = 2) : R.arcSet a = R'.arcSet a' := by
  subst hx hy₁ hL
  rw [D.arc0 a ha, D'.arc2 a' ha']

theorem ArcData.right_eq₅₃ {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₀ : y₀' = y₀) (hL : yL' = yc)
    (a : Fin R.N) (ha : a.val = 5) (a' : Fin R'.N) (ha' : a'.val = 3) : R.arcSet a = R'.arcSet a' := by
  subst hx hy₀ hL
  rw [D.arc5 a ha, D'.arc3 a' ha']

theorem ArcData.right_pair {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₀ : y₀' = y₀) (hy₁ : y₁' = y₁) (hL : yL' = yc) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  subst hx hy₀ hy₁ hL
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hx' := D'.hx
  have _hc₀' := D'.hc₀
  have _hc₁' := D'.hc₁
  have _hy := D.hc₀.trans D.hc₁
  have _hxx := D.hx.trans D'.hx
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D'.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | omega
    | exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg (by assumption))
    | refine (vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))
    | exact absurd _e₂ (ne_of_gt (by assumption))

theorem ArcData.upper_eq₁₄ {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₂ yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₂ yc' yL')
    (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (hy : y₀' = y₁)
    (a : Fin R.N) (ha : a.val = 1) (a' : Fin R'.N) (ha' : a'.val = 4) : R.arcSet a = R'.arcSet a' := by
  subst hx₀ hx₁ hy
  rw [D.arc1 a ha, D'.arc4 a' ha']

theorem ArcData.upper_pair {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₂ yc' yL' : ℝ}
    (D : ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : ArcData R' x₀' x₁' y₀' y₂ yc' yL')
    (hx₀ : x₀' = x₀) (hx₁ : x₁' = x₁) (hy : y₀' = y₁) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' → a.val = 1 ∧ a'.val = 4 := by
  subst hx₀ hx₁ hy
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hc₀' := D'.hc₀
  have _hc₁' := D'.hc₁
  have _hL₀' := D'.hL₀
  have _hL₁' := D'.hL₁
  have _hy₀₁ := D.hc₀.trans D.hc₁
  have _hy₁₂ := D'.hc₀.trans D'.hc₁
  have _hy₀₂ := _hy₀₁.trans _hy₁₂
  have _hcc := D.hc₁.trans D'.hc₀
  have _hLL := D.hL₁.trans D'.hL₀
  have _hyc' := _hy₀₁.trans D'.hc₀
  have _hyL' := _hy₀₁.trans D'.hL₀
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D'.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | omega
    | exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg (by assumption))
    | refine (vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))

private theorem _root_.SideIdentity.arcSet_injective {o hm : ℝ} {j k : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm j k c yL R) : ∀ a a' : Fin R.N, R.arcSet a = R.arcSet a' → a = a' :=
  (arcData_of_isSquare h).arcSet_injective

p2m_export "SideIdentity" "arcSet_injective"

theorem right_arcSet_eq₀₂ {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm (j+1) k c' yL' R') (hsplit : yL' = c.im) :
    ∀ a : Fin R.N, a.val = 0 → ∀ a' : Fin R'.N, a'.val = 2 → R.arcSet a = R'.arcSet a' := by
  intro a ha a' ha'
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.right_eq₀₂ D' (by simp) rfl hsplit a ha a' ha'

theorem right_arcSet_eq₅₃ {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm (j+1) k c' yL' R') (hsplit : yL' = c.im) :
    ∀ a : Fin R.N, a.val = 5 → ∀ a' : Fin R'.N, a'.val = 3 → R.arcSet a = R'.arcSet a' := by
  intro a ha a' ha'
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.right_eq₅₃ D' (by simp) rfl hsplit a ha a' ha'

theorem right_of_arcSet_eq {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm (j+1) k c' yL' R') (hsplit : yL' = c.im) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.right_pair D' (by simp) rfl rfl hsplit

theorem upper_arcSet_eq₁₄ {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm j (k+1) c' yL' R') :
    ∀ a : Fin R.N, a.val = 1 → ∀ a' : Fin R'.N, a'.val = 4 → R.arcSet a = R'.arcSet a' := by
  intro a ha a' ha'
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.upper_eq₁₄ D' rfl rfl (by simp) a ha a' ha'

theorem upper_of_arcSet_eq {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm j (k+1) c' yL' R') :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' → a.val = 1 ∧ a'.val = 4 := by
  have D := arcData_of_isSquare h
  have D' := arcData_of_isSquare h'
  exact D.upper_pair D' rfl rfl (by simp)

theorem arcSet_shape {o hm : ℝ} {j k : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm j k c yL R) (a : Fin R.N) :
    (∃ (m : ℤ) (lo hi : ℝ), (m = j ∨ m = j + 1) ∧ lo < hi ∧ o + k * hm ≤ lo ∧
      hi ≤ o + (k + 1) * hm ∧ R.arcSet a = vseg (o + m * hm) lo hi) ∨
    (∃ n : ℤ, (n = k ∨ n = k + 1) ∧ o + j * hm < o + (j + 1) * hm ∧
      R.arcSet a = hseg (o + n * hm) (o + j * hm) (o + (j + 1) * hm)) := by
  have D := arcData_of_isSquare h
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · exact Or.inl ⟨j + 1, c.im, o + (k + 1) * hm, Or.inr rfl, D.hc₁, D.hc₀.le, le_rfl,
      by exact_mod_cast ea⟩
  · exact Or.inr ⟨k + 1, Or.inr rfl, D.hx, by exact_mod_cast ea⟩
  · exact Or.inl ⟨j, yL, o + (k + 1) * hm, Or.inl rfl, D.hL₁, D.hL₀.le, le_rfl, ea⟩
  · exact Or.inl ⟨j, o + k * hm, yL, Or.inl rfl, D.hL₀, le_rfl, D.hL₁.le, ea⟩
  · exact Or.inr ⟨k, Or.inl rfl, D.hx, ea⟩
  · exact Or.inl ⟨j + 1, o + k * hm, c.im, Or.inr rfl, D.hc₀, le_rfl, D.hc₁.le,
      by exact_mod_cast ea⟩

theorem locality {o hm : ℝ} (hhm : 0 < hm) {j k j' k' : ℤ} {c c' : ℂ} {yL yL' : ℝ}
    {R R' : RadialRegion} (h : IsSquare o hm j k c yL R) (h' : IsSquare o hm j' k' c' yL' R')
    (a : Fin R.N) (a' : Fin R'.N) :
    R.arcSet a = R'.arcSet a' →
    (j' = j ∧ k' = k) ∨ (j' = j + 1 ∧ k' = k) ∨ (j = j' + 1 ∧ k' = k) ∨ (j' = j ∧ k' = k + 1) ∨ (j' = j ∧ k = k' + 1) := by
  intro heq
  rcases arcSet_shape h a with ⟨m, lo, hi, hmj, hlt, hlo, hhi, ea⟩ | ⟨n, hn, hxx, ea⟩
  · rcases arcSet_shape h' a' with ⟨m', lo', hi', hmj', -, hlo', hhi', ea'⟩ | ⟨_, -, -, ea'⟩
    · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg hlt (ea.symm.trans (heq.trans ea'))
      have hmm := int_eq_of_grid₀₀ o hhm m m' e₁
      have hk₁ := int_lt_of_grid₀₁ o hhm k k' (by linarith)
      have hk₂ := int_lt_of_grid₀₁ o hhm k' k (by linarith)
      omega
    · exact absurd (ea.symm.trans (heq.trans ea')) (vseg_ne_hseg hlt)
  · rcases arcSet_shape h' a' with ⟨_, _, _, -, -, -, -, ea'⟩ | ⟨n', hn', -, ea'⟩
    · exact absurd (ea.symm.trans (heq.trans ea')) (hseg_ne_vseg hxx)
    · obtain ⟨e₁, e₂, -⟩ := hseg_eq_hseg hxx (ea.symm.trans (heq.trans ea'))
      have hnn := int_eq_of_grid₀₀ o hhm n n' e₁
      have hjj := int_eq_of_grid₀₀ o hhm j j' e₂
      omega

theorem rightUpper_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : j ≤ J) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 0 ∧ c.im = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + (J + 1) * hm) y (o + (K + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨h0, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₁₁ o hhm j J e₁, int_eq_of_grid₁₁ o hhm k K e₃, h0, e₂⟩
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨-, -, e₃⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₁ o hhm k K (by linarith [D.hc₀])
    have h₂ := int_lt_of_grid₁₁ o hhm K k (by linarith [D.hc₁])
    exfalso; omega

theorem rightLower_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : j ≤ J) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc (o + K * hm) y}) :
    j = J ∧ k = K ∧ a.val = 5 ∧ c.im = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + (J + 1) * hm) (o + K * hm) y := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h5, ea⟩
  · obtain ⟨-, e₂, -⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₀ o hhm k K (by linarith [D.hc₀])
    have h₂ := int_lt_of_grid₀₁ o hhm K k (by linarith [D.hc₁])
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₁₁ o hhm j J e₁, int_eq_of_grid₀₀ o hhm k K e₂, h5, e₃⟩

theorem leftUpper_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : J ≤ j) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 2 ∧ yL = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + J * hm) y (o + (K + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h2, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₁, int_eq_of_grid₁₁ o hhm k K e₃, h2, e₂⟩
  · obtain ⟨-, -, e₃⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₁ o hhm k K (by linarith [D.hL₀])
    have h₂ := int_lt_of_grid₁₁ o hhm K k (by linarith [D.hL₁])
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega

theorem leftLower_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hj : J ≤ j) {y : ℝ} (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc (o + K * hm) y}) :
    j = J ∧ k = K ∧ a.val = 3 ∧ yL = y := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = vseg (o + J * hm) (o + K * hm) y := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h3, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₁ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨-, e₂, -⟩ := vseg_eq_vseg D.hL₁ (ea.symm.trans ha')
    have h₁ := int_lt_of_grid₀₀ o hhm k K (by linarith [D.hL₀])
    have h₂ := int_lt_of_grid₀₁ o hhm K k (by linarith [D.hL₁])
    exfalso; omega
  · obtain ⟨e₁, e₂, e₃⟩ := vseg_eq_vseg D.hL₀ (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₁, int_eq_of_grid₀₀ o hhm k K e₂, h3, e₃⟩
  · exact absurd (ea.symm.trans ha') (hseg_ne_vseg D.hx)
  · obtain ⟨e₁, -, -⟩ := vseg_eq_vseg D.hc₀ (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm j J e₁
    exfalso; omega

theorem bottom_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hk : K ≤ k) (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.im = o + K * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 4 := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = hseg (o + K * hm) (o + J * hm) (o + (J + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨h4, ea⟩ | ⟨-, ea⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₁)
  · obtain ⟨e₁, -, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    have := int_eq_of_grid₁₀ o hhm k K e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₁)
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₀)
  · obtain ⟨e₁, e₂, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₂, int_eq_of_grid₀₀ o hhm k K e₁, h4⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₀)

theorem top_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k : ℤ} {c : ℂ} {yL : ℝ}
    {R : RadialRegion} (h : IsSquare o hm j k c yL R) {J K : ℤ} (hk : k ≤ K) (a : Fin R.N)
    (ha : R.arcSet a = {z : ℂ | z.im = o + (K + 1) * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)}) :
    j = J ∧ k = K ∧ a.val = 1 := by
  have D := arcData_of_isSquare h
  have ha' : R.arcSet a = hseg (o + (K + 1) * hm) (o + J * hm) (o + (J + 1) * hm) := ha
  rcases D.arcSet_cases a with ⟨-, ea⟩ | ⟨h1, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩ | ⟨-, ea⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₁)
  · obtain ⟨e₁, e₂, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    exact ⟨int_eq_of_grid₀₀ o hhm j J e₂, int_eq_of_grid₁₁ o hhm k K e₁, h1⟩
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₁)
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hL₀)
  · obtain ⟨e₁, -, -⟩ := hseg_eq_hseg D.hx (ea.symm.trans ha')
    have := int_eq_of_grid₀₁ o hhm k K e₁
    exfalso; omega
  · exact absurd (ea.symm.trans ha') (vseg_ne_hseg D.hc₀)

theorem arcSet_eq_rightUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) (a : Fin R.N) (ha : a.val = 0) :
    R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  subst hy
  exact (arcData_of_isSquare h).arc0 a ha

theorem arcSet_eq_rightLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) (a : Fin R.N) (ha : a.val = 5) :
    R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  subst hy
  exact (arcData_of_isSquare h).arc5 a ha

theorem arcSet_eq_leftUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) (a : Fin R.N) (ha : a.val = 2) :
    R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  subst hy
  exact (arcData_of_isSquare h).arc2 a ha

theorem arcSet_eq_leftLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) (a : Fin R.N) (ha : a.val = 3) :
    R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  subst hy
  exact (arcData_of_isSquare h).arc3 a ha

theorem arcSet_eq_bottom {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) (a : Fin R.N) (ha : a.val = 4) :
    R.arcSet a = {z : ℂ | z.im = o + K * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} :=
  (arcData_of_isSquare h).arc4 a ha

theorem arcSet_eq_top {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) (a : Fin R.N) (ha : a.val = 1) :
    R.arcSet a = {z : ℂ | z.im = o + (K + 1) * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} :=
  (arcData_of_isSquare h).arc1 a ha

theorem exists_arcSet_eq_rightUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) :
    ∃ a : Fin R.N, a.val = 0 ∧
      R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨0, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_rightUpper h hy _ rfl

theorem exists_arcSet_eq_rightLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : c.im = y) :
    ∃ a : Fin R.N, a.val = 5 ∧
      R.arcSet a = {z : ℂ | z.re = o + (J + 1) * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨5, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_rightLower h hy _ rfl

theorem exists_arcSet_eq_leftUpper {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) :
    ∃ a : Fin R.N, a.val = 2 ∧
      R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc y (o + (K + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨2, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_leftUpper h hy _ rfl

theorem exists_arcSet_eq_leftLower {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) {y : ℝ} (hy : yL = y) :
    ∃ a : Fin R.N, a.val = 3 ∧
      R.arcSet a = {z : ℂ | z.re = o + J * hm ∧ z.im ∈ Icc (o + K * hm) y} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨3, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_leftLower h hy _ rfl

theorem exists_arcSet_eq_bottom {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) :
    ∃ a : Fin R.N, a.val = 4 ∧
      R.arcSet a = {z : ℂ | z.im = o + K * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨4, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_bottom h _ rfl

theorem exists_arcSet_eq_top {o hm : ℝ} {J K : ℤ} {c : ℂ} {yL : ℝ} {R : RadialRegion}
    (h : IsSquare o hm J K c yL R) :
    ∃ a : Fin R.N, a.val = 1 ∧
      R.arcSet a = {z : ℂ | z.im = o + (K + 1) * hm ∧ z.re ∈ Icc (o + J * hm) (o + (J + 1) * hm)} := by
  have hN := (arcData_of_isSquare h).hN
  refine ⟨⟨1, by omega⟩, rfl, ?_⟩
  exact arcSet_eq_top h _ rfl

end SideIdentity

end Part_D1SideId

section Part_D1Verts

set_option autoImplicit false

open AlgebraicCurve Set
open scoped Real

noncomputable section

namespace GridVertices

theorem strip_ne_grid (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {k m : ℤ} {y : ℝ} (h₀ : o + k * hm < y)
    (h₁ : y < o + (k + 1) * hm) (h : y = o + m * hm) : False := by
  subst h
  have h₂ := SideIdentity.int_lt_of_grid₀₀ o hhm k m h₀
  have h₃ := SideIdentity.int_lt_of_grid₀₁ o hhm m k h₁
  omega

theorem strip_eq_strip (o : ℝ) {hm : ℝ} (hhm : 0 < hm) {k k' : ℤ} {y y' : ℝ} (h₀ : o + k * hm < y)
    (h₁ : y < o + (k + 1) * hm) (h₀' : o + k' * hm < y') (h₁' : y' < o + (k' + 1) * hm) (h : y = y') :
    k = k' := by
  subst h
  have l₁ := h₀.trans h₁'
  have l₂ := h₀'.trans h₁
  have i₁ := SideIdentity.int_lt_of_grid₀₁ o hhm k k' l₁
  have i₂ := SideIdentity.int_lt_of_grid₀₁ o hhm k' k l₂
  omega

theorem complex_mk_eq {a b c d : ℝ} (h₁ : a = c) (h₂ : b = d) : (⟨a, b⟩ : ℂ) = ⟨c, d⟩ := by
  subst h₁
  subst h₂
  rfl

private def _root_.GridVertices.yL (jlo : ℤ) (ctr : ℤ × ℤ → ℂ) (p : ℤ × ℤ) : ℝ :=
  if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im

p2m_export "GridVertices" "yL"

def cornerPt (o hm : ℝ) (q : ℤ × ℤ) : ℂ := ⟨o + q.1 * hm, o + q.2 * hm⟩

def rightPt (o hm : ℝ) (ctr : ℤ × ℤ → ℂ) (q : ℤ × ℤ) : ℂ := ⟨o + (q.1 + 1) * hm, (ctr q).im⟩

def leftPt (o hm : ℝ) (jlo : ℤ) (ctr : ℤ × ℤ → ℂ) (k : ℤ) : ℂ := ⟨o + jlo * hm, (ctr (jlo, k)).im⟩

def corners (o hm : ℝ) (jlo jhi klo khi : ℤ) : Finset ℂ :=
  (Finset.Icc jlo (jhi + 1) ×ˢ Finset.Icc klo (khi + 1)).image (cornerPt o hm)

def rights (o hm : ℝ) (jlo jhi klo khi : ℤ) (ctr : ℤ × ℤ → ℂ) : Finset ℂ :=
  (Finset.Icc jlo jhi ×ˢ Finset.Icc klo khi).image (rightPt o hm ctr)

def lefts (o hm : ℝ) (jlo klo khi : ℤ) (ctr : ℤ × ℤ → ℂ) : Finset ℂ :=
  (Finset.Icc klo khi).image (leftPt o hm jlo ctr)

def B₀ (o hm : ℝ) (jlo jhi klo khi : ℤ) (ctr : ℤ × ℤ → ℂ) : Finset ℂ :=
  corners o hm jlo jhi klo khi ∪ rights o hm jlo jhi klo khi ctr ∪ lefts o hm jlo klo khi ctr

variable {o hm : ℝ} {jlo jhi klo khi : ℤ} {ctr : ℤ × ℤ → ℂ}

theorem yL_of_eq {j : ℤ} (hj : j = jlo) (k : ℤ) : yL jlo ctr (j, k) = (ctr (j, k)).im := by
  simp [yL, hj]

theorem yL_of_ne {j : ℤ} (hj : j ≠ jlo) (k : ℤ) : yL jlo ctr (j, k) = (ctr (j - 1, k)).im := by
  simp [yL, hj]

theorem yL_left (k : ℤ) : yL jlo ctr (jlo, k) = (ctr (jlo, k)).im :=
  yL_of_eq rfl k

theorem mem_corners {v : ℂ} :
    v ∈ corners o hm jlo jhi klo khi ↔
      ∃ j k : ℤ, jlo ≤ j ∧ j ≤ jhi + 1 ∧ klo ≤ k ∧ k ≤ khi + 1 ∧ v = (⟨o + j * hm, o + k * hm⟩ : ℂ) := by
  unfold corners
  constructor
  · intro h
    obtain ⟨⟨j, k⟩, hq, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hj, hk⟩ := Finset.mem_product.mp hq
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
  · rintro ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
    exact Finset.mem_image.mpr ⟨(j, k),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hj₁, hj₂⟩, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩⟩, rfl⟩

theorem mem_rights {v : ℂ} :
    v ∈ rights o hm jlo jhi klo khi ctr ↔
      ∃ j k : ℤ, jlo ≤ j ∧ j ≤ jhi ∧ klo ≤ k ∧ k ≤ khi ∧
        v = (⟨o + (j + 1) * hm, (ctr (j, k)).im⟩ : ℂ) := by
  unfold rights
  constructor
  · intro h
    obtain ⟨⟨j, k⟩, hq, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hj, hk⟩ := Finset.mem_product.mp hq
    obtain ⟨hj₁, hj₂⟩ := Finset.mem_Icc.mp hj
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
  · rintro ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩
    exact Finset.mem_image.mpr ⟨(j, k),
      Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hj₁, hj₂⟩, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩⟩, rfl⟩

theorem mem_lefts {v : ℂ} :
    v ∈ lefts o hm jlo klo khi ctr ↔
      ∃ k : ℤ, klo ≤ k ∧ k ≤ khi ∧ v = (⟨o + jlo * hm, (ctr (jlo, k)).im⟩ : ℂ) := by
  unfold lefts
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hk₁, hk₂⟩ := Finset.mem_Icc.mp hk
    exact ⟨k, hk₁, hk₂, rfl⟩
  · rintro ⟨k, hk₁, hk₂, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk₁, hk₂⟩, rfl⟩

theorem mem_B₀ {v : ℂ} :
    v ∈ B₀ o hm jlo jhi klo khi ctr ↔
      v ∈ corners o hm jlo jhi klo khi ∨ v ∈ rights o hm jlo jhi klo khi ctr ∨
        v ∈ lefts o hm jlo klo khi ctr := by
  unfold B₀
  simp only [Finset.mem_union, or_assoc]

theorem corner_mem_B₀ (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi + 1) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi + 1)
    {a b : ℝ} (ha : a = o + j * hm) (hb : b = o + k * hm) :
    (⟨a, b⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  subst ha
  subst hb
  refine mem_B₀.mpr (Or.inl ?_)
  exact mem_corners.mpr ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩

theorem right_mem_B₀ (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi) :
    (⟨o + (j + 1) * hm, (ctr (j, k)).im⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  refine mem_B₀.mpr (Or.inr (Or.inl ?_))
  exact mem_rights.mpr ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩

theorem right_mem_B₀_of_eq (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi)
    {a : ℝ} (ha : a = o + (j + 1) * hm) : (⟨a, (ctr (j, k)).im⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  subst ha
  exact right_mem_B₀ j k hj₁ hj₂ hk₁ hk₂

theorem left_mem_B₀ (k : ℤ) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi) :
    (⟨o + jlo * hm, (ctr (jlo, k)).im⟩ : ℂ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  refine mem_B₀.mpr (Or.inr (Or.inr ?_))
  exact mem_lefts.mpr ⟨k, hk₁, hk₂, rfl⟩

theorem cornerPt_injective (hhm : 0 < hm) : Function.Injective (cornerPt o hm) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h₁ : o + (a : ℝ) * hm = o + (a' : ℝ) * hm := congrArg Complex.re h
  have h₂ : o + (b : ℝ) * hm = o + (b' : ℝ) * hm := congrArg Complex.im h
  have ha : a = a' := SideIdentity.int_eq_of_grid₀₀ o hhm a a' h₁
  have hb : b = b' := SideIdentity.int_eq_of_grid₀₀ o hhm b b' h₂
  subst ha
  subst hb
  rfl

theorem rightPt_injective (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Function.Injective (rightPt o hm ctr) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h' : (⟨o + ((a : ℝ) + 1) * hm, (ctr (a, b)).im⟩ : ℂ) = ⟨o + ((a' : ℝ) + 1) * hm, (ctr (a', b')).im⟩ := h
  obtain ⟨h₁, h₂⟩ := Complex.mk.inj h'
  have ha : a = a' := SideIdentity.int_eq_of_grid₁₁ o hhm a a' h₁
  have hb₀ : o + (b : ℝ) * hm < (ctr (a, b)).im := (hctr (a, b)).2.1
  have hb₁ : (ctr (a, b)).im < o + ((b : ℝ) + 1) * hm := (hctr (a, b)).2.2
  have hb₀' : o + (b' : ℝ) * hm < (ctr (a', b')).im := (hctr (a', b')).2.1
  have hb₁' : (ctr (a', b')).im < o + ((b' : ℝ) + 1) * hm := (hctr (a', b')).2.2
  have hb : b = b' := strip_eq_strip o hhm hb₀ hb₁ hb₀' hb₁' h₂
  subst ha
  subst hb
  rfl

theorem leftPt_injective (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Function.Injective (leftPt o hm jlo ctr) := by
  intro b b' h
  have h' : (⟨o + (jlo : ℝ) * hm, (ctr (jlo, b)).im⟩ : ℂ) = ⟨o + (jlo : ℝ) * hm, (ctr (jlo, b')).im⟩ := h
  obtain ⟨-, h₂⟩ := Complex.mk.inj h'
  have hb₀ : o + (b : ℝ) * hm < (ctr (jlo, b)).im := (hctr (jlo, b)).2.1
  have hb₁ : (ctr (jlo, b)).im < o + ((b : ℝ) + 1) * hm := (hctr (jlo, b)).2.2
  have hb₀' : o + (b' : ℝ) * hm < (ctr (jlo, b')).im := (hctr (jlo, b')).2.1
  have hb₁' : (ctr (jlo, b')).im < o + ((b' : ℝ) + 1) * hm := (hctr (jlo, b')).2.2
  exact strip_eq_strip o hhm hb₀ hb₁ hb₀' hb₁' h₂

theorem card_corners (hhm : 0 < hm) (hj : jlo ≤ jhi) (hk : klo ≤ khi) :
    (corners o hm jlo jhi klo khi).card = ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) := by
  have h₁ : (Finset.Icc jlo (jhi + 1)).card = (jhi - jlo + 1).toNat + 1 := by
    rw [Int.card_Icc]
    omega
  have h₂ : (Finset.Icc klo (khi + 1)).card = (khi - klo + 1).toNat + 1 := by
    rw [Int.card_Icc]
    omega
  unfold corners
  rw [Finset.card_image_of_injective _ (cornerPt_injective hhm), Finset.card_product, h₁, h₂]

theorem card_rights (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    (rights o hm jlo jhi klo khi ctr).card = (jhi - jlo + 1).toNat * (khi - klo + 1).toNat := by
  have h₁ : (Finset.Icc jlo jhi).card = (jhi - jlo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  have h₂ : (Finset.Icc klo khi).card = (khi - klo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  unfold rights
  rw [Finset.card_image_of_injective _ (rightPt_injective hhm hctr), Finset.card_product, h₁, h₂]

theorem card_lefts (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    (lefts o hm jlo klo khi ctr).card = (khi - klo + 1).toNat := by
  have h₁ : (Finset.Icc klo khi).card = (khi - klo + 1).toNat := by
    rw [Int.card_Icc]
    omega
  unfold lefts
  rw [Finset.card_image_of_injective _ (leftPt_injective hhm hctr), h₁]

theorem disjoint_corners_rights (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Disjoint (corners o hm jlo jhi klo khi) (rights o hm jlo jhi klo khi ctr) := by
  rw [Finset.disjoint_left]
  intro v hc hr
  obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_corners.mp hc
  obtain ⟨j', k', -, -, -, -, he⟩ := mem_rights.mp hr
  have h₂ : o + (k : ℝ) * hm = (ctr (j', k')).im := congrArg Complex.im he
  have hk₀ : o + (k' : ℝ) * hm < (ctr (j', k')).im := (hctr (j', k')).2.1
  have hk₁ : (ctr (j', k')).im < o + ((k' : ℝ) + 1) * hm := (hctr (j', k')).2.2
  exact strip_ne_grid o hhm hk₀ hk₁ h₂.symm

theorem disjoint_corners_lefts (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm)) :
    Disjoint (corners o hm jlo jhi klo khi) (lefts o hm jlo klo khi ctr) := by
  rw [Finset.disjoint_left]
  intro v hc hl
  obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_corners.mp hc
  obtain ⟨k', -, -, he⟩ := mem_lefts.mp hl
  have h₂ : o + (k : ℝ) * hm = (ctr (jlo, k')).im := congrArg Complex.im he
  have hk₀ : o + (k' : ℝ) * hm < (ctr (jlo, k')).im := (hctr (jlo, k')).2.1
  have hk₁ : (ctr (jlo, k')).im < o + ((k' : ℝ) + 1) * hm := (hctr (jlo, k')).2.2
  exact strip_ne_grid o hhm hk₀ hk₁ h₂.symm

theorem disjoint_rights_lefts (hhm : 0 < hm) :
    Disjoint (rights o hm jlo jhi klo khi ctr) (lefts o hm jlo klo khi ctr) := by
  rw [Finset.disjoint_left]
  intro v hr hl
  obtain ⟨j, k, hj₁, -, -, -, rfl⟩ := mem_rights.mp hr
  obtain ⟨k', -, -, he⟩ := mem_lefts.mp hl
  have h₁ : o + ((j : ℝ) + 1) * hm = o + (jlo : ℝ) * hm := congrArg Complex.re he
  have h₃ : j + 1 = jlo := SideIdentity.int_eq_of_grid₁₀ o hhm j jlo h₁
  omega

theorem card_B₀ (hhm : 0 < hm)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm))
    (hj : jlo ≤ jhi) (hk : klo ≤ khi) :
    (B₀ o hm jlo jhi klo khi ctr).card =
      ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) +
        (jhi - jlo + 1).toNat * (khi - klo + 1).toNat + (khi - klo + 1).toNat := by
  have d₁ : Disjoint (corners o hm jlo jhi klo khi) (rights o hm jlo jhi klo khi ctr) :=
    disjoint_corners_rights hhm hctr
  have d₂ : Disjoint (corners o hm jlo jhi klo khi ∪ rights o hm jlo jhi klo khi ctr)
      (lefts o hm jlo klo khi ctr) :=
    Finset.disjoint_union_left.mpr ⟨disjoint_corners_lefts hhm hctr, disjoint_rights_lefts hhm⟩
  have c₁ := card_corners (o := o) hhm hj hk
  have c₂ := card_rights (jlo := jlo) (jhi := jhi) (klo := klo) (khi := khi) hhm hctr
  have c₃ := card_lefts (jlo := jlo) (klo := klo) (khi := khi) hhm hctr
  unfold B₀
  rw [Finset.card_union_of_disjoint d₂, Finset.card_union_of_disjoint d₁, c₁, c₂, c₃]

structure BreakData (R : RadialRegion) (x₀ x₁ y₀ y₁ yc ys : ℝ) : Prop where
  hN : R.N = 6
  b0 : ∀ i : Fin (R.N + 1), i.val = 0 → R.loop (R.φs i) = ⟨x₁, yc⟩
  b1 : ∀ i : Fin (R.N + 1), i.val = 1 → R.loop (R.φs i) = ⟨x₁, y₁⟩
  b2 : ∀ i : Fin (R.N + 1), i.val = 2 → R.loop (R.φs i) = ⟨x₀, y₁⟩
  b3 : ∀ i : Fin (R.N + 1), i.val = 3 → R.loop (R.φs i) = ⟨x₀, ys⟩
  b4 : ∀ i : Fin (R.N + 1), i.val = 4 → R.loop (R.φs i) = ⟨x₀, y₀⟩
  b5 : ∀ i : Fin (R.N + 1), i.val = 5 → R.loop (R.φs i) = ⟨x₁, y₀⟩
  b6 : ∀ i : Fin (R.N + 1), i.val = 6 → R.loop (R.φs i) = ⟨x₁, yc⟩

theorem breakData_of_rectClauses {x₀ x₁ y₀ y₁ : ℝ} {p : ℂ} {ys : ℝ} {hx₀ : x₀ < p.re} {hx₁ : p.re < x₁}
    {hy₀ : y₀ < p.im} {hy₁ : p.im < y₁} {hL₀ : y₀ < ys} {hL₁ : ys < y₁} {R : RadialRegion}
    (h : PlanarRegions.RectClauses x₀ x₁ y₀ y₁ p ys hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ R) : BreakData R x₀ x₁ y₀ y₁ p.im ys := by
  obtain ⟨-, hN, -, -, -, -, -, -, -, -, b0, b1, b2, b3, b4, b5, b6, -⟩ := h
  exact ⟨hN, b0, b1, b2, b3, b4, b5, b6⟩

theorem rect_break_mem_of (j k : ℤ) (hj₁ : jlo ≤ j) (hj₂ : j ≤ jhi) (hk₁ : klo ≤ k) (hk₂ : k ≤ khi)
    {hx₀ : o + j * hm < (ctr (j, k)).re} {hx₁ : (ctr (j, k)).re < o + (j + 1) * hm}
    {hy₀ : o + k * hm < (ctr (j, k)).im} {hy₁ : (ctr (j, k)).im < o + (k + 1) * hm}
    {hL₀ : o + k * hm < yL jlo ctr (j, k)} {hL₁ : yL jlo ctr (j, k) < o + (k + 1) * hm} {R : RadialRegion}
    (h : PlanarRegions.RectClauses (o + j * hm) (o + (j + 1) * hm) (o + k * hm) (o + (k + 1) * hm) (ctr (j, k))
      (yL jlo ctr (j, k)) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ R)
    (i : Fin (R.N + 1)) : R.loop (R.φs i) ∈ B₀ o hm jlo jhi klo khi ctr := by
  have D := breakData_of_rectClauses h
  have hN := D.hN
  have hi := i.isLt
  rcases (by omega : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6) with
    h0 | h1 | h2 | h3 | h4 | h5 | h6
  · rw [D.b0 i h0]
    exact right_mem_B₀ j k hj₁ hj₂ hk₁ hk₂
  · rw [D.b1 i h1]
    exact corner_mem_B₀ (j + 1) (k + 1) (by omega) (by omega) (by omega) (by omega)
      (by push_cast; ring) (by push_cast; ring)
  · rw [D.b2 i h2]
    exact corner_mem_B₀ j (k + 1) (by omega) (by omega) (by omega) (by omega) rfl (by push_cast; ring)
  · rw [D.b3 i h3]
    by_cases hj : j = jlo
    · rw [yL_of_eq hj k, hj]
      exact left_mem_B₀ k hk₁ hk₂
    · rw [yL_of_ne hj k]
      exact right_mem_B₀_of_eq (j - 1) k (by omega) (by omega) hk₁ hk₂ (by push_cast; ring)
  · rw [D.b4 i h4]
    exact corner_mem_B₀ j k (by omega) (by omega) (by omega) (by omega) rfl rfl
  · rw [D.b5 i h5]
    exact corner_mem_B₀ (j + 1) k (by omega) (by omega) (by omega) (by omega) (by push_cast; ring) rfl
  · rw [D.b6 i h6]
    exact right_mem_B₀ j k hj₁ hj₂ hk₁ hk₂

theorem rect_break_mem (p : ℤ × ℤ) (hp₁ : jlo ≤ p.1) (hp₂ : p.1 ≤ jhi) (hp₃ : klo ≤ p.2) (hp₄ : p.2 ≤ khi)
    {hx₀ : o + p.1 * hm < (ctr p).re} {hx₁ : (ctr p).re < o + (p.1 + 1) * hm}
    {hy₀ : o + p.2 * hm < (ctr p).im} {hy₁ : (ctr p).im < o + (p.2 + 1) * hm}
    {hL₀ : o + p.2 * hm < yL jlo ctr p} {hL₁ : yL jlo ctr p < o + (p.2 + 1) * hm} {R : RadialRegion}
    (h : PlanarRegions.RectClauses (o + p.1 * hm) (o + (p.1 + 1) * hm) (o + p.2 * hm) (o + (p.2 + 1) * hm) (ctr p)
      (yL jlo ctr p) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ R)
    (i : Fin (R.N + 1)) : R.loop (R.φs i) ∈ B₀ o hm jlo jhi klo khi ctr := by
  obtain ⟨j, k⟩ := p
  exact rect_break_mem_of j k hp₁ hp₂ hp₃ hp₄ h i

theorem window_break_mem {hhm : 0 < hm} {hj : jlo ≤ jhi} {hk : klo ≤ khi}
    {hcy : ∀ p : ℤ × ℤ, o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm}
    {hx₀ : o + jlo * hm < 0} {hx₁ : 0 < o + (jhi + 1) * hm} {hy₀ : o + klo * hm < 0}
    {hy₁ : 0 < o + (khi + 1) * hm}
    {hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0} {R : RadialRegion}
    (hW : PlanarRegions.WindowClauses o hm hhm jlo jhi klo khi hj hk (fun p => (ctr p).im) hcy hx₀ hx₁ hy₀ hy₁ hcy0 R)
    (k : Fin R.N) :
    R.loop (R.φs k.castSucc) ∈ B₀ o hm jlo jhi klo khi ctr ∧
      R.loop (R.φs k.succ) ∈ B₀ o hm jlo jhi klo khi ctr := by
  obtain ⟨-, -, -, -, -, harc, -⟩ := hW
  rcases harc k with ⟨j, hj₁, hj₂, -, e₁, e₂, -⟩ | ⟨j, hj₁, hj₂, -, e₁, e₂, -⟩ |
    ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩ | ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩ | ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩ |
    ⟨k₀, hk₁, hk₂, -, e₁, e₂, -⟩
  ·
    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ j klo (by omega) (by omega) (by omega) (by omega) rfl rfl,
      corner_mem_B₀ (j + 1) klo (by omega) (by omega) (by omega) (by omega) (by push_cast; ring) rfl⟩
  ·
    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ (j + 1) (khi + 1) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring) (by push_cast; ring),
      corner_mem_B₀ j (khi + 1) (by omega) (by omega) (by omega) (by omega) rfl (by push_cast; ring)⟩
  ·
    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ jlo (k₀ + 1) (by omega) (by omega) (by omega) (by omega) rfl (by push_cast; ring),
      left_mem_B₀ k₀ hk₁ hk₂⟩
  ·
    rw [e₁, e₂]
    exact ⟨left_mem_B₀ k₀ hk₁ hk₂,
      corner_mem_B₀ jlo k₀ (by omega) (by omega) (by omega) (by omega) rfl rfl⟩
  ·

    rw [e₁, e₂]
    exact ⟨corner_mem_B₀ (jhi + 1) k₀ (by omega) (by omega) (by omega) (by omega) (by push_cast; ring) rfl,
      right_mem_B₀ jhi k₀ hj le_rfl hk₁ hk₂⟩
  ·
    rw [e₁, e₂]
    exact ⟨right_mem_B₀ jhi k₀ hj le_rfl hk₁ hk₂,
      corner_mem_B₀ (jhi + 1) (k₀ + 1) (by omega) (by omega) (by omega) (by omega)
        (by push_cast; ring) (by push_cast; ring)⟩

def IsBreakOf (o hm : ℝ) (jlo : ℤ) (ctr : ℤ × ℤ → ℂ) (j k : ℤ) (v : ℂ) : Prop :=
  ∀ (hx₀ : o + j * hm < (ctr (j, k)).re) (hx₁ : (ctr (j, k)).re < o + (j + 1) * hm)
    (hy₀ : o + k * hm < (ctr (j, k)).im) (hy₁ : (ctr (j, k)).im < o + (k + 1) * hm)
    (hL₀ : o + k * hm < yL jlo ctr (j, k)) (hL₁ : yL jlo ctr (j, k) < o + (k + 1) * hm)
    (R : RadialRegion),
    PlanarRegions.RectClauses (o + j * hm) (o + (j + 1) * hm) (o + k * hm) (o + (k + 1) * hm) (ctr (j, k))
      (yL jlo ctr (j, k)) hx₀ hx₁ hy₀ hy₁ hL₀ hL₁ R →
    ∃ i : Fin (R.N + 1), R.loop (R.φs i) = v

theorem isBreakOf_corner_ll (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + j * hm, o + k * hm⟩ : ℂ) := by
  intro _ _ _ _ _ _ R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 4 := ⟨⟨4, by omega⟩, rfl⟩
  exact ⟨i, D.b4 i hi⟩

theorem isBreakOf_corner_ul (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + j * hm, o + ((k + 1 : ℤ) : ℝ) * hm⟩ : ℂ) := by
  intro _ _ _ _ _ _ R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 2 := ⟨⟨2, by omega⟩, rfl⟩
  exact ⟨i, (D.b2 i hi).trans (complex_mk_eq rfl (by push_cast; ring))⟩

theorem isBreakOf_corner_lr (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + ((j + 1 : ℤ) : ℝ) * hm, o + k * hm⟩ : ℂ) := by
  intro _ _ _ _ _ _ R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 5 := ⟨⟨5, by omega⟩, rfl⟩
  exact ⟨i, (D.b5 i hi).trans (complex_mk_eq (by push_cast; ring) rfl)⟩

theorem isBreakOf_corner_ur (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + ((j + 1 : ℤ) : ℝ) * hm, o + ((k + 1 : ℤ) : ℝ) * hm⟩ : ℂ) := by
  intro _ _ _ _ _ _ R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 1 := ⟨⟨1, by omega⟩, rfl⟩
  exact ⟨i, (D.b1 i hi).trans (complex_mk_eq (by push_cast; ring) (by push_cast; ring))⟩

theorem isBreakOf_right (j k : ℤ) :
    IsBreakOf o hm jlo ctr j k (⟨o + (j + 1) * hm, (ctr (j, k)).im⟩ : ℂ) := by
  intro _ _ _ _ _ _ R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 0 := ⟨⟨0, by omega⟩, rfl⟩
  exact ⟨i, D.b0 i hi⟩

theorem isBreakOf_left (k : ℤ) :
    IsBreakOf o hm jlo ctr jlo k (⟨o + jlo * hm, (ctr (jlo, k)).im⟩ : ℂ) := by
  intro _ _ _ _ _ _ R h
  have D := breakData_of_rectClauses h
  have hN := D.hN
  obtain ⟨i, hi⟩ : ∃ i : Fin (R.N + 1), i.val = 3 := ⟨⟨3, by omega⟩, rfl⟩
  exact ⟨i, (D.b3 i hi).trans (complex_mk_eq rfl (yL_left k))⟩

theorem mem_B₀_iff_break (hj : jlo ≤ jhi) (hk : klo ≤ khi) (v : ℂ) (hv : v ∈ B₀ o hm jlo jhi klo khi ctr) :
    ∃ j k : ℤ, jlo ≤ j ∧ j ≤ jhi ∧ klo ≤ k ∧ k ≤ khi ∧ IsBreakOf o hm jlo ctr j k v := by
  rcases mem_B₀.mp hv with hc | hr | hl
  · obtain ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩ := mem_corners.mp hc
    by_cases hjle : j ≤ jhi
    · by_cases hkle : k ≤ khi
      · exact ⟨j, k, hj₁, hjle, hk₁, hkle, isBreakOf_corner_ll j k⟩
      · obtain rfl : k = khi + 1 := by omega
        exact ⟨j, khi, hj₁, hjle, hk, le_rfl, isBreakOf_corner_ul j khi⟩
    · obtain rfl : j = jhi + 1 := by omega
      by_cases hkle : k ≤ khi
      · exact ⟨jhi, k, hj, le_rfl, hk₁, hkle, isBreakOf_corner_lr jhi k⟩
      · obtain rfl : k = khi + 1 := by omega
        exact ⟨jhi, khi, hj, le_rfl, hk, le_rfl, isBreakOf_corner_ur jhi khi⟩
  · obtain ⟨j, k, hj₁, hj₂, hk₁, hk₂, rfl⟩ := mem_rights.mp hr
    exact ⟨j, k, hj₁, hj₂, hk₁, hk₂, isBreakOf_right j k⟩
  · obtain ⟨k, hk₁, hk₂, rfl⟩ := mem_lefts.mp hl
    exact ⟨jlo, k, le_rfl, hj, hk₁, hk₂, isBreakOf_left k⟩

theorem B₀_off_lines (v : ℂ) (hv : v ∈ B₀ o hm jlo jhi klo khi ctr) : ∃ j : ℤ, v.re - o = j * hm := by
  rcases mem_B₀.mp hv with hc | hr | hl
  · obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_corners.mp hc
    refine ⟨j, ?_⟩
    show o + (j : ℝ) * hm - o = (j : ℝ) * hm
    ring
  · obtain ⟨j, k, -, -, -, -, rfl⟩ := mem_rights.mp hr
    refine ⟨j + 1, ?_⟩
    show o + ((j : ℝ) + 1) * hm - o = ((j + 1 : ℤ) : ℝ) * hm
    push_cast
    ring
  · obtain ⟨k, -, -, rfl⟩ := mem_lefts.mp hl
    refine ⟨jlo, ?_⟩
    show o + (jlo : ℝ) * hm - o = (jlo : ℝ) * hm
    ring

end GridVertices

end

end Part_D1Verts

section Part_D1GridRev

set_option autoImplicit false

open AlgebraicCurve Set PlanarRegions
open scoped Real

namespace ArcReversal

theorem _root_.P2MW.S_AlgebraicCurve_RadialRegion_exists_grid_geometry.SideIdentity.ArcData.right_pair' {R R' : RadialRegion} {x₀ x₁ y₀ y₁ yc yL x₀' x₁' y₀' y₁' yc' yL' : ℝ}
    (D : SideIdentity.ArcData R x₀ x₁ y₀ y₁ yc yL) (D' : SideIdentity.ArcData R' x₀' x₁' y₀' y₁' yc' yL')
    (hx : x₀' = x₁) (hy₀ : y₀' = y₀) (hy₁ : y₁' = y₁) :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  subst hx hy₀ hy₁
  intro a a' heq
  have _hx := D.hx
  have _hc₀ := D.hc₀
  have _hc₁ := D.hc₁
  have _hL₀ := D.hL₀
  have _hL₁ := D.hL₁
  have _hx' := D'.hx
  have _hc₀' := D'.hc₀
  have _hc₁' := D'.hc₁
  have _hL₀' := D'.hL₀
  have _hL₁' := D'.hL₁
  have _hy := D.hc₀.trans D.hc₁
  have _hxx := D.hx.trans D'.hx
  rcases D.arcSet_cases a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases D'.arcSet_cases a' with ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩ | ⟨ha', ea'⟩
  all_goals first
    | omega
    | exact absurd (ea.symm.trans (heq.trans ea')) (SideIdentity.vseg_ne_hseg (by assumption))
    | exact absurd (ea.symm.trans (heq.trans ea')) (SideIdentity.hseg_ne_vseg (by assumption))
    | refine (SideIdentity.vseg_eq_vseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
    | refine (SideIdentity.hseg_eq_hseg (by assumption) (ea.symm.trans (heq.trans ea'))).elim fun _e₁ _h => _h.elim fun _e₂ _ => ?_
  all_goals first
    | exact absurd _e₁ (ne_of_lt (by assumption))
    | exact absurd _e₁ (ne_of_gt (by assumption))
    | exact absurd _e₂ (ne_of_lt (by assumption))
    | exact absurd _e₂ (ne_of_gt (by assumption))

theorem right_of_arcSet_eq' {o hm : ℝ} {j k : ℤ} {c c' : ℂ} {yL yL' : ℝ} {R R' : RadialRegion}
    (h : SideIdentity.IsSquare o hm j k c yL R) (h' : SideIdentity.IsSquare o hm (j+1) k c' yL' R') :
    ∀ (a : Fin R.N) (a' : Fin R'.N), R.arcSet a = R'.arcSet a' →
      (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  have D := SideIdentity.arcData_of_isSquare h
  have D' := SideIdentity.arcData_of_isSquare h'
  exact D.right_pair' D' (by simp) rfl rfl

theorem fst_ne_or_snd_ne {p p' : ℤ × ℤ} (h : p ≠ p') : p.1 ≠ p'.1 ∨ p.2 ≠ p'.2 := by
  rcases ne_or_eq p.1 p'.1 with h₁ | h₁
  · exact Or.inl h₁
  · exact Or.inr fun h₂ => h (Prod.ext h₁ h₂)

theorem pair_of_arcSet_eq {o hm : ℝ} (hhm : 0 < hm) {j k j' k' : ℤ} {c c' : ℂ} {yL yL' : ℝ}
    {R R' : RadialRegion} (h : SideIdentity.IsSquare o hm j k c yL R) (h' : SideIdentity.IsSquare o hm j' k' c' yL' R')
    (hne : j ≠ j' ∨ k ≠ k') (a : Fin R.N) (a' : Fin R'.N) (heq : R.arcSet a = R'.arcSet a') :
    (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) ∨ (a.val = 1 ∧ a'.val = 4) ∨
      (a.val = 2 ∧ a'.val = 0) ∨ (a.val = 3 ∧ a'.val = 5) ∨ (a.val = 4 ∧ a'.val = 1) := by
  rcases SideIdentity.locality hhm h h' a a' heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hne.elim (fun hj => (hj rfl).elim) (fun hk => (hk rfl).elim)
  · rcases right_of_arcSet_eq' h h' a a' heq with h₀₂ | h₅₃
    · exact Or.inl h₀₂
    · exact Or.inr (Or.inl h₅₃)
  · rcases right_of_arcSet_eq' h' h a' a heq.symm with ⟨h₀, h₂⟩ | ⟨h₅, h₃⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h₂, h₀⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h₃, h₅⟩))))
  · exact Or.inr (Or.inr (Or.inl (SideIdentity.upper_of_arcSet_eq h h' a a' heq)))
  · obtain ⟨h₁, h₄⟩ := SideIdentity.upper_of_arcSet_eq h' h a' a heq.symm
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h₄, h₁⟩))))

theorem range_of_rightUpper {A : Set ℝ} (h : A ⊆ Ico 0 (π / 2)) :
    A ⊆ Ioo (-(π / 2)) (π / 2) ∨ A ⊆ Ioo (3 * π / 2) (5 * π / 2) :=
  Or.inl fun t ht => ⟨by linarith [(h ht).1, Real.pi_pos], (h ht).2⟩

theorem range_of_rightLower {A : Set ℝ} (h : A ⊆ Ioc (3 * π / 2) (2 * π)) :
    A ⊆ Ioo (-(π / 2)) (π / 2) ∨ A ⊆ Ioo (3 * π / 2) (5 * π / 2) :=
  Or.inr fun t ht => ⟨(h ht).1, by linarith [(h ht).2, Real.pi_pos]⟩

variable (M : GridData)

theorem isSquare_base (p : ℤ × ℤ) : SideIdentity.IsSquare M.o M.hm p.1 p.2 (M.ctr p) (M.yL p) (M.base p) := by
  unfold SideIdentity.IsSquare
  exact ⟨(M.ctr_mem p).1.1, (M.ctr_mem p).1.2, (M.ctr_mem p).2.1, (M.ctr_mem p).2.2,
    (M.yL_mem p).1, (M.yL_mem p).2, M.base_spec p⟩

def sqbit (p : ℤ × ℤ) (k : Fin (M.base p).N) : Bool := decide (k.val = 0 ∨ k.val = 1 ∨ k.val = 5)

open scoped Classical in

noncomputable def perbit (k₀ : Fin M.winReg.N) : Bool :=
  decide ((∃ j : ℤ, M.winReg.arcSet k₀ =
      {z : ℂ | z.im = M.o + M.klo * M.hm ∧ z.re ∈ Icc (M.o + j * M.hm) (M.o + (j + 1) * M.hm)}) ∨
    (∃ k : ℤ, M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.cy (M.jlo, k)) (M.o + (k + 1) * M.hm)}) ∨
    (∃ k : ℤ, M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.o + k * M.hm) (M.cy (M.jlo, k))}))

theorem idx_of_perbit {p : ℤ × ℤ} (hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (k : Fin (M.base p).N) {k₀ : Fin M.winReg.N} (heq : (M.base p).arcSet k = M.winReg.arcSet k₀)
    (hb : perbit M k₀ = true) : k.val = 2 ∨ k.val = 3 ∨ k.val = 4 := by
  simp only [perbit, decide_eq_true_eq] at hb
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  rcases hb with ⟨j, hset⟩ | ⟨k₁, hset⟩ | ⟨k₁, hset⟩
  · exact Or.inr (Or.inr
      (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2)
  · exact Or.inl
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
  · exact Or.inr (Or.inl
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1)

theorem perbit_eq_false_of_pos {p : ℤ × ℤ} (hp : p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (k : Fin (M.base p).N) {k₀ : Fin M.winReg.N} (heq : (M.base p).arcSet k = M.winReg.arcSet k₀)
    (hpos : k.val = 0 ∨ k.val = 1 ∨ k.val = 5) : perbit M k₀ = false := by
  cases h : perbit M k₀
  · rfl
  · exact absurd (idx_of_perbit M hp k heq h) (by omega)

theorem bit_sq_sq : ∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
    (M.base p).arcSet k = (M.base p').arcSet k' → sqbit M p' k' = !sqbit M p k := by
  intro p p' hne k k' heq
  rcases pair_of_arcSet_eq M.hhm (isSquare_base M p) (isSquare_base M p') (fst_ne_or_snd_ne hne)
      k k' heq with ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ <;>
    simp [sqbit, hk, hk']

theorem bit_sq_per : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
    (M.base p).arcSet k = M.winReg.arcSet k₀ → perbit M k₀ = !sqbit M p k := by
  intro p k k₀ hp heq
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  obtain ⟨-, -, -, -, -, hsix, -⟩ := M.winReg_spec
  rcases hsix k₀ with ⟨j, -, -, hset, -⟩ | ⟨j, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩ |
    ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩
  · have h4 := (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2
    have hb : perbit M k₀ = true := by
      simp only [perbit, decide_eq_true_eq]
      exact Or.inl ⟨j, hset⟩
    simp [sqbit, hb, h4]
  · have h1 := (SideIdentity.top_of_arcSet_eq M.hhm hsq (J := j) (K := M.khi) hpk.2 k (heq.trans hset)).2.2
    have hb := perbit_eq_false_of_pos M hp k heq (Or.inr (Or.inl h1))
    simp [sqbit, hb, h1]
  · have h2 :=
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hb : perbit M k₀ = true := by
      simp only [perbit, decide_eq_true_eq]
      exact Or.inr (Or.inl ⟨k₁, hset⟩)
    simp [sqbit, hb, h2]
  · have h3 :=
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hb : perbit M k₀ = true := by
      simp only [perbit, decide_eq_true_eq]
      exact Or.inr (Or.inr ⟨k₁, hset⟩)
    simp [sqbit, hb, h3]
  · have h5 :=
      (SideIdentity.rightLower_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hb := perbit_eq_false_of_pos M hp k heq (Or.inr (Or.inr h5))
    simp [sqbit, hb, h5]
  · have h0 :=
      (SideIdentity.rightUpper_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hb := perbit_eq_false_of_pos M hp k heq (Or.inl h0)
    simp [sqbit, hb, h0]

theorem rev_sq_sq : ∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (M.base p).N) (k' : Fin (M.base p').N),
    (M.base p).arcSet k = (M.base p').arcSet k' → sqbit M p k = true →
    ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((M.base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((M.base p').arcIcc k') ∧
      ψ ((M.base p').φs k'.castSucc) = (M.base p).φs k.succ ∧
      ψ ((M.base p').φs k'.succ) = (M.base p).φs k.castSucc ∧
      ∀ t ∈ (M.base p').arcIcc k', (M.base p').loop t = (M.base p).loop (ψ t) := by
  intro p p' hne k k' heq hbit
  simp only [sqbit, decide_eq_true_eq] at hbit
  have D := SideIdentity.arcData_of_rectClauses (M.base_spec p)
  have D' := SideIdentity.arcData_of_rectClauses (M.base_spec p')
  have hqre : (M.base p).q.re = (M.ctr p).re := congrArg Complex.re (M.base_q p)
  have hqim : (M.base p).q.im = (M.ctr p).im := congrArg Complex.im (M.base_q p)
  have hqre' : (M.base p').q.re = (M.ctr p').re := congrArg Complex.re (M.base_q p')
  have hqim' : (M.base p').q.im = (M.ctr p').im := congrArg Complex.im (M.base_q p')
  obtain ⟨-, -, -, -, -, -, -, -, -, -, l0, l1, l2, -, -, l5, l6, r05, r1, -, -, g0, g1, -, -, g5,
    -, -⟩ := M.base_spec p
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, l2', l3', l4', l5', -, -, -, r23', r4', -, -, g23',
    g4', -, -, -⟩ := M.base_spec p'
  rcases pair_of_arcSet_eq M.hhm (isSquare_base M p) (isSquare_base M p') (fst_ne_or_snd_ne hne)
      k k' heq with ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, hk'⟩ | ⟨hk, -⟩ | ⟨hk, -⟩ | ⟨hk, -⟩
  ·
    obtain ⟨e₁, e₂, e₃⟩ :=
      SideIdentity.vseg_eq_vseg D.hc₁ ((D.arc0 k hk).symm.trans (heq.trans (D'.arc2 k' hk')))
    refine RadialRegion.exists_reparam_across_edge.1 (M.base p) (M.base p') k k' _ _ ?_ ?_ ?_ (r05 k (Or.inl hk))
      (range_of_rightUpper (g0 k hk)) (r23' k' (Or.inl hk')) (g23' k' (Or.inl hk')) ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · exact sub_pos.mpr (M.ctr_mem p').1.1
    · linarith
    · rw [l0 k.castSucc (by simp [hk]), l3' k'.succ (by simp [hk'])]
      exact Complex.ext e₁ e₂
    · rw [l1 k.succ (by simp [hk]), l2' k'.castSucc (by simp [hk'])]
      exact Complex.ext e₁ e₃
  ·
    obtain ⟨e₁, e₂, e₃⟩ :=
      SideIdentity.vseg_eq_vseg D.hc₀ ((D.arc5 k hk).symm.trans (heq.trans (D'.arc3 k' hk')))
    refine RadialRegion.exists_reparam_across_edge.1 (M.base p) (M.base p') k k' _ _ ?_ ?_ ?_ (r05 k (Or.inr hk))
      (range_of_rightLower (g5 k hk)) (r23' k' (Or.inr hk')) (g23' k' (Or.inr hk')) ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · exact sub_pos.mpr (M.ctr_mem p').1.1
    · linarith
    · rw [l5 k.castSucc (by simp [hk]), l4' k'.succ (by simp [hk'])]
      exact Complex.ext e₁ e₂
    · rw [l6 k.succ (by simp [hk]), l3' k'.castSucc (by simp [hk'])]
      exact Complex.ext e₁ e₃
  ·
    obtain ⟨e₁, e₂, e₃⟩ :=
      SideIdentity.hseg_eq_hseg D.hx ((D.arc1 k hk).symm.trans (heq.trans (D'.arc4 k' hk')))
    refine RadialRegion.exists_reparam_across_edge.2 (M.base p) (M.base p') k k' _ _ ?_ ?_ ?_ (r1 k hk) (g1 k hk)
      (r4' k' hk') (g4' k' hk') ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).2.2
    · exact sub_pos.mpr (M.ctr_mem p').2.1
    · linarith
    · rw [l1 k.castSucc (by simp [hk]), l5' k'.succ (by simp [hk'])]
      exact Complex.ext e₃ e₁
    · rw [l2 k.succ (by simp [hk]), l4' k'.castSucc (by simp [hk'])]
      exact Complex.ext e₂ e₁
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

theorem rev_per_to_sq : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
    (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit M p k = true →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (M.winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (M.winReg.arcIcc k₀) ∧
      ψ (M.winReg.φs k₀.castSucc) = (M.base p).φs k.castSucc ∧
      ψ (M.winReg.φs k₀.succ) = (M.base p).φs k.succ ∧
      ∀ t ∈ M.winReg.arcIcc k₀, M.winReg.loop t = (M.base p).loop (ψ t) := by
  intro p k k₀ hp heq hbit
  simp only [sqbit, decide_eq_true_eq] at hbit
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  have D := SideIdentity.arcData_of_rectClauses (M.base_spec p)
  have hqre : (M.base p).q.re = (M.ctr p).re := congrArg Complex.re (M.base_q p)
  have hqim : (M.base p).q.im = (M.ctr p).im := congrArg Complex.im (M.base_q p)
  have hwre : M.winReg.q.re = 0 := by simp [M.winReg_q]
  have hwim : M.winReg.q.im = 0 := by simp [M.winReg_q]
  have hX₁ : 0 < M.o + (M.jhi + 1) * M.hm := M.zero_mem_window.1.2
  have hY₁ : 0 < M.o + (M.khi + 1) * M.hm := M.zero_mem_window.2.2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, l0, l1, l2, -, -, l5, l6, r05, r1, -, -, g0, g1, -, -, g5,
    -, -⟩ := M.base_spec p
  obtain ⟨-, -, -, -, -, hsix, -⟩ := M.winReg_spec
  rcases hsix k₀ with ⟨j, -, -, hset, -⟩ | ⟨j, -, -, hset, hcs, hsc, hr, hg⟩ |
    ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩ |
    ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩
  ·
    have h4 := (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2
    exfalso; omega
  ·
    have h1 := (SideIdentity.top_of_arcSet_eq M.hhm hsq (J := j) (K := M.khi) hpk.2 k (heq.trans hset)).2.2
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.hseg (M.o + (M.khi + 1) * M.hm) (M.o + j * M.hm) (M.o + (j + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.hseg_eq_hseg D.hx ((D.arc1 k h1).symm.trans (heq.trans hset'))
    refine RadialRegion.exists_reparam_same_side.2.2.1 (M.base p) M.winReg k k₀ _ _ ?_ ?_ ?_ (r1 k h1) (g1 k h1) hr hg ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).2.2
    · linarith
    · linarith
    · rw [l1 k.castSucc (by simp [h1]), hcs]
      exact Complex.ext e₃ e₁
    · rw [l2 k.succ (by simp [h1]), hsc]
      exact Complex.ext e₂ e₁
  ·
    have h2 :=
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    exfalso; omega
  ·
    have h3 :=
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    exfalso; omega
  ·
    have h5 :=
      (SideIdentity.rightLower_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + (M.jhi + 1) * M.hm) (M.o + k₁ * M.hm) (M.cy (M.jhi, k₁)) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hc₀ ((D.arc5 k h5).symm.trans (heq.trans hset'))
    refine RadialRegion.exists_reparam_same_side.1 (M.base p) M.winReg k k₀ _ _ ?_ ?_ ?_ (r05 k (Or.inr h5))
      (range_of_rightLower (g5 k h5)) hr hg ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · linarith
    · linarith
    · rw [l5 k.castSucc (by simp [h5]), hcs]
      exact Complex.ext e₁ e₂
    · rw [l6 k.succ (by simp [h5]), hsc]
      exact Complex.ext e₁ e₃
  ·
    have h0 :=
      (SideIdentity.rightUpper_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + (M.jhi + 1) * M.hm) (M.cy (M.jhi, k₁)) (M.o + (k₁ + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hc₁ ((D.arc0 k h0).symm.trans (heq.trans hset'))
    refine RadialRegion.exists_reparam_same_side.1 (M.base p) M.winReg k k₀ _ _ ?_ ?_ ?_ (r05 k (Or.inl h0))
      (range_of_rightUpper (g0 k h0)) hr hg ?_ ?_
    · exact sub_pos.mpr (M.ctr_mem p).1.2
    · linarith
    · linarith
    · rw [l0 k.castSucc (by simp [h0]), hcs]
      exact Complex.ext e₁ e₂
    · rw [l1 k.succ (by simp [h0]), hsc]
      exact Complex.ext e₁ e₃

theorem rev_sq_to_per : ∀ (p : ℤ × ℤ) (k : Fin (M.base p).N) (k₀ : Fin M.winReg.N),
    p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
    (M.base p).arcSet k = M.winReg.arcSet k₀ → sqbit M p k = false →
    ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((M.base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((M.base p).arcIcc k) ∧
      ψ ((M.base p).φs k.castSucc) = M.winReg.φs k₀.castSucc ∧
      ψ ((M.base p).φs k.succ) = M.winReg.φs k₀.succ ∧
      ∀ t ∈ (M.base p).arcIcc k, (M.base p).loop t = M.winReg.loop (ψ t) := by
  intro p k k₀ hp heq hbit
  simp only [sqbit, decide_eq_false_iff_not] at hbit
  obtain ⟨hpj, hpk⟩ := Set.mem_prod.mp hp
  have hsq := isSquare_base M p
  have D := SideIdentity.arcData_of_rectClauses (M.base_spec p)
  have hqre : (M.base p).q.re = (M.ctr p).re := congrArg Complex.re (M.base_q p)
  have hqim : (M.base p).q.im = (M.ctr p).im := congrArg Complex.im (M.base_q p)
  have hwre : M.winReg.q.re = 0 := by simp [M.winReg_q]
  have hwim : M.winReg.q.im = 0 := by simp [M.winReg_q]
  have hX₀ : M.o + M.jlo * M.hm < 0 := M.zero_mem_window.1.1
  have hY₀ : M.o + M.klo * M.hm < 0 := M.zero_mem_window.2.1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, l2, l3, l4, l5, -, -, -, r23, r4, -, -, g23, g4, -,
    -, -⟩ := M.base_spec p
  obtain ⟨-, -, -, -, -, hsix, -⟩ := M.winReg_spec
  rcases hsix k₀ with ⟨j, -, -, hset, hcs, hsc, hr, hg⟩ | ⟨j, -, -, hset, -⟩ |
    ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩ | ⟨k₁, -, -, hset, hcs, hsc, hr, hg⟩ |
    ⟨k₁, -, -, hset, -⟩ | ⟨k₁, -, -, hset, -⟩
  ·
    have h4 := (SideIdentity.bottom_of_arcSet_eq M.hhm hsq (J := j) (K := M.klo) hpk.1 k (heq.trans hset)).2.2
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.hseg (M.o + M.klo * M.hm) (M.o + j * M.hm) (M.o + (j + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.hseg_eq_hseg D.hx ((D.arc4 k h4).symm.trans (heq.trans hset'))
    refine RadialRegion.exists_reparam_same_side.2.2.2 M.winReg (M.base p) k₀ k _ _ ?_ ?_ ?_ hr hg (r4 k h4) (g4 k h4) ?_ ?_
    · linarith
    · exact sub_pos.mpr (M.ctr_mem p).2.1
    · linarith
    · rw [hcs, l4 k.castSucc (by simp [h4])]
      exact Complex.ext e₂.symm e₁.symm
    · rw [hsc, l5 k.succ (by simp [h4])]
      exact Complex.ext e₃.symm e₁.symm
  ·
    have h1 := (SideIdentity.top_of_arcSet_eq M.hhm hsq (J := j) (K := M.khi) hpk.2 k (heq.trans hset)).2.2
    exfalso; omega
  ·
    have h2 :=
      (SideIdentity.leftUpper_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + M.jlo * M.hm) (M.cy (M.jlo, k₁)) (M.o + (k₁ + 1) * M.hm) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hL₁ ((D.arc2 k h2).symm.trans (heq.trans hset'))
    refine RadialRegion.exists_reparam_same_side.2.1 M.winReg (M.base p) k₀ k _ _ ?_ ?_ ?_ hr hg (r23 k (Or.inl h2))
      (g23 k (Or.inl h2)) ?_ ?_
    · linarith
    · exact sub_pos.mpr (M.ctr_mem p).1.1
    · linarith
    · rw [hcs, l2 k.castSucc (by simp [h2])]
      exact Complex.ext e₁.symm e₃.symm
    · rw [hsc, l3 k.succ (by simp [h2])]
      exact Complex.ext e₁.symm e₂.symm
  ·
    have h3 :=
      (SideIdentity.leftLower_of_arcSet_eq M.hhm hsq (J := M.jlo) (K := k₁) hpj.1 k (heq.trans hset)).2.2.1
    have hset' : M.winReg.arcSet k₀ =
        SideIdentity.vseg (M.o + M.jlo * M.hm) (M.o + k₁ * M.hm) (M.cy (M.jlo, k₁)) := hset
    obtain ⟨e₁, e₂, e₃⟩ := SideIdentity.vseg_eq_vseg D.hL₀ ((D.arc3 k h3).symm.trans (heq.trans hset'))
    refine RadialRegion.exists_reparam_same_side.2.1 M.winReg (M.base p) k₀ k _ _ ?_ ?_ ?_ hr hg (r23 k (Or.inr h3))
      (g23 k (Or.inr h3)) ?_ ?_
    · linarith
    · exact sub_pos.mpr (M.ctr_mem p).1.1
    · linarith
    · rw [hcs, l3 k.castSucc (by simp [h3])]
      exact Complex.ext e₁.symm e₃.symm
    · rw [hsc, l4 k.succ (by simp [h3])]
      exact Complex.ext e₁.symm e₂.symm
  ·
    have h5 :=
      (SideIdentity.rightLower_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    exfalso; omega
  ·
    have h0 :=
      (SideIdentity.rightUpper_of_arcSet_eq M.hhm hsq (J := M.jhi) (K := k₁) hpj.2 k (heq.trans hset)).2.2.1
    exfalso; omega

end ArcReversal

end Part_D1GridRev

section Part_D1GridStarP

set_option autoImplicit false

open AlgebraicCurve Set PlanarRegions
open scoped Real

namespace StarProperty

theorem le_of_grid {o hm : ℝ} (hhm : 0 < hm) {s t : ℝ} (h : o + s * hm ≤ o + t * hm) : s ≤ t := by
  by_contra hc
  have h' := mul_lt_mul_of_pos_right (not_le.mp hc) hhm
  linarith

theorem int_le_of_grid₀₀ {o hm : ℝ} (hhm : 0 < hm) {m n : ℤ} (h : o + m * hm ≤ o + n * hm) : m ≤ n := by
  exact_mod_cast le_of_grid hhm h

theorem int_le_of_grid₀₁ {o hm : ℝ} (hhm : 0 < hm) {m n : ℤ} (h : o + m * hm ≤ o + (n + 1) * hm) :
    m ≤ n + 1 := by
  exact_mod_cast le_of_grid hhm h

theorem int_le_of_grid₁₁ {o hm : ℝ} (hhm : 0 < hm) {m n : ℤ} (h : o + (m + 1) * hm ≤ o + (n + 1) * hm) :
    m ≤ n := by
  have h' := le_of_grid hhm h
  have h'' : (m : ℝ) ≤ n := by linarith
  exact_mod_cast h''

theorem mem_vseg {x lo hi : ℝ} {z : ℂ} : z ∈ SideIdentity.vseg x lo hi ↔ z.re = x ∧ lo ≤ z.im ∧ z.im ≤ hi :=
  Iff.rfl

theorem mem_hseg {y lo hi : ℝ} {z : ℂ} : z ∈ SideIdentity.hseg y lo hi ↔ z.im = y ∧ lo ≤ z.re ∧ z.re ≤ hi :=
  Iff.rfl

theorem some_mk_eq {j kk j' kk' : ℤ} (h1 : j = j') (h2 : kk = kk') :
    (some (j, kk) : Option (ℤ × ℤ)) = some (j', kk') := by
  rw [h1, h2]

theorem some_mk_ne {j kk j' kk' : ℤ} (h : j ≠ j' ∨ kk ≠ kk') :
    (some (j, kk) : Option (ℤ × ℤ)) ≠ some (j', kk') := by
  intro e
  obtain ⟨e1, e2⟩ := Prod.mk.inj (Option.some.inj e)
  rcases h with h | h
  · exact h e1
  · exact h e2

section Window

variable (M : GridData)

theorem mem_win_iff {j kk : ℤ} :
    (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ↔ (M.jlo ≤ j ∧ j ≤ M.jhi) ∧ (M.klo ≤ kk ∧ kk ≤ M.khi) :=
  Iff.rfl

theorem cy_eq (j kk : ℤ) : (M.ctr (j, kk)).im = M.cy (j, kk) := rfl

theorem yL_jlo (kk : ℤ) : M.yL (M.jlo, kk) = M.cy (M.jlo, kk) := by
  show (if M.jlo = M.jlo then (M.ctr (M.jlo, kk)).im else (M.ctr (M.jlo - 1, kk)).im) = (M.ctr (M.jlo, kk)).im
  exact if_pos rfl

theorem yL_succ (j kk : ℤ) (hj : M.jlo ≤ j) : M.yL (j + 1, kk) = (M.ctr (j, kk)).im := by
  have h : ¬ (j + 1 = M.jlo) := by omega
  have e : j + 1 - 1 = j := by omega
  show (if j + 1 = M.jlo then (M.ctr (j + 1, kk)).im else (M.ctr (j + 1 - 1, kk)).im) = (M.ctr (j, kk)).im
  rw [if_neg h, e]

theorem isSquare_base (j kk : ℤ) :
    SideIdentity.IsSquare M.o M.hm j kk (M.ctr (j, kk)) (M.yL (j, kk)) (M.base (j, kk)) :=
  ⟨(M.ctr_mem (j, kk)).1.1, (M.ctr_mem (j, kk)).1.2, (M.ctr_mem (j, kk)).2.1, (M.ctr_mem (j, kk)).2.2,
    (M.yL_mem (j, kk)).1, (M.yL_mem (j, kk)).2, M.base_spec (j, kk)⟩

theorem arcData_base (j kk : ℤ) :
    SideIdentity.ArcData (M.base (j, kk)) (M.o + j * M.hm) (M.o + (j + 1) * M.hm) (M.o + kk * M.hm)
      (M.o + (kk + 1) * M.hm) (M.ctr (j, kk)).im (M.yL (j, kk)) :=
  SideIdentity.arcData_of_isSquare (isSquare_base M j kk)

theorem exists_idx (p : ℤ × ℤ) (n : ℕ) (hn : n < 6) : ∃ a : Fin (M.base p).N, a.val = n := by
  have hN := M.base_N p
  exact ⟨⟨n, by omega⟩, rfl⟩

theorem of_mem_baseK {j kk : ℤ} {v : ℂ} (h : v ∈ (M.base (j, kk)).K) :
    (M.o + j * M.hm ≤ v.re ∧ v.re ≤ M.o + (j + 1) * M.hm) ∧
      (M.o + kk * M.hm ≤ v.im ∧ v.im ≤ M.o + (kk + 1) * M.hm) := by
  rw [(M.base_spec (j, kk)).2.2.1] at h
  exact h

theorem mem_baseK_of {j kk : ℤ} {v : ℂ} (h1 : M.o + j * M.hm ≤ v.re) (h2 : v.re ≤ M.o + (j + 1) * M.hm)
    (h3 : M.o + kk * M.hm ≤ v.im) (h4 : v.im ≤ M.o + (kk + 1) * M.hm) : v ∈ (M.base (j, kk)).K := by
  rw [(M.base_spec (j, kk)).2.2.1]
  exact ⟨⟨h1, h2⟩, h3, h4⟩

theorem not_mem_winKint {v : ℂ} (h : v ∉ M.winReg.Kint) :
    v.re ≤ M.o + M.jlo * M.hm ∨ M.o + (M.jhi + 1) * M.hm ≤ v.re ∨
      v.im ≤ M.o + M.klo * M.hm ∨ M.o + (M.khi + 1) * M.hm ≤ v.im := by
  by_cases h1 : v.re ≤ M.o + M.jlo * M.hm
  · exact Or.inl h1
  by_cases h2 : M.o + (M.jhi + 1) * M.hm ≤ v.re
  · exact Or.inr (Or.inl h2)
  by_cases h3 : v.im ≤ M.o + M.klo * M.hm
  · exact Or.inr (Or.inr (Or.inl h3))
  by_cases h4 : M.o + (M.khi + 1) * M.hm ≤ v.im
  · exact Or.inr (Or.inr (Or.inr h4))
  exfalso
  apply h
  rw [M.winReg_Kint]
  exact ⟨⟨not_le.mp h1, not_le.mp h2⟩, not_le.mp h3, not_le.mp h4⟩

theorem right_arc₀₂ {j j' kk : ℤ} (hj : M.jlo ≤ j) (hj' : j' = j + 1) (a : Fin (M.base (j, kk)).N)
    (ha : a.val = 0) (a' : Fin (M.base (j', kk)).N) (ha' : a'.val = 2) :
    (M.base (j, kk)).arcSet a = (M.base (j', kk)).arcSet a' := by
  subst hj'
  exact SideIdentity.right_arcSet_eq₀₂ (isSquare_base M j kk) (isSquare_base M (j + 1) kk) (yL_succ M j kk hj) a ha a' ha'

theorem right_arc₅₃ {j j' kk : ℤ} (hj : M.jlo ≤ j) (hj' : j' = j + 1) (a : Fin (M.base (j, kk)).N)
    (ha : a.val = 5) (a' : Fin (M.base (j', kk)).N) (ha' : a'.val = 3) :
    (M.base (j, kk)).arcSet a = (M.base (j', kk)).arcSet a' := by
  subst hj'
  exact SideIdentity.right_arcSet_eq₅₃ (isSquare_base M j kk) (isSquare_base M (j + 1) kk) (yL_succ M j kk hj) a ha a' ha'

theorem upper_arc₁₄ {j kk kk' : ℤ} (hk' : kk' = kk + 1) (a : Fin (M.base (j, kk)).N) (ha : a.val = 1)
    (a' : Fin (M.base (j, kk')).N) (ha' : a'.val = 4) :
    (M.base (j, kk)).arcSet a = (M.base (j, kk')).arcSet a' := by
  subst hk'
  exact SideIdentity.upper_arcSet_eq₁₄ (isSquare_base M j kk) (isSquare_base M j (kk + 1)) a ha a' ha'

theorem right_of_eq {j j' kk kk' : ℤ} (hj : M.jlo ≤ j) (hj' : j' = j + 1) (hk' : kk' = kk)
    (a : Fin (M.base (j, kk)).N) (a' : Fin (M.base (j', kk')).N)
    (h : (M.base (j, kk)).arcSet a = (M.base (j', kk')).arcSet a') :
    (a.val = 0 ∧ a'.val = 2) ∨ (a.val = 5 ∧ a'.val = 3) := by
  subst hj' hk'
  exact SideIdentity.right_of_arcSet_eq (isSquare_base M j _) (isSquare_base M (j + 1) _) (yL_succ M j _ hj) a a' h

theorem upper_of_eq {j j' kk kk' : ℤ} (hj' : j' = j) (hk' : kk' = kk + 1) (a : Fin (M.base (j, kk)).N)
    (a' : Fin (M.base (j', kk')).N) (h : (M.base (j, kk)).arcSet a = (M.base (j', kk')).arcSet a') :
    a.val = 1 ∧ a'.val = 4 := by
  subst hj' hk'
  exact SideIdentity.upper_of_arcSet_eq (isSquare_base M _ _) (isSquare_base M _ _) a a' h

theorem squares_of_arc {j kk : ℤ} (hj : M.jlo ≤ j) (a : Fin (M.base (j, kk)).N) {j'' kk'' : ℤ}
    (hj'' : M.jlo ≤ j'') (a'' : Fin (M.base (j'', kk'')).N)
    (h : (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a) :
    (j'' = j ∧ kk'' = kk) ∨ ((a.val = 0 ∨ a.val = 5) ∧ j'' = j + 1 ∧ kk'' = kk) ∨
      ((a.val = 2 ∨ a.val = 3) ∧ j'' = j - 1 ∧ kk'' = kk) ∨ (a.val = 1 ∧ j'' = j ∧ kk'' = kk + 1) ∨
      (a.val = 4 ∧ j'' = j ∧ kk'' = kk - 1) := by
  rcases SideIdentity.locality M.hhm (isSquare_base M j kk) (isSquare_base M j'' kk'') a a'' h.symm with
    ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · exact Or.inl ⟨e1, e2⟩
  · have h' := right_of_eq M hj e1 e2 a a'' h.symm
    omega
  · have h' := right_of_eq M hj'' e1 e2.symm a'' a h
    omega
  · have h' := upper_of_eq M e1 e2 a a'' h.symm
    omega
  · have h' := upper_of_eq M e1.symm e2 a'' a h
    omega

theorem win_cases (k₀ : Fin M.winReg.N) :
    (∃ i : ℤ, M.jlo ≤ i ∧ i ≤ M.jhi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.im = M.o + M.klo * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)}) ∨
    (∃ i : ℤ, M.jlo ≤ i ∧ i ≤ M.jhi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.im = M.o + (M.khi + 1) * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.cy (M.jlo, i)) (M.o + (i + 1) * M.hm)}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jlo, i))}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jhi, i))}) ∨
    (∃ i : ℤ, M.klo ≤ i ∧ i ≤ M.khi ∧ M.winReg.arcSet k₀ =
      {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.cy (M.jhi, i)) (M.o + (i + 1) * M.hm)}) := by
  obtain ⟨-, -, -, -, -, hcases, -, -, -, -, -, -⟩ := M.winReg_spec
  rcases hcases k₀ with ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩ |
    ⟨i, h1, h2, e, -⟩ | ⟨i, h1, h2, e, -⟩
  · exact Or.inl ⟨i, h1, h2, e⟩
  · exact Or.inr (Or.inl ⟨i, h1, h2, e⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨i, h1, h2, e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1, h2, e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨i, h1, h2, e⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨i, h1, h2, e⟩))))

theorem win_bottom (i : ℤ) (h1 : M.jlo ≤ i) (h2 : i ≤ M.jhi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.im = M.o + M.klo * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, hb, -, -, -, -, -⟩ := M.winReg_spec
  exact hb i h1 h2

theorem win_top (i : ℤ) (h1 : M.jlo ≤ i) (h2 : i ≤ M.jhi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.im = M.o + (M.khi + 1) * M.hm ∧ z.re ∈ Icc (M.o + i * M.hm) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, -, ht, -, -, -, -⟩ := M.winReg_spec
  exact ht i h1 h2

theorem win_leftUpper (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.cy (M.jlo, i)) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, -, -, hlu, -, -, -⟩ := M.winReg_spec
  exact hlu i h1 h2

theorem win_leftLower (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + M.jlo * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jlo, i))} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hll, -, -⟩ := M.winReg_spec
  exact hll i h1 h2

theorem win_rightLower (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.o + i * M.hm) (M.cy (M.jhi, i))} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hrl, -⟩ := M.winReg_spec
  exact hrl i h1 h2

theorem win_rightUpper (i : ℤ) (h1 : M.klo ≤ i) (h2 : i ≤ M.khi) : ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ =
    {z : ℂ | z.re = M.o + (M.jhi + 1) * M.hm ∧ z.im ∈ Icc (M.cy (M.jhi, i)) (M.o + (i + 1) * M.hm)} := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hru⟩ := M.winReg_spec
  exact hru i h1 h2

theorem sq_per {j kk : ℤ} (hj : M.jlo ≤ j) (hj2 : j ≤ M.jhi) (hk : M.klo ≤ kk) (hk2 : kk ≤ M.khi)
    (a : Fin (M.base (j, kk)).N) (k₀ : Fin M.winReg.N) (h : (M.base (j, kk)).arcSet a = M.winReg.arcSet k₀) :
    (a.val = 0 ∧ j = M.jhi) ∨ (a.val = 5 ∧ j = M.jhi) ∨ (a.val = 2 ∧ j = M.jlo) ∨ (a.val = 3 ∧ j = M.jlo) ∨
      (a.val = 4 ∧ kk = M.klo) ∨ (a.val = 1 ∧ kk = M.khi) := by
  rcases win_cases M k₀ with ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ | ⟨_i, -, -, e⟩ |
    ⟨_i, -, -, e⟩
  · obtain ⟨-, e2, e3⟩ := SideIdentity.bottom_of_arcSet_eq M.hhm (isSquare_base M j kk) hk a (h.trans e)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e3, e2⟩))))
  · obtain ⟨-, e2, e3⟩ := SideIdentity.top_of_arcSet_eq M.hhm (isSquare_base M j kk) hk2 a (h.trans e)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e3, e2⟩))))
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.leftUpper_of_arcSet_eq M.hhm (isSquare_base M j kk) hj a (h.trans e)
    exact Or.inr (Or.inr (Or.inl ⟨e3, e1⟩))
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.leftLower_of_arcSet_eq M.hhm (isSquare_base M j kk) hj a (h.trans e)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e3, e1⟩)))
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.rightLower_of_arcSet_eq M.hhm (isSquare_base M j kk) hj2 a (h.trans e)
    exact Or.inr (Or.inl ⟨e3, e1⟩)
  · obtain ⟨e1, -, e3, -⟩ := SideIdentity.rightUpper_of_arcSet_eq M.hhm (isSquare_base M j kk) hj2 a (h.trans e)
    exact Or.inl ⟨e3, e1⟩

def Contains : Option (ℤ × ℤ) → ℂ → Prop
  | some p, v => p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ v ∈ (M.base p).K
  | none, v => v ∉ M.winReg.Kint

def Shares : Option (ℤ × ℤ) → Set ℂ → Prop
  | some p, Z => p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k : Fin (M.base p).N, (M.base p).arcSet k = Z
  | none, Z => ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ = Z

def Adj (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)) : Prop := ∃ Z : Set ℂ, Shares M ρ Z ∧ Shares M ρ' Z ∧ v ∈ Z

theorem contains_some_iff (p : ℤ × ℤ) (v : ℂ) :
    Contains M (some p) v ↔ p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ v ∈ (M.base p).K :=
  Iff.rfl

theorem contains_none_iff (v : ℂ) : Contains M none v ↔ v ∉ M.winReg.Kint :=
  Iff.rfl

theorem shares_some_iff (p : ℤ × ℤ) (Z : Set ℂ) :
    Shares M (some p) Z ↔
      p ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi ∧ ∃ k : Fin (M.base p).N, (M.base p).arcSet k = Z :=
  Iff.rfl

theorem shares_none_iff (Z : Set ℂ) : Shares M none Z ↔ ∃ k₀ : Fin M.winReg.N, M.winReg.arcSet k₀ = Z :=
  Iff.rfl

theorem adj_symm {v : ℂ} {ρ ρ' : Option (ℤ × ℤ)} (h : Adj M v ρ ρ') : Adj M v ρ' ρ := by
  obtain ⟨Z, h1, h2, hv⟩ := h
  exact ⟨Z, h2, h1, hv⟩

theorem adj_of_arcs {v : ℂ} {ρ ρ' : Option (ℤ × ℤ)} {Z : Set ℂ} (h : Shares M ρ Z) (h' : Shares M ρ' Z)
    (hv : v ∈ Z) : Adj M v ρ ρ' :=
  ⟨Z, h, h', hv⟩

theorem two_of_square {j kk : ℤ} (a : Fin (M.base (j, kk)).N) (j' kk' : ℤ)
    (hw' : (j', kk') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hne : j' ≠ j ∨ kk' ≠ kk)
    (a' : Fin (M.base (j', kk')).N) (heq : (M.base (j, kk)).arcSet a = (M.base (j', kk')).arcSet a')
    (hper : ∀ k₀ : Fin M.winReg.N, (M.base (j, kk)).arcSet a ≠ M.winReg.arcSet k₀)
    (hsq : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a →
        (j'' = j ∧ kk'' = kk) ∨ (j'' = j' ∧ kk'' = kk')) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ some (j, kk) ∧ Shares M ρ' ((M.base (j, kk)).arcSet a) ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' ((M.base (j, kk)).arcSet a) → ρ'' = some (j, kk) ∨ ρ'' = ρ' := by
  refine ⟨some (j', kk'), some_mk_ne hne, (shares_some_iff M _ _).2 ⟨hw', a', heq.symm⟩, ?_⟩
  intro ρ'' h''
  rcases ρ'' with _ | ⟨j'', kk''⟩
  · obtain ⟨k₀, hk₀⟩ := (shares_none_iff M _).1 h''
    exact absurd hk₀.symm (hper k₀)
  · obtain ⟨hw'', a'', ha''⟩ := (shares_some_iff M _ _).1 h''
    rcases hsq j'' kk'' hw'' a'' ha'' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl (some_mk_eq e1 e2)
    · exact Or.inr (some_mk_eq e1 e2)

theorem two_with_outside {j kk : ℤ} (a : Fin (M.base (j, kk)).N) (k₀ : Fin M.winReg.N)
    (heq : (M.base (j, kk)).arcSet a = M.winReg.arcSet k₀)
    (hsq : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a →
        j'' = j ∧ kk'' = kk) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ some (j, kk) ∧ Shares M ρ' ((M.base (j, kk)).arcSet a) ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' ((M.base (j, kk)).arcSet a) → ρ'' = some (j, kk) ∨ ρ'' = ρ' := by
  refine ⟨none, (Option.some_ne_none _).symm, (shares_none_iff M _).2 ⟨k₀, heq.symm⟩, ?_⟩
  intro ρ'' h''
  rcases ρ'' with _ | ⟨j'', kk''⟩
  · exact Or.inr rfl
  · obtain ⟨hw'', a'', ha''⟩ := (shares_some_iff M _ _).1 h''
    obtain ⟨e1, e2⟩ := hsq j'' kk'' hw'' a'' ha''
    exact Or.inl (some_mk_eq e1 e2)

theorem uniq_of_none (k₀ : Fin M.winReg.N) (q1 q2 : ℤ)
    (hsq : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = M.winReg.arcSet k₀ →
        j'' = q1 ∧ kk'' = q2) :
    ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' (M.winReg.arcSet k₀) → ρ'' = none ∨ ρ'' = some (q1, q2) := by
  intro ρ'' h''
  rcases ρ'' with _ | ⟨j'', kk''⟩
  · exact Or.inl rfl
  · obtain ⟨hw'', a'', ha''⟩ := (shares_some_iff M _ _).1 h''
    obtain ⟨e1, e2⟩ := hsq j'' kk'' hw'' a'' ha''
    exact Or.inr (some_mk_eq e1 e2)

theorem two_regions_none (Z : Set ℂ) (hsh : Shares M none Z) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ none ∧ Shares M ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' Z → ρ'' = none ∨ ρ'' = ρ' := by
  obtain ⟨k₀, rfl⟩ := (shares_none_iff M Z).1 hsh
  have hjj := M.hjlt
  have hkk := M.hklt
  rcases win_cases M k₀ with ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩ |
    ⟨i, h1, h2, e⟩ | ⟨i, h1, h2, e⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_bottom (isSquare_base M i M.klo)
    refine ⟨some (i, M.klo), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨h1, h2⟩, le_rfl, by omega⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ i M.klo ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨-, hk'', -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -⟩ := SideIdentity.bottom_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hk'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_top (isSquare_base M i M.khi)
    refine ⟨some (i, M.khi), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨h1, h2⟩, by omega, le_rfl⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ i M.khi ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨-, -, hk''⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -⟩ := SideIdentity.top_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hk'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_leftUpper (isSquare_base M M.jlo i) (yL_jlo M i)
    refine ⟨some (M.jlo, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨le_rfl, by omega⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jlo i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨hj'', -⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.leftUpper_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_leftLower (isSquare_base M M.jlo i) (yL_jlo M i)
    refine ⟨some (M.jlo, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨le_rfl, by omega⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jlo i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨hj'', -⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.leftLower_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_rightLower (isSquare_base M M.jhi i) (cy_eq M M.jhi i)
    refine ⟨some (M.jhi, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨by omega, le_rfl⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jhi i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨-, hj''⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.rightLower_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩
  · obtain ⟨a, -, ha⟩ := SideIdentity.exists_arcSet_eq_rightUpper (isSquare_base M M.jhi i) (cy_eq M M.jhi i)
    refine ⟨some (M.jhi, i), Option.some_ne_none _,
      (shares_some_iff M _ _).2 ⟨(mem_win_iff M).2 ⟨⟨by omega, le_rfl⟩, h1, h2⟩, a, ha.trans e.symm⟩,
      uniq_of_none M k₀ M.jhi i ?_⟩
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨-, hj''⟩, -⟩ := (mem_win_iff M).1 hw''
    obtain ⟨e1, e2, -, -⟩ := SideIdentity.rightUpper_of_arcSet_eq M.hhm (isSquare_base M j'' kk'') hj'' a'' (ha''.trans e)
    exact ⟨e1, e2⟩

theorem two_regions_some (j kk : ℤ) (Z : Set ℂ) (hsh : Shares M (some (j, kk)) Z) :
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ some (j, kk) ∧ Shares M ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' Z → ρ'' = some (j, kk) ∨ ρ'' = ρ' := by
  obtain ⟨hw, a, rfl⟩ := (shares_some_iff M (j, kk) Z).1 hsh
  obtain ⟨⟨hj, hj2⟩, hk, hk2⟩ := (mem_win_iff M).1 hw
  have hsquares : ∀ (j'' kk'' : ℤ), (j'', kk'') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi →
      ∀ a'' : Fin (M.base (j'', kk'')).N, (M.base (j'', kk'')).arcSet a'' = (M.base (j, kk)).arcSet a →
        M.jlo ≤ j'' ∧ j'' ≤ M.jhi ∧ M.klo ≤ kk'' ∧ kk'' ≤ M.khi ∧
        ((j'' = j ∧ kk'' = kk) ∨ ((a.val = 0 ∨ a.val = 5) ∧ j'' = j + 1 ∧ kk'' = kk) ∨
          ((a.val = 2 ∨ a.val = 3) ∧ j'' = j - 1 ∧ kk'' = kk) ∨ (a.val = 1 ∧ j'' = j ∧ kk'' = kk + 1) ∨
          (a.val = 4 ∧ j'' = j ∧ kk'' = kk - 1)) := by
    intro j'' kk'' hw'' a'' ha''
    obtain ⟨⟨hj'', hj''2⟩, hk'', hk''2⟩ := (mem_win_iff M).1 hw''
    exact ⟨hj'', hj''2, hk'', hk''2, squares_of_arc M hj a hj'' a'' ha''⟩
  have hperim := sq_per M hj hj2 hk hk2 a
  rcases (arcData_base M j kk).arcSet_cases a with ⟨h0, -⟩ | ⟨h1, -⟩ | ⟨h2, -⟩ | ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨h5, -⟩
  ·
    by_cases hlt : j < M.jhi
    · obtain ⟨a', ha'⟩ := exists_idx M (j + 1, kk) 2 (by omega)
      refine two_of_square M a (j + 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₀₂ M hj rfl a h0 a' ha') ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jhi := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_rightUpper M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_rightUpper (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a h0).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : kk < M.khi
    · obtain ⟨a', ha'⟩ := exists_idx M (j, kk + 1) 4 (by omega)
      refine two_of_square M a j (kk + 1) ((mem_win_iff M).2 ⟨⟨hj, hj2⟩, by omega, by omega⟩)
        (Or.inr (by omega)) a' (upper_arc₁₄ M rfl a h1 a' ha') ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hkk : kk = M.khi := by omega
      subst hkk
      obtain ⟨k₀, hk₀⟩ := win_top M j hj hj2
      refine two_with_outside M a k₀ ((SideIdentity.arcSet_eq_top (isSquare_base M j M.khi) a h1).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : M.jlo < j
    · obtain ⟨a', ha'⟩ := exists_idx M (j - 1, kk) 0 (by omega)
      refine two_of_square M a (j - 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₀₂ M (by omega) (by omega) a' ha' a h2).symm ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jlo := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_leftUpper M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_leftUpper (isSquare_base M M.jlo kk) (yL_jlo M kk) a h2).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : M.jlo < j
    · obtain ⟨a', ha'⟩ := exists_idx M (j - 1, kk) 5 (by omega)
      refine two_of_square M a (j - 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₅₃ M (by omega) (by omega) a' ha' a h3).symm ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jlo := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_leftLower M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_leftLower (isSquare_base M M.jlo kk) (yL_jlo M kk) a h3).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : M.klo < kk
    · obtain ⟨a', ha'⟩ := exists_idx M (j, kk - 1) 1 (by omega)
      refine two_of_square M a j (kk - 1) ((mem_win_iff M).2 ⟨⟨hj, hj2⟩, by omega, by omega⟩)
        (Or.inr (by omega)) a' (upper_arc₁₄ M (by omega) a' ha' a h4).symm ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hkk : kk = M.klo := by omega
      subst hkk
      obtain ⟨k₀, hk₀⟩ := win_bottom M j hj hj2
      refine two_with_outside M a k₀ ((SideIdentity.arcSet_eq_bottom (isSquare_base M j M.klo) a h4).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega
  ·
    by_cases hlt : j < M.jhi
    · obtain ⟨a', ha'⟩ := exists_idx M (j + 1, kk) 3 (by omega)
      refine two_of_square M a (j + 1) kk ((mem_win_iff M).2 ⟨⟨by omega, by omega⟩, hk, hk2⟩)
        (Or.inl (by omega)) a' (right_arc₅₃ M hj rfl a h5 a' ha') ?_ ?_
      · intro k₀ hk₀
        have h' := hperim k₀ hk₀
        omega
      · intro j'' kk'' hw'' a'' ha''
        have h' := hsquares j'' kk'' hw'' a'' ha''
        omega
    · have hjj : j = M.jhi := by omega
      subst hjj
      obtain ⟨k₀, hk₀⟩ := win_rightLower M kk hk hk2
      refine two_with_outside M a k₀
        ((SideIdentity.arcSet_eq_rightLower (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a h5).trans hk₀.symm) ?_
      intro j'' kk'' hw'' a'' ha''
      have h' := hsquares j'' kk'' hw'' a'' ha''
      omega

theorem two_regions : ∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares M ρ Z →
    ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares M ρ' Z ∧
      ∀ ρ'' : Option (ℤ × ℤ), Shares M ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ' := by
  intro ρ Z hsh
  rcases ρ with _ | ⟨j, kk⟩
  · exact two_regions_none M Z hsh
  · exact two_regions_some M j kk Z hsh

theorem adj_right {j kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j + 1, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j + 1, kk)).K) : Adj M v (some (j, kk)) (some (j + 1, kk)) := by
  obtain ⟨⟨hj, -⟩, -⟩ := (mem_win_iff M).1 hw
  obtain ⟨⟨-, r2⟩, i1, i2⟩ := of_mem_baseK M hv
  obtain ⟨⟨r1', -⟩, -⟩ := of_mem_baseK M hv'
  have hre : v.re = M.o + (j + 1) * M.hm := le_antisymm r2 (by exact_mod_cast r1')
  have D := arcData_base M j kk
  by_cases hc : (M.ctr (j, kk)).im ≤ v.im
  · obtain ⟨a0, ha0⟩ := exists_idx M (j, kk) 0 (by omega)
    obtain ⟨a2, ha2⟩ := exists_idx M (j + 1, kk) 2 (by omega)
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a0, D.arc0 a0 ha0⟩)
      ((shares_some_iff M _ _).2 ⟨hw', a2, (right_arc₀₂ M hj rfl a0 ha0 a2 ha2).symm.trans (D.arc0 a0 ha0)⟩)
      (mem_vseg.2 ⟨hre, hc, i2⟩)
  · obtain ⟨a5, ha5⟩ := exists_idx M (j, kk) 5 (by omega)
    obtain ⟨a3, ha3⟩ := exists_idx M (j + 1, kk) 3 (by omega)
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a5, D.arc5 a5 ha5⟩)
      ((shares_some_iff M _ _).2 ⟨hw', a3, (right_arc₅₃ M hj rfl a5 ha5 a3 ha3).symm.trans (D.arc5 a5 ha5)⟩)
      (mem_vseg.2 ⟨hre, i1, (not_le.mp hc).le⟩)

theorem adj_upper {j kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j, kk + 1) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j, kk + 1)).K) : Adj M v (some (j, kk)) (some (j, kk + 1)) := by
  obtain ⟨⟨r1, r2⟩, -, i2⟩ := of_mem_baseK M hv
  obtain ⟨-, i1', -⟩ := of_mem_baseK M hv'
  have him : v.im = M.o + (kk + 1) * M.hm := le_antisymm i2 (by exact_mod_cast i1')
  have D := arcData_base M j kk
  obtain ⟨a1, ha1⟩ := exists_idx M (j, kk) 1 (by omega)
  obtain ⟨a4, ha4⟩ := exists_idx M (j, kk + 1) 4 (by omega)
  exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a1, D.arc1 a1 ha1⟩)
    ((shares_some_iff M _ _).2 ⟨hw', a4, (upper_arc₁₄ M rfl a1 ha1 a4 ha4).symm.trans (D.arc1 a1 ha1)⟩)
    (mem_hseg.2 ⟨him, r1, r2⟩)

theorem adj_outside {j kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hv : v ∈ (M.base (j, kk)).K) (hout : v ∉ M.winReg.Kint) : Adj M v (some (j, kk)) none := by
  obtain ⟨⟨hj, hj2⟩, hk, hk2⟩ := (mem_win_iff M).1 hw
  obtain ⟨⟨r1, r2⟩, i1, i2⟩ := of_mem_baseK M hv
  rcases not_mem_winKint M hout with h1 | h2 | h3 | h4
  ·
    have hjj : j = M.jlo := le_antisymm (int_le_of_grid₀₀ M.hhm (r1.trans h1)) hj
    subst hjj
    have hre : v.re = M.o + M.jlo * M.hm := le_antisymm h1 r1
    by_cases hc : M.cy (M.jlo, kk) ≤ v.im
    · obtain ⟨a2, ha2⟩ := exists_idx M (M.jlo, kk) 2 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_leftUpper M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2 ⟨hw, a2, SideIdentity.arcSet_eq_leftUpper (isSquare_base M M.jlo kk) (yL_jlo M kk) a2 ha2⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, hc, i2⟩
    · obtain ⟨a3, ha3⟩ := exists_idx M (M.jlo, kk) 3 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_leftLower M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2 ⟨hw, a3, SideIdentity.arcSet_eq_leftLower (isSquare_base M M.jlo kk) (yL_jlo M kk) a3 ha3⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, i1, (not_le.mp hc).le⟩
  ·
    have hjj : j = M.jhi := le_antisymm hj2 (int_le_of_grid₁₁ M.hhm (h2.trans r2))
    subst hjj
    have hre : v.re = M.o + (M.jhi + 1) * M.hm := le_antisymm r2 h2
    by_cases hc : M.cy (M.jhi, kk) ≤ v.im
    · obtain ⟨a0, ha0⟩ := exists_idx M (M.jhi, kk) 0 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_rightUpper M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2
          ⟨hw, a0, SideIdentity.arcSet_eq_rightUpper (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a0 ha0⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, hc, i2⟩
    · obtain ⟨a5, ha5⟩ := exists_idx M (M.jhi, kk) 5 (by omega)
      obtain ⟨k₀, hk₀⟩ := win_rightLower M kk hk hk2
      exact adj_of_arcs M
        ((shares_some_iff M _ _).2
          ⟨hw, a5, SideIdentity.arcSet_eq_rightLower (isSquare_base M M.jhi kk) (cy_eq M M.jhi kk) a5 ha5⟩)
        ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨hre, i1, (not_le.mp hc).le⟩
  ·
    have hkk : kk = M.klo := le_antisymm (int_le_of_grid₀₀ M.hhm (i1.trans h3)) hk
    subst hkk
    have him : v.im = M.o + M.klo * M.hm := le_antisymm h3 i1
    obtain ⟨a4, ha4⟩ := exists_idx M (j, M.klo) 4 (by omega)
    obtain ⟨k₀, hk₀⟩ := win_bottom M j hj hj2
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a4, SideIdentity.arcSet_eq_bottom (isSquare_base M j M.klo) a4 ha4⟩)
      ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨him, r1, r2⟩
  ·
    have hkk : kk = M.khi := le_antisymm hk2 (int_le_of_grid₁₁ M.hhm (h4.trans i2))
    subst hkk
    have him : v.im = M.o + (M.khi + 1) * M.hm := le_antisymm i2 h4
    obtain ⟨a1, ha1⟩ := exists_idx M (j, M.khi) 1 (by omega)
    obtain ⟨k₀, hk₀⟩ := win_top M j hj hj2
    exact adj_of_arcs M ((shares_some_iff M _ _).2 ⟨hw, a1, SideIdentity.arcSet_eq_top (isSquare_base M j M.khi) a1 ha1⟩)
      ((shares_none_iff M _).2 ⟨k₀, hk₀⟩) ⟨him, r1, r2⟩

theorem horiz_chain {j j' kk : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j', kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j', kk)).K) : Relation.ReflTransGen (Adj M v) (some (j, kk)) (some (j', kk)) := by
  obtain ⟨⟨r1, r2⟩, -⟩ := of_mem_baseK M hv
  obtain ⟨⟨r1', r2'⟩, -⟩ := of_mem_baseK M hv'
  have b1 : j ≤ j' + 1 := int_le_of_grid₀₁ M.hhm (r1.trans r2')
  have b2 : j' ≤ j + 1 := int_le_of_grid₀₁ M.hhm (r1'.trans r2)
  have h3 : j' = j ∨ j' = j + 1 ∨ j = j' + 1 := by omega
  rcases h3 with e | e | e
  · subst e
    exact Relation.ReflTransGen.refl
  · subst e
    exact Relation.ReflTransGen.single (adj_right M hw hw' hv hv')
  · subst e
    exact Relation.ReflTransGen.single (adj_symm M (adj_right M hw' hw hv' hv))

theorem vert_chain {j kk kk' : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j, kk') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j, kk')).K) : Relation.ReflTransGen (Adj M v) (some (j, kk)) (some (j, kk')) := by
  obtain ⟨-, i1, i2⟩ := of_mem_baseK M hv
  obtain ⟨-, i1', i2'⟩ := of_mem_baseK M hv'
  have b1 : kk ≤ kk' + 1 := int_le_of_grid₀₁ M.hhm (i1.trans i2')
  have b2 : kk' ≤ kk + 1 := int_le_of_grid₀₁ M.hhm (i1'.trans i2)
  have h3 : kk' = kk ∨ kk' = kk + 1 ∨ kk = kk' + 1 := by omega
  rcases h3 with e | e | e
  · subst e
    exact Relation.ReflTransGen.refl
  · subst e
    exact Relation.ReflTransGen.single (adj_upper M hw hw' hv hv')
  · subst e
    exact Relation.ReflTransGen.single (adj_symm M (adj_upper M hw' hw hv' hv))

theorem sq_chain {j kk j' kk' : ℤ} {v : ℂ} (hw : (j, kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi)
    (hw' : (j', kk') ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi) (hv : v ∈ (M.base (j, kk)).K)
    (hv' : v ∈ (M.base (j', kk')).K) : Relation.ReflTransGen (Adj M v) (some (j, kk)) (some (j', kk')) := by
  obtain ⟨-, hk, hk2⟩ := (mem_win_iff M).1 hw
  obtain ⟨⟨hj', hj'2⟩, -⟩ := (mem_win_iff M).1 hw'
  obtain ⟨-, i1, i2⟩ := of_mem_baseK M hv
  obtain ⟨⟨r1', r2'⟩, -⟩ := of_mem_baseK M hv'
  have hwm : (j', kk) ∈ Icc M.jlo M.jhi ×ˢ Icc M.klo M.khi := (mem_win_iff M).2 ⟨⟨hj', hj'2⟩, hk, hk2⟩
  have hvm : v ∈ (M.base (j', kk)).K := mem_baseK_of M r1' r2' i1 i2
  exact (horiz_chain M hw hwm hv hvm).trans (vert_chain M hwm hw' hvm hv')

theorem star : ∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains M ρ v → Contains M ρ' v →
    Relation.ReflTransGen (Adj M v) ρ ρ' := by
  intro v ρ ρ' h h'
  rcases ρ with _ | ⟨j, kk⟩
  · rcases ρ' with _ | ⟨j', kk'⟩
    · exact Relation.ReflTransGen.refl
    · obtain ⟨hw', hv'⟩ := (contains_some_iff M _ _).1 h'
      exact Relation.ReflTransGen.single (adj_symm M (adj_outside M hw' hv' ((contains_none_iff M _).1 h)))
  · obtain ⟨hw, hv⟩ := (contains_some_iff M _ _).1 h
    rcases ρ' with _ | ⟨j', kk'⟩
    · exact Relation.ReflTransGen.single (adj_outside M hw hv ((contains_none_iff M _).1 h'))
    · obtain ⟨hw', hv'⟩ := (contains_some_iff M _ _).1 h'
      exact sq_chain M hw hw' hv hv'

end Window

end StarProperty

end Part_D1GridStarP

section Part_d1_planar_sol

set_option autoImplicit false

open scoped Real
open AlgebraicCurve Set PlanarRegions

namespace GridGeometry

open AlgebraicCurve.RadialRegion

theorem exists_grid_geometry (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ)
    (hjlt : jlo + 1 < jhi) (hklt : klo + 1 < khi) (ctr : ℤ × ℤ → ℂ)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm))
    (hzero : (o + jlo * hm < 0 ∧ 0 < o + (jhi + 1) * hm) ∧ (o + klo * hm < 0 ∧
      0 < o + (khi + 1) * hm))
    (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0)
    (base : ℤ × ℤ → RadialRegion)
    (hbase : ∀ p : ℤ × ℤ,
      (base p).q = ctr p ∧ (base p).N = 6 ∧
      (base p).K = {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (base p).Kint = {z : ℂ | z.re ∈ Ioo (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Ioo (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (ctr p).im (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcSet k = {z : ℂ | z.im = (o + (p.2 + 1) * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 2 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)
          (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 3 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)}) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcSet k = {z : ℂ | z.im = (o + p.2 * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (ctr p).im}) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 0 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 1 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 2 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 3 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (if p.1 = jlo then (ctr p).im else (ctr
          (p.1 - 1, p.2)).im)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 4 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 5 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 6 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin (base p).N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.cos t / ((o + (p.1 + 1) * hm) - (ctr p).re))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 1 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.sin t / ((o + (p.2 + 1) * hm) - (ctr p).im))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.cos t / ((ctr p).re - (o + p.1 * hm)))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 4 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.sin t / ((ctr p).im - (o + p.2 * hm)))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 → (base p).arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ (base p).K, z ∉ (base p).Kint →
        (base p).loop (if Complex.arg (z - ctr p) < 0 then Complex.arg
          (z - ctr p) + 2 * π else Complex.arg (z - ctr p))
          = z) ∧
      (∀ (k : Fin (base p).N) (t₁ t₂ : ℝ), t₁ ∈ (base p).arcIcc k → t₂ ∈ (base p).arcIcc k →
        t₁ ≤ t₂ →
        (base p).loop '' Icc t₁ t₂ = segment ℝ ((base p).loop t₁) ((base p).loop t₂)))
    (winReg : RadialRegion)
    (hwin :
      winReg.q = 0 ∧
      winReg.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin winReg.N, winReg.arcSet k = winReg.arcSet k' → k = k') ∧
      (∀ k : Fin winReg.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)})) :
    ∃ (sqbit : ∀ p : ℤ × ℤ, Fin (base p).N → Bool) (perbit : Fin winReg.N → Bool) (B₀ : Finset ℂ)
      (Shares : Option (ℤ × ℤ) → Set ℂ → Prop) (Contains : Option (ℤ × ℤ) → ℂ → Prop),
      (∀ (p : ℤ × ℤ) (k k' : Fin (base p).N), (base p).arcSet k = (base p).arcSet k' → k = k') ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p' k' = !sqbit p k) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ →
          perbit k₀ = !sqbit p k) ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((base p').arcIcc k') ∧
          ψ ((base p').φs k'.castSucc) = (base p).φs k.succ ∧
          ψ ((base p').φs k'.succ) = (base p).φs k.castSucc ∧
          ∀ t ∈ (base p').arcIcc k', (base p').loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (winReg.arcIcc k₀) ∧
          ψ (winReg.φs k₀.castSucc) = (base p).φs k.castSucc ∧
          ψ (winReg.φs k₀.succ) = (base p).φs k.succ ∧
          ∀ t ∈ winReg.arcIcc k₀, winReg.loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = false →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((base p).arcIcc k) ∧
          ψ ((base p).φs k.castSucc) = winReg.φs k₀.castSucc ∧
          ψ ((base p).φs k.succ) = winReg.φs k₀.succ ∧
          ∀ t ∈ (base p).arcIcc k, (base p).loop t = winReg.loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (Z : Set ℂ), Shares (some p) Z ↔
        p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧ ∃ k : Fin (base p).N, (base p).arcSet k = Z) ∧
      (∀ Z : Set ℂ, Shares none Z ↔ ∃ k₀ : Fin winReg.N, winReg.arcSet k₀ = Z) ∧
      (∀ (p : ℤ × ℤ) (v : ℂ), Contains (some p) v ↔ p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧
        v ∈ (base p).K) ∧
      (∀ v : ℂ, Contains none v ↔ v ∉ winReg.Kint) ∧
      (∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares ρ Z →
        ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares ρ' Z ∧
          ∀ ρ'' : Option (ℤ × ℤ), Shares ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ') ∧
      (∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains ρ v → Contains ρ' v →
        Relation.ReflTransGen
          (fun ρ₁ ρ₂ : Option (ℤ × ℤ) => ∃ Z : Set ℂ, Shares ρ₁ Z ∧ Shares ρ₂ Z ∧ v ∈ Z) ρ ρ') ∧
      B₀.card = ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) +
        (jhi - jlo + 1).toNat * (khi - klo + 1).toNat + (khi - klo + 1).toNat ∧
      (∀ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∀ i : Fin ((base p).N + 1), (base p).loop
        ((base p).φs i) ∈ B₀) ∧
      (∀ i : Fin (winReg.N + 1), winReg.loop (winReg.φs i) ∈ B₀) ∧
      (∀ v ∈ B₀, ∃ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∃ k : Fin (base p).N,
        v = (base p).loop ((base p).φs k.castSucc) ∨ v = (base p).loop ((base p).φs k.succ)) ∧
      (∀ v ∈ B₀, ∃ j : ℤ, v.re - o = j * hm) := by
  let M : GridData := ⟨o, hm, hhm, jlo, jhi, klo, khi, hjlt, hklt, ctr, hctr, hzero, hcy0, base, hbase,
    winReg, hwin⟩
  have hsq : ∀ p : ℤ × ℤ, SideIdentity.IsSquare o hm p.1 p.2 (ctr p) (M.yL p) (base p) := fun p =>
    ⟨(hctr p).1.1, (hctr p).1.2, (hctr p).2.1, (hctr p).2.2, (M.yL_mem p).1, (M.yL_mem p).2, hbase p⟩
  have hj : jlo ≤ jhi := by omega
  have hk : klo ≤ khi := by omega
  have hbreak : ∀ (R : RadialRegion), 0 < R.N → ∀ i : Fin (R.N + 1),
      ∃ k : Fin R.N, i = k.castSucc ∨ i = k.succ := by
    intro R hN i
    by_cases h : i.val < R.N
    · exact ⟨⟨i.val, h⟩, Or.inl (Fin.ext (by simp))⟩
    · refine ⟨⟨R.N - 1, by omega⟩, Or.inr (Fin.ext ?_)⟩
      have hi := i.isLt
      simp only [Fin.val_succ]
      omega
  refine ⟨ArcReversal.sqbit M, ArcReversal.perbit M, GridVertices.B₀ o hm jlo jhi klo khi ctr, StarProperty.Shares M,
    StarProperty.Contains M, ?_, ArcReversal.bit_sq_sq M, ArcReversal.bit_sq_per M, ArcReversal.rev_sq_sq M,
    ArcReversal.rev_per_to_sq M, ArcReversal.rev_sq_to_per M, fun _ _ => Iff.rfl, fun _ => Iff.rfl,
    fun _ _ => Iff.rfl, fun _ => Iff.rfl, StarProperty.two_regions M, StarProperty.star M, ?_, ?_, ?_, ?_,
    fun v hv => GridVertices.B₀_off_lines v hv⟩
  · exact fun p k k' h => SideIdentity.arcSet_injective (hsq p) k k' h
  · exact GridVertices.card_B₀ hhm hctr hj hk
  · intro p hp i
    exact GridVertices.rect_break_mem (ctr := ctr) p hp.1.1 hp.1.2 hp.2.1 hp.2.2
      (hx₀ := (hctr p).1.1) (hx₁ := (hctr p).1.2) (hy₀ := (hctr p).2.1) (hy₁ := (hctr p).2.2)
      (hL₀ := (M.yL_mem p).1) (hL₁ := (M.yL_mem p).2) (hbase p) i
  · intro i
    have hN : 0 < winReg.N := by
      have h2 := M.two_le_winReg_N
      exact lt_of_lt_of_le Nat.zero_lt_two h2
    obtain ⟨k, hk' | hk'⟩ := hbreak winReg hN i
    · rw [hk']
      exact (GridVertices.window_break_mem (ctr := ctr) (hhm := hhm) (hj := hj) (hk := hk)
        (hcy := fun p => (hctr p).2) (hx₀ := hzero.1.1) (hx₁ := hzero.1.2) (hy₀ := hzero.2.1)
        (hy₁ := hzero.2.2) (hcy0 := hcy0) hwin k).1
    · rw [hk']
      exact (GridVertices.window_break_mem (ctr := ctr) (hhm := hhm) (hj := hj) (hk := hk)
        (hcy := fun p => (hctr p).2) (hx₀ := hzero.1.1) (hx₁ := hzero.1.2) (hy₀ := hzero.2.1)
        (hy₁ := hzero.2.2) (hcy0 := hcy0) hwin k).2
  · intro v hv
    obtain ⟨j, kk, hj₁, hj₂, hk₁, hk₂, hb⟩ := GridVertices.mem_B₀_iff_break hj hk v hv
    obtain ⟨i, hi⟩ := hb (hctr (j, kk)).1.1 (hctr (j, kk)).1.2 (hctr (j, kk)).2.1 (hctr (j, kk)).2.2
      (M.yL_mem (j, kk)).1 (M.yL_mem (j, kk)).2 (base (j, kk)) (hbase (j, kk))
    have hN : 0 < (base (j, kk)).N := by
      rw [(hbase (j, kk)).2.1]
      omega
    obtain ⟨k', hk' | hk'⟩ := hbreak (base (j, kk)) hN i
    · exact ⟨(j, kk), ⟨⟨hj₁, hj₂⟩, ⟨hk₁, hk₂⟩⟩, k', Or.inl (by rw [← hi, hk'])⟩
    · exact ⟨(j, kk), ⟨⟨hj₁, hj₂⟩, ⟨hk₁, hk₂⟩⟩, k', Or.inr (by rw [← hi, hk'])⟩

end GridGeometry

end Part_d1_planar_sol

open scoped Real
open AlgebraicCurve Set

theorem solution (o hm : ℝ) (hhm : 0 < hm) (jlo jhi klo khi : ℤ)
    (hjlt : jlo + 1 < jhi) (hklt : klo + 1 < khi) (ctr : ℤ × ℤ → ℂ)
    (hctr : ∀ p : ℤ × ℤ, (o + p.1 * hm < (ctr p).re ∧ (ctr p).re < o + (p.1 + 1) * hm) ∧
      (o + p.2 * hm < (ctr p).im ∧ (ctr p).im < o + (p.2 + 1) * hm))
    (hzero : (o + jlo * hm < 0 ∧ 0 < o + (jhi + 1) * hm) ∧ (o + klo * hm < 0 ∧
      0 < o + (khi + 1) * hm))
    (hcy0 : ∀ k : ℤ, o + k * hm < 0 → 0 < o + (k + 1) * hm → (ctr (jhi, k)).im = 0)
    (base : ℤ × ℤ → RadialRegion)
    (hbase : ∀ p : ℤ × ℤ,
      (base p).q = ctr p ∧ (base p).N = 6 ∧
      (base p).K = {z : ℂ | z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (base p).Kint = {z : ℂ | z.re ∈ Ioo (o + p.1 * hm) (o + (p.1 + 1) * hm) ∧
        z.im ∈ Ioo (o + p.2 * hm) (o + (p.2 + 1) * hm)} ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (ctr p).im (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcSet k = {z : ℂ | z.im = (o + (p.2 + 1) * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 2 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)
          (o + (p.2 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 3 → (base p).arcSet k = {z : ℂ | z.re = (o + p.1 * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (if p.1 = jlo then (ctr p).im else (ctr (p.1 - 1, p.2)).im)}) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcSet k = {z : ℂ | z.im = (o + p.2 * hm) ∧
        z.re ∈ Icc (o + p.1 * hm) (o + (p.1 + 1) * hm)}) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcSet k = {z : ℂ | z.re = (o + (p.1 + 1) * hm) ∧
        z.im ∈ Icc (o + p.2 * hm) (ctr p).im}) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 0 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 1 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 2 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + (p.2 + 1) * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 3 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (if p.1 = jlo then (ctr p).im else (ctr
          (p.1 - 1, p.2)).im)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 4 →
        (base p).loop ((base p).φs k) = ⟨(o + p.1 * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 5 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (o + p.2 * hm)⟩) ∧
      (∀ k : Fin ((base p).N + 1), k.val = 6 →
        (base p).loop ((base p).φs k) = ⟨(o + (p.1 + 1) * hm), (ctr p).im⟩) ∧
      (∀ k : Fin (base p).N, k.val = 0 ∨ k.val = 5 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.cos t / ((o + (p.1 + 1) * hm) - (ctr p).re))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 1 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (Real.sin t / ((o + (p.2 + 1) * hm) - (ctr p).im))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 →
        (∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.cos t / ((ctr p).re - (o + p.1 * hm)))⁻¹)) ∧
      (∀ k : Fin (base p).N, k.val = 4 →
        ∀ t ∈ (base p).arcIcc k, (base p).r t = (-Real.sin t / ((ctr p).im - (o + p.2 * hm)))⁻¹) ∧
      (∀ k : Fin (base p).N, k.val = 0 → (base p).arcIcc k ⊆ Ico 0 (π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 1 → (base p).arcIcc k ⊆ Ioo 0 π) ∧
      (∀ k : Fin (base p).N, k.val = 2 ∨ k.val = 3 → (base p).arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∧
      (∀ k : Fin (base p).N, k.val = 4 → (base p).arcIcc k ⊆ Ioo π (2 * π)) ∧
      (∀ k : Fin (base p).N, k.val = 5 → (base p).arcIcc k ⊆ Ioc (3 * π / 2) (2 * π)) ∧
      (∀ z ∈ (base p).K, z ∉ (base p).Kint →
        (base p).loop (if Complex.arg (z - ctr p) < 0 then Complex.arg
          (z - ctr p) + 2 * π else Complex.arg (z - ctr p))
          = z) ∧
      (∀ (k : Fin (base p).N) (t₁ t₂ : ℝ), t₁ ∈ (base p).arcIcc k → t₂ ∈ (base p).arcIcc k →
        t₁ ≤ t₂ →
        (base p).loop '' Icc t₁ t₂ = segment ℝ ((base p).loop t₁) ((base p).loop t₂)))
    (winReg : RadialRegion)
    (hwin :
      winReg.q = 0 ∧
      winReg.K = {z : ℂ | z.re ∈ Icc (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Icc (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.Kint = {z : ℂ | z.re ∈ Ioo (o + jlo * hm) (o + (jhi + 1) * hm) ∧
        z.im ∈ Ioo (o + klo * hm) (o + (khi + 1) * hm)} ∧
      winReg.N = 2 * (jhi - jlo + 1).toNat + 4 * (khi - klo + 1).toNat ∧
      (∀ k k' : Fin winReg.N, winReg.arcSet k = winReg.arcSet k' → k = k') ∧
      (∀ k : Fin winReg.N,
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + j * hm, o + klo * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (j + 1) * hm, o + klo * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.sin t / (-(o + klo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo π (2 * π)) ∨
        (∃ j : ℤ, jlo ≤ j ∧ j ≤ jhi ∧
          winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
            z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (j + 1) * hm, o + (khi + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + j * hm, o + (khi + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.sin t / (o + (khi + 1) * hm))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo 0 π) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, o + (k₀ + 1) * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + jlo * hm, (ctr (jlo, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + jlo * hm, o + k₀ * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (-Real.cos t / (-(o + jlo * hm)))⁻¹) ∧
          winReg.arcIcc k ⊆ Ioo (π / 2) (3 * π / 2)) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, o + k₀ * hm⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2))) ∨
        (∃ k₀ : ℤ, klo ≤ k₀ ∧ k₀ ≤ khi ∧
          winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
            z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)} ∧
          winReg.loop (winReg.φs k.castSucc) = ⟨o + (jhi + 1) * hm, (ctr (jhi, k₀)).im⟩ ∧
          winReg.loop (winReg.φs k.succ) = ⟨o + (jhi + 1) * hm, o + (k₀ + 1) * hm⟩ ∧
          (∀ t ∈ winReg.arcIcc k, winReg.r t = (Real.cos t / (o + (jhi + 1) * hm))⁻¹) ∧
          (winReg.arcIcc k ⊆ Ioo (-(π / 2)) (π / 2) ∨
            winReg.arcIcc k ⊆ Ioo (3 * π / 2) (5 * π / 2)))) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + klo * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ j : ℤ, jlo ≤ j → j ≤ jhi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.im = o + (khi + 1) * hm ∧
          z.re ∈ Icc (o + j * hm) (o + (j + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc ((ctr (jlo, k₀)).im) (o + (k₀ + 1) * hm)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + jlo * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jlo, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc (o + k₀ * hm) ((ctr (jhi, k₀)).im)}) ∧
      (∀ k₀ : ℤ, klo ≤ k₀ → k₀ ≤ khi → ∃ k : Fin winReg.N,
        winReg.arcSet k = {z : ℂ | z.re = o + (jhi + 1) * hm ∧
          z.im ∈ Icc ((ctr (jhi, k₀)).im) (o + (k₀ + 1) * hm)})) :
    ∃ (sqbit : ∀ p : ℤ × ℤ, Fin (base p).N → Bool) (perbit : Fin winReg.N → Bool) (B₀ : Finset ℂ)
      (Shares : Option (ℤ × ℤ) → Set ℂ → Prop) (Contains : Option (ℤ × ℤ) → ℂ → Prop),
      (∀ (p : ℤ × ℤ) (k k' : Fin (base p).N), (base p).arcSet k = (base p).arcSet k' → k = k') ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p' k' = !sqbit p k) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ →
          perbit k₀ = !sqbit p k) ∧
      (∀ p p' : ℤ × ℤ, p ≠ p' → ∀ (k : Fin (base p).N) (k' : Fin (base p').N),
        (base p).arcSet k = (base p').arcSet k' → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictAntiOn ψ ((base p').arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((base p').arcIcc k') ∧
          ψ ((base p').φs k'.castSucc) = (base p).φs k.succ ∧
          ψ ((base p').φs k'.succ) = (base p).φs k.castSucc ∧
          ∀ t ∈ (base p').arcIcc k', (base p').loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = true →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ (winReg.arcIcc k₀) ∧ ContDiffOn ℝ 1 ψ (winReg.arcIcc k₀) ∧
          ψ (winReg.φs k₀.castSucc) = (base p).φs k.castSucc ∧
          ψ (winReg.φs k₀.succ) = (base p).φs k.succ ∧
          ∀ t ∈ winReg.arcIcc k₀, winReg.loop t = (base p).loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (k : Fin (base p).N) (k₀ : Fin winReg.N),
        p ∈ Icc jlo jhi ×ˢ Icc klo khi → (base p).arcSet k = winReg.arcSet k₀ → sqbit p k = false →
        ∃ ψ : ℝ → ℝ, StrictMonoOn ψ ((base p).arcIcc k) ∧ ContDiffOn ℝ 1 ψ ((base p).arcIcc k) ∧
          ψ ((base p).φs k.castSucc) = winReg.φs k₀.castSucc ∧
          ψ ((base p).φs k.succ) = winReg.φs k₀.succ ∧
          ∀ t ∈ (base p).arcIcc k, (base p).loop t = winReg.loop (ψ t)) ∧
      (∀ (p : ℤ × ℤ) (Z : Set ℂ), Shares (some p) Z ↔
        p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧ ∃ k : Fin (base p).N, (base p).arcSet k = Z) ∧
      (∀ Z : Set ℂ, Shares none Z ↔ ∃ k₀ : Fin winReg.N, winReg.arcSet k₀ = Z) ∧
      (∀ (p : ℤ × ℤ) (v : ℂ), Contains (some p) v ↔ p ∈ Icc jlo jhi ×ˢ Icc klo khi ∧
        v ∈ (base p).K) ∧
      (∀ v : ℂ, Contains none v ↔ v ∉ winReg.Kint) ∧
      (∀ (ρ : Option (ℤ × ℤ)) (Z : Set ℂ), Shares ρ Z →
        ∃ ρ' : Option (ℤ × ℤ), ρ' ≠ ρ ∧ Shares ρ' Z ∧
          ∀ ρ'' : Option (ℤ × ℤ), Shares ρ'' Z → ρ'' = ρ ∨ ρ'' = ρ') ∧
      (∀ (v : ℂ) (ρ ρ' : Option (ℤ × ℤ)), Contains ρ v → Contains ρ' v →
        Relation.ReflTransGen
          (fun ρ₁ ρ₂ : Option (ℤ × ℤ) => ∃ Z : Set ℂ, Shares ρ₁ Z ∧ Shares ρ₂ Z ∧ v ∈ Z) ρ ρ') ∧
      B₀.card = ((jhi - jlo + 1).toNat + 1) * ((khi - klo + 1).toNat + 1) +
        (jhi - jlo + 1).toNat * (khi - klo + 1).toNat + (khi - klo + 1).toNat ∧
      (∀ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∀ i : Fin ((base p).N + 1), (base p).loop
        ((base p).φs i) ∈ B₀) ∧
      (∀ i : Fin (winReg.N + 1), winReg.loop (winReg.φs i) ∈ B₀) ∧
      (∀ v ∈ B₀, ∃ p ∈ Icc jlo jhi ×ˢ Icc klo khi, ∃ k : Fin (base p).N,
        v = (base p).loop ((base p).φs k.castSucc) ∨ v = (base p).loop ((base p).φs k.succ)) ∧
      (∀ v ∈ B₀, ∃ j : ℤ, v.re - o = j * hm) := by
  exact GridGeometry.exists_grid_geometry (o := o) (hm := hm) (hhm := hhm) (jlo := jlo) (jhi := jhi) (klo := klo) (khi := khi) (hjlt := hjlt) (hklt := hklt) (ctr := ctr) (hctr := hctr) (hzero := hzero) (hcy0 := hcy0) (base := base) (hbase := hbase) (winReg := winReg) (hwin := hwin)

end S_AlgebraicCurve_RadialRegion_exists_grid_geometry
end P2MW
export P2MW.S_AlgebraicCurve_RadialRegion_exists_grid_geometry (solution)
