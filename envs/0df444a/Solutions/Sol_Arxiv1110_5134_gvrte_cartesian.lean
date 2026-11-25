-- Prove2me | solution 1 for Arxiv1110_5134.gvrte_cartesian
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:17:45.566899+00:00
-- url     : https://prove2.me/submissions/c1689271-751e-4908-b596-9d42710867f6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic
import Theorems.Thm_Arxiv1110_5134_cartesian_streaming_forms

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n : Vec3 → ℝ) (c : ℝ) (hc : 0 < c)
    (F : ℝ → Vec3 → ℝ → ℝ → Stokes) (t : ℝ) (q : Vec3) (θ φ : ℝ)
    (hn : 0 < n q) (hnd : DifferentiableAt ℝ n q)
    (hFq : DifferentiableAt ℝ (fun y => F t y θ φ) q)
    (hFθ : DifferentiableAt ℝ (fun θ' => F t q θ' φ) θ)
    (hFφ : DifferentiableAt ℝ (fun φ' => F t q θ φ') φ) (hθ : Real.sin θ ≠ 0)
    (κe κa : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ) (Ib : Stokes)
    (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (L : Dir → Stokes) :
    (n q / c) • deriv (fun t' => F t' q θ φ) t +
        n q ^ 2 • cartStream n (fun y θ' φ' => (n y ^ 2)⁻¹ • F t y θ' φ') q θ φ +
        (κe + rytovMatrix κ) *ᵥ F t q θ φ = κa *ᵥ Ib + scatSource Z L ↔
      (n q / c) • deriv (fun t' => F t' q θ φ) t +
        dirDot θ φ (cartGrad (fun y => F t y θ φ) q) +
        angularCons ((n q)⁻¹ • cartGrad n q) (F t) q θ φ +
        (κe + rytovMatrix κ) *ᵥ F t q θ φ = κa *ᵥ Ib + scatSource Z L := by
  have h := (cartesian_streaming_forms n (F t) q θ φ hn hnd hFq hFθ hFφ hθ).2.2
  rw [h, ← add_assoc]
