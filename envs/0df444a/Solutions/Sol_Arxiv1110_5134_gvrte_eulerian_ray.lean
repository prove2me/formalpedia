-- Prove2me | solution 1 for Arxiv1110_5134.gvrte_eulerian_ray
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-25T08:39:40.246278+00:00
-- url     : https://prove2.me/submissions/34ff50c0-2566-4a5c-8340-291e14831667

import Mathlib
import Definitions.Def_Arxiv1110_5134_Basic

open MeasureTheory Filter Topology Arxiv1110_5134
open scoped Matrix

theorem solution (n : ℝ → ℝ) (c : ℝ) (hc : 0 < c) (F : ℝ → ℝ → Stokes)
    (τ : ℝ → ℝ) (s : ℝ) (hn : 0 < n s) (hnd : DifferentiableAt ℝ n s)
    (hτ : HasDerivAt τ (n s / c) s)
    (hF : DifferentiableAt ℝ (fun p : ℝ × ℝ => F p.1 p.2) (τ s, s))
    (κe κa : Matrix (Fin 4) (Fin 4) ℝ) (κ : ℝ) (Ib : Stokes)
    (Z : Dir → Matrix (Fin 4) (Fin 4) ℝ) (L : Dir → Stokes) :
    transportOp n (fun t => F (τ t) t) s =
      (n s / c) • deriv (fun t' => F t' s) (τ s) + transportOp n (F (τ s)) s ∧
    (transportOp n (fun t => F (τ t) t) s + (κe + rytovMatrix κ) *ᵥ F (τ s) s =
        κa *ᵥ Ib + scatSource Z L ↔
      (n s / c) • deriv (fun t' => F t' s) (τ s) + transportOp n (F (τ s)) s +
          (κe + rytovMatrix κ) *ᵥ F (τ s) s = κa *ᵥ Ib + scatSource Z L) := by
  let D := fderiv ℝ (fun p : ℝ × ℝ => F p.1 p.2) (τ s, s)
  have hD : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2) D (τ s, s) := hF.hasFDerivAt
  have hg : HasDerivAt (fun t => (τ t, t)) (n s / c, 1) s :=
    hτ.prodMk (hasDerivAt_id s)
  have hcomp_raw := hD.comp_hasDerivAt (f := fun t => (τ t, t)) s hg
  have hcomp : HasDerivAt (fun t => F (τ t) t) (D (n s / c, 1)) s := hcomp_raw
  have hg1 : HasDerivAt (fun t' => (t', s)) (1, 0) (τ s) :=
    (hasDerivAt_id (τ s)).prodMk (hasDerivAt_const (τ s) s)
  have ht1_raw := hD.comp_hasDerivAt (f := fun t' => (t', s)) (τ s) hg1
  have ht1 : HasDerivAt (fun t' => F t' s) (D (1, 0)) (τ s) := ht1_raw
  have hg2 : HasDerivAt (fun t => (τ s, t)) (0, 1) s :=
    (hasDerivAt_const s (τ s)).prodMk (hasDerivAt_id s)
  have ht2_raw := hD.comp_hasDerivAt (f := fun t => (τ s, t)) s hg2
  have ht2 : HasDerivAt (fun t => F (τ s) t) (D (0, 1)) s := ht2_raw
  have hlin : D (n s / c, 1) = (n s / c) • D (1, 0) + D (0, 1) := by
    have hp : ((n s / c, 1) : ℝ × ℝ) = (n s / c) • (1, 0) + (0, 1) := by
      ext <;> simp
    rw [hp, map_add, map_smul]
  have hn2 : n s ^ 2 ≠ 0 := pow_ne_zero 2 hn.ne'
  have hinv := (hnd.hasDerivAt.pow 2).inv hn2
  have hprod1 := hinv.smul hcomp
  have hprod2 := hinv.smul ht2
  have hd1 : deriv (fun t => (n t ^ 2)⁻¹ • F (τ t) t) s =
      (n s ^ 2)⁻¹ • D (n s / c, 1) +
      (-(↑2 * n s ^ (2 - 1) * deriv n s) / (n s ^ 2) ^ 2) • F (τ s) s := hprod1.deriv
  have hd2 : deriv (fun t => (n t ^ 2)⁻¹ • F (τ s) t) s =
      (n s ^ 2)⁻¹ • D (0, 1) +
      (-(↑2 * n s ^ (2 - 1) * deriv n s) / (n s ^ 2) ^ 2) • F (τ s) s := hprod2.deriv
  have h1 : transportOp n (fun t => F (τ t) t) s =
      (n s / c) • deriv (fun t' => F t' s) (τ s) + transportOp n (F (τ s)) s := by
    unfold transportOp
    rw [hd1, hd2, ht1.deriv, hlin]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hn2]
    ring
  exact ⟨h1, by rw [h1]⟩
