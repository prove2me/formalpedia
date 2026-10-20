-- Prove2me | Definitions.Def_Hintz2026_Domain
-- name    : Hintz2026_Domain
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T13:13:07.589834+00:00
-- url     : https://prove2.me/theorems/dfe4be28-4cc2-42cd-836d-d55e9faa0f8c
-- title:
--   Hintz2026 — Domain, parameters, and building blocks
-- statement:
--   Defines the subextremal Kerr-Newman parameter structure (mass $M>0$, spin $a$, charge $Q\neq 0$ with $a^2+Q^2<M^2$), the discriminant $\Delta = r^2 - 2Mr + a^2 + Q^2$, outer horizon radius $r_+ = M + \sqrt{M^2-a^2-Q^2}$, the domain $U = \{(r,\theta) : r > r_+,\ 0 < \theta < \pi\}$, and the complex coordinate $\bar{\rho} = r + ia\cos\theta$ with its conjugate $\bar{\rho}^* = r - ia\cos\theta$. Includes the facts that $U$ is open and nonempty, $\Delta > 0$ on $U$, $\bar{\rho}, \bar{\rho}^* \neq 0$ on $U$, and $Q^2 - M^2 < 0$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6)

import Mathlib

/-!
# Hintz 2026 — Domain, parameters, and building blocks

Source: Hintz, arXiv:2609.33661v1.
Definitions: SubextremalKN, Δ, r₊, U, ρ̄, ρ̄*.
-/

open Complex
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

structure SubextremalKN where
  M : ℝ
  a : ℝ
  Q : ℝ
  hM : 0 < M
  hQ : Q ≠ 0
  hSub : a ^ 2 + Q ^ 2 < M ^ 2

variable (p : SubextremalKN)

def Del (r : ℝ) : ℝ := r ^ 2 - 2 * p.M * r + p.a ^ 2 + p.Q ^ 2

def rPlus : ℝ := p.M + Real.sqrt (p.M ^ 2 - p.a ^ 2 - p.Q ^ 2)

theorem disc_pos : p.M ^ 2 - p.a ^ 2 - p.Q ^ 2 > 0 := by linarith [p.hSub]

theorem rPlus_pos : 0 < rPlus p := by
  unfold rPlus; linarith [p.hM, Real.sqrt_nonneg (p.M ^ 2 - p.a ^ 2 - p.Q ^ 2)]

def U : Set (Fin 2 → ℝ) :=
  {x | rPlus p < x 0 ∧ 0 < x 1 ∧ x 1 < Real.pi}

theorem isOpen_U : IsOpen (U p) :=
  IsOpen.inter (isOpen_lt continuous_const (continuous_apply 0))
    (IsOpen.inter (isOpen_lt continuous_const (continuous_apply 1))
      (isOpen_lt (continuous_apply 1) continuous_const))

theorem nonempty_U : (U p).Nonempty := by
  refine ⟨![rPlus p + 1, Real.pi / 2], ?_⟩
  simp only [U, Set.mem_setOf_eq, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  exact ⟨by linarith, by positivity, by linarith [Real.pi_pos]⟩

theorem Del_pos {r : ℝ} (hr : rPlus p < r) : 0 < Del p r := by
  unfold Del rPlus at *
  have hd := disc_pos p
  nlinarith [Real.sq_sqrt (le_of_lt hd), Real.sqrt_nonneg (p.M ^ 2 - p.a ^ 2 - p.Q ^ 2)]

theorem sin_pos_of_mem {x : Fin 2 → ℝ} (hx : x ∈ U p) : 0 < Real.sin (x 1) :=
  Real.sin_pos_of_pos_of_lt_pi hx.2.1 hx.2.2

def rhoBar (x : Fin 2 → ℝ) : ℂ := ⟨x 0, p.a * Real.cos (x 1)⟩

def rhoBarStar (x : Fin 2 → ℝ) : ℂ := ⟨x 0, -(p.a * Real.cos (x 1))⟩

theorem rhoBarStar_eq_conj (x : Fin 2 → ℝ) :
    rhoBarStar p x = conj (rhoBar p x) := by
  apply Complex.ext
  · simp [rhoBar, rhoBarStar, Complex.conj_re]
  · simp [rhoBar, rhoBarStar, Complex.conj_im]

theorem rhoBar_normSq (x : Fin 2 → ℝ) :
    Complex.normSq (rhoBar p x) = x 0 ^ 2 + p.a ^ 2 * Real.cos (x 1) ^ 2 := by
  simp only [rhoBar, Complex.normSq_mk]; ring

theorem rhoBar_ne_zero {x : Fin 2 → ℝ} (hx : x ∈ U p) : rhoBar p x ≠ 0 := by
  intro h
  have : Complex.normSq (rhoBar p x) = 0 := by rw [h]; simp
  rw [rhoBar_normSq] at this
  have hr : 0 < x 0 := lt_trans (rPlus_pos p) hx.1
  nlinarith [sq_nonneg (p.a * Real.cos (x 1)), sq_nonneg (x 0)]

theorem rhoBarStar_ne_zero {x : Fin 2 → ℝ} (hx : x ∈ U p) : rhoBarStar p x ≠ 0 := by
  rw [rhoBarStar_eq_conj]; simp [rhoBar_ne_zero p hx]

theorem Q_sq_sub_M_sq_neg : p.Q ^ 2 - p.M ^ 2 < 0 := by nlinarith [p.hSub]

theorem Q_sq_sub_M_sq_ne_zero : p.Q ^ 2 - p.M ^ 2 ≠ 0 := ne_of_lt (Q_sq_sub_M_sq_neg p)

theorem rhoBar_eq_ofReal (x : Fin 2 → ℝ) :
    rhoBar p x = ↑(x 0) + ↑(p.a * Real.cos (x 1)) * I := by
  rw [← Complex.mk_eq_add_mul_I]; rfl

theorem rhoBarStar_eq_ofReal (x : Fin 2 → ℝ) :
    rhoBarStar p x = ↑(x 0) - ↑(p.a * Real.cos (x 1)) * I := by
  have h := rhoBarStar_eq_conj p x
  rw [h, rhoBar_eq_ofReal, map_add, map_mul, conj_ofReal, conj_ofReal, conj_I]
  ring

end Hintz2026

end


