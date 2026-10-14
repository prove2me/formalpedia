-- Prove2me | Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
-- name    : NoHair_KerrNewmanEinstein_Atoms
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-13T06:55:40.241886+00:00
-- url     : https://prove2.me/theorems/1d7fc455-1a2a-4cba-9119-999fd3949a4e
-- title:
--   Kerr–Newman solves the Einstein equation: Atoms (block 2 of 13)
-- statement:
--   **Atoms.** Coordinate partials of the atoms, of the Kerr–Schild profile and of the potential factor; the metric, its inverse and its Christoffel symbols as formulas in the atoms.
--
--   This block belongs to a machine-checked proof that the Kerr–Newman metric $g=\eta+f\,k\otimes k$ (Kerr–Schild form, $f=r^2(2mr-e^2)/(r^4+a^2z^2)$) and field $F=dA$, $A=\frac{e r^3}{r^4+a^2z^2}k$, satisfy the Einstein equation $G_{\mu\nu}=2(F_{\mu\alpha}F_\nu{}^\alpha-\tfrac14 g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta})$ at every point with $r>0$, using the definitions `NoHair_coordinates` and `NoHair_kerrNewman` (statement `NoHair.kerrNewman_einstein`). Everything is expressed through the atoms $r$, $k_1,k_2,k_3$ and $W=1/(r^2+a^2k_3^2)$, which satisfy $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$. The curvature computation becomes polynomial identities modulo these two relations; each identity is closed by `linear_combination` with cofactors precomputed by a Gröbner-basis division. The proof is split into 13 blocks only so that each compiles within the platform's time limit; they contain no `sorry` and use only the standard axioms.
-- source:
--   Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*. Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, https://doi.org/10.1063/1.1704351; Kerr–Schild form as in the platform definition `NoHair_kerrNewman`.

/-
Kerr–Newman satisfies the Einstein equation (Kerr–Schild coordinates): Atoms (2 of 13).
Coordinate partials of the atoms, of the Kerr–Schild profile and of the potential factor; the metric, its inverse and its Christoffel symbols as formulas in the atoms.
The development is split into parts only so that each piece compiles within the platform limits.
-/
import Mathlib
import Definitions.Def_NoHair_KerrNewmanEinstein_Base

set_option autoImplicit false
set_option linter.all false
set_option Elab.async false

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem hasCP_R (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksRadius a w) z (dRt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  refine ⟨ksRadius_differentiableAt a z hz, fun k =>
    (hasDerivAt_ksRadius_line a z (coordBasis k) hz).congr_deriv ?_⟩
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  simp only [hx1, hx2, hx3]
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [coordBasis, dRt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [coordBasis, dRt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((-R ^ (2 : ℕ) * K1 + R * K2 * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dRt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((-R ^ (2 : ℕ) * K2 - R * K1 * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dRt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((-R ^ (2 : ℕ) * K3 - K3 * a ^ (2 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW

theorem hasCP_K1 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksNull a w 1) z (dKt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) 1) := by
  refine HasCP.of_fderiv (ksNull_differentiableAt a z hz 1) (fun k => ?_)
  rw [fderiv_k1 a z hz]
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  simp only [dk1f, drf, hx1, hx2, hx3]
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) ((-R ^ (3 : ℕ)) / ((R ^ 2 + a ^ 2) * (R ^ 2 + a ^ 2 * K3 ^ 2))) * hrel + ((-R * K2 ^ (2 : ℕ) - R * K3 ^ (2 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) ((-R ^ (2 : ℕ) * a) / ((R ^ 2 + a ^ 2) * (R ^ 2 + a ^ 2 * K3 ^ 2))) * hrel + ((R * K1 * K2 - K3 ^ (2 : ℕ) * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R * K1 * K3 + K2 * K3 * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW

theorem hasCP_K2 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksNull a w 2) z (dKt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) 2) := by
  refine HasCP.of_fderiv (ksNull_differentiableAt a z hz 2) (fun k => ?_)
  rw [fderiv_k2 a z hz]
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  simp only [dk2f, drf, hx1, hx2, hx3]
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) ((R ^ (2 : ℕ) * a) / ((R ^ 2 + a ^ 2) * (R ^ 2 + a ^ 2 * K3 ^ 2))) * hrel + ((R * K1 * K2 + K3 ^ (2 : ℕ) * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) ((R * a ^ (2 : ℕ)) / ((R ^ 2 + a ^ 2) * (R ^ 2 + a ^ 2 * K3 ^ 2))) * hrel + ((R * K2 ^ (2 : ℕ) - R) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R * K2 * K3 - K1 * K3 * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW

theorem hasCP_K3 (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksNull a w 3) z (dKt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) 3) := by
  refine HasCP.of_fderiv (ksNull_differentiableAt a z hz 3) (fun k => ?_)
  rw [fderiv_k3 a z hz]
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  simp only [dk3f, drf, hx1, hx2, hx3]
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R * K1 * K3 - K2 * K3 * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R * K2 * K3 + K1 * K3 * a) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW
  · simp [coordBasis, dKt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R * K3 ^ (2 : ℕ) - R) / ((R ^ 2 + a ^ 2 * K3 ^ 2))) * hW

theorem hasCP_W (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => Wf a w) z (dWt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  have hR := hasCP_R a z hz
  have hK3 := hasCP_K3 a z hz
  have hne : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have h := HasCP.div (HasCP.cst 1 z) ((hR.pow 2).add ((HasCP.cst (a ^ 2) z).mul (hK3.pow 2))) hne
  refine h.congr_d (fun k => ?_)
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [dRt, dKt, dWt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [dRt, dKt, dWt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((2 * R ^ (5 : ℕ) * K1 * W ^ (2 : ℕ) - 2 * R ^ (4 : ℕ) * K2 * W ^ (2 : ℕ) * a + 2 * R ^ (3 : ℕ) * K1 * W - 2 * R ^ (2 : ℕ) * K2 * W * a - 2 * R * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) - 2 * R * K1 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) + 2 * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) + 2 * K2 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW
  · simp [dRt, dKt, dWt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((2 * R ^ (5 : ℕ) * K2 * W ^ (2 : ℕ) + 2 * R ^ (4 : ℕ) * K1 * W ^ (2 : ℕ) * a + 2 * R ^ (3 : ℕ) * K2 * W + 2 * R ^ (2 : ℕ) * K1 * W * a - 2 * R * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) - 2 * R * K2 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) - 2 * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) - 2 * K1 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW
  · simp [dRt, dKt, dWt] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((2 * R ^ (5 : ℕ) * K3 * W ^ (2 : ℕ) + 4 * R ^ (3 : ℕ) * K3 * W ^ (2 : ℕ) * a ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K3 * W - 2 * R * K3 ^ (5 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) + 4 * R * K3 ^ (3 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) - 2 * R * K3 ^ (3 : ℕ) * W * a ^ (2 : ℕ) + 4 * R * K3 * W * a ^ (2 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW

theorem hasCP_profile (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => ksProfile m a e w) z (dfA a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  have hR := hasCP_R a z hz
  have h3 := hasCP_coord z 3
  have hden : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := (ks_den_pos a z hz).ne'
  have h : HasCP (fun w => ksProfile m a e w) z _ :=
    ((hR.pow 2).mul (((HasCP.cst (2 * m) z).mul hR).sub (HasCP.cst (e ^ 2) z))).div
      ((hR.pow 4).add ((HasCP.cst (a ^ 2) z).mul (h3.pow 2))) hden
  refine h.congr_d (fun k => ?_)
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  simp only [hx3]
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [coordBasis, dRt, dfA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [coordBasis, dRt, dfA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((2 * R ^ (6 : ℕ) * K1 * W ^ (2 : ℕ) * m - 2 * R ^ (5 : ℕ) * K1 * W ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (5 : ℕ) * K2 * W ^ (2 : ℕ) * a * m - 4 * R ^ (4 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (2 : ℕ) * m + 2 * R ^ (4 : ℕ) * K1 * W * m + 2 * R ^ (4 : ℕ) * K2 * W ^ (2 : ℕ) * a * e ^ (2 : ℕ) - 2 * R ^ (3 : ℕ) * K1 * W * e ^ (2 : ℕ) + 4 * R ^ (3 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (3 : ℕ) * m - 2 * R ^ (3 : ℕ) * K2 * W * a * m - 6 * R ^ (2 : ℕ) * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * m - 6 * R ^ (2 : ℕ) * K1 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) * m + 2 * R ^ (2 : ℕ) * K2 * W * a * e ^ (2 : ℕ) + 2 * R * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) + 2 * R * K1 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) * e ^ (2 : ℕ) + 6 * R * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) * m + 6 * R * K2 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ) * m - 2 * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) * e ^ (2 : ℕ) - 2 * K2 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ) * e ^ (2 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW
  · simp [coordBasis, dRt, dfA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((2 * R ^ (6 : ℕ) * K2 * W ^ (2 : ℕ) * m + 2 * R ^ (5 : ℕ) * K1 * W ^ (2 : ℕ) * a * m - 2 * R ^ (5 : ℕ) * K2 * W ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (4 : ℕ) * K1 * W ^ (2 : ℕ) * a * e ^ (2 : ℕ) - 4 * R ^ (4 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (2 : ℕ) * m + 2 * R ^ (4 : ℕ) * K2 * W * m - 4 * R ^ (3 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (3 : ℕ) * m + 2 * R ^ (3 : ℕ) * K1 * W * a * m - 2 * R ^ (3 : ℕ) * K2 * W * e ^ (2 : ℕ) - 2 * R ^ (2 : ℕ) * K1 * W * a * e ^ (2 : ℕ) - 6 * R ^ (2 : ℕ) * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * m - 6 * R ^ (2 : ℕ) * K2 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) * m - 6 * R * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) * m - 6 * R * K1 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ) * m + 2 * R * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) + 2 * R * K2 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) * e ^ (2 : ℕ) + 2 * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) * e ^ (2 : ℕ) + 2 * K1 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ) * e ^ (2 : ℕ)) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW
  · simp [coordBasis, dRt, dfA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((2 * R ^ (7 : ℕ) * K3 * W ^ (2 : ℕ) * m - 2 * R ^ (6 : ℕ) * K3 * W ^ (2 : ℕ) * e ^ (2 : ℕ) - 4 * R ^ (5 : ℕ) * K3 ^ (3 : ℕ) * W ^ (2 : ℕ) * a ^ (2 : ℕ) * m + 6 * R ^ (5 : ℕ) * K3 * W ^ (2 : ℕ) * a ^ (2 : ℕ) * m + 2 * R ^ (5 : ℕ) * K3 * W * m - 4 * R ^ (4 : ℕ) * K3 * W ^ (2 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (4 : ℕ) * K3 * W * e ^ (2 : ℕ) - 6 * R ^ (3 : ℕ) * K3 ^ (5 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * m + 4 * R ^ (3 : ℕ) * K3 ^ (3 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * m - 6 * R ^ (3 : ℕ) * K3 ^ (3 : ℕ) * W * a ^ (2 : ℕ) * m + 6 * R ^ (3 : ℕ) * K3 * W * a ^ (2 : ℕ) * m + 2 * R ^ (2 : ℕ) * K3 ^ (5 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) - 4 * R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) + 2 * R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 4 * R ^ (2 : ℕ) * K3 * W * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R * K3 ^ (5 : ℕ) * W ^ (2 : ℕ) * a ^ (6 : ℕ) * m - 2 * R * K3 ^ (3 : ℕ) * W * a ^ (4 : ℕ) * m + 4 * R * K3 * a ^ (2 : ℕ) * m - 2 * K3 * a ^ (2 : ℕ) * e ^ (2 : ℕ)) / (R * (R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW

theorem hasCP_H (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    HasCP (fun w => e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2)) z
      (dHA a e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z)) := by
  have hR := hasCP_R a z hz
  have h3 := hasCP_coord z 3
  have hden : ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2 ≠ 0 := (ks_den_pos a z hz).ne'
  have h : HasCP (fun w => e * ksRadius a w ^ 3 / (ksRadius a w ^ 4 + a ^ 2 * w 3 ^ 2)) z _ :=
    ((HasCP.cst e z).mul (hR.pow 3)).div ((hR.pow 4).add ((HasCP.cst (a ^ 2) z).mul (h3.pow 2))) hden
  refine h.congr_d (fun k => ?_)
  have hx1 := ks_x1 a z hz
  have hx2 := ks_x2 a z hz
  have hx3 := ks_x3 a z hz
  have hrel := ks_rel a z hz
  have hW := ks_W a z hz
  have hRne : ksRadius a z ≠ 0 := hz.ne'
  have hQ : ksRadius a z ^ 2 + a ^ 2 ≠ 0 := by positivity
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  simp only [hx3]
  set R := ksRadius a z
  set K1 := ksNull a z 1
  set K2 := ksNull a z 2
  set K3 := ksNull a z 3
  set W := Wf a z
  fin_cases k
  · simp [coordBasis, dRt, dHA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + (0) * hW
  · simp [coordBasis, dRt, dHA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R ^ (6 : ℕ) * K1 * W ^ (2 : ℕ) * e - R ^ (5 : ℕ) * K2 * W ^ (2 : ℕ) * a * e - 2 * R ^ (4 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (2 : ℕ) * e + R ^ (4 : ℕ) * K1 * W * e + 2 * R ^ (3 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (3 : ℕ) * e - R ^ (3 : ℕ) * K2 * W * a * e - 3 * R ^ (2 : ℕ) * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e - 3 * R ^ (2 : ℕ) * K1 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) * e + 3 * R * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) * e + 3 * R * K2 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ) * e) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW
  · simp [coordBasis, dRt, dHA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R ^ (6 : ℕ) * K2 * W ^ (2 : ℕ) * e + R ^ (5 : ℕ) * K1 * W ^ (2 : ℕ) * a * e - 2 * R ^ (4 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (2 : ℕ) * e + R ^ (4 : ℕ) * K2 * W * e - 2 * R ^ (3 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a ^ (3 : ℕ) * e + R ^ (3 : ℕ) * K1 * W * a * e - 3 * R ^ (2 : ℕ) * K2 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e - 3 * R ^ (2 : ℕ) * K2 * K3 ^ (2 : ℕ) * W * a ^ (2 : ℕ) * e - 3 * R * K1 * K3 ^ (4 : ℕ) * W ^ (2 : ℕ) * a ^ (5 : ℕ) * e - 3 * R * K1 * K3 ^ (2 : ℕ) * W * a ^ (3 : ℕ) * e) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW
  · simp [coordBasis, dRt, dHA] <;> linear_combination (norm := (field_simp; ring)) (0) * hrel + ((R ^ (6 : ℕ) * K3 * W ^ (2 : ℕ) * e - 2 * R ^ (4 : ℕ) * K3 ^ (3 : ℕ) * W ^ (2 : ℕ) * a ^ (2 : ℕ) * e + 3 * R ^ (4 : ℕ) * K3 * W ^ (2 : ℕ) * a ^ (2 : ℕ) * e + R ^ (4 : ℕ) * K3 * W * e - 3 * R ^ (2 : ℕ) * K3 ^ (5 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e + 2 * R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W ^ (2 : ℕ) * a ^ (4 : ℕ) * e - 3 * R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W * a ^ (2 : ℕ) * e + 3 * R ^ (2 : ℕ) * K3 * W * a ^ (2 : ℕ) * e - K3 ^ (5 : ℕ) * W ^ (2 : ℕ) * a ^ (6 : ℕ) * e - K3 ^ (3 : ℕ) * W * a ^ (4 : ℕ) * e + 2 * K3 * a ^ (2 : ℕ) * e) / ((R ^ 2 + a ^ 2 * K3 ^ 2) ^ (2 : ℕ))) * hW

/-! ## Metric, inverse metric and Christoffel symbols on `U` -/

theorem hasCP_K (a : ℝ) (z : E4) (hz : 0 < ksRadius a z) (l : Fin 4) :
    HasCP (fun w => ksNull a w l) z
      (dKt a (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) l) := by
  fin_cases l
  · exact (HasCP.cst 1 z).congr_d (fun k => by fin_cases k <;> simp [dKt])
  · exact hasCP_K1 a z hz
  · exact hasCP_K2 a z hz
  · exact hasCP_K3 a z hz

theorem profile_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    ksProfile m a e z = fA a m e (ksRadius a z) (Wf a z) := by
  show ksRadius a z ^ 2 * (2 * m * ksRadius a z - e ^ 2) / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) = _
  rw [ks_x3 a z hz]
  unfold fA Wf
  have hR : ksRadius a z ≠ 0 := hz.ne'
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  field_simp
  try ring

theorem cp_metric (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (l k j : Fin 4) :
    coordPartial (fun w => kerrNewmanMetric m a e w l k) j z
      = dgA a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) l k j := by
  have h := (HasCP.cst (minkowski l k) z).add
    (((hasCP_profile m a e z hz).mul (hasCP_K a z hz l)).mul (hasCP_K a z hz k))
  have h2 := h.eq j
  beta_reduce at h2
  have e1 : (fun w => kerrNewmanMetric m a e w l k)
      = (fun w => minkowski l k + ksProfile m a e w * ksNull a w l * ksNull a w k) := rfl
  rw [e1, h2, profile_eq m a e z hz]
  simp only [dgA, Kv, ← ksNull_eq_Kv a z]
  ring

theorem invMetric_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    invMetric (kerrNewmanMetric m a e) z = Matrix.of (fun i l =>
      ginvA a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i l) := by
  have hnull := ks_null a z hz
  have hG : kerrNewmanMetric m a e z = Matrix.of fun μ ν =>
      minkowski μ ν + ksProfile m a e z * ksNull a z μ * ksNull a z ν := rfl
  unfold invMetric
  rw [hG, Matrix.inv_eq_right_inv (mul_inv_KS _ _ hnull)]
  ext i l
  simp only [Matrix.of_apply, ginvA, Ks, profile_eq m a e z hz, ksNull_zero, minkowski_eq]

theorem chr_eq (m a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) (i j k : Fin 4) :
    christoffel (kerrNewmanMetric m a e) z i j k
      = chrS a m e (ksRadius a z) (ksNull a z 1) (ksNull a z 2) (ksNull a z 3) (Wf a z) i j k := by
  simp only [christoffel, chrS, invMetric_eq m a e z hz, Matrix.of_apply, cp_metric m a e z hz]

end NoHair.KNE


