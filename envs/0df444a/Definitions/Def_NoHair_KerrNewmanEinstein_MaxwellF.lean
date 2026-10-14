-- Prove2me | Definitions.Def_NoHair_KerrNewmanEinstein_MaxwellF
-- name    : NoHair_KerrNewmanEinstein_MaxwellF
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-13T07:54:09.415975+00:00
-- url     : https://prove2.me/theorems/793b0e65-68d6-4245-846f-09e4e7d08828
-- title:
--   Kerr–Newman solves the Einstein equation: block MaxwellF
-- statement:
--   **MaxwellF.** The Maxwell side in closed form: field strength, raised field strength and the invariant F_{ab}F^{ab} (pure polynomial identities).
--
--   This block belongs to a machine-checked proof that the Kerr–Newman metric $g=\eta+f\,k\otimes k$ (Kerr–Schild form, $f=r^2(2mr-e^2)/(r^4+a^2z^2)$) and field $F=dA$, $A=\frac{e r^3}{r^4+a^2z^2}k$, satisfy the Einstein equation $G_{\mu\nu}=2(F_{\mu\alpha}F_\nu{}^\alpha-\tfrac14 g_{\mu\nu}F_{\alpha\beta}F^{\alpha\beta})$ at every point with $r>0$, using the definitions `NoHair_coordinates` and `NoHair_kerrNewman` (statement `NoHair.kerrNewman_einstein`). Everything is expressed through the atoms $r$, $k_1,k_2,k_3$ and $W=1/(r^2+a^2k_3^2)$, which satisfy $k_1^2+k_2^2+k_3^2=1$ and $W(r^2+a^2k_3^2)=1$. The curvature computation becomes polynomial identities modulo these two relations; each identity is closed by `linear_combination` with cofactors precomputed by a Gröbner-basis division. The proof is split into 16 blocks only so that each compiles within the platform's time limit; they contain no `sorry` and use only the standard axioms.
-- source:
--   Original formalization for the Prove2Me mission *No-Hair Conjecture: Uniqueness of Stationary Kerr–Newman Black Holes*. Kerr–Newman metric: E. T. Newman et al., J. Math. Phys. 6 (1965) 918, https://doi.org/10.1063/1.1704351; Kerr–Schild form as in the platform definition `NoHair_kerrNewman`.

/-
Kerr–Newman satisfies the Einstein equation (Kerr–Schild coordinates): block MaxwellF.
The Maxwell side in closed form: field strength, raised field strength and the invariant F_{ab}F^{ab} (pure polynomial identities).
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

theorem fS_00 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 0 0 = FA a e R K1 K2 K3 W 0 0 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_01 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 0 1 = FA a e R K1 K2 K3 W 0 1 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc01, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_02 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 0 2 = FA a e R K1 K2 K3 W 0 2 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc02, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_03 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 0 3 = FA a e R K1 K2 K3 W 0 3 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc03, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_10 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 1 0 = FA a e R K1 K2 K3 W 1 0 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc01, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_11 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 1 1 = FA a e R K1 K2 K3 W 1 1 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_12 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 1 2 = FA a e R K1 K2 K3 W 1 2 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc12, Matrix.cons_val]
  linear_combination ((R ^ (3 : ℕ) * W ^ (3 : ℕ) * a * e - 3 * R * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * e)) * hrel + ((2 * R * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a * e)) * hW

theorem fS_13 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 1 3 = FA a e R K1 K2 K3 W 1 3 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc13, Matrix.cons_val]
  linear_combination (0) * hrel + ((-2 * R * K2 * K3 * W ^ (2 : ℕ) * a * e)) * hW

theorem fS_20 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 2 0 = FA a e R K1 K2 K3 W 2 0 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc02, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_21 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 2 1 = FA a e R K1 K2 K3 W 2 1 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc12, Matrix.cons_val]
  linear_combination ((-R ^ (3 : ℕ) * W ^ (3 : ℕ) * a * e + 3 * R * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * e)) * hrel + ((-2 * R * K3 ^ (2 : ℕ) * W ^ (2 : ℕ) * a * e)) * hW

theorem fS_22 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 2 2 = FA a e R K1 K2 K3 W 2 2 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_23 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 2 3 = FA a e R K1 K2 K3 W 2 3 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc23, Matrix.cons_val]
  linear_combination (0) * hrel + ((2 * R * K1 * K3 * W ^ (2 : ℕ) * a * e)) * hW

theorem fS_30 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 3 0 = FA a e R K1 K2 K3 W 3 0 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc03, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fS_31 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 3 1 = FA a e R K1 K2 K3 W 3 1 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc13, Matrix.cons_val]
  linear_combination (0) * hrel + ((2 * R * K2 * K3 * W ^ (2 : ℕ) * a * e)) * hW

theorem fS_32 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 3 2 = FA a e R K1 K2 K3 W 3 2 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Fc23, Matrix.cons_val]
  linear_combination (0) * hrel + ((-2 * R * K1 * K3 * W ^ (2 : ℕ) * a * e)) * hW

theorem fS_33 (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    FS a e R K1 K2 K3 W 3 3 = FA a e R K1 K2 K3 W 3 3 := by
  simp only [FS, FA, HA, dHA, dKt, Kv, Matrix.cons_val]
  linear_combination (0) * hrel + (0) * hW

theorem fU_00 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 0 μ * ginvA a m e R K1 K2 K3 W 0 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 0 0 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination (0) * hrel + (0) * hW

theorem fU_01 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 0 μ * ginvA a m e R K1 K2 K3 W 1 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 0 1 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu01, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((2 * R ^ (5 : ℕ) * K1 * W ^ (4 : ℕ) * m * e - R ^ (4 : ℕ) * K1 * W ^ (4 : ℕ) * e ^ (3 : ℕ) - 6 * R ^ (3 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e + 3 * R ^ (2 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_02 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 0 μ * ginvA a m e R K1 K2 K3 W 2 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 0 2 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu02, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((2 * R ^ (5 : ℕ) * K2 * W ^ (4 : ℕ) * m * e - R ^ (4 : ℕ) * K2 * W ^ (4 : ℕ) * e ^ (3 : ℕ) - 6 * R ^ (3 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e + 3 * R ^ (2 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_03 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 0 μ * ginvA a m e R K1 K2 K3 W 3 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 0 3 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu03, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((2 * R ^ (5 : ℕ) * K3 * W ^ (4 : ℕ) * m * e - R ^ (4 : ℕ) * K3 * W ^ (4 : ℕ) * e ^ (3 : ℕ) - 6 * R ^ (3 : ℕ) * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e + 6 * R ^ (3 : ℕ) * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e + 3 * R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) - 3 * R ^ (2 : ℕ) * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) - 2 * R * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * m * e + K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_10 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 1 μ * ginvA a m e R K1 K2 K3 W 0 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 1 0 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu01, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-2 * R ^ (5 : ℕ) * K1 * W ^ (4 : ℕ) * m * e + R ^ (4 : ℕ) * K1 * W ^ (4 : ℕ) * e ^ (3 : ℕ) + 6 * R ^ (3 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e - 3 * R ^ (2 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_11 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 1 μ * ginvA a m e R K1 K2 K3 W 1 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 1 1 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination (0) * hrel + (0) * hW

theorem fU_12 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 1 μ * ginvA a m e R K1 K2 K3 W 2 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 1 2 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu12, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination (0) * hrel + (0) * hW

theorem fU_13 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 1 μ * ginvA a m e R K1 K2 K3 W 3 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 1 3 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu13, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-6 * R ^ (3 : ℕ) * K1 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e + 3 * R ^ (2 : ℕ) * K1 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) + 2 * R * K1 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * m * e - K1 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_20 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 2 μ * ginvA a m e R K1 K2 K3 W 0 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 2 0 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu02, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-2 * R ^ (5 : ℕ) * K2 * W ^ (4 : ℕ) * m * e + R ^ (4 : ℕ) * K2 * W ^ (4 : ℕ) * e ^ (3 : ℕ) + 6 * R ^ (3 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e - 3 * R ^ (2 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_21 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 2 μ * ginvA a m e R K1 K2 K3 W 1 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 2 1 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu12, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination (0) * hrel + (0) * hW

theorem fU_22 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 2 μ * ginvA a m e R K1 K2 K3 W 2 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 2 2 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination (0) * hrel + (0) * hW

theorem fU_23 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 2 μ * ginvA a m e R K1 K2 K3 W 3 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 2 3 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-6 * R ^ (3 : ℕ) * K2 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e + 3 * R ^ (2 : ℕ) * K2 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) + 2 * R * K2 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * m * e - K2 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_30 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 3 μ * ginvA a m e R K1 K2 K3 W 0 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 3 0 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu03, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-2 * R ^ (5 : ℕ) * K3 * W ^ (4 : ℕ) * m * e + R ^ (4 : ℕ) * K3 * W ^ (4 : ℕ) * e ^ (3 : ℕ) + 6 * R ^ (3 : ℕ) * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e - 6 * R ^ (3 : ℕ) * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e - 3 * R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) + 3 * R ^ (2 : ℕ) * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) + 2 * R * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * m * e - K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_31 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 3 μ * ginvA a m e R K1 K2 K3 W 1 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 3 1 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu13, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((6 * R ^ (3 : ℕ) * K1 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e - 3 * R ^ (2 : ℕ) * K1 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) - 2 * R * K1 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * m * e + K1 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_32 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 3 μ * ginvA a m e R K1 K2 K3 W 2 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 3 2 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((6 * R ^ (3 : ℕ) * K2 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e - 3 * R ^ (2 : ℕ) * K2 * K3 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (3 : ℕ) - 2 * R * K2 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * m * e + K2 * K3 ^ (3 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (3 : ℕ))) * hrel + (0) * hW

theorem fU_33 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W 3 μ * ginvA a m e R K1 K2 K3 W 3 ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W 3 3 := by
  simp only [ginvA, FA, FupA, Ks, fA, etaT, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination (0) * hrel + (0) * hW

theorem fF (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ α, ∑ β, FA a e R K1 K2 K3 W α β * FupA a m e R K1 K2 K3 W α β = FFA a m e R K1 K2 K3 W := by
  simp only [FA, FupA, FFA, Fc01, Fc02, Fc03, Fc12, Fc13, Fc23, Fu01, Fu02, Fu03, Fu12, Fu13, Fu23, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-2 * R ^ (8 : ℕ) * W ^ (6 : ℕ) * e ^ (2 : ℕ) + 30 * R ^ (6 : ℕ) * K3 ^ (2 : ℕ) * W ^ (6 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (6 : ℕ) * W ^ (6 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 30 * R ^ (4 : ℕ) * K3 ^ (4 : ℕ) * W ^ (6 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) + 30 * R ^ (4 : ℕ) * K3 ^ (2 : ℕ) * W ^ (6 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) + 2 * R ^ (2 : ℕ) * K3 ^ (6 : ℕ) * W ^ (6 : ℕ) * a ^ (6 : ℕ) * e ^ (2 : ℕ) - 30 * R ^ (2 : ℕ) * K3 ^ (4 : ℕ) * W ^ (6 : ℕ) * a ^ (6 : ℕ) * e ^ (2 : ℕ) + 2 * K3 ^ (6 : ℕ) * W ^ (6 : ℕ) * a ^ (8 : ℕ) * e ^ (2 : ℕ))) * hrel + ((-2 * R ^ (6 : ℕ) * W ^ (5 : ℕ) * e ^ (2 : ℕ) + 10 * R ^ (4 : ℕ) * K3 ^ (2 : ℕ) * W ^ (5 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (4 : ℕ) * W ^ (4 : ℕ) * e ^ (2 : ℕ) + 10 * R ^ (2 : ℕ) * K3 ^ (4 : ℕ) * W ^ (5 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ) + 12 * R ^ (2 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * K3 ^ (6 : ℕ) * W ^ (5 : ℕ) * a ^ (6 : ℕ) * e ^ (2 : ℕ) - 2 * K3 ^ (4 : ℕ) * W ^ (4 : ℕ) * a ^ (4 : ℕ) * e ^ (2 : ℕ))) * hW

theorem fS (a e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    FS a e R K1 K2 K3 W μ ν = FA a e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact fS_00 a e R K1 K2 K3 W hrel hW
  · exact fS_01 a e R K1 K2 K3 W hrel hW
  · exact fS_02 a e R K1 K2 K3 W hrel hW
  · exact fS_03 a e R K1 K2 K3 W hrel hW
  · exact fS_10 a e R K1 K2 K3 W hrel hW
  · exact fS_11 a e R K1 K2 K3 W hrel hW
  · exact fS_12 a e R K1 K2 K3 W hrel hW
  · exact fS_13 a e R K1 K2 K3 W hrel hW
  · exact fS_20 a e R K1 K2 K3 W hrel hW
  · exact fS_21 a e R K1 K2 K3 W hrel hW
  · exact fS_22 a e R K1 K2 K3 W hrel hW
  · exact fS_23 a e R K1 K2 K3 W hrel hW
  · exact fS_30 a e R K1 K2 K3 W hrel hW
  · exact fS_31 a e R K1 K2 K3 W hrel hW
  · exact fS_32 a e R K1 K2 K3 W hrel hW
  · exact fS_33 a e R K1 K2 K3 W hrel hW

theorem fU (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    ∑ α, ∑ β, ginvA a m e R K1 K2 K3 W μ α * ginvA a m e R K1 K2 K3 W ν β * FA a e R K1 K2 K3 W α β = FupA a m e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact fU_00 a m e R K1 K2 K3 W hrel hW
  · exact fU_01 a m e R K1 K2 K3 W hrel hW
  · exact fU_02 a m e R K1 K2 K3 W hrel hW
  · exact fU_03 a m e R K1 K2 K3 W hrel hW
  · exact fU_10 a m e R K1 K2 K3 W hrel hW
  · exact fU_11 a m e R K1 K2 K3 W hrel hW
  · exact fU_12 a m e R K1 K2 K3 W hrel hW
  · exact fU_13 a m e R K1 K2 K3 W hrel hW
  · exact fU_20 a m e R K1 K2 K3 W hrel hW
  · exact fU_21 a m e R K1 K2 K3 W hrel hW
  · exact fU_22 a m e R K1 K2 K3 W hrel hW
  · exact fU_23 a m e R K1 K2 K3 W hrel hW
  · exact fU_30 a m e R K1 K2 K3 W hrel hW
  · exact fU_31 a m e R K1 K2 K3 W hrel hW
  · exact fU_32 a m e R K1 K2 K3 W hrel hW
  · exact fU_33 a m e R K1 K2 K3 W hrel hW

end NoHair.KNE


