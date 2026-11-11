-- Prove2me | Definitions.Def_FlowSparsSchur_Main_Heat
-- name    : FlowSparsSchur_Main_Heat
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:23:00.704365+00:00
-- url     : https://prove2.me/theorems/84856025-a87b-46f3-941f-081a068160ba
-- title:
--   Heat capacity, heat kernel $H_t=e^{-tM^{-1}L}M^{-1}$, its columns, and potential dissipation $I(f)=(Lf)^\top\log f$
-- statement:
--   Let $L$ be the Laplacian of a graph on a finite set $V$. A **heat capacity** is a vector $\mu\in\mathbb R^V_{>0}$ with $\mu^\top\mathbf 1=1$; $M=\mathrm{diag}(\mu)$. The **heat kernel** (Definitions 9.23 and 9.31) and its **column** at $v$ (Definition 9.33) are
--   $$H_t=e^{-tM^{-1}L}M^{-1},\qquad h_{t,v}=H_tb_v ,$$
--   with the matrix exponential $e^{A}=\sum_{j\ge0}A^j/j!$. For a strictly positive $f\in\mathbb R^V_{>0}$ the **potential dissipation** (Definition 9.41) is
--   $$I(f)=(Lf)^\top\log f ,$$
--   the logarithm natural and entrywise. For $H=\mathrm{Schur}(G,S)$, $I_H$ uses $L_{\mathrm{Schur}(G,S)}$.
--
--   **Formalization Note** The exponential is Mathlib's `NormedSpace.exp` on matrices. `dissipation` is applied only to strictly positive vectors in the statements.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), pp. 29–46, Definitions 9.3, 9.23, 9.31, 9.33, 9.41

import Mathlib

/-!
# Heat kernel and potential dissipation

Goranci, Henzinger, Momeni, Räcke, Sricharan, *Breaking the Quadratic Time Barrier for Flow
Sparsifiers via Schur Complement Localization*, STOC 2027 submission, Definitions 9.3, 9.23, 9.31,
9.33, 9.41 (pp. 29–46).

For a Laplacian `L ∈ ℝ^{V × V}` and a heat capacity `µ ∈ ℝ^V_{>0}` with `µᵀ1 = 1`, `M = diag(µ)`:
* the heat kernel is `H_t = e^{−t M⁻¹ L} M⁻¹` (Definitions 9.23 and 9.31), with the matrix
  exponential `e^A = Σ_j A^j / j!` (Mathlib's `NormedSpace.exp`);
* `h_{t,v} = H_t b_v` is its column at `v` (Definition 9.33);
* the potential dissipation of a strictly positive `f` is `I_G(f) = (L_G f)ᵀ log f`, the logarithm
  natural and entrywise (Definition 9.41).
-/

namespace FlowSparsSchur.Main

open Matrix

variable {V : Type} [Fintype V] [DecidableEq V]

/-- The heat kernel `H_t = e^{−t M⁻¹ L} M⁻¹`, `M = diag(µ)` (Definition 9.31). -/
noncomputable def heatKernel (L : Matrix V V ℝ) (μ : V → ℝ) (t : ℝ) : Matrix V V ℝ :=
  NormedSpace.exp (-t • (diagonal (fun v => (μ v)⁻¹) * L)) * diagonal (fun v => (μ v)⁻¹)

/-- The column `h_{t,v} = H_t b_v` of the heat kernel at `v` (Definition 9.33). -/
noncomputable def heatColumn (L : Matrix V V ℝ) (μ : V → ℝ) (t : ℝ) (v : V) : V → ℝ :=
  fun u => heatKernel L μ t u v

/-- The potential dissipation `I(f) = (L f)ᵀ log f` (Definition 9.41), for `L` the Laplacian of the
graph; it is used only for strictly positive `f`. -/
noncomputable def dissipation (L : Matrix V V ℝ) (f : V → ℝ) : ℝ :=
  (L *ᵥ f) ⬝ᵥ (fun v => Real.log (f v))

/-- `µ` is a heat capacity distribution: strictly positive with `µᵀ1 = 1` (Definition 9.3). -/
def IsHeatCapacity (μ : V → ℝ) : Prop := (∀ v, 0 < μ v) ∧ ∑ v, μ v = 1

end FlowSparsSchur.Main


