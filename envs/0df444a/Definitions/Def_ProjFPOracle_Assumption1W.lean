-- Prove2me | Definitions.Def_ProjFPOracle_Assumption1W
-- name    : ProjFPOracle_Assumption1W
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:31:39.620993+00:00
-- url     : https://prove2.me/theorems/495265d2-1b68-47db-ab88-ac747f6660c1
-- title:
--   Assumption 1(W): second-moment bounds in projected space
-- statement:
--   **Assumption 1(W).** There are scalars $\sigma_L,\sigma_b>0$ such that for every unit vector $u\in\mathbb S$, every basis vector $\varphi_j$ and every observation index $i$,
--   $$
--   \mathbb E\langle\varphi_j,(L_i-L)u\rangle^2\le\sigma_L^2\|u\|^2,\qquad \mathbb E\langle\varphi_j,b_i-b\rangle^2\le\sigma_b^2 .
--   $$
--   In the projected coordinates $A_i=\Phi_dL_i\Phi_d^*$, $h_i=\Phi_db_i$, $M=\Phi_dL\Phi_d^*$, $m=\Phi_db$, and with $u=\Phi_d^*w$, these read
--   $$
--   \mathbb E\big[((A_i-M)w)_j^2\big]\le\sigma_L^2\sum_k w_k^2,\qquad \mathbb E\big[(h_{i,j}-m_j)^2\big]\le\sigma_b^2 ,
--   $$
--   for all $w\in\mathbb R^d$ and $j\in\{1,\dots,d\}$; this is what the definition states, with the given $\sigma_L,\sigma_b>0$.
--
--   The constants $\sigma_L,\sigma_b$ set the noise scale in the stepsize, the sample-size threshold and the higher-order term $\mathcal H_n$ of Theorem 1.
--
--   **Formalization Note** The bound is stated for all $w$ with the factor $\sum_kw_k^2$, which is the printed unit-norm form since both sides scale by $\|w\|^2$.
-- source:
--   Mou, Pananjady & Wainwright, Optimal Oracle Inequalities for Projected Fixed-Point Equations, arXiv:2012.05299v1, Assumption 1(W), p.8, Eq. (11)

import Mathlib

open MeasureTheory Matrix

namespace ProjFPOracle

/-- **Assumption 1(W), second-moment bound in projected space** (Mou, Pananjady & Wainwright,
*Optimal Oracle Inequalities for Projected Fixed-Point Equations*, arXiv:2012.05299v1, Eq. (11),
p.8): "There exist scalars `σ_L, σ_b > 0` such that for any unit-norm vector `u ∈ 𝕊` and any basis
vector in `{φ_j}_{j=1}^d` we have the bounds `E⟨φ_j, (L_i − L)u⟩² ≤ σ_L² ‖u‖²` (11a) and
`E⟨φ_j, b_i − b⟩² ≤ σ_b²` (11b)."

`Assumption1W P A h M m σL σb` states this with the given `σ_L, σ_b > 0`, in the projected
coordinates `A_i = Φ_d L_i Φ_d^*`, `h_i = Φ_d b_i`, `M = Φ_d L Φ_d^*`, `m = Φ_d b`.

**Formalization Note** For `u = Φ_d^* w ∈ 𝕊`, `⟨φ_j, (L_i − L)u⟩ = ((A_i − M) w)_j` and
`‖u‖² = ∑_k w_k²`. The bound is stated for every `w ∈ ℝ^d` with the factor `∑_k w_k²`; this is the
printed unit-norm form, since both sides scale by `‖w‖²`. It is required for every observation
index `i ≥ 1` (the observations are identically distributed). -/
def Assumption1W {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → Ω → Matrix (Fin d) (Fin d) ℝ) (h : ℕ → Ω → Fin d → ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (m : Fin d → ℝ) (σL σb : ℝ) : Prop :=
  0 < σL ∧ 0 < σb ∧
  (∀ i, 1 ≤ i → ∀ (j : Fin d) (w : Fin d → ℝ),
    ∫ ω, (((A i ω - M) *ᵥ w) j) ^ 2 ∂P ≤ σL ^ 2 * ∑ k, w k ^ 2) ∧
  (∀ i, 1 ≤ i → ∀ j : Fin d, ∫ ω, (h i ω j - m j) ^ 2 ∂P ≤ σb ^ 2)

end ProjFPOracle


