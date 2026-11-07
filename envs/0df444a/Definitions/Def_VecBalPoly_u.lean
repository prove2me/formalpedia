-- Prove2me | Definitions.Def_VecBalPoly_u
-- name    : VecBalPoly_u
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T23:11:48.426395+00:00
-- url     : https://prove2.me/theorems/640a9822-5534-46ad-8671-c7a3b61ee27f
-- title:
--   The safety barrier $u_{i\sigma}$ (2.4) and its gradient (4.4)
-- statement:
--   For a row $i$ and a sign $\sigma\in\{-1,1\}$, the safety barrier is
--   $$u_{i\sigma}=\frac{\sigma d_i-2K^3}{r_i}+\frac{G_i}{2r_i^2}+12K,$$
--   and the vector
--   $$g_{i\sigma}=\frac{\sigma b_i}{r_i}-\frac{p_i\circ x_V}{r_i^2}\in\mathbb R^V,$$
--   which is its gradient in the active coordinates (milestone (4.4)–(4.5)). The algorithm keeps $u_{i\sigma}\le0$ for medium rows, which bounds $|d_i|$ by $2K^3$.
--
--   **Formalization Note** The first term is the single fraction $(\sigma d_i-2K^3)/r_i$, as on the rendered page. The barrier is used on medium rows only, where $r_i^2\ge q_i>0$. The sign $\sigma$ is coded as a Boolean ($\mathrm{true}\mapsto1$, $\mathrm{false}\mapsto-1$).
-- source:
--   S. Guo, E. X. Fang, J. Lu, Vector Balancing in Polynomial Time, arXiv:2609.23540 (held file sha256 b777ade4…), (2.4), p.4 (PDF p.5); (4.4), p.10 (PDF p.11)

import Mathlib
import Definitions.Def_VecBalPoly_q

namespace VecBalPoly

variable {m n : ℕ}

/-- The sign `σ ∈ {−1, 1}` coded by a Boolean: `true ↦ 1`, `false ↦ −1`. -/
def sgn : Bool → ℝ
  | true => 1
  | false => -1

/-- **The safety barrier (2.4)**
`u_{iσ} = (σdᵢ − 2K³)/rᵢ + Gᵢ/(2rᵢ²) + 12K`, for a row `i` and a sign `σ ∈ {−1, 1}`.
Source: Guo, Fang, Lu, *Vector Balancing in Polynomial Time*, arXiv:2609.23540 (held file sha256
b777ade4…), §2.2, (2.4), p.4 (PDF p.5).

**Formalization Note** The first term is the single fraction `(σdᵢ − 2K³)/rᵢ`, as on the rendered
page. The barrier is read on medium rows only, where `rᵢ² ≥ qᵢ > 0`; every statement that uses it
restricts to medium rows. `σ` is a `Bool` (`sgn true = 1`, `sgn false = −1`). -/
noncomputable def u (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) (σ : Bool) : ℝ :=
  (sgn σ * d A st i - 2 * K ^ 3) / st.r i + G A st i / (2 * st.r i ^ 2) + 12 * K

/-- **The barrier gradient (4.4)** `g_{iσ} = σbᵢ/rᵢ − (pᵢ ∘ x_V)/rᵢ²`, a vector of `ℝ^V`.
Source: ibid., §4.3, (4.4), p.10 (PDF p.11).

**Formalization Note** A vector of `ℝ^V` is a vector of `ℝⁿ` that vanishes off `V`. That this is
the gradient of (2.4) in the active coordinates is part of the milestone `eq_4_5`. -/
noncomputable def gradU (A : Matrix (Fin m) (Fin n) ℝ) (st : St m n) (i : Fin m) (σ : Bool) :
    Fin n → ℝ :=
  fun j => if j ∈ st.V then sgn σ * b A st i j / st.r i - p A st i j * st.x j / st.r i ^ 2 else 0

end VecBalPoly


