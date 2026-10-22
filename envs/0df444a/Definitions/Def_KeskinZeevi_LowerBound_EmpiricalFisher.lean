-- Prove2me | Definitions.Def_KeskinZeevi_LowerBound_EmpiricalFisher
-- name    : KeskinZeevi_LowerBound_EmpiricalFisher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-03T02:43:05.209883+00:00
-- url     : https://prove2.me/theorems/4137b987-2067-4580-b4a3-e8ba54f9c560
-- title:
--   Empirical Fisher information and the quadratic form C(θ) E[𝒥_t] C(θ)ᵀ
-- statement:
--   For a single product, the **empirical Fisher information** (11) after $t$ periods is the random $2\times 2$ matrix
--   $$\mathcal{J}_t = \sum_{s=1}^t \begin{bmatrix} 1 & p_s \\ p_s & p_s^2 \end{bmatrix},$$
--   with $\mathcal{J}_0 = 0$. Its expectation $\mathbb{E}^\pi_\theta[\mathcal{J}_t]$ is taken entrywise. For the $1\times 2$ row vector $C(\theta) = [-\varphi(\theta)\ \ 1]$ of Lemma 1, the scalar
--   $$C(\theta)\, \mathbb{E}^\pi_\theta[\mathcal{J}_t]\, C(\theta)^{\mathsf T}$$
--   is the quantity in the denominator of inequality (14).
--
--   **Formalization Note.** `empFisher π θ ε t ω` sums over the first $t$ periods (Lean periods $0,\dots,t-1$), so it is the paper's $\mathcal{J}_t$. The quadratic form is written as `cRow θ ⬝ᵥ (expFisher … *ᵥ cRow θ)`.
-- source:
--   Keskin and Zeevi, Dynamic Pricing with an Unknown Demand Model, Operations Research 62(5), 2014, p. 1145, Eq. (11), and p. 1146, Lemma 1

import Mathlib
import Definitions.Def_KeskinZeevi_LowerBound_Model
import Definitions.Def_KeskinZeevi_LowerBound_Policy
import Definitions.Def_KeskinZeevi_LowerBound_Regret

namespace KeskinZeevi.LowerBound

open MeasureTheory Matrix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The empirical Fisher information (11), single product:
`𝒥_t = Σ_{s=1}^t [1 p_s; p_s p_s²]`. The sum runs over the first `t` periods (Lean periods
`0, …, t − 1`), so `empFisher π θ ε t ω` is the paper's `𝒥_t`, and `empFisher … 0 = 0`. -/
noncomputable def empFisher {l u : ℝ} (π : Policy l u) (θ : ℝ × ℝ) (ε : ℕ → Ω → ℝ) (t : ℕ)
    (ω : Ω) : Matrix (Fin 2) (Fin 2) ℝ :=
  ∑ s ∈ Finset.range t, !![1, price π θ ε s ω; price π θ ε s ω, price π θ ε s ω ^ 2]

/-- The expectation `E^π_θ[𝒥_t]` of the empirical Fisher information, taken entrywise. -/
noncomputable def expFisher (P : Measure Ω) (ε : ℕ → Ω → ℝ) {l u : ℝ} (π : Policy l u)
    (θ : ℝ × ℝ) (t : ℕ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => ∫ ω, empFisher π θ ε t ω i j ∂P

/-- The `1 × 2` row vector `C(θ) = [−φ(θ) 1]` of Lemma 1 (p. 1146). -/
noncomputable def cRow (θ : ℝ × ℝ) : Fin 2 → ℝ :=
  ![-optPrice θ, 1]

/-- The scalar `C(θ) E^π_θ[𝒥_t] C(θ)ᵀ` of Lemma 1 (p. 1146). -/
noncomputable def infoQuad (P : Measure Ω) (ε : ℕ → Ω → ℝ) {l u : ℝ} (π : Policy l u)
    (θ : ℝ × ℝ) (t : ℕ) : ℝ :=
  cRow θ ⬝ᵥ (expFisher P ε π θ t *ᵥ cRow θ)

end KeskinZeevi.LowerBound


