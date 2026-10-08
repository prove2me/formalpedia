-- Prove2me | Definitions.Def_KLTNuclear_RestrictedEigen_ConeConstant
-- name    : KLTNuclear_RestrictedEigen_ConeConstant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T08:41:29.51963+00:00
-- url     : https://prove2.me/theorems/796b3252-f1b4-4e28-8440-e58768b7620a
-- title:
--   The cone ℂ_{A,c₀} and the restricted constant μ_{c₀}(A) (witness form)
-- statement:
--   Let $\mathbb A$ be a linear subspace of $\mathbb R^{m_1 \times m_2}$ and let $A \in \mathbb A$ have singular value decomposition $A = \sum_{j=1}^r \sigma_j u_j v_j^\top$ with support $(S_1, S_2)$, where $S_1 = \operatorname{span}\{u_j\}$ and $S_2 = \operatorname{span}\{v_j\}$. For $B \in \mathbb R^{m_1\times m_2}$ put
--   $$
--   \mathcal P_A(B) = B - P_{S_1^\perp} B P_{S_2^\perp}, \qquad \mathcal P_A^\perp(B) = P_{S_1^\perp} B P_{S_2^\perp}.
--   $$
--   For $c_0 \ge 0$, the **cone**
--   $$
--   \mathbb C_{A, c_0} = \big\{ B \in \mathbb A : \|\mathcal P_A^\perp(B)\|_1 \le c_0 \|\mathcal P_A(B)\|_1 \big\}
--   $$
--   collects the matrices of $\mathbb A$ whose part outside the tangent space at $A$ is controlled by their part inside it. A number $\mu'$ is a **cone constant** for $(A, c_0)$ if $\mu' > 0$ and
--   $$
--   \|\mathcal P_A(B)\|_2 \le \mu' \|B\|_{L_2(\Pi)} \qquad \text{for all } B \in \mathbb C_{A, c_0},
--   $$
--   where $\|\cdot\|_2$ is the Frobenius norm. The paper's restricted constant is the infimum of the cone constants,
--   $$
--   \mu_{c_0}(A) = \inf\big\{\mu' > 0 : \|\mathcal P_A(B)\|_2 \le \mu'\|B\|_{L_2(\Pi)}\ \ \forall B \in \mathbb C_{A, c_0}\big\},
--   $$
--   and $\mu(A) := \mu_5(A)$. It plays the role of the restricted eigenvalue condition of sparse vector estimation: Theorem 2 uses it in place of the global isometry Assumption 1.
--
--   **Formalization Note** The definition records the predicate "μ' is a cone constant" rather than the infimum. A real infimum of an empty set would be $0$, whereas the paper's $\mu_{c_0}(A)$ is $+\infty$ when no constant exists, so every theorem is stated for every cone constant $\mu'$. This is equivalent to the infimum form because the bounds are continuous and increasing in $\mu'$. The support enters through an SVD `S` of $A$; $\mathcal P_A$ is `tangentProjection S` and $\mathcal P_A^\perp$ is `normalProjection S`. These projections depend only on the column and row spaces of $A$, not on the chosen SVD. The cone lies inside $\mathbb A$, as on the page.
-- source:
--   Koltchinskii, Lounici, Tsybakov, Nuclear-Norm Penalization and Optimal Rates for Noisy Low-Rank Matrix Completion, arXiv:1011.6256v4, p. 10, definitions of 𝒫_A, ℂ_{A,c₀}, μ_{c₀}(A) and μ(A) := μ₅(A)

import Mathlib
import Definitions.Def_KLTNuclear_RestrictedEigen_Model

namespace KLTNuclear.RestrictedEigen

open MeasureTheory MatrixCompletion

/-! The cone ℂ_{A,c₀} and the restricted constant μ_{c₀}(A) of Koltchinskii, Lounici and
Tsybakov, arXiv:1011.6256v4, p. 10. Here `𝔸` is a linear subspace of ℝ^{m₁×m₂}, `S` is an SVD
of `A ∈ 𝔸` (so its column and row spans are the support (S₁, S₂) of `A`), 𝒫_A is
`tangentProjection S` and 𝒫_A⊥ is `normalProjection S`. -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The cone ℂ_{A,c₀} = {B ∈ 𝔸 : ‖𝒫_A⊥(B)‖₁ ≤ c₀ ‖𝒫_A(B)‖₁} (p. 10). -/
def cone {m₁ m₂ : ℕ} (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {A : RealMatrix m₁ m₂} {r : ℕ}
    (S : SVD A r) (c₀ : ℝ) : Set (RealMatrix m₁ m₂) :=
  {B | B ∈ 𝔸 ∧ nuclearNorm (normalProjection S B) ≤ c₀ * nuclearNorm (tangentProjection S B)}

/-- `μ'` belongs to the set whose infimum is μ_{c₀}(A) (p. 10):
μ' > 0 and ‖𝒫_A(B)‖₂ ≤ μ' ‖B‖_{L₂(Π)} for every B ∈ ℂ_{A,c₀}.
The paper's μ_{c₀}(A) is the infimum of all such `μ'` (+∞ when there is none). -/
def IsConeConstant (P : Measure Ω) {n m₁ m₂ : ℕ} (X : Fin n → Ω → RealMatrix m₁ m₂)
    (𝔸 : Submodule ℝ (RealMatrix m₁ m₂)) {A : RealMatrix m₁ m₂} {r : ℕ} (S : SVD A r)
    (c₀ μ' : ℝ) : Prop :=
  0 < μ' ∧ ∀ B ∈ cone 𝔸 S c₀,
    frobeniusNorm (tangentProjection S B) ≤ μ' * Real.sqrt (KLTNuclear.Oracle.l2NormSq P X B)

end KLTNuclear.RestrictedEigen


