-- Prove2me | Definitions.Def_CandesTao_Decoding_RestrictedIsometry
-- name    : CandesTao_Decoding_RestrictedIsometry
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-30T22:02:18.546754+00:00
-- url     : https://prove2.me/theorems/503a5ae4-1ea8-4d2e-83c6-3392f1dfd344
-- title:
--   Restricted isometry constants $\delta_S$ and restricted orthogonality constants $\theta_{S,S'}$ (Definition 1.1)
-- statement:
--   Let $F$ be a real $p \times m$ matrix with columns $v_1, \dots, v_m \in \mathbb{R}^p$, and let $H$ be the linear span of these columns (the paper's Hilbert space $H$). For an index set $T$ and real coefficients $c$ supported on $T$, $F_T c = \sum_{j \in T} c_j v_j = Fc$.
--
--   **Definition 1.1 (restricted isometry constants).** For an integer $S$, the **$S$-restricted isometry constant** $\delta_S = \delta_S(F)$ is the smallest quantity such that
--   $$
--   (1 - \delta_S)\,\|c\|^2 \le \|F_T c\|^2 \le (1 + \delta_S)\,\|c\|^2
--   $$
--   for all subsets $T$ of cardinality at most $S$ and all real coefficients $(c_j)_{j \in T}$ (equation (1.7)). Similarly, the **$S, S'$-restricted orthogonality constant** $\theta_{S,S'} = \theta_{S,S'}(F)$ is the smallest quantity such that
--   $$
--   |\langle F_T c, F_{T'} c' \rangle| \le \theta_{S,S'} \, \|c\| \, \|c'\|
--   $$
--   holds for all disjoint sets $T, T'$ of cardinality $|T| \le S$ and $|T'| \le S'$ (equation (1.8)). The paper abbreviates $\theta_{S,S}$ to $\theta_S$.
--
--   These numbers measure how close the columns of $F$ are to an orthonormal system when only sparse linear combinations, involving at most $S$ (resp. $S$ and $S'$) columns, are considered. They are non-decreasing in $S$ and $S'$, and every hypothesis of the mission's theorems is expressed through them. The file also names the $j$-th column $v_j$ of $F$ and the span $H$ of the columns.
--
--   **Formalization Note** Each constant is the infimum of the set of *nonnegative* $\delta$ (resp. $\theta$) that satisfy the defining inequalities for every admissible $T$ (and $T'$) and every coefficient vector. That set is nonempty, closed and bounded below, so the infimum is attained and is the paper's "smallest quantity". On the paper's domain ($1 \le S \le m$ for $\delta_S$, and $S + S' \le m$ with $S, S' \ge 1$ for $\theta_{S,S'}$) the smallest such quantity is automatically nonnegative, so the clause $\delta \ge 0$ changes nothing there and only fixes a harmless value in degenerate cases (for instance $\delta_0 = 0$). The definitions are total in $S$ and $S'$; the theorems of the mission state the paper's domain conditions as explicit hypotheses.
-- source:
--   Candès--Tao 2005, Decoding by Linear Programming, IEEE Trans. Inform. Theory 51(12):4203-4215, doi:10.1109/TIT.2005.858979; arXiv:math/0502327v1 (https://arxiv.org/abs/math/0502327), p. 5, Definition 1.1, eqs. (1.7) and (1.8); columns v_j and the space H, p. 4, Section 1.4

import Mathlib.LinearAlgebra.Span.Defs
import Definitions.Def_CandesTao_Decoding_Norms

namespace CandesTao.Decoding

/-- The `j`-th column `v_j ∈ ℝ^p` of the `p × m` matrix `F`. -/
def column {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (j : Fin m) : Fin p → ℝ :=
  fun i => F i j

/-- The Hilbert space `H` spanned by the columns `v_j` of `F`. -/
def columnSpan {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) : Submodule ℝ (Fin p → ℝ) :=
  Submodule.span ℝ (Set.range (column F))

/-- The `S`-restricted isometry constant `δ_S` of `F` (Definition 1.1, (1.7)): the least
`δ ≥ 0` such that `(1 - δ) ‖c‖² ≤ ‖F c‖² ≤ (1 + δ) ‖c‖²` for every real vector `c`
supported on a set of at most `S` columns. -/
noncomputable def restrictedIsometryConst {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ) (S : ℕ) :
    ℝ :=
  sInf {δ : ℝ | 0 ≤ δ ∧ ∀ T : Finset (Fin m), T.card ≤ S → ∀ c : Fin m → ℝ, SupportedOn c T →
    (1 - δ) * l2Norm c ^ 2 ≤ l2Norm (F.mulVec c) ^ 2 ∧
    l2Norm (F.mulVec c) ^ 2 ≤ (1 + δ) * l2Norm c ^ 2}

/-- The `S, S'`-restricted orthogonality constant `θ_{S,S'}` of `F` (Definition 1.1, (1.8)):
the least `θ ≥ 0` such that `|⟨F c, F c'⟩| ≤ θ ‖c‖ ‖c'‖` for all real vectors `c`, `c'`
supported on disjoint sets of at most `S` and at most `S'` columns respectively. -/
noncomputable def restrictedOrthogonalityConst {p m : ℕ} (F : Matrix (Fin p) (Fin m) ℝ)
    (S S' : ℕ) : ℝ :=
  sInf {θ : ℝ | 0 ≤ θ ∧ ∀ T T' : Finset (Fin m), Disjoint T T' → T.card ≤ S → T'.card ≤ S' →
    ∀ c c' : Fin m → ℝ, SupportedOn c T → SupportedOn c' T' →
    |dotProduct (F.mulVec c) (F.mulVec c')| ≤ θ * l2Norm c * l2Norm c'}

end CandesTao.Decoding


