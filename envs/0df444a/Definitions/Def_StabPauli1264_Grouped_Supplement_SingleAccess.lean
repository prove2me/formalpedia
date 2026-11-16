-- Prove2me | Definitions.Def_StabPauli1264_Grouped_Supplement_SingleAccess
-- name    : StabPauli1264_Grouped_Supplement_SingleAccess
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T06:45:54.392203+00:00
-- url     : https://prove2.me/theorems/b619dfbd-3c0f-47f6-928a-d7de345ec683
-- title:
--   Random single-Pauli learners and the complexity $N_{\mathrm{single}}$
-- statement:
--   Under **random single-Pauli access** each copy of the unknown state $\rho$ yields an example $(I,S)$ with
--
--   $$\Pr[I=i,S=s]=p_i\,\frac{1+s\,b_i}{2},\qquad b_i=\operatorname{tr}(\rho P_i)$$
--
--   (Eq. (3)), independently across copies. A proper learner using $N$ copies is an arbitrary randomized rule from the $N$ examples to stabilizer tableaux whose outputs are valid; it is not given $p$. Its success probability is the probability that the output state $\hat\sigma$ satisfies $R(\hat\sigma)-R^*\le\varepsilon$.
--
--   $N_{\mathrm{single}}(M,\varepsilon,\delta)$ is the least $N$ such that one such learner $(\varepsilon,\delta)$-learns $M$ under every distribution $p$ and every density matrix $\rho$; it is $+\infty$ if there is none.
--
--   **Formalization Note** As in the base mission, laws have real masses, the complexity is an infimum in $\mathbb N\cup\{\infty\}$, and outcome bit `true` stands for $-1$ (base `sign`). Computation is unrestricted (Definition 5.3).
-- source:
--   Yingjian Liu, Xiaoyi Yang, Zhaohui Yang, STOC 2027 submission #1264 (October 2026), Eq. (3) p. 3; §2 p. 6; Definition 5.3 p. 13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1264.pdf

import Definitions.Def_StabPauli1264_Grouped_Supplement_Structure
set_option autoImplicit false

namespace StabPauli1264.Grouped.Supplement

open QAlgorithms.Stabilizer StabPauli1264.Grouped
open scoped BigOperators Classical ENNReal

/-- One random single-Pauli example `(I, S)`: an index and an outcome bit (`true` is `−1`, as in
the base `sign`). -/
abbrev SingleExample (m : ℕ) := Fin m × Bool

/-- Eq. (3): `Pr[I = i, S = s] = p_i (1 + s b_i)/2` on a fresh copy. -/
noncomputable def singleWeight {n m : ℕ} (M : Window n m) (p : EvalLaw m) (ρ : Mat n)
    (z : SingleExample m) : ℝ :=
  p.mass z.1 * (1 + sign z.2 * bias M ρ z.1) / 2

/-- A statistical proper learner under random single-Pauli access with exactly `N` copies: an
arbitrary randomized rule from the `N` examples to tableaux. It is not given `p`. -/
structure SingleProcedure (n m N : ℕ) where
  output : (Fin N → SingleExample m) → OAI.ThorpCompatibility.Law (Tableau n)

/-- Properness: only valid tableaux are output with positive probability. -/
def SinglePermitted {n m N : ℕ} (A : SingleProcedure n m N) : Prop :=
  ∀ h T, (A.output h).mass T ≠ 0 → IsValidTableau T

/-- Probability that the output is a valid tableau with excess risk at most `ε`; the `N` examples
are i.i.d. with law Eq. (3). -/
noncomputable def singleSuccess {n m N : ℕ} (M : Window n m) (p : EvalLaw m)
    (A : SingleProcedure n m N) (ρ : Mat n) (ε : ℝ) : ℝ :=
  ∑ h : Fin N → SingleExample m, (∏ t, singleWeight M p ρ (h t)) *
    ∑ T : Tableau n, (A.output h).mass T *
      if IsValidTableau T ∧ excess M p ρ (response M T) ≤ ε then 1 else 0

/-- One learner, chosen before `p` and `ρ`, `(ε, δ)`-learns `M` under every `p` and every density
matrix from `N` random single-Pauli copies. -/
def SingleAchievable {n m : ℕ} (M : Window n m) (ε δ : ℝ) (N : ℕ) : Prop :=
  ∃ A : SingleProcedure n m N, SinglePermitted A ∧
    ∀ p : EvalLaw m, ∀ ρ : Density n, 1 - δ ≤ singleSuccess M p A ρ.matrix ε

/-- `N_single(M, ε, δ)`: the least such `N`, as an extended natural (`⊤` if none exists). -/
noncomputable def singleComplexity {n m : ℕ} (M : Window n m) (ε δ : ℝ) : ℕ∞ :=
  sInf {K | ∃ N : ℕ, K = (N : ℕ∞) ∧ SingleAchievable M ε δ N}

end StabPauli1264.Grouped.Supplement


