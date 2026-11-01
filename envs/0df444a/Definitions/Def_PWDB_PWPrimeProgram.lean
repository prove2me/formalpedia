-- Prove2me | Definitions.Def_PWDB_PWPrimeProgram
-- name    : PWDB_PWPrimeProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:38:19.542892+00:00
-- url     : https://prove2.me/theorems/496c374d-7a7e-4cc6-9909-cc1c3e5fa06b
-- title:
--   Reformulated primal worst problem (P-W′)
-- statement:
--   With $L_0 = \{0\} \cup L$ and $I_0 = \{0\} \cup I$, problem (P-W′) is
--   $$
--   \begin{aligned}
--   \inf\ & (-f_0)^{*2}(x, y_{00}) + \sum_{\ell\in L} \nu_{0\ell}\, c_\ell^*(y_{0\ell}/\nu_{0\ell})\\
--   \text{s.t.}\ & (-f_i)^{*2}(x, y_{i0}) + \sum_{\ell\in L} \nu_{i\ell}\, c_\ell^*(y_{i\ell}/\nu_{i\ell}) \le 0 \quad \forall i \in I,\\
--   & \sum_{\ell \in L_0} y_{i\ell} = 0 \quad \forall i \in I_0, \qquad \nu_{i\ell} \ge 0 .
--   \end{aligned}
--   $$
--   The module defines the objective `pwpObj`, the constraint functions `pwpCon`, the feasible region `pwpFeas`, the value `pwpVal`, and the constraints in the form of Definition 1 (`pwpIneq`, `pwpEq`).
--
--   **Formalization Note** $I_0$ and $L_0$ are `Option ι`, `Option L`, with `none` the index $0$. $\nu c^*(y/\nu)$ is the convex perspective of $c^*$.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), problem (P-W′), p.11

import Mathlib
import Definitions.Def_PWDB_conj
import Definitions.Def_PWDB_persp
import Definitions.Def_PWDB_PartialConj

open scoped InnerProductSpace

namespace PWDB

/-- **One row of the reformulated primal worst problem (P-W′)** (Zhen, Kuhn & Wiesemann,
arXiv:2105.00760v2, p.11): `(−g)∗2(x, y0) + Σ_{ℓ∈L} νℓ cℓ∗(yℓ/νℓ)`, where `y : L0 → F` with
`L0 = {0} ∪ L` (`Option L`, `none` is `0`) and `ν : L → ℝ`.

**Formalization Note** `(−g)∗2` is `pconj2` of `−g`; `νℓ cℓ∗(yℓ/νℓ)` is the convex perspective
`persp (conj (c ℓ))` (Definition A.2), so at `νℓ = 0` it is the support function of `dom(cℓ∗∗)`.
None of the summands is `−∞` for (RF) data and proper `cℓ`. -/
noncomputable def pwpTerm {E F L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype L] (c : L → F → EReal) (g : E → F → ℝ) (x : E) (y : Option L → F) (ν : L → ℝ) :
    EReal :=
  pconj2 (fun x z => -((g x z : ℝ) : EReal)) x (y none) +
    ∑ ℓ, persp (conj (c ℓ)) (y (some ℓ)) (ν ℓ)

/-- **Objective of (P-W′)** (arXiv:2105.00760v2, p.11):
`(−f0)∗2(x, y00) + Σ_{ℓ∈L} ν0ℓ cℓ∗(y0ℓ/ν0ℓ)` at `p = (x, y, ν)`, `y : I0 → L0 → F`,
`ν : I0 → L → ℝ`, with `I0 = Option ι` and `L0 = Option L` (`none` is the index `0`). -/
noncomputable def pwpObj {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype L] (c : L → F → EReal) (f₀ : E → F → ℝ)
    (p : E × (Option ι → Option L → F) × (Option ι → L → ℝ)) : EReal :=
  pwpTerm c f₀ p.1 (p.2.1 none) (p.2.2 none)

/-- **The `i`-th constraint function of (P-W′)** (arXiv:2105.00760v2, p.11):
`(−fi)∗2(x, yi0) + Σ_{ℓ∈L} νiℓ cℓ∗(yiℓ/νiℓ)`, `i ∈ I`. -/
noncomputable def pwpCon {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype L] (c : L → F → EReal) (f : ι → E → F → ℝ) (i : ι)
    (p : E × (Option ι → Option L → F) × (Option ι → L → ℝ)) : EReal :=
  pwpTerm c (f i) p.1 (p.2.1 (some i)) (p.2.2 (some i))

/-- **Feasible region of (P-W′)** (arXiv:2105.00760v2, p.11): the constraints
`(−fi)∗2(x, yi0) + Σ_ℓ νiℓ cℓ∗(yiℓ/νiℓ) ≤ 0` for `i ∈ I`, `Σ_{ℓ∈L0} yiℓ = 0` for `i ∈ I0`,
`νiℓ ≥ 0`, and (p.40) objective value other than `+∞`. -/
def pwpFeas {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype L]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) :
    Set (E × (Option ι → Option L → F) × (Option ι → L → ℝ)) :=
  {p | (∀ i, pwpCon c f i p ≤ 0) ∧ (∀ k, ∑ ℓ, p.2.1 k ℓ = 0) ∧ (∀ k ℓ, 0 ≤ p.2.2 k ℓ) ∧
    pwpObj c f₀ p ≠ ⊤}

/-- **Optimal value (infimum) of (P-W′)** (arXiv:2105.00760v2, p.11), in `EReal`. -/
noncomputable def pwpVal {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype L] (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) : EReal :=
  ⨅ p ∈ pwpFeas c f₀ f, pwpObj c f₀ p

/-- **Inequality constraints of (P-W′) in the form of Definition 1** (arXiv:2105.00760v2, p.6 and
p.11): the constraints `pwpCon i ≤ 0`, `i ∈ I`, and the affine constraints `−νiℓ ≤ 0`,
`i ∈ I0`, `ℓ ∈ L`. -/
noncomputable def pwpIneq {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype L] (c : L → F → EReal) (f : ι → E → F → ℝ) :
    ι ⊕ (Option ι × L) → (E × (Option ι → Option L → F) × (Option ι → L → ℝ)) → EReal :=
  fun k p => Sum.elim (fun i => pwpCon c f i p) (fun q => ((-(p.2.2 q.1 q.2) : ℝ) : EReal)) k

/-- **Equality constraints of (P-W′) in the form of Definition 1** (arXiv:2105.00760v2, p.6 and
p.11): the vector equations `Σ_{ℓ∈L0} yiℓ = 0`, `i ∈ I0`, as the scalar linear equations
`⟨v, Σ_ℓ yiℓ⟩ = 0`, one for each `i ∈ I0` and `v ∈ F` (the same set and the same Slater conditions
as the coordinate equations, since all are linear and finite). -/
noncomputable def pwpEq {E F ι L : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [Fintype L] :
    Option ι × F → (E × (Option ι → Option L → F) × (Option ι → L → ℝ)) → EReal :=
  fun q p => ((⟪q.2, ∑ ℓ, p.2.1 q.1 ℓ⟫_ℝ : ℝ) : EReal)

end PWDB


