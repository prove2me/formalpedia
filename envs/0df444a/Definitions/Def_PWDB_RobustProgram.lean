-- Prove2me | Definitions.Def_PWDB_RobustProgram
-- name    : PWDB_RobustProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:38:12.389639+00:00
-- url     : https://prove2.me/theorems/598d4754-50c6-464a-b9de-ef2faf62bca8
-- title:
--   Uncertainty set $Z$, primal worst (P-W) and dual best (D-B) problems
-- statement:
--   Let $c_\ell : F \to \overline{\mathbb R}$, $\ell \in L$, and $Z = \{z \in F \mid c_\ell(z) \le 0\ \forall \ell \in L\}$ (eq. (1)). With $f_0, f_i : E \times F \to \mathbb R$, the **primal worst problem** is
--   $$
--   \inf_x\ \sup_{z_0 \in Z} f_0(x, z_0) \quad\text{s.t.}\quad \sup_{z_i \in Z} f_i(x, z_i) \le 0\ \ \forall i \in I, \tag{P-W}
--   $$
--   and the **dual best problem** is
--   $$
--   \sup\ -f_0^{*1}(w_0, z_0) - \sum_{i\in I}\lambda_i f_i^{*1}(w_i/\lambda_i, z_i) \quad\text{s.t.}\quad \sum_{i \in I_0} w_i = 0,\ z_i \in Z\ (i \in I_0),\ \lambda \ge 0. \tag{D-B}
--   $$
--   The module defines `Z`, the worst-case function `worst c g x` $= \sup_{z\in Z} g(x,z)$, the feasible regions `pwFeas`, `dbFeas`, the objective `dbObj` and the values `pwVal`, `dbVal`.
--
--   **Formalization Note** A (D-B) point is $(w_0, z_0, w, z, \lambda)$. The term $\lambda_i f_i^{*1}(w_i/\lambda_i, z_i)$ is the partial perspective of $f_i^{*1}$, so at $\lambda_i = 0$ it is $0$ for $w_i = 0$ and $+\infty$ otherwise, never $0 \cdot f_i^{*1}$.
-- source:
--   Zhen, Kuhn & Wiesemann, A Unified Theory of Robust and Distributionally Robust Optimization via the Primal-Worst-Equals-Dual-Best Principle, arXiv:2105.00760v2 (19 Jul 2023), eq. (1), p.9; problems (P-W) and (D-B), p.10; conventions p.40

import Mathlib
import Definitions.Def_PWDB_PartialConj
import Definitions.Def_PWDB_pPersp

namespace PWDB

/-- **Uncertainty set** `Z` (Zhen, Kuhn & Wiesemann, arXiv:2105.00760v2, eq. (1), p.9):
`Z = {z ∈ ℝ^{dz} | cℓ(z) ≤ 0 ∀ℓ ∈ L}`, "described by the constraint functions
`cℓ : ℝ^{dz} → R̄`, `ℓ ∈ L`". The paper assumes `Z` nonempty and (C); every statement of the
mission carries both as hypotheses. -/
def Z {F L : Type*} (c : L → F → EReal) : Set F :=
  {z | ∀ ℓ, c ℓ z ≤ 0}

/-- **Worst-case function** `F(x) = sup_{z∈Z} f(x, z)` (arXiv:2105.00760v2, (P-W), p.10, and the
notation `Fi(x) = sup_{zi∈Z} fi(x, zi)` of (20), p.54), in `EReal`. -/
noncomputable def worst {E F L : Type*} (c : L → F → EReal) (g : E → F → ℝ) (x : E) : EReal :=
  ⨆ z ∈ Z c, ((g x z : ℝ) : EReal)

/-- **Feasible region of the primal worst problem (P-W)** (arXiv:2105.00760v2, p.10):
`inf sup_{z0∈Z} f0(x, z0) s.t. sup_{zi∈Z} fi(x, zi) ≤ 0 ∀i ∈ I, x free`. Feasibility (p.40)
excludes the objective value `+∞`. -/
def pwFeas {E F ι L : Type*} (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) : Set E :=
  {x | (∀ i, worst c (f i) x ≤ 0) ∧ worst c f₀ x ≠ ⊤}

/-- **Optimal value (infimum) of (P-W)** (arXiv:2105.00760v2, p.10), in `EReal`. -/
noncomputable def pwVal {E F ι L : Type*} (c : L → F → EReal) (f₀ : E → F → ℝ)
    (f : ι → E → F → ℝ) : EReal :=
  ⨅ x ∈ pwFeas c f₀ f, worst c f₀ x

/-- **Objective of the dual best problem (D-B)** (arXiv:2105.00760v2, p.10):
`−f0∗1(w0, z0) − Σ_{i∈I} λi fi∗1(wi/λi, zi)` at `p = (w₀, z₀, w, z, λ)`.

**Formalization Note** `fi∗1` is `pconj1` of `fi` viewed as `EReal`-valued, and
`λi fi∗1(wi/λi, zi)` is the convex partial perspective of `fi∗1` (Definition A.4, p.41), so at
`λi = 0` it is the support function of `dom(fi∗1∗1(·, zi))` at `wi` (for (RF) data: `0` if `wi = 0`,
`+∞` otherwise), never `0 · fi∗1(…)`. -/
noncomputable def dbObj {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (f₀ : E → F → ℝ) (f : ι → E → F → ℝ)
    (p : E × F × (ι → E) × (ι → F) × (ι → ℝ)) : EReal :=
  -(pconj1 (fun x z => ((f₀ x z : ℝ) : EReal)) p.1 p.2.1 +
    ∑ i, pPersp (pconj1 (fun x z => ((f i x z : ℝ) : EReal))) (p.2.2.1 i) (p.2.2.2.2 i)
      (p.2.2.2.1 i))

/-- **Feasible region of (D-B)** (arXiv:2105.00760v2, p.10): `Σ_{i∈I0} wi = 0`, `wi` free,
`zi ∈ Z`, `i ∈ I0`, `λ ≥ 0`; feasibility (p.40) excludes the objective value `−∞`. Points are
`p = (w₀, z₀, w, z, λ)`. -/
def dbFeas {E F ι L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fintype ι]
    (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) :
    Set (E × F × (ι → E) × (ι → F) × (ι → ℝ)) :=
  {p | p.1 + ∑ i, p.2.2.1 i = 0 ∧ p.2.1 ∈ Z c ∧ (∀ i, p.2.2.2.1 i ∈ Z c) ∧
    (∀ i, 0 ≤ p.2.2.2.2 i) ∧ dbObj f₀ f p ≠ ⊥}

/-- **Optimal value (supremum) of (D-B)** (arXiv:2105.00760v2, p.10), in `EReal`. -/
noncomputable def dbVal {E F ι L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fintype ι] (c : L → F → EReal) (f₀ : E → F → ℝ) (f : ι → E → F → ℝ) : EReal :=
  ⨆ p ∈ dbFeas c f₀ f, dbObj f₀ f p

end PWDB


