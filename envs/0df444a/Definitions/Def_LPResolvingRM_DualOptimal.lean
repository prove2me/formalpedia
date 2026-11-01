-- Prove2me | Definitions.Def_LPResolvingRM_DualOptimal
-- name    : LPResolvingRM_DualOptimal
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:40:07.492984+00:00
-- url     : https://prove2.me/theorems/8dd64583-603a-4678-b48c-8c3ff6774225
-- title:
--   The dual program (7), the dual-price margins $\mu_j-c_j^\top\lambda$, $\mathcal J^*$, $\mathcal J'$ and the constant $\Lambda$
-- statement:
--   The dual of the fluid LP is
--   $$\min\ b^\top\lambda+\sum_{j=1}^n\gamma_j\quad\text{s.t.}\quad p_jc_j^\top\lambda+\gamma_j\ge p_j\mu_j\ (j=1,\dots,n),\quad \lambda\ge0,\ \gamma\ge0. \tag{7}$$
--   Its optimal $\lambda^*$ is the dual price of the resources. With the raw data, the order types split into
--   $$\mathcal J^*=\{j:\mu_j\ge c_j^\top\lambda^*\},\qquad \mathcal J'=\{j:\mu_j<c_j^\top\lambda^*\}.$$
--   Write $\max_{j\in[n]}|\mu_j-c_j^\top\lambda|$ for the largest margin and
--   $$\Lambda:=\max\Big\{\|\lambda\|_1,\ \max_{j\in[n]}|\mu_j-c_j^\top\lambda|\Big\},$$
--   the constant that replaces $\|\lambda^*\|_1$ in the corrected Theorem 4 and Lemma 3.
--
--   **Formalization Note** The maximum over $j$ is a supremum over the finite type `Fin n` (nonempty under Assumption 1).
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, (7), p.8; J*, J′, p.9; Corollary 1, p.10; Theorem 4, p.37

import Definitions.Def_LPResolvingRM_Instance

open scoped Classical

namespace LPResolvingRM

/-- Feasibility for the **dual program (7)** of the fluid LP (arXiv:2101.11092v3, p.8):
`p_j c_jᵀλ + γ_j ≥ p_jμ_j` for `j = 1, …, n`, `λ ≥ 0`, `γ ≥ 0`. -/
def DualFeasible {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) (γ : Fin n → ℝ) : Prop :=
  (∀ i, 0 ≤ lam i) ∧ (∀ j, 0 ≤ γ j) ∧
    ∀ j, I.p j * I.μ j ≤ I.p j * ∑ i, I.c j i * lam i + γ j

/-- **Dual optimal solution of (7)** (arXiv:2101.11092v3, p.8):
`min bᵀλ + ∑_j γ_j` over the dual feasible set. Its `λ`-part is the dual price `λ*` of the
resource constraints. -/
def DualOptimal {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) (γ : Fin n → ℝ) : Prop :=
  DualFeasible I lam γ ∧ ∀ lam' γ', DualFeasible I lam' γ' →
    ∑ i, I.b i * lam i + ∑ j, γ j ≤ ∑ i, I.b i * lam' i + ∑ j, γ' j

/-- The **dual-price margin** `μ_j − c_jᵀλ` of type `j` (arXiv:2101.11092v3, pp.9–10), computed
with the raw (not normalized) `μ_j` and `c_j`. -/
def gap {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) (j : Fin n) : ℝ :=
  I.μ j - ∑ i, I.c j i * lam i

/-- The **basic order types** `J* := {j : μ_j ≥ c_jᵀλ*}` (arXiv:2101.11092v3, p.9). -/
noncomputable def Jstar {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j => 0 ≤ gap I lam j

/-- The **non-basic order types** `J' := {j : μ_j < c_jᵀλ*}` (arXiv:2101.11092v3, p.9). -/
noncomputable def Jprime {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun j => gap I lam j < 0

/-- `max_{j ∈ [n]} |μ_j − c_jᵀλ|` (arXiv:2101.11092v3, Corollary 1, p.10).

**Formalization Note.** A supremum over the finite type `Fin n`; it is a maximum for `n ≥ 1`,
which Assumption 1 forces (`∑_j p_j = 1`). -/
noncomputable def maxGap {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) : ℝ :=
  ⨆ j : Fin n, |gap I lam j|

/-- The **corrected regret constant** `Λ := max{‖λ‖₁, max_{j ∈ [n]} |μ_j − c_jᵀλ|}` that replaces
`‖λ*‖₁` in Theorem 4 (p.37) and Lemma 3 (p.13) of arXiv:2101.11092v3.

**Formalization Note.** The printed constant `‖λ*‖₁` is false (see the theorems using `Λ`);
the proof of Theorem 4 (p.41) bounds `max_j |μ_j − c_jᵀλ*|` and `‖λ*‖₁` separately, and `Λ`
dominates both. `‖λ‖₁ = ∑_i |λ_i|`. -/
noncomputable def bigLambda {n m : ℕ} (I : Instance n m) (lam : Fin m → ℝ) : ℝ :=
  max (∑ i, |lam i|) (maxGap I lam)

end LPResolvingRM


