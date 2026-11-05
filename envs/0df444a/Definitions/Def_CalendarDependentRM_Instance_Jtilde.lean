-- Prove2me | Definitions.Def_CalendarDependentRM_Instance_Jtilde
-- name    : CalendarDependentRM_Instance_Jtilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:56.786347+00:00
-- url     : https://prove2.me/theorems/bc862702-85af-48c6-9bc1-c780931b013f
-- title:
--   The relaxed dynamic program (9) and its slopes and intercepts (10)
-- statement:
--   Relaxing $a_{ij}u_j\le y_i$ with multipliers $\mu^k_{it}(q)$ gives the **relaxed dynamic program (9)**:
--
--   $$
--   \tilde J^k_t(y,q;\mu)=\max_{u\in\{0,1\}^{|\mathcal J|}}\Big\{\sum_j\lambda^k_{jt}\big\{f_ju_j+\theta^k_t(q)\tilde J^k_{t+1}(y-a_ju_j,q;\mu)+(1-\theta^k_t(q))\tilde J^{k+1}_1(y-a_ju_j,t;\mu)\big\}+\sum_i\sum_j\lambda^k_{jt}\mu^k_{it}(q)[y_i-a_{ij}u_j]\Big\},
--   $$
--
--   with $\tilde J^{K+1}_1=0$. The **slopes and intercepts (10)** are
--
--   $$
--   \alpha^k_{it}(q;\mu)=\mu^k_{it}(q)+\theta^k_t(q)\alpha^k_{i,t+1}(q;\mu)+(1-\theta^k_t(q))\alpha^{k+1}_{i1}(t;\mu),
--   $$
--
--   $$
--   \beta^k_t(q;\mu)=\sum_j\lambda^k_{jt}\Big[f_j-\sum_ia_{ij}\alpha^k_{it}(q;\mu)\Big]^++\theta^k_t(q)\beta^k_{t+1}(q;\mu)+(1-\theta^k_t(q))\beta^{k+1}_1(t;\mu),
--   $$
--
--   with zero boundary conditions at stage $K+1$. They lead to the linear program (11) whose dual yields Theorem 3.1.
--
--   **Formalization Note** The relaxation lets capacities go negative, so $y$ is integer valued. The printed outer sum in (9) reads $\sum_{j\in\mathcal T}$, a slip for $\sum_{j\in\mathcal J}$.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §B, displays (9), (10), ER p.3 (PDF 25)

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance

open scoped Classical

namespace CalendarDependentRM

namespace Instance

variable {R J : Type*} [Fintype J] {K T : ℕ} (I : Instance R J K T)

/-- **The value functions of the relaxed dynamic program (9)**, Li, Rusmevichientong & Topaloglu,
*Revenue Management with Calendar-Aware and Dependent Demands*, arXiv:2409.02637v2, display (9), Extended
Results p. 3, first line:
`J̃^k_t(y, q; µ) = max_{u ∈ {0,1}^{|J|}} { Σ_j λ^k_jt { f_j u_j + θ^k_t(q) J̃^k_{t+1}(y − a_j u_j, q; µ)
+ (1 − θ^k_t(q)) J̃^{k+1}_1(y − a_j u_j, t; µ) } + Σ_i Σ_j λ^k_jt µ^k_it(q) [y_i − a_ij u_j] }`,
with `J̃^{K+1}_1 = 0`.

**Formalization Note** `µ k i t q` is `µ^k_it(q)`. The printed outer sum reads `Σ_{j∈𝒯}`, a slip for `Σ_{j∈𝒥}`.
The relaxation drops `a_ij u_j ≤ y_i`, so the capacity can become negative and `y` is integer valued.
`k`, `t` are 0-based natural numbers; `Jtilde k T` is `0` and is always multiplied by `θ^k_T(q) = 0`. -/
noncomputable def Jtilde [Fintype R] (μ : Fin K → R → Fin T → Fin T → ℝ) (k t : ℕ) (y : R → ℤ)
    (q : Fin T) : ℝ :=
  if h : k < K ∧ t < T then
    Finset.univ.sup' (Finset.univ_nonempty (α := J → Bool)) fun u =>
      (∑ j, I.lam ⟨k, h.1⟩ ⟨t, h.2⟩ j *
        (I.f j * ((u j).toNat : ℝ) +
          I.chain.theta ⟨k, h.1⟩ t q *
            Jtilde μ k (t + 1) (fun i => y i - (I.a i j : ℤ) * ((u j).toNat : ℤ)) q +
          (1 - I.chain.theta ⟨k, h.1⟩ t q) *
            Jtilde μ (k + 1) 0 (fun i => y i - (I.a i j : ℤ) * ((u j).toNat : ℤ)) ⟨t, h.2⟩)) +
      ∑ i, ∑ j, I.lam ⟨k, h.1⟩ ⟨t, h.2⟩ j * μ ⟨k, h.1⟩ i ⟨t, h.2⟩ q *
        ((y i : ℝ) - (I.a i j : ℝ) * ((u j).toNat : ℝ))
  else 0
termination_by (K - k, T - t)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- **The slopes `α^k_it(q; µ)` of (10)**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, display (10),
Extended Results p. 3:
`α^k_it(q; µ) = µ^k_it(q) + θ^k_t(q) α^k_{i,t+1}(q; µ) + (1 − θ^k_t(q)) α^{k+1}_{i1}(t; µ)`, with
`α^{K+1}_{i1} = 0`. -/
noncomputable def alpha (μ : Fin K → R → Fin T → Fin T → ℝ) (k t : ℕ) (i : R) (q : Fin T) : ℝ :=
  if h : k < K ∧ t < T then
    μ ⟨k, h.1⟩ i ⟨t, h.2⟩ q +
      I.chain.theta ⟨k, h.1⟩ t q * alpha μ k (t + 1) i q +
      (1 - I.chain.theta ⟨k, h.1⟩ t q) * alpha μ (k + 1) 0 i ⟨t, h.2⟩
  else 0
termination_by (K - k, T - t)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- **The intercepts `β^k_t(q; µ)` of (10)**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, display (10),
Extended Results p. 3:
`β^k_t(q; µ) = Σ_j λ^k_jt [f_j − Σ_i a_ij α^k_it(q; µ)]^+ + θ^k_t(q) β^k_{t+1}(q; µ)
+ (1 − θ^k_t(q)) β^{k+1}_1(t; µ)`, with `β^{K+1}_1 = 0`. -/
noncomputable def beta [Fintype R] (μ : Fin K → R → Fin T → Fin T → ℝ) (k t : ℕ) (q : Fin T) : ℝ :=
  if h : k < K ∧ t < T then
    (∑ j, I.lam ⟨k, h.1⟩ ⟨t, h.2⟩ j *
        max (I.f j - ∑ i, (I.a i j : ℝ) * I.alpha μ k t i q) 0) +
      I.chain.theta ⟨k, h.1⟩ t q * beta μ k (t + 1) q +
      (1 - I.chain.theta ⟨k, h.1⟩ t q) * beta μ (k + 1) 0 ⟨t, h.2⟩
  else 0
termination_by (K - k, T - t)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

end Instance

end CalendarDependentRM


