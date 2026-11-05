-- Prove2me | Definitions.Def_CalendarDependentRM_Instance
-- name    : CalendarDependentRM_Instance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:35:08.201292+00:00
-- url     : https://prove2.me/theorems/6f42c54a-f493-4283-9d1c-452d78de80bf
-- title:
--   The revenue management instance, dynamic program (1), OPT, fluid approximation (2), and the guarantee
-- statement:
--   An instance consists of finite sets of resources $\mathcal L$ and products $\mathcal J$, the demand process over $K$ stages, the incidence $a_{ij}\in\{0,1\}$ (product $j$ uses resource $i$), revenues $f_j$, request probabilities $\lambda^k_{jt}$ with $\sum_j\lambda^k_{jt}=1$, and integer capacities $c_i$.
--
--   The **dynamic program (1)** has state $(y,q)$, the remaining capacities and the previous demand, and decisions $u\in\mathcal F(y)=\{u\in\{0,1\}^{|\mathcal J|}: a_{ij}u_j\le y_i\ \forall i,j\}$:
--
--   $$
--   J^k_t(y,q)=\max_{u\in\mathcal F(y)}\Big\{\sum_{j}\lambda^k_{jt}\big[f_ju_j+\theta^k_t(q)J^k_{t+1}(y-a_ju_j,q)+(1-\theta^k_t(q))J^{k+1}_1(y-a_ju_j,t)\big]\Big\},
--   $$
--
--   with $J^{K+1}_1=0$, and $\mathrm{OPT}=J^1_1(c,\hat D^0)$.
--
--   The **fluid approximation (2)** maximizes $\sum_k\sum_t\sum_q\sum_j f_jP\{D^k\ge t,D^{k-1}=q\}\,x^k_{jt}(q)$ over $x\ge0$ subject to $x^k_{jt}(q)\le\lambda^k_{jt}$ and, for all $i,t,q,k$,
--
--   $$
--   \sum_{\ell=1}^{k-1}\sum_s\sum_p\sum_j a_{ij}P\{D^\ell\ge s,D^{\ell-1}=p\mid D^k\ge t,D^{k-1}=q\}\,x^\ell_{js}(p)+\sum_{s=1}^t\sum_j a_{ij}x^k_{js}(q)\le c_i.
--   $$
--
--   With $c_{\min}=\min_ic_i$ and $L=\max_j\sum_ia_{ij}$, the **guarantee** of Theorem 4.1 is
--
--   $$
--   \max\Big\{\frac1{4L},\ 1-4\frac{\sqrt{(c_{\min}+\frac1{\epsilon^6}(K-1))\log c_{\min}}}{c_{\min}}-\frac L{c_{\min}}\Big\}.
--   $$
--
--   The definition also records the expected consumption $n^k_{it}(q)=\sum_ja_{ij}\gamma x^k_{jt}(q)$.
--
--   **Formalization Note** The value function takes natural-number indices and vanishes past the last stage or period. Natural subtraction in $y-a_ju_j$ does not truncate for $u\in\mathcal F(y)$. The optimal value $\overline Z_{LP}$ is `objective x` at an optimal `x`, never a supremum. A conditional coefficient given a null event reads $0$.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §2, pp.7–8, display (1); §3, display (2), p.8; p.12; p.16–17

import Mathlib
import Definitions.Def_CalendarDependentRM_DemandChain

open scoped Classical

namespace CalendarDependentRM

/-- **A network revenue management instance with staged Markov demand.**
Li, Rusmevichientong & Topaloglu, *Revenue Management with Calendar-Aware and Dependent Demands*,
arXiv:2409.02637v2, §2, p. 7.

* `R`, `J`: the resources `𝓛` and products `𝓙`;
* `chain`: the demand process over the `K` stages, with demand at most `T` per stage;
* `A j`: the resources used by product `j`, the support of `a_j ∈ {0, 1}^{|𝓛|}`;
* `f j`: the revenue of product `j`;
* `lam k t j`: the probability `λ^k_jt` that the customer at period `t` of stage `k` requests `j`;
* `c i`: the capacity of resource `i`.

**Formalization Note** Stages, periods and demands are 0-based, as in `DemandChain`. Capacities are
natural numbers because the paper's state space is `ℤ₊^{|𝓛|}`. The paper puts no sign on `f`. -/
structure Instance (R J : Type*) [Fintype J] (K T : ℕ) where
  /-- The Markov demand process. -/
  chain : DemandChain K T
  /-- The resources used by product `j`. -/
  A : J → Finset R
  /-- The revenue `f_j`. -/
  f : J → ℝ
  /-- The request probability `λ^k_jt`. -/
  lam : Fin K → Fin T → J → ℝ
  lam_nonneg : ∀ k t j, 0 ≤ lam k t j
  lam_sum : ∀ k t, ∑ j, lam k t j = 1
  /-- The capacity `c_i`. -/
  c : R → ℕ

namespace Instance

variable {R J : Type*} [Fintype J] {K T : ℕ} (I : Instance R J K T)

/-- The incidence `a_ij ∈ {0, 1}`: `a_ij = 1` iff product `j` uses resource `i`,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §2, p. 7. -/
noncomputable def a (i : R) (j : J) : ℕ :=
  if i ∈ I.A j then 1 else 0

/-- `u ∈ 𝓕(y)`: `a_ij u_j ≤ y_i` for all `i`, `j`, the feasible decisions of
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §2, p. 7. -/
def InF (y : R → ℕ) (u : J → Bool) : Prop :=
  ∀ i j, I.a i j * (u j).toNat ≤ y i

lemma inF_false (y : R → ℕ) : I.InF y (fun _ => false) := by
  intro i j; simp

/-- **The value functions of the dynamic program (1)**, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, display (1), p. 7:
`J^k_t(y, q) = max_{u ∈ 𝓕(y)} Σ_j λ^k_jt { f_j u_j + θ^k_t(q) J^k_{t+1}(y − a_j u_j, q)
+ (1 − θ^k_t(q)) J^{k+1}_1(y − a_j u_j, t) }`, with `J^{K+1}_1 = 0`.

**Formalization Note** `k`, `t` are 0-based natural numbers. `valueFn K 0 = 0` is the paper's boundary
condition. `valueFn k T` is `0` as well, and it is always multiplied by `θ^k_T(q) = 0`. The state `y` is
a vector of naturals and `y − a_j u_j` is natural subtraction, which does not truncate for `u ∈ 𝓕(y)`. -/
noncomputable def valueFn (k t : ℕ) (y : R → ℕ) (q : Fin T) : ℝ :=
  if h : k < K ∧ t < T then
    (Finset.univ.filter (I.InF y)).sup'
      ⟨fun _ => false, by simpa using I.inF_false y⟩ fun u =>
        ∑ j, I.lam ⟨k, h.1⟩ ⟨t, h.2⟩ j *
          (I.f j * ((u j).toNat : ℝ) +
            I.chain.theta ⟨k, h.1⟩ t q *
              valueFn k (t + 1) (fun i => y i - I.a i j * (u j).toNat) q +
            (1 - I.chain.theta ⟨k, h.1⟩ t q) *
              valueFn (k + 1) 0 (fun i => y i - I.a i j * (u j).toNat) ⟨t, h.2⟩)
  else 0
termination_by (K - k, T - t)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · exact Prod.Lex.left _ _ (by omega)

/-- **The optimal total expected revenue** `OPT = J¹₁(c, D̂⁰)`, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, p. 8. -/
noncomputable def OPT : ℝ :=
  I.valueFn 0 0 I.c I.chain.D0

/-- **Feasibility in the fluid approximation (2)**, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, display (2), p. 8. For `x = (x^k_jt(q))`, here `x k j t q`: `x ≥ 0`, the capacity
constraints

`Σ_{ℓ=1}^{k-1} Σ_s Σ_p Σ_j a_ij P{D^ℓ ≥ s, D^{ℓ-1} = p | D^k ≥ t, D^{k-1} = q} x^ℓ_js(p)
+ Σ_{s=1}^t Σ_j a_ij x^k_js(q) ≤ c_i`

for all `i`, `t`, `q`, `k`, and `x^k_jt(q) ≤ λ^k_jt`.

**Formalization Note** The conditional probability reads `0` when `{D^k ≥ t, D^{k-1} = q}` is null
(`DemandChain.condProb`); there the paper's coefficient is undefined. The second sum stays. That leaves
the optimal value unchanged: at such `(k, t, q)` the constraint involves, besides variables already
bounded by the constraint at the last reachable period, only variables with zero objective coefficient,
which the policy never uses. -/
structure Feasible (x : Fin K → J → Fin T → Fin T → ℝ) : Prop where
  nonneg : ∀ k j t q, 0 ≤ x k j t q
  capacity : ∀ i k t q,
    (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin K => ℓ < k), ∑ s, ∑ p, ∑ j,
        (I.a i j : ℝ) * I.chain.condProb (I.chain.reach ℓ s p) (I.chain.reach k t q) * x ℓ j s p) +
      ∑ s ∈ Finset.Iic t, ∑ j, (I.a i j : ℝ) * x k j s q ≤ (I.c i : ℝ)
  le_lam : ∀ k j t q, x k j t q ≤ I.lam k t j

/-- **The objective of the fluid approximation (2)**, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, display (2), p. 8: `Σ_k Σ_t Σ_q Σ_j f_j P{D^k ≥ t, D^{k-1} = q} x^k_jt(q)`.
At an optimal `x` this is the paper's `Z_LP`. -/
noncomputable def objective (x : Fin K → J → Fin T → Fin T → ℝ) : ℝ :=
  ∑ k, ∑ t, ∑ q, ∑ j, I.f j * I.chain.prob (I.chain.reach k t q) * x k j t q

/-- **An optimal solution of the fluid approximation (2)**, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, display (2), p. 8. -/
def IsOptimal (x : Fin K → J → Fin T → Fin T → ℝ) : Prop :=
  I.Feasible x ∧ ∀ y, I.Feasible y → I.objective y ≤ I.objective x

/-- `n^k_it(q) = Σ_j a_ij γ x^k_jt(q)`, the expectation of `N^k_it(q)` in
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §5, p. 16 (defined there as `E{N^k_it(q)}`),
in the closed form the paper derives on p. 17 and uses from then on.
Here `i`, `k`, `t`, `q` are the resource, stage, period and previous demand. -/
noncomputable def meanN (γ : ℝ) (x : Fin K → J → Fin T → Fin T → ℝ) (i : R) (k : Fin K)
    (t q : Fin T) : ℝ :=
  ∑ j, (I.a i j : ℝ) * (γ * x k j t q)

/-- **`c_min = min_{i ∈ 𝓛} c_i`**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, p. 12, cast to `ℝ`. -/
noncomputable def cmin [Fintype R] [Nonempty R] : ℝ :=
  ((Finset.univ.inf' Finset.univ_nonempty I.c : ℕ) : ℝ)

/-- **`L = max_{j ∈ 𝓙} Σ_{i ∈ 𝓛} a_ij`**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, p. 12,
cast to `ℝ`: the maximum number of resources used by a product. -/
noncomputable def L : ℝ :=
  ((Finset.univ.sup fun j => (I.A j).card : ℕ) : ℝ)

/-- **The performance guarantee** of Theorem 4.1 of Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, p. 12:
`max{ 1/(4L), 1 − 4 √((c_min + (1/ε⁶)(K − 1)) log c_min) / c_min − L / c_min }`, natural logarithm. -/
noncomputable def bound [Fintype R] [Nonempty R] (ε : ℝ) : ℝ :=
  max (1 / (4 * I.L))
    (1 - 4 * Real.sqrt ((I.cmin + (1 / ε ^ 6) * ((K : ℝ) - 1)) * Real.log I.cmin) / I.cmin -
      I.L / I.cmin)

end Instance

end CalendarDependentRM


