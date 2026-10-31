-- Prove2me | Definitions.Def_NonlinearPriority_Params
-- name    : NonlinearPriority_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:22:03.105682+00:00
-- url     : https://prove2.me/theorems/34100ab0-a7d7-4970-babb-7114db5584b3
-- title:
--   Parameters of the multiclass $M/G/1$ queue: $K,\lambda,p_i,S_i,\mu_i$, stability $\rho<1$
-- statement:
--   A single server serves $K\ge 2$ types of customers. Customers arrive in a Poisson stream of rate $\lambda>0$; an arrival is of type $i$ with probability $p_i>0$, where $\sum_{i=1}^K p_i=1$. The service times of type $i$ have law $S_i$, a probability measure on $[0,\infty)$ with mean $1/\mu_i$, $\mu_i>0$. The traffic intensities are
--   $$\rho_i=\frac{\lambda p_i}{\mu_i},\qquad \rho=\sum_{i=1}^K\rho_i=\lambda\sum_{i=1}^K\frac{p_i}{\mu_i},$$
--   and the system is stable: $\rho<1$.
--
--   The structure also provides the derived quantities used throughout: the $n$th service moments $\tau^{(n)}_i=\int x^n\,dS_i$ and $\tau^{(n)}=\sum_j p_j\tau^{(n)}_j$, the residual loads $\bar\rho_m=1-\sum_{j\le m}\rho_j$ (with $\bar\rho_0=1$), and the partial sums $\sum_{\ell\le m}p_\ell\tau^{(2)}_\ell$ that appear in (A.8)–(A.10).
--
--   **Formalization Note** Types are `Fin K` (0-based), so the first $m$ types are those with index $<m$ and `rhoBar m` is exactly the paper's $\bar\rho_m$. The rate $\mu_i$ is a field tied to $S_i$ by $\int x\,dS_i=1/\mu_i$. Moments are Bochner integrals (value $0$ if infinite); statements that use them assume finiteness.
-- source:
--   Ouyang–Argon–Ziya, Assigning Priorities (or Not), Management Science (2021, Articles in Advance), doi:10.1287/mnsc.2020.3952, §3, p.3 (PDF 4); Table A.1, p.15 (PDF 16)

import Mathlib

open MeasureTheory

namespace NonlinearPriority

/-- **The parameters of the multiclass single-server queue** (§3, p. 3, PDF 4; Table A.1, p. 15,
PDF 16). Ouyang, Argon and Ziya, *Assigning Priorities (or Not) in Service Systems with Nonlinear
Waiting Costs*, Management Science (Articles in Advance 2021), doi:10.1287/mnsc.2020.3952.

"Consider a single-server queueing system with K types of customers, in which K is an integer and
2 ≤ K < ∞. Customers arrive to the system according to a Poisson process with rate λ > 0, and each
arriving customer belongs to type i ∈ {1, 2, …, K} with probability pi > 0, where Σ pi = 1,
independently of the arrival process. Service times for type i customers are i.i.d. with rate
μi > 0 … we assume that ρ < 1 for stability."

* `K` types, `2 ≤ K`;
* `lam` is the arrival rate λ > 0;
* `p i > 0` with `Σ p i = 1`;
* `S i` is the service-time law of type `i`, a probability measure concentrated on `[0, ∞)`;
* `mu i > 0` is the service rate: the mean of `S i` is `1 / mu i`;
* stability: `ρ = λ Σ pᵢ/μᵢ < 1` (the paper's `ρ ≡ λ/μ` with `μ ≡ 1/Σ pᵢ/μᵢ`, the same number).

**Formalization Note.** `lam` stands for λ. Types are `Fin K` (0-based): the paper's type `i` is
`⟨i - 1, _⟩`. `μᵢ` is kept as a field tied to `S i` by `∫ x ∂(S i) = 1/μᵢ`; since `1/μᵢ ≠ 0` this
equation also forces `S i` to have a finite mean. The paper's positivity of the moments `τ(n)ᵢ > 0`
follows from a positive mean of a nonnegative law; their *finiteness* is not part of the model and
is assumed separately where a statement needs it. -/
structure Params (K : ℕ) where
  /-- the arrival rate λ -/
  lam : ℝ
  /-- the type probabilities `pᵢ` -/
  p : Fin K → ℝ
  /-- the service-time law of each type -/
  S : Fin K → Measure ℝ
  /-- the service rates `μᵢ` -/
  mu : Fin K → ℝ
  two_le : 2 ≤ K
  lam_pos : 0 < lam
  p_pos : ∀ i, 0 < p i
  p_sum : ∑ i, p i = 1
  S_prob : ∀ i, IsProbabilityMeasure (S i)
  S_nonneg : ∀ i, S i (Set.Iio 0) = 0
  mu_pos : ∀ i, 0 < mu i
  mean_eq : ∀ i, ∫ x, x ∂(S i) = 1 / mu i
  stable : lam * ∑ i, p i / mu i < 1

namespace Params

variable {K : ℕ} (P : Params K)

instance instIsProbabilityMeasureS (i : Fin K) : IsProbabilityMeasure (P.S i) := P.S_prob i

/-- `ρᵢ = λ pᵢ / μᵢ`, the traffic intensity of type `i` (p. 3; Table A.1). -/
noncomputable def rho (i : Fin K) : ℝ := P.lam * P.p i / P.mu i

/-- `ρ̄ₘ = 1 − Σ_{j ≤ m} ρⱼ` in the paper's 1-based numbering (Table A.1, p. 15), `ρ̄₀ = 1`.
With 0-based types `Fin K` the first `m` types are those with index `< m`, so `rhoBar P m` is
exactly the paper's `ρ̄ₘ` (no shift in `m`). -/
noncomputable def rhoBar (m : ℕ) : ℝ := 1 - ∑ j ∈ Finset.univ.filter (fun j : Fin K => (j : ℕ) < m), P.rho j

/-- `τ(n)ᵢ = ∫ xⁿ dSᵢ`, the `n`th moment of the service time of type `i` (p. 3). Bochner
integral: it is `0` when the moment is infinite, so statements that use it assume finiteness. -/
noncomputable def tau (n : ℕ) (i : Fin K) : ℝ := ∫ x, x ^ n ∂(P.S i)

/-- `τ(n) = Σⱼ pⱼ τ(n)ⱼ`, the `n`th moment of the service time of a random customer (p. 3). -/
noncomputable def tauAll (n : ℕ) : ℝ := ∑ j, P.p j * P.tau n j

/-- `Σ_{ℓ ≤ m} pℓ τ(2)ℓ` over the first `m` types (paper's 1-based `Σ_{ℓ=1}^{m}`), as it appears
in (A.8)–(A.10), p. 19. -/
noncomputable def sumP2 (m : ℕ) : ℝ := ∑ l ∈ Finset.univ.filter (fun l : Fin K => (l : ℕ) < m), P.p l * P.tau 2 l

end Params

end NonlinearPriority


