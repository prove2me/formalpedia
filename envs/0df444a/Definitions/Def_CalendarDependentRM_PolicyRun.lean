-- Prove2me | Definitions.Def_CalendarDependentRM_PolicyRun
-- name    : CalendarDependentRM_PolicyRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:08.701323+00:00
-- url     : https://prove2.me/theorems/88c5b24e-4bb5-408a-bc06-2f7fcab7e816
-- title:
--   A realization of the approximate policy and its §5 random variables
-- statement:
--   Given a tuning parameter $\gamma\in[0,1]$ and a solution $x$ of the fluid approximation, the **approximate policy** works as follows. If there is a request for product $j$ at period $t$ of stage $k$ and the demand in stage $k-1$ was $q$, then it is willing to accept with probability $\gamma x^k_{jt}(q)/\lambda^k_{jt}$; it accepts if it is willing and there is enough capacity, and otherwise rejects.
--
--   A realization on a probability space consists of the demands $D^k$ with the law of the Markov process, the requested product at each period, and the willingness indicators $X^k_{jt}(q)$. The demand path, the request and the willingness indicators are independent in the sense stated in the fields. On this data we define:
--
--   1. the remaining capacity, which moves only at reached periods $t\le D^k$;
--   2. $G^k_{jt}$, the event that capacity remains for product $j$;
--   3. the revenue and its expectation $\mathrm{APX}$;
--   4. $\Psi^k_t(q)=\mathbf 1(D^k\ge t,D^{k-1}=q)$ and $N^k_{it}(q)=\sum_ja_{ij}A^k_{jt}X^k_{jt}(q)$;
--   5. $U^m_i=\sum_{\ell\le m}\sum_s\sum_p\Psi^\ell_s(p)N^\ell_{is}(p)$ and $V^m_i=\sum_{\ell\le m}\sum_s\sum_p\Psi^\ell_s(p)n^\ell_{is}(p)$;
--   6. the Doob martingale $M^m_i(\ell)=E\{V^m_i\mid D^\ell,\dots,D^m\}$.
--
--   These are the objects of the performance analysis.
--
--   **Formalization Note** The capacity path uses the global period index $n=kT+t$. $M^m_i(\ell)$ keeps the paper's numbering of $m,\ell$; at $\ell=0$ the deterministic $D^0$ adds no information, which covers the range $\ell=0,\dots,k-1$ of Lemma 5.2 and gives $M^0_i(0)=0$. At $\lambda^k_{jt}=0$ the ratio reads $0$ and the product is never requested.
-- source:
--   Li, Rusmevichientong & Topaloglu, Revenue Management with Calendar-Aware and Dependent Demands, arXiv:2409.02637v2, §4, p.11; §5, pp.14–17; Table 1, ER p.17 (PDF 39)

import Mathlib
import Definitions.Def_CalendarDependentRM_Instance

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace CalendarDependentRM

/-- **A realization of the approximate policy** on a probability space `(Ω, P)`, for a tuning
parameter `γ ∈ [0, 1]` and a fluid solution `x`. Li, Rusmevichientong & Topaloglu,
*Revenue Management with Calendar-Aware and Dependent Demands*, arXiv:2409.02637v2, §4, p. 11
("Approximate Policy from the Fluid Approximation"), §5, pp. 14–15, and Table 1, Extended Results p. 17.

* `D k ω`: the demand in stage `k`;
* `req k t ω`: the product requested at period `t` of stage `k` (`A^k_jt = 1` means `req k t ω = j`);
* `will k t j q ω`: `X^k_jt(q) = 1`, the policy is willing to accept a request for `j` at that period
  when the demand of the previous stage was `q`;
* `law_D`, `law_req`, `law_will`: the demand path follows the Markov process,
  `P{A^k_jt = 1} = λ^k_jt`, `P{X^k_jt(q) = 1} = γ x^k_jt(q) / λ^k_jt`;
* `indep_slices`: the slices `(req k t, will k t · ·)` are independent over `(k, t)`;
* `indep_req_will`: within a slice, the request is independent of the willingness indicators;
* `indep_D`: the demand path is independent of all the slices.

**Formalization Note** The paper calls `A`, `X` "simple Bernoulli draws independent of the decisions of
the approximate policy, remaining capacities … or realizations of the demands". The three fields ask for
no more than that, and less in one respect: the `X^k_jt(q)` for different `(j, q)` in one slice may be
correlated, and every fully independent family is a run. `J` carries a measurable structure with
measurable singletons, which for finite `J` is the discrete one. At `λ^k_jt = 0`, Lean's `0 / 0 = 0` gives
`P{X^k_jt(q) = 1} = 0` when `x` is feasible, and such a product is never requested at that period. -/
structure PolicyRun {R J : Type*} [Fintype J] [MeasurableSpace J] {K T : ℕ}
    (I : Instance R J K T) (γ : ℝ) (x : Fin K → J → Fin T → Fin T → ℝ) {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- The tuning parameter lies in `[0, 1]`. -/
  gamma_mem : γ ∈ Set.Icc (0 : ℝ) 1
  /-- The demand in stage `k`. -/
  D : Fin K → Ω → Fin T
  /-- The product requested at period `t` of stage `k`. -/
  req : Fin K → Fin T → Ω → J
  /-- `X^k_jt(q) = 1`. -/
  will : Fin K → Fin T → J → Fin T → Ω → Bool
  measurable_D : ∀ k, Measurable (D k)
  measurable_req : ∀ k t, Measurable (req k t)
  measurable_will : ∀ k t j q, Measurable (will k t j q)
  law_D : ∀ d : Fin K → Fin T, P.real {ω | ∀ k, D k ω = d k} = I.chain.pathProb d
  law_req : ∀ k t j, P.real {ω | req k t ω = j} = I.lam k t j
  law_will : ∀ k t j q, P.real {ω | will k t j q ω = true} = γ * (x k j t q / I.lam k t j)
  indep_slices : iIndepFun
    (fun (s : Fin K × Fin T) ω => (req s.1 s.2 ω, fun j q => will s.1 s.2 j q ω)) P
  indep_req_will : ∀ k t, IndepFun (req k t) (fun ω j q => will k t j q ω) P
  indep_D : IndepFun (fun ω k => D k ω)
    (fun ω (s : Fin K × Fin T) => (req s.1 s.2 ω, fun j q => will s.1 s.2 j q ω)) P

namespace Instance

variable {R J : Type*} [Fintype J] {K T : ℕ} (I : Instance R J K T)

/-- There is enough capacity for product `j` at the capacity vector `y`: `y_i ≥ a_ij` for every `i`.
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Table 1 line 7, Extended Results p. 17. -/
def Servable (y : R → ℕ) (j : J) : Prop :=
  ∀ i ∈ I.A j, 1 ≤ y i

/-- The capacity vector `y − a_j` after accepting product `j`, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, Table 1 line 9, Extended Results p. 17.

**Formalization Note** Natural subtraction, only ever applied behind `Servable`. -/
noncomputable def consume (y : R → ℕ) (j : J) : R → ℕ :=
  fun i => if i ∈ I.A j then y i - 1 else y i

end Instance

namespace PolicyRun

variable {R J : Type*} [Fintype J] [MeasurableSpace J] {K T : ℕ} {I : Instance R J K T}
  {γ : ℝ} {x : Fin K → J → Fin T → Fin T → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] (run : PolicyRun I γ x P)

/-- The demand `D^{k-1}` of the stage before `k` on the sample point `ω`, with `D⁰ = D̂⁰`. -/
def Dprev (k : Fin K) (ω : Ω) : Fin T :=
  I.chain.prev (fun m => run.D m ω) k

/-- **Remaining capacity** under the approximate policy on the global period index `n = k T + t`,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, Table 1, Extended Results p. 17: `rem ω 0 = c`; at
`n = k T + t`, the requested product `j` consumes capacity if the period is reached (`D^k ≥ t`), the
policy is willing, and `j` is servable; otherwise the capacity stays.

**Formalization Note** The capacity moves only at reached periods, since Table 1 ends stage `k` at
period `D^k` and passes the capacity on to stage `k + 1`. -/
noncomputable def rem (ω : Ω) : ℕ → R → ℕ
  | 0 => I.c
  | n + 1 =>
    if h : n < T * K then
      have hT : 0 < T := Nat.pos_of_ne_zero (by rintro rfl; simp at h)
      have hk : n / T < K := Nat.div_lt_of_lt_mul h
      have ht : n % T < T := Nat.mod_lt n hT
      if (⟨n % T, ht⟩ : Fin T) ≤ run.D ⟨n / T, hk⟩ ω ∧
          run.will ⟨n / T, hk⟩ ⟨n % T, ht⟩ (run.req ⟨n / T, hk⟩ ⟨n % T, ht⟩ ω)
            (run.Dprev ⟨n / T, hk⟩ ω) ω = true ∧
          I.Servable (rem ω n) (run.req ⟨n / T, hk⟩ ⟨n % T, ht⟩ ω) then
        I.consume (rem ω n) (run.req ⟨n / T, hk⟩ ⟨n % T, ht⟩ ω)
      else rem ω n
    else rem ω n

/-- **`G^k_jt = 1`**: there is enough capacity for product `j` at period `t` of stage `k`,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §5, p. 14. -/
def G (k : Fin K) (t : Fin T) (j : J) (ω : Ω) : Prop :=
  I.Servable (run.rem ω ((k : ℕ) * T + (t : ℕ))) j

/-- **The total revenue of the approximate policy** on the sample point `ω`,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §5, p. 15: the sum over `k`, `t`, `j` of `f_j` times
the sales `Σ_q Ψ^k_t(q) G^k_jt A^k_jt X^k_jt(q)`. -/
noncomputable def revenue (ω : Ω) : ℝ :=
  ∑ k, ∑ t, ∑ j,
    if t ≤ run.D k ω ∧ run.req k t ω = j ∧ run.will k t j (run.Dprev k ω) ω = true ∧
        run.G k t j ω then I.f j else 0

/-- **`APX`, the total expected revenue of the approximate policy**,
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, p. 12.

**Formalization Note** `revenue` takes finitely many values and is measurable, so the Bochner integral
is the true expectation (proved in `Solutions/verification/CalendarDependentRM_sanity.lean`). -/
noncomputable def APX : ℝ :=
  ∫ ω, run.revenue ω ∂P

/-- The event `{Ψ^k_t(q) = 1} = {D^k ≥ t, D^{k-1} = q}`, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, §5, p. 14. -/
def Psi (k : Fin K) (t q : Fin T) : Set Ω :=
  {ω | t ≤ run.D k ω ∧ run.Dprev k ω = q}

/-- **`N^k_it(q) = Σ_j a_ij A^k_jt X^k_jt(q)`**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2,
§5, p. 15: the requested product uses resource `i` and the policy would accept it given previous demand `q`.

**Formalization Note** One product is requested per period, so the sum has at most one nonzero term and
this is its value as an indicator, on the run's sample space. -/
noncomputable def N (i : R) (k : Fin K) (t q : Fin T) (ω : Ω) : ℝ :=
  if i ∈ I.A (run.req k t ω) ∧ run.will k t (run.req k t ω) q ω = true then 1 else 0

/-- **`U^m_i = Σ_{ℓ=1}^m Σ_s Σ_p Ψ^ℓ_s(p) N^ℓ_is(p)`**, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, §5, p. 16.

**Formalization Note** `m` is the paper's superscript: the sum runs over the first `m` stages, that is, the
0-based stages `ℓ < m`. So `U⁰_i = 0`, as the paper sets it on p. 18. -/
noncomputable def U (i : R) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin K => (ℓ : ℕ) < m), ∑ s, ∑ p,
    if ω ∈ run.Psi ℓ s p then run.N i ℓ s p ω else 0

/-- **`V^m_i = Σ_{ℓ=1}^m Σ_s Σ_p Ψ^ℓ_s(p) n^ℓ_is(p)`**, Li, Rusmevichientong & Topaloglu,
arXiv:2409.02637v2, §5, p. 16, with the same index convention as `U`. -/
noncomputable def V (i : R) (m : ℕ) (ω : Ω) : ℝ :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin K => (ℓ : ℕ) < m), ∑ s, ∑ p,
    if ω ∈ run.Psi ℓ s p then I.meanN γ x i ℓ s p else 0

/-- **`M^m_i(ℓ) = E{V^m_i | D^{[ℓ,m]}}`**, Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, §5, p. 17:
the expectation of `V^m_i` given the demands of the paper's stages `ℓ, …, m`.

**Formalization Note** `m` and `ℓ` are the paper's numbers, and stage `r : Fin K` is the paper's stage `r + 1`.
The paper defines `M^m_i(ℓ)` for `ℓ = 1, …, m` and sets `M⁰_i(0) = 0`, while Lemma 5.2 ranges over
`ℓ = 0, …, k − 1`. This definition covers all of these uniformly: at `ℓ = 0` the deterministic `D⁰` adds no
information, so `M^m_i(0) = M^m_i(1)`, and over the empty range it is the mean of an empty sum, `M⁰_i(0) = 0`.
On a null conditioning event `P[|E]` is the zero measure; each `ω` lies in its own event, and the events with
positive mass carry probability one. -/
noncomputable def M (i : R) (m ℓ : ℕ) (ω : Ω) : ℝ :=
  ∫ ω', run.V i m ω' ∂(ProbabilityTheory.cond P
    {ω' | ∀ r : Fin K, ℓ ≤ (r : ℕ) + 1 → (r : ℕ) + 1 ≤ m → run.D r ω' = run.D r ω})

/-- The event `{U^{k-1}_i + Σ_{s=1}^t N^k_is(q) ≥ c_i}`, the event of the last line of display (4) of
Li, Rusmevichientong & Topaloglu, arXiv:2409.02637v2, p. 16, at the 0-based stage `k`.

**Formalization Note** `U i k` with `k` the 0-based stage is the paper's `U^{k-1}_i` at the paper's stage
`k + 1`. -/
def overBudget (i : R) (k : Fin K) (t q : Fin T) : Set Ω :=
  {ω | (I.c i : ℝ) ≤ run.U i (k : ℕ) ω + ∑ s ∈ Finset.Iic t, run.N i k s q ω}

end PolicyRun

end CalendarDependentRM


