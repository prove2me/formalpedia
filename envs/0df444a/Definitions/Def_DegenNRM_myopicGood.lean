-- Prove2me | Definitions.Def_DegenNRM_myopicGood
-- name    : DegenNRM_myopicGood
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:36:34.056966+00:00
-- url     : https://prove2.me/theorems/4b8a20e3-81be-4666-a48b-00ca59f2ce20
-- title:
--   The good event $\mathcal G$, $q^\pi_{j,t}$ and $\mathrm{Myopic}_t(\pi,c,\mathcal G)$ of (19)
-- statement:
--   Fix remaining capacities $c$, $s$ periods left and the type $j$ of the arriving query. Let $\tilde d_{t+1}=D\in\mathbb N^n$ be the type counts of the $s-1$ later arrivals. Then:
--
--   1. the **good event** is $\mathcal G=\{|\tilde d_{k,t+1}-p_k(s-1)|\le\sqrt{(s-1)\log(s-1)}\ \forall k\in[n]\}$;
--   2. $q^\pi_{j,t}$, the probability that the policy serves the query, is $F_j([\hat M,\infty))$ if $c\ge a_j$ and $0$ otherwise, with $\hat M$ of Algorithm 2;
--   3. with $\tilde q^*_t$ an optimal solution of (12) at $(c,\tilde d_t)$, $\tilde d_t=D+e_j$, the integrand of (19) is
--   $$\sum_{k=1}^n\tilde d_{k,t+1}G_k(\tilde q^*_{k,t})+\int_{1-\tilde q^*_{j,t}}^{1-q^\pi_{j,t}}F_j^{-1}(q)\,dq-q^\pi_{j,t}\,\bar V^{\mathrm{Semi}}_{c-a_j}(\tilde d_{t+1})-(1-q^\pi_{j,t})\,\bar V^{\mathrm{Semi}}_c(\tilde d_{t+1});$$
--   4. $\mathrm{Myopic}_t(\pi,c,\mathcal G)=P(\mathcal G)\cdot\mathbb E[\text{integrand}\mid\mathcal G]$, the expectation over the later arrivals.
--
--   These are the objects of Lemmas 5–7, which bound the myopic regret on the good event in the three cases of Algorithm 2.
--
--   **Formalization Note** The paper's (19) also averages over the type $j_t$, while the three cases of Lemmas 5–7 are conditions on $\hat q^*_{j_t,t}$; the objects are therefore defined for a fixed type $j_t=j$. The conditional expectation on an event $A$ is $\big(\int_A f\big)/P(A)$, which is $0$ when $P(A)=0$.
-- source:
--   Jiang, Ma & Zhang, Degeneracy is OK: Logarithmic Regret for Network Revenue Management with Indiscrete Distributions, arXiv:2210.07996v5, §3.3, pp.15–16, (16)–(19)

import Mathlib
import Definitions.Def_DegenNRM_arrivalLaw
import Definitions.Def_DegenNRM_semiValue
import Definitions.Def_DegenNRM_algorithm2
import Definitions.Def_DegenNRM_kappa1

open MeasureTheory

namespace DegenNRM

/-- **The good event `G`** (Jiang, Ma & Zhang, arXiv:2210.07996v5, §3.3, p.16): with `s` periods
left (so `s - 1` arrivals after the current one, with type counts `d̃_{t+1} = D`),
`G = {|d̃_{j,t+1} - p_j (s - 1)| ≤ √((s - 1) log (s - 1)) for all j ∈ [n]}`, as a set of count
vectors `D`. -/
def goodEvent {m n : ℕ} (inst : Instance m n) (s : ℕ) : Set (Fin n → ℕ) :=
  {D | ∀ j, |(D j : ℝ) - inst.p j * ((s : ℝ) - 1)| ≤ Real.sqrt (((s : ℝ) - 1) * Real.log ((s : ℝ) - 1))}

/-- **The conditional expectation on an event**, `E[f | A] = E[f · 1_A] / P(A)`
(arXiv:2210.07996v5, (19)–(23), pp.16–18).

**Formalization Note.** When `P(A) = 0` this is `0` (Lean's `x / 0 = 0`); it only appears
multiplied by `P(A)` or in bounds where the left side is then `0` as well. -/
noncomputable def condMean {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Set Ω)
    (f : Ω → ℝ) : ℝ :=
  (∫ ω in A, f ω ∂μ) / μ.real A

/-- **The ex-ante acceptance probability `q^π_{j,t}`** of Algorithm 1 with the estimator of
Algorithm 2 for a type-`j` query, at remaining capacity `c` with `s` periods left
(arXiv:2210.07996v5, p.16: "q^π_{j,t} denotes the ex-ante probability that query t will be
served by the online policy π"). The query is served iff its reward is at least `M̂` of
Algorithm 2 and `c ≥ a_j`, so `q^π_{j,t} = F_j([M̂, ∞))` if `c ≥ a_j` and `0` otherwise; `qh` is
the type-`j` entry `q̂*_{j,t}` of the algorithm's optimal solution of (13). -/
noncomputable def acceptProb {m n : ℕ} (inst : Instance m n) (s : ℕ) (c : Fin m → ℝ)
    (j : Fin n) (qh : ℝ) : ℝ :=
  open Classical in
  if ∀ i, inst.a j i ≤ c i then
    (inst.F j).real {r | estimator inst (kappa1 inst) (s : ℝ) j qh ≤ r}
  else 0

/-- **The integrand of (19)** (arXiv:2210.07996v5, §3.3, p.16), for an arriving type `j`,
remaining capacity `c`, acceptance probability `qπ = q^π_{j,t}`, future type counts
`D = d̃_{t+1}` and the semi-fluid solution `qt = q̃*_t` of (12) at `(c, d̃_t)`:

`Σ_k d̃_{k,t+1} ∫_{1-q̃*_{k,t}}^1 F_k⁻¹ + ∫_{1-q̃*_{j,t}}^{1-q^π_{j,t}} F_j⁻¹
  - q^π_{j,t} · V̄^Semi_{c-a_j}(d̃_{t+1}) - (1 - q^π_{j,t}) · V̄^Semi_c(d̃_{t+1})`,

with `V̄^Semi` the value of (9). -/
noncomputable def myopicIntegrand {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (j : Fin n)
    (qπ : ℝ) (D : Fin n → ℕ) (qt : Fin n → ℝ) : ℝ :=
  (∑ k, (D k : ℝ) * Gfun inst k (qt k)) + (∫ q in (1 - qt j)..(1 - qπ), quantile inst j q)
    - qπ * semiValue inst (c - inst.a j) (fun k => (D k : ℝ))
    - (1 - qπ) * semiValue inst c (fun k => (D k : ℝ))

/-- **`Myopic_t(π, c, G)` of (19), for an arriving query of type `j`** (arXiv:2210.07996v5,
§3.3, (19), p.16):

`Myopic_t(π, c, G) = P(G) · E_{I_{t+1}}[ (integrand of (19)) | G ]`,

where the expectation is over the `s - 1` arrivals after period `t` (whose type counts are
`d̃_{t+1}`), `q^π_{j,t}` is `acceptProb` computed from `qh = q̂*_t`, and `qt D` is the semi-fluid
solution `q̃*_t` used when the future counts are `D`.

**Formalization Note.** The paper's `Myopic_t(π, c, G)` also averages over the type `j_t` of
the current query, while its three cases (Lemmas 5–7) are conditions on `q̂*_{j_t,t}`; the
lemmas are therefore stated for a fixed type `j_t = j` (reading R9 of the mission), and
Theorem 1's proof averages them over `j_t`. The future arrivals are a sample path of `s - 1`
periods under `pathLaw`. -/
noncomputable def myopicGood {m n : ℕ} (inst : Instance m n) (c : Fin m → ℝ) (s : ℕ) (j : Fin n)
    (qh : Fin n → ℝ) (qt : (Fin n → ℕ) → (Fin n → ℝ)) : ℝ :=
  (pathLaw inst (s - 1)).real {ω | typeCount ω ∈ goodEvent inst s} *
    condMean (pathLaw inst (s - 1)) {ω | typeCount ω ∈ goodEvent inst s}
      (fun ω => myopicIntegrand inst c j (acceptProb inst s c j (qh j)) (typeCount ω)
        (qt (typeCount ω)))

end DegenNRM


