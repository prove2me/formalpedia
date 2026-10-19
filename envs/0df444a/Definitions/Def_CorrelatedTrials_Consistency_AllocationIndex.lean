-- Prove2me | Definitions.Def_CorrelatedTrials_Consistency_AllocationIndex
-- name    : CorrelatedTrials_Consistency_AllocationIndex
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:36.708223+00:00
-- url     : https://prove2.me/theorems/db375f60-1bb3-42a0-b4d2-e46141362f13
-- title:
--   (9)–(10), (EC.6), (EC.8) — predictive change $Z^\tau_i$, the cPDE allocation index $\nu^*_i$ and the one-step index $\nu^{cKG_1}_i$
-- statement:
--   Fix a belief $(\mu,\Sigma)$ about the arms' means, an arm $i$ with $\Sigma_{i,i}>0$, its sampling variance $\lambda_i$ and cost $c_i$. Consider sampling arm $i$ alone, repeatedly.
--
--   **Auxiliary sampling space.** Draw $\xi\sim N(0,\Sigma_{i,i})$ (the prior deviation $\theta_i-\mu_i$) independent of i.i.d. $\varepsilon_1,\varepsilon_2,\dots\sim N(0,1)$, and let the $r$-th sample be $Y^r=\mu_i+\xi+\sqrt{\lambda_i}\,\varepsilon_r$. The filtration is $\mathcal F_\tau=\sigma(Y^1,\dots,Y^\tau)$, with $\mathcal F_0$ trivial.
--
--   **Predictive change** (9)–(10). The change in arm $i$'s posterior mean after $\tau$ samples is, by (8),
--
--   $$
--   Z^\tau_i=\mu^{t+\tau}_i-\mu^t_i=\frac{\Sigma_{i,i}\sum_{r=1}^{\tau}(Y^r-\mu_i)}{\lambda_i+\tau\,\Sigma_{i,i}},
--   $$
--
--   which is $N\big(0,\lambda_i\tau/(n_i(n_i+\tau))\big)$ with $n_i=\lambda_i/\Sigma_{i,i}$.
--
--   **The cPDE allocation index** (EC.8). With $f(z)=\max_j\{\mu_j+(\Sigma_{i,j}/\Sigma_{i,i})z\}$,
--
--   $$
--   \nu^*_i(\mu,\Sigma)=\sup_{T_i\ge1}\ \mathbb E\Big[-T_i+\frac1{c_i}\,f\big(Z^{T_i}_i\big)\Big]-\frac1{c_i}\max_j\mu_j ,
--   $$
--
--   the supremum being over stopping times $T_i$ of $(\mathcal F_\tau)$ with $1\le T_i\le N$ for some integer $N$.
--
--   **The one-step index** (EC.6) with $\tau=1$:
--
--   $$
--   \nu^{cKG_1}_i(\mu,\Sigma)=-1+\frac1{c_i}\,\mathbb E\big[f(Z^1_i)\big]-\frac1{c_i}\max_j\mu_j .
--   $$
--
--   $\nu^*_i$ is the expected value, per unit of sampling cost, of sampling arm $i$ adaptively before selecting the best arm; the cPDE policy samples an arm with the largest $\nu^*_i$.
--
--   **Formalization Note**
--   1. $\nu^*_i$ is the form (EC.8) of p. ec3, which Theorem 1 and its proof use. The definition (15) on p. 11 lacks the term $-\frac1{c_i}\max_j\mu_j$; with (15) Theorem 1 ii) would be false and, for unequal costs, the policy would differ.
--   2. The paper's supremum is over all stopping times $T_i\ge1$; the formal one is over bounded stopping times, which has the same value and makes every expectation finite. A real supremum (`sSup`) is used; the set contains $T_i\equiv1$ and is bounded above.
--   3. The variance of $\xi$ is written $\max(\Sigma_{i,i},0)$ so that the definition is total; values with $\Sigma_{i,i}\le0$ are never used.
--   4. Samples are indexed from $0$ in Lean (`auxSample l r` is $Y^{r+1}-\mu_i$).
-- source:
--   Chick, Gans, Yapar, Bayesian Sequential Learning for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of August 31, 2020), pp. 9–10, (8)–(10); p. ec3, (EC.6), (EC.8)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace CorrelatedTrials.Consistency

/-! The auxiliary sampling problem of §3.1–3.2 (Chick, Gans, Yapar, Bayesian Sequential Learning
for Clinical Trials of Multiple Correlated Medical Interventions, SSRN 3184758 (version of
August 31, 2020), pp. 9–12, (8)–(10), and p. ec3, (EC.6), (EC.8)): from a belief `(µ, Σ)`, keep
sampling arm `i` alone. -/

/-- The sample space of the auxiliary problem: a prior draw `ξ` of `θ_i − µ_i` and an i.i.d.
noise sequence `(ε_r)_{r ∈ ℕ}`. -/
abbrev AuxSpace := ℝ × (ℕ → ℝ)

/-- The law of the auxiliary problem for a current posterior variance `s = Σ_{i,i}`:
`ξ ∼ N(0, Σ_{i,i})` independent of i.i.d. `ε_r ∼ N(0, 1)`.

Formalization Note: the variance is `Real.toNNReal s`, so the definition is total; it is only
used with `s > 0`. -/
noncomputable def auxMeasure (s : ℝ) : Measure AuxSpace :=
  (gaussianReal 0 (Real.toNNReal s)).prod (Measure.infinitePi fun _ : ℕ => gaussianReal 0 1)

/-- The `(r+1)`-th sample of arm `i`, centred at the current mean `µ_i`:
`Y^{r+1} − µ_i = ξ + √λ_i ε_r`, so that `Y^{r+1} | θ_i ∼ N(θ_i, λ_i)` with
`θ_i − µ_i ∼ N(0, Σ_{i,i})` (§1.2, p. 6). Here `l = λ_i`. -/
noncomputable def auxSample (l : ℝ) (r : ℕ) (ω : AuxSpace) : ℝ :=
  ω.1 + Real.sqrt l * ω.2 r

/-- The centred partial sum `∑_{r=1}^{τ} (Y^r − µ_i)` of the first `τ` samples (`0` at `τ = 0`). -/
noncomputable def auxSum (l : ℝ) (τ : ℕ) (ω : AuxSpace) : ℝ :=
  ∑ r ∈ Finset.range τ, auxSample l r ω

lemma auxSum_stronglyMeasurable (l : ℝ) (τ : ℕ) : StronglyMeasurable (auxSum l τ) := by
  apply Measurable.stronglyMeasurable
  unfold auxSum auxSample
  fun_prop

/-- The filtration of the auxiliary problem: `F_τ = σ(Y^1, …, Y^τ)`, the natural filtration of
the partial sums (equivalently of the samples); `F_0` is trivial. -/
noncomputable def auxFiltration (l : ℝ) : Filtration ℕ (inferInstance : MeasurableSpace AuxSpace) :=
  Filtration.natural (fun τ => auxSum l τ) (fun τ => auxSum_stronglyMeasurable l τ)

/-- The predictive change of arm `i`'s mean after `τ` samples, `Z^τ_i ≡ µ^{t+τ}_i − µ^t_i`
((9), p. 10). By (8) with `Ȳ^τ = (∑_{r ≤ τ} Y^r)/τ`,
`Z^τ_i = Σ_{i,i} ∑_{r=1}^{τ} (Y^r − µ_i) / (λ_i + τ Σ_{i,i})`, whose law is
`N(0, λ_i τ / (n_i (n_i + τ)))` with `n_i = λ_i / Σ_{i,i}` ((10)). Here `l = λ_i`, `s = Σ_{i,i}`. -/
noncomputable def Zproc (l s : ℝ) (τ : ℕ) (ω : AuxSpace) : ℝ :=
  s * auxSum l τ ω / (l + τ * s)

/-- The terminal reward `max_j {µ_j + (Σ_{i,j}/Σ_{i,i}) z}` of (EC.6) and (EC.8). -/
noncomputable def terminal {M : ℕ} (mu : Fin M → ℝ) (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M)
    (z : ℝ) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ fun j => mu j + Sig i j / Sig i i * z

/-- `max_j µ_j`. -/
noncomputable def maxMean {M : ℕ} (mu : Fin M → ℝ) (i : Fin M) : ℝ :=
  Finset.univ.sup' ⟨i, Finset.mem_univ i⟩ mu

/-- The admissible lookaheads of (EC.8): stopping times `T` of the auxiliary filtration with
`1 ≤ T ≤ N` for some `N : ℕ`. -/
def AdmissibleLookahead (l : ℝ) (T : AuxSpace → WithTop ℕ) : Prop :=
  IsStoppingTime (auxFiltration l) T ∧ ∃ N : ℕ, ∀ ω, 1 ≤ T ω ∧ T ω ≤ (N : WithTop ℕ)

/-- The value `E[−T_i + (1/c_i) max_j {µ_j + (Σ_{i,j}/Σ_{i,i}) Z^{T_i}_i}] − (1/c_i) max_j µ_j`
of a lookahead `T` in (EC.8). -/
noncomputable def lookaheadValue {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) (T : AuxSpace → WithTop ℕ) : ℝ :=
  (∫ ω, (-(((T ω).untopA : ℕ) : ℝ)
      + (1 / c i) * terminal mu Sig i (stoppedValue (Zproc (lam i) (Sig i i)) T ω))
      ∂(auxMeasure (Sig i i)))
    - (1 / c i) * maxMean mu i

/-- The cPDE allocation index (EC.8) (p. ec3):
`ν*_i(µ, Σ) = sup_{T_i ≥ 1} E[−T_i + (1/c_i) max_j {µ_j + (Σ_{i,j}/Σ_{i,i}) Z^{T_i}_i} | µ, Σ]
 − (1/c_i) max_j {µ_j}`.

Formalization Note:
1. This is (EC.8), the form Theorem 1 and its proof use. The printed definition (15) (p. 11)
   lacks the term `−(1/c_i) max_j µ_j`; with (15) Theorem 1 ii) would be false.
2. The supremum ranges over stopping times of the auxiliary sampling filtration with
   `1 ≤ T_i ≤ N` for some `N`. The paper's supremum over all stopping times `T_i ≥ 1` has the
   same value (unbounded stopping times are approximated by truncations), and bounded `T_i`
   make every expectation finite.
3. It is a real `sSup` of a nonempty set (it contains `T_i ≡ 1`) that is bounded above.
4. Values at a `Σ` with `Σ_{i,i} ≤ 0` are not meaningful; every use has `Σ` positive definite. -/
noncomputable def nuStar {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) : ℝ :=
  sSup {v | ∃ T, AdmissibleLookahead (lam i) T ∧ v = lookaheadValue lam c mu Sig i T}

/-- The one-step cKG index `ν^{cKG1}_i`, (EC.6) (p. ec3) with `τ = 1`:
`ν^{cKG1}_i(µ, Σ) = −1 + (1/c_i) E[max_j {µ_j + (Σ_{i,j}/Σ_{i,i}) Z^1_i} | µ, Σ]
 − (1/c_i) max_j {µ_j}`. -/
noncomputable def nuCKG1 {M : ℕ} (lam c : Fin M → ℝ) (mu : Fin M → ℝ)
    (Sig : Matrix (Fin M) (Fin M) ℝ) (i : Fin M) : ℝ :=
  -1 + (1 / c i) * (∫ ω, terminal mu Sig i (Zproc (lam i) (Sig i i) 1 ω) ∂(auxMeasure (Sig i i)))
    - (1 / c i) * maxMean mu i

end CorrelatedTrials.Consistency


