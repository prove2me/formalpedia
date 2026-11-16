-- Prove2me | Definitions.Def_SymNormLoad_Supplement_IsRandCompetitiveRelated
-- name    : SymNormLoad_Supplement_IsRandCompetitiveRelated
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:56:12.116925+00:00
-- url     : https://prove2.me/theorems/86268ef8-c6df-421d-a605-4b2708f90613
-- title:
--   $\rho$-competitive randomized online algorithm on related machines
-- statement:
--   Fix $M$ machines with speeds $v_1,\dots,v_M$ and an objective $\Psi$ on $\mathbb R^M$. A **randomized online algorithm** is a probability space $(\Omega,\mu)$ of coins together with, for each outcome $\omega\in\Omega$, a deterministic online rule $A_\omega$ that assigns each arriving job, irrevocably, from the prefix of jobs seen so far. The coins are drawn independently of the input (an oblivious adversary).
--
--   The algorithm is **$\rho$-competitive** if for every finite sequence of jobs with positive sizes $p_1,\dots,p_N$ and every integral offline assignment $\sigma$ of the jobs to machines,
--   $$
--   \mathbb E_{\omega\sim\mu}\bigl[\Psi(L_{A_\omega})\bigr]\;\le\;\rho\cdot\Psi(L_\sigma),
--   $$
--   where $L_{A_\omega}$ is the load vector produced by $A_\omega$ on the processing times $p_j/v_i$ and $L_\sigma$ the load vector of $\sigma$. Taking the minimum over $\sigma$, this is $\mathbb E[\Psi(L_A)]\le\rho\cdot\mathrm{OPT}$ on each fixed input: expected cost is taken separately on each input sequence, with no additive constant.
--
--   **Formalization Note** The deterministic rules and load vectors are the base mission's published `OnlineAlgorithm`, `runAssign` and `loadVec`. $\Omega$ is an arbitrary measurable space (no finiteness or countability) and $\mu$ any measure; the theorems using this predicate assume $\mu$ is a probability measure and that the assignment $\omega\mapsto$ (run of $A_\omega$) is measurable on each input, which makes the integrand a bounded simple function, so the Bochner integral is the true expectation.
-- source:
--   Chen–Im–Sirri, Online Load Balancing under Symmetric Norms, manuscript (STOC 2027 submission), footnote 1, p.2 (randomized competitive ratio), Section 1.1, p.2 (related machines), proof of Lemma 4.3, p.27 (coins independent of the input)

import Mathlib
import Definitions.Def_SymNormLoad_loadVec
import Definitions.Def_SymNormLoad_OnlineAlgorithm
import Definitions.Def_SymNormLoad_Supplement_relatedTimes

open MeasureTheory

namespace SymNormLoad.Supplement

/-- **`ρ`-competitive randomized online algorithm on related machines.** Chen–Im–Sirri, *Online
Load Balancing under Symmetric Norms*, manuscript (STOC 2027 submission), footnote 1, p.2: the
competitive ratio is the worst-case ratio of an algorithm's cost to the offline optimum OPT, using
expected cost on each fixed input sequence for randomized algorithms. The related-machine model
is that of §1.1, p.2 (speeds `v`, sizes `s`, processing times `s_j / v_i`).

A randomized online algorithm is a probability space `(Ω, μ)` of coins and, for each outcome `ω`,
a deterministic online rule `A ω` (the published `SymNormLoad.OnlineAlgorithm`, which sees only
the prefix of jobs). The coins are drawn independently of the input (oblivious adversary; proof
of Lemma 4.3, p.27). `(Ψ, v, μ, A)` is `ρ`-competitive when, for every finite sequence of jobs
with positive sizes `s` and every integral offline assignment `σ`,
`E_ω[Ψ(L_{A ω})] ≤ ρ · Ψ(L_σ)`.

**Formalization Note** OPT is the minimum of `Ψ(L_σ)` over the finitely many integral
assignments `σ`, so "`E[Ψ(L_A)] ≤ ρ · OPT`" is stated for every `σ`. There is no additive
constant. Since the speeds are fixed and known, a rule reading the prefix of processing-time
vectors `relatedTimes v s` is the same as one reading the prefix of sizes. Only positive sizes
are quantified, as in the paper's model; `Ω` is an arbitrary measurable space (no finiteness or
countability). The expectation is a Bochner integral; theorems that use this predicate assume
that `ω ↦ runAssign (A ω) (relatedTimes v s)` is measurable, which makes the integrand a bounded
simple function and the integral the true expectation. -/
def IsRandCompetitiveRelated {M : ℕ} (Ψ : (Fin M → ℝ) → ℝ) (v : Fin M → ℝ)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (A : Ω → OnlineAlgorithm M) (ρ : ℝ) : Prop :=
  ∀ (N : ℕ) (s : Fin N → ℝ), (∀ j, 0 < s j) →
    ∀ σ : Fin N → Fin M,
      ∫ ω, Ψ (loadVec (relatedTimes v s) (runAssign (A ω) (relatedTimes v s))) ∂μ
        ≤ ρ * Ψ (loadVec (relatedTimes v s) σ)

end SymNormLoad.Supplement


