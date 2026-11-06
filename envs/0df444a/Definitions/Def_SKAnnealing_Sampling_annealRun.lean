-- Prove2me | Definitions.Def_SKAnnealing_Sampling_annealRun
-- name    : SKAnnealing_Sampling_annealRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:35.66431+00:00
-- url     : https://prove2.me/theorems/a3285b0f-dcb3-40e1-aefa-79592df671ff
-- title:
--   Simulated annealing: schedule $\beta_j=\min(jc/N,\beta)$ and the exact output law
-- statement:
--   **Simulated annealing** (Definition 2.2) starts from the uniform law $2^{-N}$ on $\{\pm1\}^N$ and runs $m$ steps of Glauber dynamics at each inverse temperature of a schedule $\beta_1<\beta_2<\dots<\beta_L$. Its output distribution is the exact law of the final state:
--   $$\nu_0=\mathrm{Unif}(\{\pm1\}^N),\qquad \nu_j=\nu_{j-1}\,P_{\beta_j}^{\,m}\quad(j=1,\dots,L),$$
--   where $P_{\beta}$ is the Glauber kernel of the target Gibbs measure at inverse temperature $\beta$ (a row vector times a matrix power).
--
--   Two instances are defined.
--   1. For a general Hamiltonian $H$ and a schedule $b_1,\dots,b_L$ (Lemma 2.3), $P_{b_j}$ is the Glauber kernel of $\mu_{b_jH}$.
--   2. For the SK model at inverse temperature $\beta$ with temperature gap $c/N$ (Theorem 1.1), the schedule is
--   $$\beta_j=\min\Big(\frac{jc}{N},\,\beta\Big),\qquad j=1,\dots,L=\Big\lceil\frac{\beta N}{c}\Big\rceil,$$
--   and $P_{\beta_j}$ is Glauber dynamics for $\mu_{\beta_jW}$ (`OAI.CriticalSK.discreteKernel (β_j • W)`). Every gap is at most $c/N$, the schedule increases strictly from $\beta_0=0$, and it ends at $\beta_L=\beta$ exactly. This output law is the $\widehat\mu$ of Theorem 1.1.
--
--   **Formalization Note** At $\beta=0$ there is no stage and the output is the uniform law, which equals $\mu_0$. The schedule and its properties are checked in the verification file.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Definitions 2.1–2.2, p. 11; Lemma 2.3, p. 11; Theorem 1.1, p. 1

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_glauberKernel
import Definitions.Def_SKAnnealing_Sampling_gibbsOf

open OAI.CriticalSK

namespace SKAnnealing.Sampling

/-- The uniform law on `{±1}^N`, `2^{−N}` at every configuration (the initialization of simulated annealing). -/
noncomputable def uniformLaw (N : ℕ) : Spin N → ℝ :=
  fun _ => (1 / 2 : ℝ) ^ N

/-- **Simulated annealing** (Definition 2.2): the exact law of the state after the first `j` temperature
stages, starting from the uniform law and running `m` steps of the kernel `K k` at stage `k = 1, …, j`:
`ν_0 = Unif`, `ν_{k} = ν_{k−1} (K k)^m`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Definition 2.2, p. 11; Lemma 2.3, p. 11 ("Starting from a uniformly random initialization, run m
Glauber updates at each inverse temperature β_j").

**Formalization Note** The output distribution is a row vector times kernel powers in schedule order
(`Matrix.vecMul` is the row-vector product), so it is the law of the run, not a sample. -/
noncomputable def annealRun {N : ℕ} (K : ℕ → Matrix (Spin N) (Spin N) ℝ) (m : ℕ) :
    ℕ → (Spin N → ℝ)
  | 0 => uniformLaw N
  | j + 1 => Matrix.vecMul (annealRun K m j) ((K (j + 1)) ^ m)

/-- Output law of simulated annealing for a general Hamiltonian `H` with schedule `b 1, …, b L`
(Lemma 2.3): `m` Glauber steps for `µ_{b_j H}` at each `j = 1, …, L`, from the uniform law. -/
noncomputable def annealOutputOf {N : ℕ} (H : Spin N → ℝ) (b : ℕ → ℝ) (L m : ℕ) : Spin N → ℝ :=
  annealRun (fun j => glauberKernel (gibbsOf H (b j))) m L

/-- Number of temperature stages `L = ⌈βN/c⌉` for the schedule with gap `c/N` ending at `β`. -/
noncomputable def annealLength (β c : ℝ) (N : ℕ) : ℕ :=
  ⌈β * N / c⌉₊

/-- The annealing schedule `β_j = min(jc/N, β)`: gaps at most `c/N`, and `β_L = β` for `L = annealLength β c N`. -/
noncomputable def annealTemp (β c : ℝ) (N : ℕ) (j : ℕ) : ℝ :=
  min ((j : ℝ) * c / N) β

/-- **The output distribution `µ̂` of Theorem 1.1**: simulated annealing on the SK model `µ_{βW}`, with
inverse temperature gap `c/N` and `m` Glauber steps (`OAI.CriticalSK.discreteKernel`, Definition 2.1)
at each inverse temperature `β_j = min(jc/N, β)`, `j = 1, …, ⌈βN/c⌉`, from the uniform law.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Theorem 1.1, p. 1; Definitions 2.1–2.2, p. 11.

**Formalization Note** Reading R2: the schedule `β_j = min(jc/N, β)`, `L = ⌈βN/c⌉`; every gap is `≤ c/N`, the
schedule is strictly increasing from `β_0 = 0`, and `β_L = β` exactly (verification file). At `β = 0` there
is no stage and the output is the uniform law `= µ_0`. -/
noncomputable def annealOutput {N : ℕ} (W : Disorder N) (β c : ℝ) (m : ℕ) : Spin N → ℝ :=
  annealRun (fun j => discreteKernel (annealTemp β c N j • W)) m (annealLength β c N)

end SKAnnealing.Sampling


