-- Prove2me | Definitions.Def_SKAnnealing_Sampling_glauberKernel
-- name    : SKAnnealing_Sampling_glauberKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:15:36.133867+00:00
-- url     : https://prove2.me/theorems/3c9508d5-a136-4ebc-8fe9-e526759b7fbd
-- title:
--   Glauber (heat-bath) dynamics and its Dirichlet form for a law on $\{\pm1\}^N$
-- statement:
--   Let $p$ be a law on $\{\pm1\}^N$. The **heat-bath update at site $i$**, $P_i$, moves from $x$ to a configuration $y$ that agrees with $x$ off site $i$, with probability $p(y)/\big(p(x)+p(x^{\oplus i})\big)$, where $x^{\oplus i}$ is $x$ with spin $i$ flipped. **Glauber dynamics** (Definition 2.1) picks $i\in[N]$ uniformly and applies $P_i$:
--   $$P=\frac1N\sum_{i=1}^N P_i .$$
--   Its **Dirichlet form** is
--   $$\mathcal E_p(f,f)=\frac1N\sum_{i=1}^N\mathbf E_p\big[(f-P_if)^2\big].$$
--
--   This is the Markov chain run by simulated annealing, and $\mathcal E_p$ is "the standard Dirichlet form" of the weak Poincaré inequality (2). For a Gibbs measure it coincides with the published kernel `OAI.CriticalSK.discreteKernel`, and $\mathcal E$ is the published `dirichlet` divided by $N$.
--
--   **Formalization Note** Because $P_i$ is a conditional expectation, $\mathbf E_p[(f-P_if)^2]=\mathbf E_p[f\,(f-P_if)]$, so $\mathcal E_p(f,f)=\langle f,(I-P)f\rangle_p$, the usual Dirichlet form of the discrete-time chain.
-- source:
--   Du, Huang, Mohanty, Rajaraman, Sampling from the Sherrington–Kirkpatrick Model up to Criticality, arXiv:2610.17717 (PDF of October 29, 2026), Definition 2.1, p. 11; display (2), p. 2

import Mathlib
import Definitions.Def_CriticalSK
import Definitions.Def_SKAnnealing_Sampling_lawMean

open OAI.CriticalSK

namespace SKAnnealing.Sampling

/-- Heat-bath update at site `i` for a general law `p`: from `x`, resample `x_i` from `p` conditioned on
`x_{−i}`. Same body as `OAI.CriticalSK.siteKernel` with `p` in place of `gibbs W`. -/
noncomputable def siteKernelOf {N : ℕ} (p : Spin N → ℝ) (i : Fin N) : Matrix (Spin N) (Spin N) ℝ :=
  fun x y => if sameExcept i x y then
    p y / (∑ z : Spin N, if sameExcept i x z then p z else 0)
  else 0

/-- **Glauber dynamics** (Definition 2.1) for a law `p` on `{±1}^N`: pick `i ∈ [N]` uniformly and
transition to `x' ∼ p | x_{−i}`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), Definition 2.1, p. 11.

**Formalization Note** `glauberKernel (gibbs J) = discreteKernel J` (checked in the verification file);
the general form is needed for Lemma 2.3, whose Hamiltonian `H` is arbitrary. -/
noncomputable def glauberKernel {N : ℕ} (p : Spin N → ℝ) : Matrix (Spin N) (Spin N) ℝ :=
  (N : ℝ)⁻¹ • ∑ i : Fin N, siteKernelOf p i

/-- The standard Dirichlet form of the Glauber chain of `p`,
`E(f, f) = N⁻¹ ∑_i E_p[(f − P_i f)^2]`, where `P_i` is the heat-bath update at site `i`.

Du, Huang, Mohanty, Rajaraman, *Sampling from the Sherrington–Kirkpatrick Model up to Criticality*, arXiv:2610.17717 (PDF of October 29, 2026), display (2), p. 2 ("the standard Dirichlet form").

**Formalization Note** Reading R7: the Dirichlet form of the discrete-time chain of Definition 2.1, so the
factor `N⁻¹`; for `p = gibbs J` this is `OAI.CriticalSK.dirichlet J f / N`. Since `P_i` is a conditional
expectation, `E_p[(f − P_i f)^2] = E_p[f (f − P_i f)]`, the usual `⟨f, (I − P) f⟩_p`. -/
noncomputable def glauberDirichlet {N : ℕ} (p : Spin N → ℝ) (f : Spin N → ℝ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ i : Fin N,
    lawMean p (fun x => (f x - ∑ y : Spin N, siteKernelOf p i x y * f y) ^ 2)

end SKAnnealing.Sampling


