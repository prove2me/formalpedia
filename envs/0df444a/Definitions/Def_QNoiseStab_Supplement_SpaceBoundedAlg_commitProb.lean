-- Prove2me | Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_commitProb
-- name    : QNoiseStab_Supplement_SpaceBoundedAlg_commitProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:19:09.886474+00:00
-- url     : https://prove2.me/theorems/64013a8b-3f30-466a-b118-6ec03c30b04a
-- title:
--   Probability of a commit sequence on a given input
-- statement:
--   Fix an algorithm with instruments $\mathcal I_0,\dots,\mathcal I_T$, an encoded input $y\in\mathbb Z_d^{\,n}$ and a root $\omega$, and let $O=O_y\otimes I_W$ be the phase oracle. For a sequence $o=(o_0,\dots,o_T)$ of step outcomes (each "no output" or a commit), define the unnormalized states
--
--   $$
--   \rho_0=\mathcal I_0(o_0)(\rho_{\mathrm{start}}),\qquad \rho_{t+1}=\mathcal I_{t+1}(o_{t+1})\bigl(O\rho_tO^\dagger\bigr),
--   $$
--
--   where $\mathcal I_t(o)(\rho)=\sum_r K_{t,o,r}\,\rho\,K_{t,o,r}^\dagger$. The **probability of the commit sequence** $o$ on input $y$ is $\operatorname{tr}\rho_T$.
--
--   This is the joint distribution of all intermediate measurement outcomes of the run; success probabilities of space-bounded algorithms are sums of these numbers.
--
--   **Formalization Note** The real part of the trace is taken, which is the trace itself since $\rho_T$ is positive semidefinite.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1, p.6 (input oracle O and the run U_T O ⋯ O U_0); §2.2, p.7 (intermediate measurements)

import Mathlib
import Definitions.Def_QNoiseStab_phaseQuery
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg

set_option autoImplicit false

open Matrix

namespace QNoiseStab.Supplement

/-- The **probability of a commit sequence** `o = (o_0, …, o_T)` when the algorithm runs on the
(encoded) input `y : Fin n → ZMod d` with phase oracle `O_y = phaseQuery ω y ⊗ 1_W`
(Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.1, p.6, the oracle `O|i,p,w⟩|x⟩ = ω_d^{p x_i}|i,p,w⟩|x⟩` and the run
`U_t O U_{t−1} ⋯ O U_0`; §2.2, p.7, intermediate measurements). With the unnormalized states
`ρ_0 = 𝓘_0(o_0)(start)` and `ρ_{t+1} = 𝓘_{t+1}(o_{t+1})(O_y ρ_t O_y†)`, where
`𝓘_t(o)(ρ) = Σ_r K_{t,o,r} ρ K_{t,o,r}†`, the probability is `Re tr ρ_T`.

**Formalization Note** The real part is taken only to land in `ℝ`: the trace of a positive
semidefinite matrix is real. Since every instrument is trace preserving, these numbers sum to one
over all commit sequences when `O_y` is unitary. -/
noncomputable def SpaceBoundedAlg.commitProb {n d : ℕ} [NeZero d] {W K V ι : Type} [Fintype W]
    [DecidableEq W] [Fintype K] [Fintype V] [Fintype ι] {T : ℕ}
    (A : SpaceBoundedAlg n d W K V ι T) (ω : ℂ) (y : Fin n → ZMod d)
    (o : Fin (T + 1) → Option (K × V)) : ℝ :=
  let O : Matrix ((Fin n × ZMod d) × W) ((Fin n × ZMod d) × W) ℂ :=
    Matrix.kronecker (phaseQuery ω y) (1 : Matrix W W ℂ)
  (Matrix.trace
    (Fin.induction (motive := fun _ => Matrix ((Fin n × ZMod d) × W) ((Fin n × ZMod d) × W) ℂ)
      ((A.step 0).apply (o 0) A.start)
      (fun t ρ => (A.step t.succ).apply (o t.succ) (O * ρ * Oᴴ)) (Fin.last T))).re

end QNoiseStab.Supplement


