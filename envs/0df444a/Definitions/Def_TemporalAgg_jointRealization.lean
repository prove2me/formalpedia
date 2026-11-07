-- Prove2me | Definitions.Def_TemporalAgg_jointRealization
-- name    : TemporalAgg_jointRealization
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:37:13.01071+00:00
-- url     : https://prove2.me/theorems/2a433a7f-b620-421e-a667-be8e21f14272
-- title:
--   Joint realization $\mathcal R^t$ spliced from static realizations
-- statement:
--   Let $(\Omega,\mu)$ be a probability space. For every time $s$ let $\mathcal S^s:\Omega\to\mathcal U^n$ be a random vector (the **static realization** at time $s$: one sample of every object from its time-$s$ distribution), and let $\mathrm{last}_t(u)(\omega)$ be the time at which object $u$'s realization current at time $t$ was sampled. The **joint realization** at time $t$ is
--
--   $$
--   \mathcal R^t_u(\omega)=\mathcal S^{\,\mathrm{last}_t(u)(\omega)}_u(\omega),\qquad u=1,\dots,n .
--   $$
--
--   In the process of §1.2, each object keeps the realization of the last time it was sampled. If every sample taken at time $s$ is read as coordinate $u$ of one fresh vector $\mathcal S^s$ drawn from the product of the time-$s$ distributions, the joint realization of the paper is exactly this splice. This is how the proof of Lemma 3.2 views it ("$\mathcal R^t$ is spliced from at most $\log_2 n+1$ of them").
--
--   **Formalization Note** An object sampled several times within step $s$ (by the adversary, then again by the algorithm) keeps its last time-$s$ draw, and that draw is taken as coordinate $u$ of $\mathcal S^s$.
-- source:
--   Haeupler, Paramonov, Temporal Aggregation: Maintaining Randomness against Adaptive Adversaries, STOC 2027 submission (manuscript of 2026-11-03, sha256 42ebf866…), §1.2, p.3; proof of Lemma 3.2, p.16

import Mathlib

namespace TemporalAgg

/-- **Joint realization** `ℛᵗ` (Haeupler, Paramonov, *Temporal Aggregation: Maintaining
Randomness against Adaptive Adversaries*, STOC 2027 submission, manuscript of 2026-11-03,
sha256 42ebf866…, §1.2, p.3).

Given static realizations `S s ω : 𝒰ⁿ` for each time `s` and a state process `last ω t u` (the
time at which object `u`'s current realization at time `t` was sampled), the joint realization at
time `t` is `ℛᵗ_u = 𝒮^{last ω t u}_u`.

**Formalization Note** This is the coupling the paper's proof of Lemma 3.2 uses (p.16, "ℛᵗ is
spliced from … of them"): in the paper's process, draw at each time `s` a full vector `𝒮ˢ` from
the product of the time-`s` distributions and let every sample taken at time `s` be its
coordinate (an object sampled several times within step `s` keeps its last time-`s` draw, which
is taken as coordinate `u` of `𝒮ˢ`). Then the joint realization is this splice. -/
def jointRealization {Ω U : Type*} {n : ℕ} (S : ℕ → Ω → Fin n → U)
    (last : Ω → ℕ → Fin n → ℕ) (ω : Ω) (t : ℕ) : Fin n → U :=
  fun u => S (last ω t u) ω u

end TemporalAgg


