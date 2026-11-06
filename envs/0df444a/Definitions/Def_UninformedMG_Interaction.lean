-- Prove2me | Definitions.Def_UninformedMG_Interaction
-- name    : UninformedMG_Interaction
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:38:01.026871+00:00
-- url     : https://prove2.me/theorems/ffef8b21-a4df-4be2-a4ed-cb37ba051570
-- title:
--   Online interaction with an adaptive opponent and adversarial initial states
-- statement:
--   On a probability space $(\Omega,\mathbb P)$, $K$ episodes are played. At the beginning of episode $k$ the learner and the opponent commit to Markov policies $\mu^k$ and $\nu^k$, and the episode starts from an adversarially chosen initial state $s^k_1$. At step $h$ both players observe $s^k_h$ and simultaneously draw $a^k_h\sim\mu^k_h(\cdot\mid s^k_h)$ and $b^k_h\sim\nu^k_h(\cdot\mid s^k_h)$, independently given the history and the current state; then $s^k_{h+1}\sim P_h(\cdot\mid s^k_h,a^k_h,b^k_h)$.
--
--   The history is a filtration indexed by (episode, step) in lexicographic order: $F^k$ contains the past, $s^k_1$, $\mu^k$ and $\nu^k$, and $F^k_h$ adds the observations up to $s^k_h$. Formally:
--
--   1. $s^k_h$ is $F^k_h$-measurable, and $a^k_h,b^k_h$ are $F^k_{h+1}$-measurable;
--   2. $\mu^k$, $\nu^k$ and $s^k_1$ are $F^k$-measurable Markov policies and states, otherwise arbitrary;
--   3. almost surely, for all $a,b,s'$,
--   $$\mathbb P\big(a^k_h=a,\ b^k_h=b,\ s^k_{h+1}=s'\,\big|\,F^k_h\big)=\mu^k_h(a\mid s^k_h)\,\nu^k_h(b\mid s^k_h)\,P_h(s'\mid s^k_h,a,b).$$
--
--   The opponent may adapt $\nu^k$ to the whole history, including the learner's past actions and $\mu^k$, and may know the game and the algorithm. It cannot anticipate future random draws, because the step law conditions on the full history.
--
--   **Formalization Note** Episodes and steps are 0-based. The filtration is the history of the probability space, which contains the opponent's actions, and not the learner's information. The learner's loss is $\ell^k_h=\ell_h(s^k_h,a^k_h,b^k_h)$.
-- source:
--   Liu, Luo, Ratliff, Zhang, Near-Optimal √K-Regret for Online Learning in Uninformed Markov Games, arXiv:2611.01649 (held version, sha256 1d229c89…), Section 1.1 and additional notations, pp.2–3 (PDF pp.4–5)

import Mathlib
import Definitions.Def_UninformedMG_Game

namespace UninformedMG

open MeasureTheory

variable {H : ℕ}

/-- **The online interaction against an adaptive opponent** (Section 1.1, pp.2–3 = PDF pp.4–5).
Liu, Luo, Ratliff, Zhang, arXiv:2611.01649 (held version, sha256 1d229c89…).

On a probability space `(Ω, P)`, `K` episodes are played. At the beginning of episode `k` the
learner and the opponent commit to Markov policies `μ^k` and `ν^k`, and the episode starts from an
adversarially chosen initial state `s^k_1`. At step `h` the players observe `s^k_h` and
simultaneously draw `a^k_h ∼ μ^k_h(· | s^k_h)` and `b^k_h ∼ ν^k_h(· | s^k_h)`, independently
conditional on the history and the current state; the environment moves to
`s^k_{h+1} ∼ P_h(· | s^k_h, a^k_h, b^k_h)`. The opponent may adapt `ν^k` to the whole history,
including the learner's past actions and `μ^k`, but cannot anticipate future random draws.

Fields:
1. `filt` is the history filtration, indexed lexicographically by (episode, layer): `filt (k, 0)`
   is `F^k` (the history, `s^k_1`, `μ^k`, `ν^k`, before the trajectory is sampled) and
   `filt (k, h)` is `F^k_{h+1}` (additionally the observations up to `s^k_{h+1}`);
2. `st k h` is `s^k_{h+1}`, measurable for `filt (k, h)`; `act k h`, `opp k h` are `a^k_{h+1}`,
   `b^k_{h+1}`, measurable for `filt (k, h + 1)`;
3. `lpol k`, `opol k` are `μ^k`, `ν^k`: Markov policies at every outcome, measurable for
   `filt (k, 0)` and otherwise arbitrary (the adaptive opponent; `st k 0` is the adversarial
   initial state, also otherwise arbitrary);
4. `step_law`: almost surely,
   `P(a^k_h = a, b^k_h = b, s^k_{h+1} = s' | F^k_h) = μ^k_h(a|s^k_h) ν^k_h(b|s^k_h) P_h(s'|s^k_h,a,b)`.

**Formalization Note.** Episodes and steps are 0-based (Lean episode `k` is the paper's `k + 1`).
The step law, conditional on the full history σ-algebra (which contains `μ^k`, `ν^k`, `s^k_1` and
all past actions of both players), is the paper's "independently conditional on the history and
current state" and "cannot anticipate future random draws". The filtration is the history of the
probability space (it contains the opponent's actions), not the learner's information. -/
structure Interaction (G : Game H) (K : ℕ) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The history filtration, index `(k, h)` in lexicographic order. -/
  filt : Filtration (Fin K ×ₗ Fin (H + 1)) ‹MeasurableSpace Ω›
  /-- States `s^k_{h+1}`. -/
  st : Fin K → (h : Fin (H + 1)) → Ω → G.St h
  /-- Learner actions `a^k_{h+1}`. -/
  act : Fin K → (h : Fin H) → Ω → G.Act h
  /-- Opponent actions `b^k_{h+1}` (unobserved by the learner). -/
  opp : Fin K → (h : Fin H) → Ω → G.Opp h
  /-- The learner's committed policy `μ^k`. -/
  lpol : Fin K → Ω → LPolicy G
  /-- The opponent's committed policy `ν^k`. -/
  opol : Fin K → Ω → OPolicy G
  lpol_valid : ∀ k ω, IsLPolicy G (lpol k ω)
  opol_valid : ∀ k ω, IsOPolicy G (opol k ω)
  st_meas : ∀ k h, Measurable[filt (toLex (k, h))] (st k h)
  act_meas : ∀ k (h : Fin H), Measurable[filt (toLex (k, h.succ))] (act k h)
  opp_meas : ∀ k (h : Fin H), Measurable[filt (toLex (k, h.succ))] (opp k h)
  lpol_meas : ∀ k, Measurable[filt (toLex (k, 0))] (lpol k)
  opol_meas : ∀ k, Measurable[filt (toLex (k, 0))] (opol k)
  step_law : ∀ k (h : Fin H) (a : G.Act h) (b : G.Opp h) (s' : G.St h.succ),
    P[({ω | act k h ω = a ∧ opp k h ω = b ∧ st k h.succ ω = s'}.indicator (fun _ => (1 : ℝ)))
        | filt (toLex (k, h.castSucc))] =ᵐ[P]
      fun ω => lpol k ω h (st k h.castSucc ω) a * opol k ω h (st k h.castSucc ω) b *
        G.trans h (st k h.castSucc ω) a b s'

/-- The trajectory of episode `k` at the outcome `ω`. -/
def Interaction.traj {G : Game H} {K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (I : Interaction G K Ω P) (k : Fin K) (ω : Ω) : Traj G :=
  ⟨fun h => I.st k h ω, fun h => I.act k h ω, fun h => I.opp k h ω⟩

/-- The learner's loss `ℓ^k_h = ℓ_h(s^k_h, a^k_h, b^k_h)` along a trajectory (p.2). -/
def Traj.loss {G : Game H} (τ : Traj G) (h : Fin H) : ℝ :=
  G.loss h (τ.st h.castSucc) (τ.act h) (τ.opp h)

end UninformedMG


