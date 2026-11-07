-- Prove2me | Definitions.Def_BeyondDS_TrialStep
-- name    : BeyondDS_TrialStep
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:56.107882+00:00
-- url     : https://prove2.me/theorems/aa60b2ff-2f5e-436f-9f24-56e4cf128709
-- title:
--   Adaptive trial processes, distinct destinations, $\delta_{ep}$ and $\delta_{fin}$
-- statement:
--   **Trial process.** A process on states $\sigma$ has, at each state, one of three steps: stop (the finite phase ended); noise (any next-state law that is not a counted draw); or a completed random transmission trial, whose selection bit is fixed first and whose destination $d$ is then drawn uniformly from $[n]$, the next state having law $D(d)$. "A trial is selected predictably if the decision whether to count it is determined before its fresh destination is sampled." The module defines the law of the list of selected destinations in a phase of bounded length.
--
--   **Distinct destinations.** For a row $f:[K]\to[n]$ of destinations and $U\subseteq[n]$, $D_U(f)=|f([K])\cap U|$.
--
--   **Error terms** (14), (15):
--
--   $$\delta_{ep}=e^{-2n}+n^2e^{-K^2/(16n)},\qquad \delta_{fin}=e^{-K/128}+n\,e^{-K^2/(16n)}.$$
--
--   **Formalization Note** All kernels are free, so any adaptive adversary, schedule and corruption rule embeds, with the whole execution in the state.
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §7.2, p.23 (PDF p.24); eqs. (14), (15), p.24 (PDF p.25)

import Mathlib

set_option autoImplicit false

namespace BeyondDS

/-- The next step of an adaptive process of random trials (§7.2, p.23), from a state of type `σ`.

* `stop`: the finite phase ended.
* `noise D`: anything that is not a counted random draw, with next state law `D`.
* `trial sel D`: a completed random transmission trial. Whether it is counted, `sel`, is fixed before its
  destination is drawn (p.23: "A trial is selected predictably if the decision whether to count it is
  determined before its fresh destination is sampled"). Then a uniform destination `d` is drawn and `D d`
  is the next state law.

**Formalization Note.** All kernels are free, so any adaptive adversary and any corruption rule embeds:
the state holds the whole execution. -/
inductive TrialStep (n : ℕ) (σ : Type) where
  | stop
  | noise (D : PMF σ)
  | trial (sel : Bool) (D : Fin n → PMF σ)

/-- The destinations of the selected trials, in order, in a phase of at most `fuel` steps. -/
noncomputable def selectedDests {n : ℕ} [NeZero n] {σ : Type} (kind : σ → TrialStep n σ) :
    ℕ → σ → PMF (List (Fin n))
  | 0, _ => PMF.pure []
  | f + 1, s =>
    match kind s with
    | TrialStep.stop => PMF.pure []
    | TrialStep.noise D => D.bind (selectedDests kind f)
    | TrialStep.trial sel D =>
      (PMF.uniformOfFintype (Fin n)).bind fun d =>
        (D d).bind fun s' =>
          (selectedDests kind f s').map fun l => if sel then d :: l else l

/-- The number of distinct destinations in `U` of a row of destinations (Lemma 7.2, p.23). -/
def distinctIn {K n : ℕ} (f : Fin K → Fin n) (U : Finset (Fin n)) : ℕ :=
  ((Finset.univ.image f) ∩ U).card

/-- `δep` of (14), p.24. -/
noncomputable def deltaEp (n K : ℕ) : ℝ :=
  Real.exp (-(2 * n : ℝ)) + (n : ℝ) ^ 2 * Real.exp (-((K : ℝ) ^ 2 / (16 * n)))

/-- `δfin` of (15), p.24. -/
noncomputable def deltaFin (n K : ℕ) : ℝ :=
  Real.exp (-((K : ℝ) / 128)) + (n : ℝ) * Real.exp (-((K : ℝ) ^ 2 / (16 * n)))

end BeyondDS


