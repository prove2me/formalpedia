-- Prove2me | Definitions.Def_HighDimProb_RandomProcesses_ProcessTailProb
-- name    : HighDimProb_RandomProcesses_ProcessTailProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T21:31:29.340034+00:00
-- url     : https://prove2.me/theorems/eb5fe7a0-fc51-4c08-bfb2-4170403a1278
-- title:
--   The tail probability $P\{\sup_{t\in T} X_t \ge \tau\}$ of a random process
-- statement:
--   This is the **tail probability of the supremum** of a random process, the quantity Slepian's
--   inequality (Theorem 7.2.1) directly compares between two processes.
--
--   Fix a probability space $(\Omega,\mathcal F,P)$, a family $(X_t)_{t\in T}$ of real random
--   variables indexed by an arbitrary set $T$, and a threshold $\tau\in\mathbb R$. As with the
--   expected supremum (`ProcessESup`), and for the same reason (the pointwise supremum
--   $\sup_{t\in T}X_t(\omega)$ need not be measurable when $T$ is uncountable), this is defined
--   through the process's finite-dimensional marginals:
--
--   $$
--   P\Bigl\{\sup_{t\in T} X_t \ge \tau\Bigr\} \;:=\;
--   \sup_{T_0 \subseteq T \text{ finite, nonempty}} P\Bigl\{\max_{t\in T_0} X_t \ge \tau\Bigr\}.
--   $$
--
--   For a finite $T_0$, $\{\max_{t\in T_0} X_t \ge \tau\} = \{\exists\, t\in T_0,\ X_t \ge \tau\}$,
--   so each term of the supremum is an ordinary event probability.
--
--   **Formalization Note** Unlike `ProcessESup`, this quantity is real-valued (not `EReal`): every
--   term in the defining set is a probability, hence bounded above by $1$, so no junk value from
--   unboundedness can arise; if $T=\varnothing$ the defining set is empty, giving `sSup ∅ = 0`, the
--   correct value (the supremum over no points is $-\infty$, always below any threshold $\tau$).
-- source:
--   Vershynin, High-Dimensional Probability (2018), p. 156, footnote 3 to Section 7.2

import Mathlib

open MeasureTheory

namespace HighDimProb.RandomProcesses

/-- The **tail probability of the supremum**, `P{sup_{t∈T} X_t ≥ τ}`, of a random process
`(X_t)_{t∈T}` on a probability space `(Ω, P)`, understood through its finite-dimensional
marginals in the same sense as `processESup` (Vershynin, *High-Dimensional Probability* (2018),
p. 156, footnote 3):

`P{sup_{t∈T} X_t ≥ τ} := sup { P{max_{t∈T0} X_t ≥ τ} : T0 ⊆ T finite and nonempty }`,

where `P{max_{t∈T0} X_t ≥ τ} = P{∃ t ∈ T0, X_t ≥ τ}` for a finite `T0`. Real-valued (unlike
`processESup`): the set being taken `sSup` of here is always bounded above by `1` (each term is
a probability), so no junk-value risk from unboundedness; it is empty, giving `sSup ∅ = 0`,
exactly when `T` itself is empty, which is the correct value (the supremum over no points is
`-∞`, so it is below every real `τ`). -/
noncomputable def processTailProb {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {T : Type}
    (X : T → Ω → ℝ) (τ : ℝ) : ℝ :=
  sSup {p : ℝ | ∃ T0 : {s : Finset T // s.Nonempty}, p = P.real {ω | ∃ t ∈ T0.1, X t ω ≥ τ}}

end HighDimProb.RandomProcesses


