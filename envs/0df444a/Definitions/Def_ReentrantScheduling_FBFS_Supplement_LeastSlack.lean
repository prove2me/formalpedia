-- Prove2me | Definitions.Def_ReentrantScheduling_FBFS_Supplement_LeastSlack
-- name    : ReentrantScheduling_FBFS_Supplement_LeastSlack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T13:13:40.666641+00:00
-- url     : https://prove2.me/theorems/e95c2c75-a7d8-4482-8ddd-62234283825c
-- title:
--   §II and §VI — least-slack dispatch, due-date window and population envelopes
-- statement:
--   Let $L$ be a finite reentrant flow line and let $R$ be a raw run of its parts. A part $a$ has release time $\alpha(a)$ and due date $\delta(a)$; buffer $i$ has a fixed real estimate $\zeta_i$. Its slack there is
--
--   $$\delta(a)-\zeta_i.$$
--
--   At every nonnegative service start, the selected part has no greater slack than any waiting part at the same center. Equal slack allows arbitrary choices. Physical precedence, shared machine capacity and nonidling hold, but there is no FIFO restriction: a part may overtake another in the same buffer. The due-date window is $-\gamma_1\le\delta(a)-\alpha(a)\le\gamma_2$ for every part.
--
--   The all-time population envelope is $\sup_{t\ge0}x(t)$ and the asymptotic envelope is $\limsup_{t\to\infty}x(t)$, where the published $x(t)$ includes waiting and in-service parts. These quantities use extended nonnegative reals and preserve infinite counts. This extension provides the statement vocabulary for Theorem 4.
--
--   **Formalization Note** The immutable published Line and raw Run are reused. Buffers are 0-based, times use $\mathbb R\cup\{+\infty\}$, and counts use encard. Initial parts may have residual service at time zero. The inherited Line requires strictly positive processing times, a disclosed pin absent from the printed standing assumptions; zero processing times are outside this representation. The initial-count witness in Theorem 4 always exists because raw runs have finitely many releases by each finite time.
-- source:
--   Lu & Kumar, Distributed Scheduling Based on Due Dates and Buffer Priorities, IEEE TAC 36(12), 1991, p. 1408, §II, Least Slack Policy; p. 1413, §VI, (16) and Theorem 4

import Mathlib
import Definitions.Def_ReentrantScheduling_FBFS_Model

namespace ReentrantScheduling.FBFS.Supplement

/-- The due-date window (16), imposed on every part, including the initial parts. -/
def DueWindow {L : Line} (R : Run L) (δ : R.Part → ℝ) (γ₁ γ₂ : ℝ) : Prop :=
  ∀ p, -γ₁ ≤ δ p - R.α p ∧ δ p - R.α p ≤ γ₂

/-- Least-slack dispatch (§II, p. 1408), with physical nonpreemptive service.
The raw published Run is reused. No head-of-buffer or line-order constraint is imposed:
LS can overtake within a buffer. Equal slack permits any choice, including simultaneous starts.
The buffers are 0-based. Initial service can have a negative start and positive residual time. -/
structure LSAdmissible {L : Line} (R : Run L) (δ : R.Part → ℝ)
    (ζ : Fin L.l → ℝ) : Prop where
  precedence : ∀ p i, R.entry p ≤ i →
    (R.arrive p i ≤ R.start p i ∨
      (R.initial p ∧ i = R.entry p ∧ ((-(L.τ i) : ℝ) : WithTop ℝ) < R.start p i ∧
        R.start p i ≤ ((0 : ℝ) : WithTop ℝ)))
  capacity : ∀ σ (t : ℝ), 0 ≤ t → (R.busySlots σ t).encard ≤ L.m σ
  nonidling : ∀ σ (t : ℝ), 0 ≤ t →
    (∃ p i, L.center i = σ ∧ R.Waiting p i t) →
    (R.busySlots σ t).encard = L.m σ
  leastSlack : ∀ p i (t : ℝ), 0 ≤ t → R.entry p ≤ i →
    R.start p i = (t : WithTop ℝ) →
    ∀ q j, L.center j = L.center i → R.Waiting q j t → δ p - ζ i ≤ δ q - ζ j

/-- All-time population supremum, over nonnegative real time, in a complete order.
The count is the published x(t), including parts in service; infinite values are preserved. -/
noncomputable def populationSup {L : Line} (R : Run L) : ENNReal :=
  ⨆ t : {t : ℝ // 0 ≤ t}, ((R.x t.1 : ℕ∞) : ENNReal)

/-- Asymptotic population in the same complete order. No real-valued supremum fallback is used. -/
noncomputable def populationLimsup {L : Line} (R : Run L) : ENNReal :=
  Filter.limsup (fun t : ℝ => ((R.x t : ℕ∞) : ENNReal)) Filter.atTop

end ReentrantScheduling.FBFS.Supplement


