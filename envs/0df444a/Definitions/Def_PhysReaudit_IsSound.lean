-- Prove2me | Definitions.Def_PhysReaudit_IsSound
-- name    : PhysReaudit_IsSound
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T06:47:11.624784+00:00
-- url     : https://prove2.me/theorems/6e4006fc-66e8-4208-877a-788ed502f7eb
-- title:
--   $\delta$-soundness and $\varepsilon$-completeness of an audit rule
-- statement:
--   Let $R$ be an audit rule with side law $\nu$, at depth $d$ with survival $a$, and let $\Delta_q=b-\kappa a^dq$.
--
--   1. $R$ is **$\delta$-sound** if it accepts with probability at most $\delta$ whenever $\Delta_q<0$: $\mathbb P_q(R\text{ accepts})\le\delta$ for every $q\in[0,1]$ with $\Delta_q<0$.
--   2. $R$ is **$\varepsilon$-complete** if it accepts with probability at least $1-\delta$ whenever $\Delta_q\ge\varepsilon$: $\mathbb P_q(R\text{ accepts})\ge1-\delta$ for every $q\in[0,1]$ with $\Delta_q\ge\varepsilon$.
--
--   Stopping without a certificate is allowed. With $t$ and $q_0$ as in the paper, soundness is required on $q>t$ and completeness on $q\le q_0$; nothing is required on $(q_0,t]$.
--
--   **Formalization Note** Probabilities are compared in $[0,\infty]$.
-- source:
--   Q. Li, When Can Physical Evidence Survive a World-Model Update? Finite-cost re-auditing and reusable policy certificates, review revision of 3 November 2026 (STOC 2027 submission, sha256 a20c437b34115b84982339e9a6fa319cb3a66f66d9d4c474465cbb954c79093d), §4, p.3 (PDF p.4): "A rule is δ-sound if it accepts with probability at most δ whenever ∆q < 0, and ε-complete if it accepts with probability at least 1 − δ whenever ∆q ≥ ε. Stopping without a certificate is allowed."

import Mathlib
import Definitions.Def_PhysReaudit_Delta
import Definitions.Def_PhysReaudit_Rule
import Definitions.Def_PhysReaudit_run
import Definitions.Def_PhysReaudit_lawQ

open MeasureTheory

namespace PhysReaudit

/-- δ-soundness (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4)): "A rule is δ-sound if it accepts with probability at most δ
whenever ∆q < 0". The condition ranges over every target parameter `q ∈ [0, 1]` with `Δ_q < 0`. -/
def IsSound {W : Type} [MeasurableSpace W] (R : Rule W) (ν : Measure W) (a : ℝ) (d : ℕ)
    (b κ δ : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1, Delta a d b κ q < 0 →
    lawQ ν a q {ω | accepts R d ω} ≤ ENNReal.ofReal δ

/-- ε-completeness (Q. Li, *When Can Physical Evidence Survive a World-Model Update?*, review revision of 3 November 2026 (sha256 a20c437b…), §4, p.3 (PDF p.4)): "ε-complete if it accepts with probability at least 1 − δ
whenever ∆q ≥ ε". The condition ranges over every `q ∈ [0, 1]` with `Δ_q ≥ ε`. -/
def IsComplete {W : Type} [MeasurableSpace W] (R : Rule W) (ν : Measure W) (a : ℝ) (d : ℕ)
    (b κ ε δ : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1, ε ≤ Delta a d b κ q →
    ENNReal.ofReal (1 - δ) ≤ lawQ ν a q {ω | accepts R d ω}

end PhysReaudit


