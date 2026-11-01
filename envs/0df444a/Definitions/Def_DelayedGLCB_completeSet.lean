-- Prove2me | Definitions.Def_DelayedGLCB_completeSet
-- name    : DelayedGLCB_completeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T08:24:29.099974+00:00
-- url     : https://prove2.me/theorems/9388d01e-5a1a-4dc6-a7d9-fcfcd71791d7
-- title:
--   Complete and missing timestamps $T_t$, $M_t$, the missing count $G_t$ and its running maximum $G^*_t$
-- statement:
--   Let $D_1,D_2,\dots$ be real delays. At the beginning of round $t$:
--
--   1. the **complete timestamps** are $T_t=\{s\in[1,t-1] : s+D_s\le t-1\}$, the rounds whose reward has arrived;
--   2. the **missing timestamps** are $M_t=[1,t-1]\setminus T_t$;
--   3. the **number of missing rewards** is $G_t=|M_t|=(t-1)-|T_t|$;
--   4. the **running maximum** is $G^*_t=\max_{1\le s\le t}G_s$.
--
--   $G_t$ is the quantity that inflates the confidence width of DUCB-GLCB, and $G^*_T$ enters the regret bound.
--
--   **Formalization Note** The paper writes $G_t=\sum_{s=1}^{t-1}\mathbb I\{s+D_s\ge t\}$, and Algorithm 1 sets $G_t=(t-1)-|T_t|$. The two agree for integer delays. For a fractional delay the reward of round $s$ is read as arriving at the end of round $\lceil s+D_s\rceil$, so a round is missing exactly when $s+D_s>t-1$.
-- source:
--   Blanchet, Xu, Zhou, Delay-Adaptive Learning in Generalized Linear Contextual Bandits, arXiv:2003.05174v1, §3.1, p.7 (T_t); §3.2, p.7 (G_t); Algorithm 1, lines 2 and 7, p.7; §3.3, p.8 (G*_t); p.26 (M_t)

import Mathlib

namespace DelayedGLCB

open Classical in
/-- **The complete-information timestamps `T_t`.**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, §3.1, p.7: "Denote `T_t = {s : s ≤ t − 1, D_s + s ≤ t − 1}`
as the set containing timestamps with complete information tuples at the beginning of round `t`."

`completeSet D ω t = {s ∈ [1, t − 1] : s + D_s(ω) ≤ t − 1}`.

**Formalization Note.** Rounds start at `1`; delays are real. -/
noncomputable def completeSet {Ω : Type*} (D : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : Finset ℕ :=
  (Finset.Ico 1 t).filter fun s => (s : ℝ) + D s ω ≤ (t : ℝ) - 1

open Classical in
/-- **The missing-reward timestamps `M_t`**: the rounds `s ∈ [1, t − 1]` whose reward has not
arrived at the beginning of round `t`, i.e. `[1, t − 1] \ T_t`
(Blanchet, Xu, Zhou, arXiv:2003.05174v1, p.26, the set `M_t`; p.5, "incomplete information tuple").

**Formalization Note.** For a real delay, `s ∉ T_t` means `s + D_s > t − 1`; for integer delays this is
the paper's `s + D_s ≥ t`. -/
noncomputable def missingSet {Ω : Type*} (D : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : Finset ℕ :=
  (Finset.Ico 1 t).filter fun s => ¬ ((s : ℝ) + D s ω ≤ (t : ℝ) - 1)

/-- **The number of missing rewards `G_t`.**
Blanchet, Xu, Zhou, arXiv:2003.05174v1, §3.2, p.7: "Denote `G_t = Σ_{s=1}^{t−1} 𝕀{s + D_s ≥ t}` as the
number of missing reward when the agent is making a prediction at round `t`", and Algorithm 1,
lines 2 and 7: `G_{τ+1} = τ − |T_{τ+1}|`, `G_{t+1} = t − |T_{t+1}|`.

`missingCount D ω t = |M_t| = (t − 1) − |T_t|`.

**Formalization Note.** Algorithm 1 defines `G_t = (t − 1) − |T_t|`, the count of rounds `s < t`
with `s + D_s > t − 1`. For integer delays this equals the printed sum `Σ 𝕀{s + D_s ≥ t}`; for a
fractional delay the reward of round `s` is read as arriving at the end of round `⌈s + D_s⌉`, which
makes the two descriptions agree. -/
noncomputable def missingCount {Ω : Type*} (D : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℕ :=
  (missingSet D ω t).card

/-- **The running maximum `G*_t = max_{1 ≤ s ≤ t} G_s`**
(Blanchet, Xu, Zhou, arXiv:2003.05174v1, §3.3, p.8).

**Formalization Note.** `Finset.sup` over `[1, t]` in `ℕ`; at `t = 0` the value is `0`. -/
noncomputable def runMaxMissing {Ω : Type*} (D : ℕ → Ω → ℝ) (ω : Ω) (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sup fun s => missingCount D ω s

end DelayedGLCB


