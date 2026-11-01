-- Prove2me | Definitions.Def_SambaPG_sambaRun
-- name    : SambaPG_sambaRun
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:38:40.742401+00:00
-- url     : https://prove2.me/theorems/6d3bd28e-c38c-4723-a518-3b6ee9e79008
-- title:
--   The SAMBA process $p(t)$ started from $p(0)$
-- statement:
--   Given the randomness of `SambaNoise`, a learning rate $\alpha$, a draw rule, a leader rule and an initial vector $p(0)$, the **SAMBA process** $(p(t):t\in\mathbb Z_+)$ is defined recursively: at time $t$,
--
--   1. the leading arm is $a_\star(t)=\mathrm{lead}(p(t),V_t)$;
--   2. the arm played is $I(t)=\mathrm{draw}(p(t),U_t)$, and it pays the reward $R_{I(t)}(t)$;
--   3. $p(t+1)$ is the SAMBA update (6) of $p(t)$ with leading arm $a_\star(t)$, played arm $I(t)$ and reward $R_{I(t)}(t)$.
--
--   The arm played and the leading arm at each time are also named, for use in the regret.
--
--   **Formalization Note** Time starts at $0$, as in (5) and (6); the algorithm box counts $t=1,\dots,T$. The initial vector is a parameter: the main theorem starts from the uniform vector, the milestones from a general one.
-- source:
--   Denisov & Walton, Regret Analysis of a Markov Policy Gradient Algorithm for Multi-arm Bandits, arXiv:2007.10229v3, algorithm box, p.4; §3.4, p.7, eq. (6)

import Mathlib
import Definitions.Def_SambaPG_sambaStep
import Definitions.Def_SambaPG_SambaNoise

open MeasureTheory

namespace SambaPG

variable {A : Type*} [Fintype A] [DecidableEq A] {B : BernoulliBandit A} {Ω : Type*}
  [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The SAMBA process `p(t) = (p_a(t) : a ∈ A)` started from `p₀`.**
Denisov & Walton, arXiv:2007.10229v3, algorithm box, p.4, and §3.4, p.7, eq. (6).

`sambaRun ξ α draw lead p₀ t ω` is the probability vector at time `t ∈ ℤ₊`. At time `t` the
leading arm is `ℓ = lead p(t) (V t)`, the arm played is `i = draw p(t) (U t)`, its reward is
`R_i(t)`, and `p(t + 1) = sambaStep α p(t) ℓ i R_i(t)`.

**Formalization Note.** Time is indexed from `0`, as in (5) and (6); the algorithm box counts
`t = 1, …, T`. The initial vector `p₀` is a parameter: Theorem 1 uses the uniform vector of the
algorithm box, the milestones a general `p₀`. -/
noncomputable def sambaRun (ξ : SambaNoise B μ) (α : ℝ) (draw lead : (A → ℝ) → ℝ → A)
    (p₀ : A → ℝ) : ℕ → Ω → A → ℝ
  | 0 => fun _ => p₀
  | t + 1 => fun ω =>
      let p := sambaRun ξ α draw lead p₀ t ω
      let i := draw p (ξ.U t ω)
      sambaStep α p (lead p (ξ.V t ω)) i (ξ.R t ω i)

/-- The arm `I(t)` played by SAMBA at time `t`: `I_a(t) = 1` exactly for `a = playedArm … t ω`. -/
noncomputable def playedArm (ξ : SambaNoise B μ) (α : ℝ) (draw lead : (A → ℝ) → ℝ → A)
    (p₀ : A → ℝ) (t : ℕ) (ω : Ω) : A :=
  draw (sambaRun ξ α draw lead p₀ t ω) (ξ.U t ω)

/-- The leading arm `a⋆(t)` of SAMBA at time `t`. -/
noncomputable def leaderArm (ξ : SambaNoise B μ) (α : ℝ) (draw lead : (A → ℝ) → ℝ → A)
    (p₀ : A → ℝ) (t : ℕ) (ω : Ω) : A :=
  lead (sambaRun ξ α draw lead p₀ t ω) (ξ.V t ω)

end SambaPG


