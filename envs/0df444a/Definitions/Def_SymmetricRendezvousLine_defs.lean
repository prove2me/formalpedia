-- Prove2me | Definitions.Def_SymmetricRendezvousLine_defs
-- name    : SymmetricRendezvousLine_defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T09:52:23.682126+00:00
-- url     : https://prove2.me/theorems/c5135b79-2bd8-4ff3-8dc5-c63e025a11e0
-- title:
--   Symmetric and asymmetric rendezvous on the line: strategies, meeting time, values
-- statement:
--   This file sets up the **rendezvous search problem on the line**.
--
--   Two players are placed on the real line at distance $2$: player I at $0$ and player II at $2$. Each player has its own notion of "forward", which is an independent fair coin flip relative to the line, so neither player knows in which direction the other lies. Both move with speed at most $1$.
--
--   1. A **feasible path** is a function $f:\mathbb R\to\mathbb R$ with $f(0)=0$ and $|f(s)-f(t)|\le|s-t|$ for all $s,t\ge0$; it describes a player's position over time in its *own* frame.
--   2. A **mixed strategy** $S$ is a probability space $(\Omega,P)$ together with a random path $\omega\mapsto f_\omega$ such that every $f_\omega$ is feasible and $\omega\mapsto f_\omega(t)$ is measurable for every $t$.
--   3. The **meeting time** of two trajectories $x,y$ is
--   $$T(x,y)=\inf\{t\ge0 : x(t)=y(t)\}\in[0,\infty],$$
--   with $T=\infty$ if they never meet.
--   4. For orientations $\varepsilon_1,\varepsilon_2\in\{+1,-1\}$, player I occupies $\varepsilon_1 f(t)$ and player II occupies $2+\varepsilon_2 g(t)$. The **expected meeting time** of strategies $S_1,S_2$ (independent randomisations, $f\sim S_1$, $g\sim S_2$) is
--   $$E(S_1,S_2)=\frac14\sum_{\varepsilon_1,\varepsilon_2\in\{\pm1\}}\mathbb E_{f\sim S_1,\;g\sim S_2}\big[T(\varepsilon_1 f,\;2+\varepsilon_2 g)\big].$$
--   5. The **symmetric rendezvous value** is $R=\inf_S E(S,S)$ (both players must use the same strategy) and the **asymmetric rendezvous value** is $R^a=\inf_{S_1,S_2}E(S_1,S_2)$.
--   6. An **integer zigzag** is a path with $f(0)=0$ that, on each interval $[n,n+1]$ ($n\in\mathbb N$), moves with constant velocity $+1$ or $-1$. The **discrete symmetric value** $R_{\mathrm{disc}}$ is the infimum of $E(S,S)$ over strategies all of whose paths are integer zigzags.
--
--   These objects are the common vocabulary for the goal (the conjecture $R=4.25$) and for every milestone of the mission.
--
--   **Formalization Note** Values live in $[0,\infty]$ (`ENNReal`) and expectations are Lebesgue integrals of non-negative functions, so strategies that never meet with positive probability simply have value $\infty$. Sample spaces range over `Type`; this loses no generality since any law on path space can be realised on $\Omega=\mathbb R^{\mathbb R}$. Measurability of each position, together with continuity of paths, makes the meeting time a random variable.
-- source:
--   Open Problem Garden, 'Rendezvous on a line' (posted by mdevos, 2007), http://www.openproblemgarden.org/op/rendezvous_on_a_line; model of S. Alpern, The rendezvous search problem, SIAM J. Control Optim. 33(3) (1995) 673-683, and S. Alpern, S. Gal, Rendezvous search on the line with distinguishable players, SIAM J. Control Optim. 33(4) (1995) 1270-1276.

import Mathlib

open MeasureTheory

namespace SymmetricRendezvousLine

/-- A feasible path for one player, written in that player's own frame: the player
starts at the origin of its own frame and moves with speed at most `1`, i.e. the path
is `1`-Lipschitz on `[0, ∞)`. Values at negative times are irrelevant. -/
def IsFeasiblePath (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |f s - f t| ≤ |s - t|

/-- A mixed strategy: a probability space `(Ω, P)` together with a random feasible path
`ω ↦ path ω`, measurable in `ω` at every fixed time. -/
structure MixedStrategy where
  /-- The sample space of the player's private randomisation. -/
  Ω : Type
  /-- The σ-algebra on the sample space. -/
  [mΩ : MeasurableSpace Ω]
  /-- The probability measure on the sample space. -/
  P : Measure Ω
  /-- `P` is a probability measure. -/
  [isProb : IsProbabilityMeasure P]
  /-- The random path, in the player's own frame. -/
  path : Ω → ℝ → ℝ
  /-- Every realised path is feasible. -/
  path_feasible : ∀ ω, IsFeasiblePath (path ω)
  /-- The position at each fixed time is a random variable. -/
  path_measurable : ∀ t : ℝ, Measurable fun ω => path ω t

attribute [instance] MixedStrategy.mΩ MixedStrategy.isProb

/-- The meeting time of two trajectories `x, y` on the line: the first time `t ≥ 0` with
`x t = y t`, and `∞` if they never meet. -/
noncomputable def meetingTime (x y : ℝ → ℝ) : ENNReal :=
  ⨅ (t : ℝ) (_ : 0 ≤ t ∧ x t = y t), ENNReal.ofReal t

/-- The orientation of a player's own "forward" direction relative to the line
(unknown to the player): `true ↦ +1`, `false ↦ -1`. -/
def orient (b : Bool) : ℝ := if b then 1 else -1

/-- Expected meeting time when player I (starting at `0`) uses `S₁` and player II
(starting at `2`) uses `S₂`, with independent randomisations. Each player's forward
direction is an independent fair coin, so each of the four orientation pairs has
probability `1/4`. -/
noncomputable def expectedMeetingTime (S₁ S₂ : MixedStrategy) : ENNReal :=
  (1 / 4 : ENNReal) * ∑ b₁ : Bool, ∑ b₂ : Bool,
    ∫⁻ p, meetingTime (fun t => orient b₁ * S₁.path p.1 t)
        (fun t => 2 + orient b₂ * S₂.path p.2 t) ∂(S₁.P.prod S₂.P)

/-- The symmetric rendezvous value `R` on the line: the infimum, over all mixed strategies
`S`, of the expected meeting time when both players use the same strategy `S`. -/
noncomputable def symmetricRendezvousValue : ENNReal :=
  ⨅ S : MixedStrategy, expectedMeetingTime S S

/-- The asymmetric rendezvous value on the line: players may use different strategies. -/
noncomputable def asymmetricRendezvousValue : ENNReal :=
  ⨅ (S₁ : MixedStrategy) (S₂ : MixedStrategy), expectedMeetingTime S₁ S₂

/-- A path that starts at `0`, moves at full speed `1`, and changes direction only at
integer times. -/
def IsIntegerZigzag (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ ∀ n : ℕ, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
    ∀ t ∈ Set.Icc (n : ℝ) (n + 1), f t = f n + s * (t - n)

/-- The symmetric rendezvous value restricted to mixed strategies all of whose paths are
integer zigzags. -/
noncomputable def discreteSymmetricRendezvousValue : ENNReal :=
  ⨅ (S : MixedStrategy) (_ : ∀ ω, IsIntegerZigzag (S.path ω)), expectedMeetingTime S S

end SymmetricRendezvousLine


