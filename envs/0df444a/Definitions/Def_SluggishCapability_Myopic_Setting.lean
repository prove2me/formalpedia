-- Prove2me | Definitions.Def_SluggishCapability_Myopic_Setting
-- name    : SluggishCapability_Myopic_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T23:04:51.320381+00:00
-- url     : https://prove2.me/theorems/b425fc60-c97a-4858-bfe6-b1e035efdd52
-- title:
--   §2–§3, pp. 6–11 — training program (P, f), constraint (1), myopic rule (2), period cost, extended (capability, state) chain, recurrent states, the two-state program
-- statement:
--   This file fixes the model of Eliaz and Spiegler's sluggish agent facing a trainer.
--
--   **Training program.** A trainer chooses a finite set of states $S$, a transition matrix $P$ on $S$ and an output function $f : S \to \mathbb{N}$ assigning a *challenge level* $d = f(s) \ge 0$ to each state. The program is **feasible** for an integer $\mu \ge 1$ and a slack $\varepsilon \in (0,1)$ if $P$ is stochastic and irreducible and its invariant distribution $\lambda_P$ satisfies the intensity constraint (1):
--   $$\sum_{s \in S} \lambda_P(s)\, f(s) \le \mu + \varepsilon .$$
--
--   **Sluggish agent.** At each period the agent picks a non-negative integer capability $m_t \in \{m_{t-1}-1, m_{t-1}, m_{t-1}+1\}$ after observing the challenge $d_t$, and pays the period cost $C_t = c\, m_t + \max(0, d_t - m_t)$ with $c \in (0,1)$. The **myopic rule** (2) moves capability one notch toward the challenge:
--   $$m_t = \begin{cases} m_{t-1}+1 & d_t > m_{t-1},\\ m_{t-1} & d_t = m_{t-1},\\ \max\{0, m_{t-1}-1\} & d_t < m_{t-1}.\end{cases}$$
--
--   **Extended process.** The pair $(m_t, s_t)$ is a Markov chain: from $(m, s)$ it moves to $(g(m, f(s')), s')$ with probability $P(s, s')$, where $g$ is the update (2). Capability is truncated to $\{0, \dots, M\}$ for a level $M \ge \max_s f(s)$; the update never leaves $[0, \max(m, f(s'))]$, so the truncated kernel is stochastic and capabilities above $M$ are transient.
--
--   **Recurrence.** A state $y$ is *reachable* from $x$ if some power of the kernel has a positive $(x, y)$ entry (zero steps allowed), and $x$ is *recurrent* if every state reachable from $x$ reaches $x$ back. On a finite chain almost every path is eventually absorbed in a recurrent class and visits each of its states infinitely often, so the paper's **lowest long-run capability** $m^*$ (the lowest value of $m$ taken beyond a large $t$, p. 9) is the minimum of $m$ over the recurrent class the path is absorbed in.
--
--   **The two-state program** of Proposition 1(ii) has states $L$ and $H$, $\Pr(L \to H) = 1$, $\Pr(H \to L) = \beta$, $\Pr(H \to H) = 1 - \beta$, and $f(L) = 0$, $f(H) = 2\mu$.
--
--   **Formalization Note** Stochastic matrices, distributions, stationarity (row vectors, $\pi P = \pi$) and irreducibility come from the published definition `mm_basic`. Feasibility asks for *some* invariant distribution satisfying (1); by irreducibility it is the unique one. `myopicStep m d` uses truncated natural-number subtraction for $\max\{0, m-1\}$. The extended chain lives on `Fin (M + 1) × S`. In `twoStateP` and `twoStateF`, index `0` is $L$ and index `1` is $H$. `Reaches` and `IsRecurrentState` have the same bodies as those of the published `YoungConventions.Perturbed.FiniteChain`, redefined here to stay inside the `mm_basic` vocabulary.
-- source:
--   Eliaz, Spiegler, Capability Building in Sluggish Organizations, authors' manuscript of March 28, 2022 (Management Science 2023, doi:10.1287/mnsc.2022.4445), pp. 6–11, §2 (constraint (1), cost C_t, rule (2), extended process and m*), §3 Proposition 1(ii)

import Mathlib
import Definitions.Def_mm_basic

namespace SluggishCapability.Myopic

open MarkovMixing

/-- The myopic/mechanistic update (2), p. 8: given last period's capability `m = m_{t-1}` and the
current challenge `d = d_t`, the agent moves capability one notch toward `d`:
`m + 1` if `d > m`, `m` if `d = m`, and `max{0, m − 1}` if `d < m`.
Here `m - 1` is truncated natural-number subtraction, which is exactly `max{0, m − 1}`. -/
def myopicStep (m d : ℕ) : ℕ :=
  if m < d then m + 1 else if d = m then m else m - 1

/-- The period cost `C_t = c·m_t + max(0, d_t − m_t)` of choosing capability `m` against
challenge `d`, p. 7 (the paper takes `c ∈ (0, 1)`). -/
noncomputable def periodCost (c : ℝ) (m d : ℕ) : ℝ :=
  c * (m : ℝ) + max 0 ((d : ℝ) - (m : ℝ))

/-- A feasible training program (§2, p. 7): `P` is a stochastic, irreducible transition matrix on
the finite state set `S`, and an invariant distribution `λ` of `P` satisfies the intensity
constraint (1), `∑_{s ∈ S} λ(s) f(s) ≤ µ + ε`. By irreducibility the invariant distribution is
unique (`MarkovMixing.exists_unique_stationary`), so this is the paper's `λP`. -/
def IsFeasibleProgram {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (μ : ℕ) (ε : ℝ) : Prop :=
  IsStochastic P ∧ MarkovMixing.Irreducible P ∧
    ∃ lam : S → ℝ, IsStationary P lam ∧ ∑ s, lam s * (f s : ℝ) ≤ (μ : ℝ) + ε

/-- The extended Markov process on (capability, trainer state), p. 9, with capability truncated
to `Fin (M + 1) = {0, …, M}`: from `(m, s)` the trainer state moves to `s'` with probability
`P s s'`, and capability moves to `myopicStep m (f s')` (rule (2) against the new challenge
`f s'`). Its rows sum to one when `f s ≤ M` for every `s`, since the update never leaves
`[0, max(m, f s')]`; capabilities above `M` are transient and are not needed. -/
noncomputable def extKernel {S : Type*} [Fintype S] [DecidableEq S]
    (P : Matrix S S ℝ) (f : S → ℕ) (M : ℕ) :
    Matrix (Fin (M + 1) × S) (Fin (M + 1) × S) ℝ :=
  fun x y => if (y.1 : ℕ) = myopicStep (x.1 : ℕ) (f y.2) then P x.2 y.2 else 0

/-- `y` is reachable from `x` under the transition matrix `K` (in `t ≥ 0` steps). -/
def Reaches {X : Type*} [Fintype X] [DecidableEq X] (K : Matrix X X ℝ) (x y : X) : Prop :=
  ∃ t : ℕ, 0 < (K ^ t) x y

/-- `x` is a recurrent state of the finite chain `K`: every state reachable from `x` reaches `x`
back. -/
def IsRecurrentState {X : Type*} [Fintype X] [DecidableEq X] (K : Matrix X X ℝ) (x : X) : Prop :=
  ∀ y, Reaches K x y → Reaches K y x

/-- The two-state program of Proposition 1(ii), p. 11. Index `0` is `L` and index `1` is `H`:
`Pr(L → L) = 0`, `Pr(L → H) = 1`, `Pr(H → L) = β`, `Pr(H → H) = 1 − β`. -/
def twoStateP (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, 1; β, 1 - β]

/-- The output function of Proposition 1(ii), p. 11 (index `0` is `L`, `1` is `H`):
`f(L) = 0`, `f(H) = 2µ`. -/
def twoStateF (μ : ℕ) : Fin 2 → ℕ :=
  ![0, 2 * μ]

end SluggishCapability.Myopic


