-- Prove2me | Definitions.Def_GoTBandit_Main_GoTChain
-- name    : GoTBandit_Main_GoTChain
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:14:40.334166+00:00
-- url     : https://prove2.me/theorems/967043a5-a45d-478e-8cfa-d53e64fb90c1
-- title:
--   §III, §V, Eqs. (5)–(8), (28), (31), (32), pp. 4, 9–11 — the GoT Markov chain P^ε on Z = ∏(A_n × {C, D}), phase lengths, path laws
-- statement:
--   This file defines the **Game of Thrones (GoT) dynamics** as a finite Markov chain, together with the phase lengths of the algorithm and the path probabilities used by the concentration lemmas.
--
--   **Phase lengths.** For integers $c_1,c_2,c_3$ and $\delta>0$, the $k$-th epoch has an exploration phase of $\lceil c_1k^\delta\rceil$ turns, a GoT phase of $\lceil c_2k^\delta\rceil$ turns and an exploitation phase of $c_32^k$ turns.
--
--   **States.** Each player $n$ has a baseline action $\bar a_n$ and a mood $S_n\in\{C,D\}$ (content or discontent). The state space is $Z=\prod_{n=1}^N(\mathcal A_n\times\{C,D\})$, and the **optimal state** for a profile $a^*$ is $z^*=[a^*,C^N]$.
--
--   **Transitions.** Fix utilities $u_n(a)=U_{n,a_n}\eta_{a_n}(a)$, a perturbation $\varepsilon>0$ and an exponent $c$. From state $z$, every player independently chooses an action:
--
--   $$
--   p_n^{a_n}=\begin{cases}\dfrac{\varepsilon^c}{M-1},& a_n\ne\bar a_n,\\[4pt] 1-\varepsilon^c,& a_n=\bar a_n,\end{cases}\quad\text{if } S_n=C,\qquad p_n^{a_n}=\frac1M\quad\text{if } S_n=D,
--   $$
--
--   (Eqs. (5)–(6)). Then, given the profile $a$, every player independently updates her mood: if $\bar a_n=a_n$, $u_n(a)>0$ and $S_n=C$ she stays content (Eq. (7)); otherwise she becomes content with probability $\frac{u_n(a)}{u_{n,\max}}\varepsilon^{u_{n,\max}-u_n(a)}$ and discontent otherwise (Eq. (8)). Her new baseline is the action she played. The product of these probabilities is the transition matrix $P^\varepsilon$ of the chain on $Z$.
--
--   **Path laws.** For a transition matrix $A$ on $Z$ and an initial law $\phi$, the probability of a path $(z_0,\dots,z_L)$ is $\phi(z_0)\prod_{t=0}^{L-1}A(z_t,z_{t+1})$; the file defines the probability of a set of paths, the number of visits of a path to a state during the turns $1,\dots,L$, the joint law of independent runs indexed by the window $k-\lfloor k/2\rfloor\le i\le k$ of the last $\lfloor k/2\rfloor+1$ epochs, and the window minimum and maximum of a sequence. It also defines $\|\phi\|_\pi=\sqrt{\sum_{z}\phi_z^2/\pi_z}$.
--
--   These objects are the vocabulary of Theorem V.6 and Lemmas V.7–V.8.
--
--   **Formalization Note** Stochastic matrices, distributions, stationarity and mixing times come from the published MarkovMixing definitions (`mm_basic`, `mm_mixing`); distributions are row vectors. The content probability of Eq. (8) is clipped to $[0,1]$; for positive utilities and $0<\varepsilon\le1$ the clipping is inactive because $u_n\le u_{n,\max}$. Eq. (5) divides by $M-1$, so the matrix is a stochastic matrix only for $M\ge2$, $c>0$ and $0<\varepsilon<1$, which every statement using it assumes. Real powers $\varepsilon^c$, $k^\delta$ are `Real.rpow`. $\|\phi\|_\pi$ uses Lean's $x/0=0$ where $\pi_z=0$; statements using it assume $\phi$ vanishes there. Lemma V.7's state at turn $t$ of a GoT phase is the state after the turn's transition, so a run of $L$ turns is a path $(z_0,\dots,z_L)$ from the starting state $z_0$ and visits are counted at $z_1,\dots,z_L$.
-- source:
--   Bistritz and Leshem, Game of Thrones: Fully Distributed Learning for Multiplayer Bandits, arXiv:1810.11162v7, pp. 4, 9–11, §III (phase lengths), §III-A Eqs. (5)–(8), Definition V.1 Eq. (28), Lemma V.7 Eq. (31), Lemma V.8 Eq. (32)

import Mathlib
import Definitions.Def_GoTBandit_Main_Assignment
import Definitions.Def_mm_basic
import Definitions.Def_mm_mixing

open Finset

namespace GoTBandit.Main

noncomputable section

/-- A player's personal state `S_n ∈ {C, D}`: content or discontent (§III-A). -/
inductive Mood
  | C
  | D
  deriving DecidableEq

instance : Fintype Mood :=
  ⟨{Mood.C, Mood.D}, by intro x; cases x <;> simp⟩

/-- The GoT state space `Z = ∏_n (A_n × {C, D})`; `z n = (ā_n, S_n)` is player `n`'s
baseline action and mood. -/
abbrev Z (N M : ℕ) := Fin N → Fin M × Mood

variable {N M : ℕ}

/-- The optimal state `z* = [a*, C^N]`. -/
def zStar (aStar : Fin N → Fin M) : Z N M :=
  fun n => (aStar n, Mood.C)

/-- Length `⌈c1 k^δ⌉` of the exploration phase of epoch `k`. -/
def expLen (c1 : ℕ) (δ : ℝ) (k : ℕ) : ℕ :=
  ⌈(c1 : ℝ) * (k : ℝ) ^ δ⌉₊

/-- Length `⌈c2 k^δ⌉` of the GoT phase of epoch `k`. -/
def gotLen (c2 : ℕ) (δ : ℝ) (k : ℕ) : ℕ :=
  ⌈(c2 : ℝ) * (k : ℝ) ^ δ⌉₊

/-- Length `c3 2^k` of the exploitation phase of epoch `k`. -/
def exploitLen (c3 : ℕ) (k : ℕ) : ℕ :=
  c3 * 2 ^ k

/-- The action law of Eqs. (5)–(6) of a player in state `s = (ā, S)`: a content player keeps
`ā` with probability `1 − ε^c` and plays each other arm with probability `ε^c/(M − 1)`; a
discontent player plays each arm with probability `1/M`. -/
def actProb (ε c : ℝ) (s : Fin M × Mood) (a' : Fin M) : ℝ :=
  match s.2 with
  | Mood.C => if a' = s.1 then 1 - ε ^ c else ε ^ c / ((M : ℝ) - 1)
  | Mood.D => 1 / (M : ℝ)

/-- The probability `(u_n/u_{n,max}) ε^{u_{n,max} − u_n}` of becoming content in Eq. (8),
clipped to `[0, 1]` (the clipping is inactive for positive utilities and `0 < ε ≤ 1`). -/
def contentProb (U : Fin N → Fin M → ℝ) (ε : ℝ) (a : Fin N → Fin M) (n : Fin N) : ℝ :=
  max 0 (min 1 (gUtil U a n / uMax U n * ε ^ (uMax U n - gUtil U a n)))

/-- The mood transition of Eqs. (7)–(8) of player `n` in state `s = (ā_n, S_n)` after the
profile `a` was played: probability of the new mood `S'`. -/
def moodProb (U : Fin N → Fin M → ℝ) (ε : ℝ) (s : Fin M × Mood) (a : Fin N → Fin M)
    (n : Fin N) (S' : Mood) : ℝ :=
  if s.1 = a n ∧ 0 < gUtil U a n ∧ s.2 = Mood.C then
    (if S' = Mood.C then 1 else 0)
  else
    (if S' = Mood.C then contentProb U ε a n else 1 - contentProb U ε a n)

/-- The transition matrix `P^ε` of the GoT dynamics on `Z` with utilities
`u_n(a) = U_{n,a_n} η_{a_n}(a)`: players choose actions independently by (5)–(6), then
update their moods independently by (7)–(8); the new baseline is the action played. -/
def gotMatrix (U : Fin N → Fin M → ℝ) (ε c : ℝ) : Matrix (Z N M) (Z N M) ℝ :=
  fun z z' => ∏ n, actProb ε c (z n) (z' n).1 *
    moodProb U ε (z n) (fun m => (z' m).1) n (z' n).2

/-- `‖ϕ‖_π = √(∑_z ϕ_z² / π_z)` (Lemma V.7). -/
def normPi (ϕ π : Z N M → ℝ) : ℝ :=
  Real.sqrt (∑ z, ϕ z ^ 2 / π z)

/-- The probability of the path `p = (z_0, z_1, …, z_L)` of a chain with transition matrix
`A` started from the law `ϕ`. -/
def pathWeight (A : Matrix (Z N M) (Z N M) ℝ) (ϕ : Z N M → ℝ) (L : ℕ)
    (p : Fin (L + 1) → Z N M) : ℝ :=
  ϕ (p 0) * ∏ t : Fin L, A (p t.castSucc) (p t.succ)

/-- The probability of a set `E` of paths `(z_0, …, z_L)`. -/
def pathProb (A : Matrix (Z N M) (Z N M) ℝ) (ϕ : Z N M → ℝ) (L : ℕ)
    (E : Set (Fin (L + 1) → Z N M)) : ℝ :=
  ∑ p, E.indicator (pathWeight A ϕ L) p

/-- The number of turns `t = 1, …, L` at which the path `p` is in the state `z₀`. -/
def visits {L : ℕ} (z₀ : Z N M) (p : Fin (L + 1) → Z N M) : ℕ :=
  (univ.filter (fun t : Fin L => p t.succ = z₀)).card

/-- The window `k − ⌊k/2⌋, …, k` of the last `⌊k/2⌋ + 1` epochs. -/
def window (k : ℕ) : Finset ℕ :=
  Finset.Icc (k - k / 2) k

theorem window_nonempty (k : ℕ) : (window k).Nonempty :=
  ⟨k, Finset.mem_Icc.2 ⟨Nat.sub_le _ _, le_rfl⟩⟩

/-- `min_{k−⌊k/2⌋ ≤ i ≤ k} f i`. -/
def windowMin (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (window k).inf' (window_nonempty k) f

/-- `max_{k−⌊k/2⌋ ≤ i ≤ k} f i`. -/
def windowMax (f : ℕ → ℝ) (k : ℕ) : ℝ :=
  (window k).sup' (window_nonempty k) f

/-- The joint law of independent runs, one per epoch `i ∈ W`: run `i` is the chain `A i`
started from `ϕ i` for `L i` steps. Probability of a set `E` of tuples of paths. -/
def windowProb (A : ℕ → Matrix (Z N M) (Z N M) ℝ) (ϕ : ℕ → Z N M → ℝ) (L : ℕ → ℕ)
    (W : Finset ℕ) (E : Set ((i : W) → Fin (L i + 1) → Z N M)) : ℝ :=
  ∑ p, E.indicator (fun p => ∏ i : W, pathWeight (A i) (ϕ i) (L i) (p i)) p

end

end GoTBandit.Main


