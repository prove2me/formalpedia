-- Prove2me | Definitions.Def_RegretMatching_Approach_Setting
-- name    : RegretMatching_Approach_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T00:02:09.81897+00:00
-- url     : https://prove2.me/theorems/f1fe068a-c0c5-46a6-b4b5-5a98e3d1af12
-- title:
--   §3–§4, pp. 1133–1139 — (3.1) with zero diagonal, the vector payoff v, D_t, ℝ^L_−, [x]^±, Blackwell's two-player play, (4.2a); §2 objects from the shared module
-- statement:
--   This file fixes the objects of Hart and Mas-Colell (2000), §2–§3 and §4(c), used in Theorem A and its proof.
--
--   **The game.** $\Gamma=(N,(S^i)_{i\in N},(u^i)_{i\in N})$ is a finite game in strategic form: $N$ is a finite set of players, each $S^i$ is a finite set of strategies, and $u^i:S\to\mathbb R$ is player $i$'s payoff, where $S=\prod_{i\in N}S^i$. For $s\in S$ and $k\in S^i$, $u^i(k,s^{-i})$ is the payoff to $i$ when $i$'s coordinate of $s$ is replaced by $k$.
--
--   **Correlated $\varepsilon$-equilibrium** (DEFINITION, p. 1129). A probability distribution $\psi$ on $S$ is a correlated $\varepsilon$-equilibrium if for every $i\in N$ and all $j,k\in S^i$,
--   $$\sum_{s\in S:\ s^i=j}\psi(s)\,\big[u^i(k,s^{-i})-u^i(s)\big]\le\varepsilon .$$
--   A correlated equilibrium is the case $\varepsilon=0$.
--
--   **Histories and regrets.** The game is played at $t=1,2,\dots$; $h_t=(s_1,\dots,s_t)$ is the history up to $t$. For $j,k\in S^i$,
--   $$D^i_t(j,k)=\frac1t\sum_{\tau\le t:\ s^i_\tau=j}\big[u^i(k,s^{-i}_\tau)-u^i(s_\tau)\big],\qquad R^i_t(j,k)=\max\{D^i_t(j,k),0\}$$
--   ((2.1b), second line, and (2.1c)); the empirical distribution of play is $z_t(s)=\frac1t\,|\{\tau\le t: s_\tau=s\}|$ (2.3). The unconditional regret of §4(c) is $D^i_t(k)=\frac1t\sum_{\tau=1}^t[u^i(k,s^{-i}_\tau)-u^i(s_\tau)]$ (4.2a).
--
--   **Equation (3.1)** (p. 1133). With the convention $R^i_t(j,j):=0$, a vector $q$ on $S^i$ satisfies (3.1) at the history $h_t$ if
--   $$\sum_{k\in S^i}q(k)R^i_t(k,j)=q(j)\sum_{k\in S^i}R^i_t(j,k)\qquad\text{for every }j\in S^i .$$
--
--   **Plays.** A behaviour profile $\sigma$ gives, for each $t$, history $h_t$ and player $i$, a vector $\sigma_t(h_t)^i$ on $S^i$. A play of $\sigma$ on a probability space $(\Omega,P)$ is a sequence of $S$-valued random variables $s_1,s_2,\dots$ such that the events $\{s_t=x\}$ are measurable and, for every history $h_t$ of positive probability,
--   $$P[s_{t+1}=x\mid h_t]=\prod_{i\in N}\sigma_t(h_t)^i(x^i)\quad\text{for all }x\in S,$$
--   i.e. given the history, players randomize independently according to $\sigma$.
--
--   **The approachability objects** (proof of Theorem A, pp. 1136–1137). $L=\{(j,k)\in S^i\times S^i: j\ne k\}$. For $\lambda\in\mathbb R^L$, $\Lambda_\lambda$ is the $S^i\times S^i$ matrix with entries $\lambda(j,k)$ for $j\ne k$ and $0$ for $j=k$. The vector payoff $v(s^i,s^{-i})\in\mathbb R^L$ has $(j,k)$-coordinate $u^i(k,s^{-i})-u^i(j,s^{-i})$ if $s^i=j$ and $0$ otherwise, and $D_t=\frac1t\sum_{\tau\le t}v(s_\tau)$ is the average vector payoff. $\mathbb R^L_-=\{x\in\mathbb R^L: x\le0\}$ is the nonpositive orthant, and $[x]^-$, $[x]^+$ are the coordinatewise $\min\{x,0\}$ and $\max\{x,0\}$.
--
--   **Blackwell's setting** (pp. 1134–1135). A decision-maker with finite action set $A$ faces an opponent with finite action set $B$; the vector payoff is $v:A\times B\to\mathbb R^L$, and $D_t=\frac1t\sum_{\tau\le t}v(a_\tau,b_\tau)$. A play of the procedures $f$ (of the decision-maker) and $g$ (of the opponent) is a sequence of $A\times B$-valued random variables whose next pair, given any history of positive probability, has law $f_t(h_t)(a)\,g_t(h_t)(b)$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** Time is 0-based in Lean: `play τ` is $s_{\tau+1}$ and a history $h_t$ is a tuple `Fin t → S` (or `Fin t → A × B`). All regret quantities are functions of a finite history; at $t=0$ they are $0$ (Lean's $1/0=0$), and every statement uses histories of length $t+1\ge1$. $\Delta(Q)$ is Mathlib's `stdSimplex`. The zero diagonal of (3.1) is made explicit (`regretR0`), although $R^i_t(j,j)=0$ holds anyway. $\mathbb R^L$ is `EuclideanSpace ℝ L`. `IsPlay` conditions on the event $\{(s_1,\dots,s_t)=h_t\}$ only when it has positive probability. The game, correlated $\varepsilon$-equilibrium, $D^i_t$, $R^i_t$, $z_t$ and `IsPlay` are not re-declared here: they are imported from the shared module `RegretMatching.Main.Setting` (the companion mission on the Main Theorem) and used as `RegretMatching.Main.IsCorrEq`, `regretD`, `regretR`, `empDist`, `IsPlay`. This file adds `hist` for plays with values in any type (for $X=S$ it is the shared `hist`), `regretR0`, (3.1), (4.2a), the approachability objects and Blackwell's two-player play `IsPlay2`.
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), pp. 1129–1139: §2 DEFINITION, (2.1b), (2.1c), (2.3), footnote 4; §3 (3.1), Blackwell's setting pp. 1134–1135, proof of THEOREM A pp. 1136–1137; §4(c) (4.2a)

import Mathlib
import Definitions.Def_RegretMatching_Main_Setting

namespace RegretMatching.Approach

open MeasureTheory ProbabilityTheory Finset

/-!
Hart and Mas-Colell (2000), §2 and §3. Conventions:
* the game: players `ι` (finite), strategy sets `S i` (finite), payoffs `u i : (∀ i, S i) → ℝ`;
  `u i (Function.update s i k)` is the paper's `uⁱ(k, s⁻ⁱ)`;
* time: `play τ` is the paper's `s_{τ+1}`; the history `h_t = (s_1, …, s_t)` is a tuple
  `h : Fin t → X` with `h τ = s_{τ+1}`;
* every regret quantity is a deterministic function of a finite history.
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- The history `h_t = (s_1, …, s_t)` of a play with values in `X`:
`hist play t ω τ = play τ ω`. -/
def hist {X Ω : Type} (play : ℕ → Ω → X) (t : ℕ) (ω : Ω) : Fin t → X :=
  fun τ => play τ ω

/-- The regrets with the diagonal set to zero (p. 1133: "formally letting `Rⁱ_t(j, j) := 0`"). -/
noncomputable def regretR0 (u : ι → (∀ i, S i) → ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) (j k : S i) : ℝ :=
  if j = k then 0 else RegretMatching.Main.regretR u h i j k

/-- (3.1): `∑_{k ∈ Sⁱ} q(k) Rⁱ_t(k, j) = q(j) ∑_{k ∈ Sⁱ} Rⁱ_t(j, k)` for every `j ∈ Sⁱ`,
with `Rⁱ_t(j, j) := 0`. -/
def SatisfiesEq31 (u : ι → (∀ i, S i) → ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) (q : S i → ℝ) : Prop :=
  ∀ j : S i, ∑ k : S i, q k * regretR0 u h i k j = q j * ∑ k : S i, regretR0 u h i j k

/-- (4.2a), §4(c): the unconditional regret
`Dⁱ_t(k) = (1/t) ∑_{τ=1}^{t} [uⁱ(k, s⁻ⁱ_τ) − uⁱ(s_τ)]`. -/
noncomputable def uncondD (u : ι → (∀ i, S i) → ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) (k : S i) : ℝ :=
  (1 / (t : ℝ)) * ∑ τ : Fin t, (u i (Function.update (h τ) i k) - u i (h τ))

/-- The index set `L = {(j, k) ∈ A × A : j ≠ k}` (proof of THEOREM A, p. 1136). -/
abbrev OffDiag (A : Type) : Type := {p : A × A // p.1 ≠ p.2}

/-- The nonnegative `A × A` matrix with entries `λ(j, k)` for `j ≠ k` and `0` for `j = k`
(p. 1137), built from `λ ∈ ℝ^L`. -/
def lamMat {A : Type} [DecidableEq A] (lam : OffDiag A → ℝ) (j k : A) : ℝ :=
  if h : j = k then 0 else lam ⟨(j, k), h⟩

/-- The vector payoff of the proof of THEOREM A (p. 1136): `v(a, s⁻ⁱ) ∈ ℝ^L` with
`(j, k)`-coordinate `uⁱ(k, s⁻ⁱ) − uⁱ(j, s⁻ⁱ)` if `a = j` and `0` otherwise.
The `i`-th coordinate of the profile `s` is ignored. -/
noncomputable def vecPay (u : ι → (∀ i, S i) → ℝ) (i : ι) (a : S i) (s : ∀ i, S i) :
    EuclideanSpace ℝ (OffDiag (S i)) :=
  WithLp.toLp 2 (fun l : OffDiag (S i) =>
    if a = l.1.1 then u i (Function.update s i l.1.2) - u i (Function.update s i l.1.1) else 0)

/-- The average vector payoff `D_t = (1/t) ∑_{τ ≤ t} v(s_τ)` of player `i` along a history. -/
noncomputable def avgPay (u : ι → (∀ i, S i) → ℝ) (i : ι) {t : ℕ} (h : Fin t → (∀ i, S i)) :
    EuclideanSpace ℝ (OffDiag (S i)) :=
  (1 / (t : ℝ)) • ∑ τ : Fin t, vecPay u i (h τ i) (h τ)

/-- The nonpositive orthant `ℝ^L_− = {x ∈ ℝ^L : x ≤ 0}`. -/
def negOrthant (L : Type) : Set (EuclideanSpace ℝ L) := {x | ∀ l, x l ≤ 0}

/-- `[x]⁻`: the coordinatewise `min (x l) 0`. -/
noncomputable def negPart {L : Type} (x : EuclideanSpace ℝ L) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (fun l => min (x l) 0)

/-- `[x]⁺`: the coordinatewise `max (x l) 0`. -/
noncomputable def posPart {L : Type} (x : EuclideanSpace ℝ L) : EuclideanSpace ℝ L :=
  WithLp.toLp 2 (fun l => max (x l) 0)

/-! ### The abstract repeated decision problem of Blackwell's theorem (pp. 1134–1135)

Decision-maker `i` has the finite action set `A`, the opponent `−i` the finite action set `B`;
the vector payoff is `v : A → B → ℝ^L`. A history is a tuple of pairs `Fin t → A × B`. -/

/-- The average vector payoff `D_t = (1/t) ∑_{τ ≤ t} v(sⁱ_τ, s⁻ⁱ_τ)` along a history of pairs. -/
noncomputable def avgVec {A B L : Type} (v : A → B → EuclideanSpace ℝ L) {t : ℕ}
    (h : Fin t → A × B) : EuclideanSpace ℝ L :=
  (1 / (t : ℝ)) • ∑ τ : Fin t, v (h τ).1 (h τ).2

/-- A play of the procedures `f` (of `i`) and `g` (of `−i`) on `(Ω, P)`: each event
`{s_{t+1} = (a, b)}` is measurable, and given any history `h_t` of positive probability,
`P[s_{t+1} = (a, b) | h_t] = f t h_t a · g t h_t b` (the two randomize independently given
the history). -/
def IsPlay2 {A B Ω : Type} [MeasurableSpace Ω]
    (f : (t : ℕ) → (Fin t → A × B) → A → ℝ) (g : (t : ℕ) → (Fin t → A × B) → B → ℝ)
    (P : Measure Ω) (play : ℕ → Ω → A × B) : Prop :=
  (∀ (t : ℕ) (x : A × B), MeasurableSet {ω | play t ω = x}) ∧
    ∀ (t : ℕ) (h : Fin t → A × B), P {ω | hist play t ω = h} ≠ 0 →
      ∀ (a : A) (b : B),
        (P[|{ω | hist play t ω = h}] {ω | play t ω = (a, b)}).toReal = f t h a * g t h b

end RegretMatching.Approach


