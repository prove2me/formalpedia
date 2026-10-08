-- Prove2me | Definitions.Def_RegretMatching_Main_Setting
-- name    : RegretMatching_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T23:04:44.793642+00:00
-- url     : https://prove2.me/theorems/59e8dbe7-32b9-4a32-aa55-bced68a5cd67
-- title:
--   §2 and Appendix, pp. 1129–1131, 1143–1145 — finite game, correlated ε-equilibrium, regrets (2.1b–c), regret-matching (2.2), z_t (2.3), plays, Π_t, ρ_t, the ŝ-process, α, α̂
-- statement:
--   This file fixes the objects of Hart and Mas-Colell (2000), §2 and the Appendix.
--
--   **The game.** $\Gamma=(N,(S^i)_{i\in N},(u^i)_{i\in N})$ is a finite game in strategic form: $N$ is a finite set of players, each $S^i$ is a finite set of strategies, and $u^i:S\to\mathbb R$ is player $i$'s payoff, where $S=\prod_{i\in N}S^i$. For $s\in S$ and $k\in S^i$, $u^i(k,s^{-i})$ is the payoff to $i$ when $i$'s coordinate of $s$ is replaced by $k$.
--
--   **Correlated $\varepsilon$-equilibrium** (DEFINITION, p. 1129). A probability distribution $\psi$ on $S$ is a correlated $\varepsilon$-equilibrium if for every $i\in N$ and all $j,k\in S^i$,
--   $$\sum_{s\in S:\ s^i=j}\psi(s)\,\big[u^i(k,s^{-i})-u^i(s)\big]\le\varepsilon .$$
--   A correlated equilibrium is the case $\varepsilon=0$.
--
--   **Histories and regrets.** The game is played at $t=1,2,\dots$; $h_t=(s_1,\dots,s_t)$ is the history up to $t$. For $j,k\in S^i$,
--   $$D^i_t(j,k)=\frac1t\sum_{\tau\le t:\ s^i_\tau=j}\big[u^i(k,s^{-i}_\tau)-u^i(s_\tau)\big],\qquad R^i_t(j,k)=\max\{D^i_t(j,k),0\}$$
--   ((2.1b), second line, and (2.1c)); the empirical distribution of play is $z_t(s)=\frac1t\,|\{\tau\le t: s_\tau=s\}|$ (2.3).
--
--   **Regret matching** (2.2). Fix $\mu>0$. The transition matrix of player $i$ after $h_t$ is
--   $$\Pi^i_t(j,k)=\tfrac1\mu R^i_t(j,k)\ (k\ne j),\qquad \Pi^i_t(j,j)=1-\sum_{k'\ne j}\tfrac1\mu R^i_t(j,k'),$$
--   and at time $t+1$ player $i$ plays $p^i_{t+1}(k)=\Pi^i_t(s^i_t,k)$; the initial mixed action $p^i_1\in\Delta(S^i)$ is arbitrary.
--
--   **Plays.** A behaviour profile $\sigma$ gives, for each $t$, history $h_t$ and player $i$, a vector $\sigma_t(h_t)^i$ on $S^i$. A play of $\sigma$ on a probability space $(\Omega,P)$ is a sequence of $S$-valued random variables $s_1,s_2,\dots$ such that the events $\{s_t=x\}$ are measurable and, for every history $h_t$ of positive probability,
--   $$P[s_{t+1}=x\mid h_t]=\prod_{i\in N}\sigma_t(h_t)^i(x^i)\quad\text{for all }x\in S,$$
--   i.e. given the history, players randomize independently according to $\sigma$. $P[A\mid h_t]$ and $E[X\mid h_t]$ denote probability and expectation under $P$ conditioned on the event $\{(s_1,\dots,s_t)=h_t\}$.
--
--   **Appendix objects** (pp. 1143–1145), for a fixed player $i$: $A_t(j,k)=1_{\{s^i_t=j\}}[u^i(k,s^{-i}_t)-u^i(s_t)]$; $\rho_t=\sum_{j\ne k}[R_t(j,k)]^2$, the squared distance of $D_t\in\mathbb R^L$ to the nonpositive orthant, $L=\{(j,k):j\ne k\}$; the auxiliary process $\hat s$, started at $\hat s_t=s_t$ and moving with the fixed transition probabilities $P[\hat s_{t+w}=y\mid\hat s_{t+w-1}=x]=\prod_{i'}\Pi^{i'}_t(x^{i'},y^{i'})$; and
--   $$\alpha_{t,w}(j,s^{-i})=\sum_{k\in S^i}\Pi_t(k,j)P[s_{t+w}=(k,s^{-i})\mid h_t]-P[s_{t+w}=(j,s^{-i})\mid h_t],$$
--   with $\hat\alpha_{t,w}$ the same expression for the $\hat s$-process. Finally $t_n=\lfloor n^{5/3}\rfloor$, and `multiStep` gives the $w$-step conditional probabilities of a process on a finite set from its one-step conditional probabilities (proof of Step M4).
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** Time is 0-based in Lean: `play τ` is $s_{\tau+1}$ and a history $h_t$ is a tuple `Fin t → S`; for $t\ge1$ the last play $s_t$ is `h ⟨t-1, _⟩`, and $s_{t+w}$ is `play (t + w - 1)`. All regret quantities are functions of a finite history, so the deterministic PROPOSITION and the probabilistic steps share one definition. At $t=0$, $D_0=R_0=z_0=0$ (Lean's $1/0=0$); every statement has $t\ge1$. $\Delta(Q)$ is Mathlib's `stdSimplex`. $\rho_t$ is defined by the sum $\sum_{j\ne k}[D^+_t(j,k)]^2$, which the paper shows equals the squared distance (p. 1144, footnote 33). The $\hat s$-process is not built as a second random process: its law is explicit, and $P[\hat s_{t+w}=s\mid h_t]$ is the $(s_t,s)$ entry of the $w$-th power of the product matrix $\prod_{i'}\Pi^{i'}_t$ (`shatProb`, with the start state as an argument). In `alpha` and `alphaHat` the $i$-th coordinate of the profile argument is ignored. Conditional probabilities use Mathlib's `ProbabilityTheory.cond`, and every statement that conditions on $h_t$ assumes $P[h_t]>0$ (p. 1144: "only those that occur with positive probability are considered").
-- source:
--   Hart and Mas-Colell, A simple adaptive procedure leading to correlated equilibrium, Econometrica 68 (2000), pp. 1129–1131, §2, DEFINITION, (2.1a)–(2.3), footnotes 3–6; pp. 1133, §3 Remark (independence given the history); pp. 1143–1145, Appendix (A_t, D_t, R_t, Π_t, ρ_t, the ŝ-process, α, α̂, t_n); p. 1147, proof of Step M4

import Mathlib

namespace RegretMatching.Main

open MeasureTheory ProbabilityTheory Finset

/-!
Hart and Mas-Colell (2000), §2 and Appendix. Conventions:
* the game: players `ι` (finite), strategy sets `S i` (finite), payoffs `u i : (∀ i, S i) → ℝ`;
  `u i (Function.update s i k)` is the paper's `uⁱ(k, s⁻ⁱ)`;
* time: `play τ` is the paper's `s_{τ+1}`; the history `h_t = (s_1, …, s_t)` is a tuple
  `h : Fin t → ∀ i, S i` with `h τ = s_{τ+1}`; for `t ≥ 1` the last play `s_t` is `h ⟨t - 1, _⟩`;
* every regret quantity is a deterministic function of a finite history.
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- Correlated `ε`-equilibrium (DEFINITION, p. 1129): `ψ ∈ Δ(S)` and for every `i`, `j`, `k`,
`∑_{s : sⁱ = j} ψ(s) [uⁱ(k, s⁻ⁱ) − uⁱ(s)] ≤ ε`. A correlated equilibrium is `IsCorrEq u 0 ψ`. -/
def IsCorrEq (u : ι → (∀ i, S i) → ℝ) (ε : ℝ) (ψ : (∀ i, S i) → ℝ) : Prop :=
  ψ ∈ stdSimplex ℝ (∀ i, S i) ∧
    ∀ (i : ι) (j k : S i),
      ∑ s ∈ univ.filter (fun s : (∀ i, S i) => s i = j),
        ψ s * (u i (Function.update s i k) - u i s) ≤ ε

/-- The history `h_t = (s_1, …, s_t)` of a play: `hist play t ω τ = play τ ω`. -/
def hist {Ω : Type} (play : ℕ → Ω → (∀ i, S i)) (t : ℕ) (ω : Ω) : Fin t → (∀ i, S i) :=
  fun τ => play τ ω

/-- (2.1b), second line: `Dⁱ_t(j, k) = (1/t) ∑_{τ ≤ t : sⁱ_τ = j} [uⁱ(k, s⁻ⁱ_τ) − uⁱ(s_τ)]`. -/
noncomputable def regretD (u : ι → (∀ i, S i) → ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) (j k : S i) : ℝ :=
  (1 / (t : ℝ)) * ∑ τ ∈ univ.filter (fun τ : Fin t => h τ i = j),
    (u i (Function.update (h τ) i k) - u i (h τ))

/-- (2.1c): `Rⁱ_t(j, k) = [Dⁱ_t(j, k)]⁺ = max {Dⁱ_t(j, k), 0}`. -/
noncomputable def regretR (u : ι → (∀ i, S i) → ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) (j k : S i) : ℝ :=
  max (regretD u h i j k) 0

/-- (2.3): the empirical distribution `z_t(s) = (1/t) |{τ ≤ t : s_τ = s}|`. -/
noncomputable def empDist {t : ℕ} (h : Fin t → (∀ i, S i)) : (∀ i, S i) → ℝ :=
  fun s => (1 / (t : ℝ)) * ((univ.filter (fun τ : Fin t => h τ = s)).card : ℝ)

/-- The transition matrix `Π_t` of player `i` (p. 1144; row `j` is (2.2) with last strategy `j`):
`Π_t(j, k) = Rⁱ_t(j, k)/μ` for `k ≠ j`, and `Π_t(j, j) = 1 − ∑_{k' ≠ j} Rⁱ_t(j, k')/μ`. -/
noncomputable def PiMat (u : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) : Matrix (S i) (S i) ℝ :=
  fun j k =>
    if k = j then 1 - ∑ k' ∈ univ.erase j, regretR u h i j k' / μ
    else regretR u h i j k / μ

/-- The regret-matching procedure (2.2) as a behaviour profile: `rmMixed u μ p₁ t h i` is the
mixed action `pⁱ_{t+1}` of player `i` at period `t + 1` after the history `h = h_t`.
At `t = 0` it is the arbitrary initial play `p₁`; after `h_{t+1}` it is row `sⁱ_{t+1}` of
`Π_{t+1}`. -/
noncomputable def rmMixed (u : ι → (∀ i, S i) → ℝ) (μ : ℝ) (p₁ : ∀ i, S i → ℝ) :
    (t : ℕ) → (Fin t → (∀ i, S i)) → (i : ι) → S i → ℝ
  | 0, _ => p₁
  | t + 1, h => fun i => PiMat u μ h i (h (Fin.last t) i)

/-- A play of the behaviour profile `σ` on `(Ω, P)`: each event `{s_{t+1} = x}` is measurable,
and given any history `h_t` of positive probability, the law of `s_{t+1}` is the product
`∏_i σ t h_t i (xⁱ)` (players randomize independently given the history). At `t = 0` the
history is empty and the clause gives the law of `s_1`. -/
def IsPlay {Ω : Type} [MeasurableSpace Ω]
    (σ : (t : ℕ) → (Fin t → (∀ i, S i)) → (i : ι) → S i → ℝ)
    (P : Measure Ω) (play : ℕ → Ω → (∀ i, S i)) : Prop :=
  (∀ (t : ℕ) (x : ∀ i, S i), MeasurableSet {ω | play t ω = x}) ∧
    ∀ (t : ℕ) (h : Fin t → (∀ i, S i)), P {ω | hist play t ω = h} ≠ 0 →
      ∀ x : (∀ i, S i),
        (P[|{ω | hist play t ω = h}] {ω | play t ω = x}).toReal = ∏ i, σ t h i (x i)

/-- `P[A | h_t]`: the conditional probability of the event `A` given the history `h_t = h`. -/
noncomputable def condProb {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (play : ℕ → Ω → (∀ i, S i)) {t : ℕ} (h : Fin t → (∀ i, S i)) (A : Set Ω) : ℝ :=
  (P[|{ω | hist play t ω = h}] A).toReal

/-- `E[X | h_t]`: the conditional expectation of the random variable `X` given `h_t = h`. -/
noncomputable def condExpHist {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (play : ℕ → Ω → (∀ i, S i)) {t : ℕ} (h : Fin t → (∀ i, S i)) (X : Ω → ℝ) : ℝ :=
  ∫ ω, X ω ∂(P[|{ω | hist play t ω = h}])

/-- Appendix, p. 1143: `A_t(j, k) = 1_{sⁱ_t = j} [uⁱ(k, s⁻ⁱ_t) − uⁱ(s_t)]`, as a function of
the profile `s = s_t`. -/
noncomputable def regretA (u : ι → (∀ i, S i) → ℝ) (i : ι) (s : ∀ i, S i) (j k : S i) : ℝ :=
  if s i = j then u i (Function.update s i k) - u i s else 0

/-- Appendix, p. 1144: `ρ_t = ∑_{j ≠ k} [D⁺_t(j, k)]²`, the squared Euclidean distance of
`D_t ∈ ℝ^L` to the nonpositive orthant `ℝ^L_−`, `L = {(j, k) : j ≠ k}`. -/
noncomputable def rho (u : ι → (∀ i, S i) → ℝ) (i : ι) {t : ℕ} (h : Fin t → (∀ i, S i)) : ℝ :=
  ∑ p ∈ (univ : Finset (S i)).offDiag, (regretR u h i p.1 p.2) ^ 2

/-- The one-step transition matrix of the auxiliary `ŝ`-process (p. 1144):
`P[ŝ_{t+w} = y | ŝ_{t+w−1} = x] = ∏_{i'} Π^{i'}_t(x^{i'}, y^{i'})`. -/
noncomputable def PhatProd (u : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ} (h : Fin t → (∀ i, S i)) :
    Matrix (∀ i, S i) (∀ i, S i) ℝ :=
  fun x y => ∏ i', PiMat u μ h i' (x i') (y i')

/-- `P[ŝ_{t+w} = s | h_t]` for the stationary `ŝ`-process started at `ŝ_t = x₀` (in use,
`x₀ = s_t`): the `(x₀, s)` entry of the `w`-th power of `PhatProd`. -/
noncomputable def shatProb (u : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (x₀ : ∀ i, S i) (w : ℕ) (s : ∀ i, S i) : ℝ :=
  (PhatProd u μ h ^ w) x₀ s

/-- p. 1144: `α_{t,w}(j, s⁻ⁱ) = ∑_k Π_t(k, j) P[s_{t+w} = (k, s⁻ⁱ) | h_t] − P[s_{t+w} = (j, s⁻ⁱ) | h_t]`.
The `i`-th coordinate of `s` is ignored. With `h = h_t`, `t ≥ 1`, `s_{t+w}` is `play (t + w - 1)`. -/
noncomputable def alpha (u : ι → (∀ i, S i) → ℝ) (μ : ℝ) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (play : ℕ → Ω → (∀ i, S i)) {t : ℕ} (h : Fin t → (∀ i, S i))
    (i : ι) (w : ℕ) (j : S i) (s : ∀ i, S i) : ℝ :=
  ∑ k : S i, PiMat u μ h i k j *
      condProb P play h {ω | play (t + w - 1) ω = Function.update s i k}
    - condProb P play h {ω | play (t + w - 1) ω = Function.update s i j}

/-- p. 1145: `α̂_{t,w}(j, s⁻ⁱ) = ∑_k Π_t(k, j) P[ŝ_{t+w} = (k, s⁻ⁱ) | h_t] − P[ŝ_{t+w} = (j, s⁻ⁱ) | h_t]`
for the `ŝ`-process started at `x₀`. The `i`-th coordinate of `s` is ignored. -/
noncomputable def alphaHat (u : ι → (∀ i, S i) → ℝ) (μ : ℝ) {t : ℕ} (h : Fin t → (∀ i, S i))
    (x₀ : ∀ i, S i) (i : ι) (w : ℕ) (j : S i) (s : ∀ i, S i) : ℝ :=
  ∑ k : S i, PiMat u μ h i k j * shatProb u μ h x₀ w (Function.update s i k)
    - shatProb u μ h x₀ w (Function.update s i j)

/-- p. 1145: `t_n = ⌊n^{5/3}⌋`. -/
noncomputable def tSeq (n : ℕ) : ℕ := ⌊(n : ℝ) ^ ((5 : ℝ) / 3)⌋₊

/-- The `w`-step conditional probabilities of a process on a finite set `B` given by its
one-step conditional probabilities `κ n (b₀, …, b_{n−1}) bₙ = P[Xₙ = bₙ | X₀ = b₀, …, X_{n−1} = b_{n−1}]`
(proof of Step M4, p. 1147): `multiStep κ n b 0 b' = κ n b b'`, and
`multiStep κ n b (w+1) b' = ∑_{bₙ} κ n b bₙ · multiStep κ (n+1) (b, bₙ) w b'`, which is
`P[X_{n+w} = b' | X₀ = b₀, …, X_{n−1} = b_{n−1}]`. -/
noncomputable def multiStep {B : Type} [Fintype B] (κ : (n : ℕ) → (Fin n → B) → B → ℝ) :
    (n : ℕ) → (Fin n → B) → ℕ → B → ℝ
  | n, b, 0 => κ n b
  | n, b, w + 1 => fun b' => ∑ bn : B, κ n b bn * multiStep κ (n + 1) (Fin.snoc b bn) w b'

end RegretMatching.Main


