-- Prove2me | Definitions.Def_TimeDepFolk_Asymptotic_Model
-- name    : TimeDepFolk_Asymptotic_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:37.245545+00:00
-- url     : https://prove2.me/theorems/4890fa09-5ce7-4ec0-a33e-7fa3ca1d5594
-- title:
--   §2–§3, pp. 8–12 — evaluations, patience, θ[T]; the repeated game with perfect monitoring: histories, behavior strategies, γ_θ, σ|h_T, SPE, E_θ; minmax levels v^i and F
-- statement:
--   This file fixes the model of repeated games with time-dependent discounting of X. Li (§2–§3), together with the auxiliary quantities used in the proof of the asymptotic perfect folk theorem (§5.1 and Appendix 7.1). The stage game is a finite game in the sense of the referenced definition `agt_games`: a finite set of players $I$, a finite action set $A^i$ for each player, and stage payoffs $g^i : A=\prod_{i\in I}A^i \to \mathbb R$, written $g=(g^i)_{i\in I}$; mixed actions are lotteries (nonnegative weights summing to one), and the players randomize independently.
--
--   1. **Evaluation** (Definition 2.1). A sequence $(\theta_t)_{t\ge1}$ in $[0,1]$ that is decreasing in $t$ and satisfies $\sum_{t\ge1}\theta_t=1$; $\theta_t$ is the weight of the stage-$t$ payoff.
--   2. **Patient evaluations** (Definition 2.2). A sequence $(\theta^k)_{k\ge1}$ of evaluations is patient if
--   $$\lim_{k\to\infty}\frac{\theta^k_t}{\theta^k_{t+1}}=1\quad\text{uniformly in } t\ge1 .$$
--   3. **Continuation evaluation** (Notation, p. 11). For $T\ge1$, $\theta_t[T]=\theta_{T-1+t}\big/\sum_{s\ge T}\theta_s$, the weights of the subgame that starts at stage $T$.
--   4. **Histories and behavior strategies.** A history of $t$ played stages is $(a_1,\dots,a_t)\in A^t$. A behavior strategy $\sigma^i$ of player $i$ assigns a mixed action in $\Delta(A^i)$ to every finite history (perfect observation of past actions). The probability that the first $T$ stages produce the history $(a_1,\dots,a_T)$ under a profile $\sigma$ is $\prod_{s=1}^{T}\prod_{i\in I}\sigma^i_s(a_1,\dots,a_{s-1})(a^i_s)$.
--   5. **Payoff.** For weights $w=(w_t)_{t\ge1}$, $\gamma^i_w(\sigma)=\sum_{t\ge1}w_t\,\mathbb E_\sigma[g^i(a_t)]$, which is the $\theta$-evaluated payoff $\gamma_\theta(\sigma)=\mathbb E_\sigma\big[\sum_t\theta_t g(a_t)\big]$ of p. 11 when $w=\theta$. For a pure action sequence $h_\infty=(a_t)$, $\gamma_w(h_\infty)=\sum_t w_t g(a_t)\in\mathbb R^I$.
--   6. **Induced strategy** (p. 11). After a history $h_T$ of $T-1$ played stages, $(\sigma|_{h_T})_s(h_s)=\sigma_{T+s-1}(h_Th_s)$, with $h_Th_s$ the concatenation.
--   7. **Nash and subgame perfect equilibrium** (Definitions 2.3–2.4). $\sigma$ is a Nash equilibrium of the game with weights $w$ if $\gamma^i_w(\tau^i,\sigma^{-i})\le\gamma^i_w(\sigma)$ for every player $i$ and every behavior strategy $\tau^i$. It is a subgame perfect equilibrium of $\Gamma_\theta$ if, for every $T\ge1$ and every history $h_T$ (on or off the path), $\sigma|_{h_T}$ is a Nash equilibrium of the subgame $\Gamma_{\theta[T]}(h_T)$. $E_\theta\subseteq\mathbb R^I$ is the set of payoff vectors $\gamma_\theta(\sigma)$ of subgame perfect equilibria $\sigma$.
--   8. **Minmax levels and $\mathcal F$** (p. 12).
--   $$v^i=\min_{s\in\prod_{j\ne i}\Delta(A^j)}\ \max_{a^i\in A^i}\ \sum_{a^{-i}\in A^{-i}}s(a^{-i})\,g^i(a^i,a^{-i}),$$
--   the minimum being over **independent** mixed actions of the other players (no correlation); $S=\operatorname{co}\{g(a):a\in A\}$ is the feasible set, and $\mathcal F=\{x\in S: x^i\ge v^i\ \forall i\}$ the set of feasible and individually rational payoff vectors.
--   9. **One-shot deviation** (§5.1 Part C). $(a^i,\sigma^i)$: player $i$ plays the pure action $a^i$ at the first stage of the (sub)game and follows $\sigma^i$ afterwards; the others follow $\sigma^{-i}$.
--   10. **Punishment length and $z$** (§5.1, pp. 17–18). For $\kappa,\eta>0$, a positive integer $L$ satisfies (5.1) at stage $T$ if $3\eta/\kappa\le\sum_{t=1}^{L+1}\theta_t[T]<4\eta/\kappa$. For weights $w$ and actions $(a_1,\dots,a_L)$, $\diamondsuit=\sum_{t=1}^{L}w_t\big/\big(1-\sum_{t=1}^{L}w_t\big)$, $p^j=\sum_{t=1}^{L}w_tg^j(a_t)\big/\sum_{t=1}^{L}w_t$ and $z^j=\diamondsuit\times p^j$.
--   11. **Edge matrices** (Appendix 7.1, p. 33). For points $x_1,\dots,x_L\in\mathbb R^I$ and an index $\ell$, $X_\ell=(x_s-x_\ell)_{s\ne\ell}$ is the $I\times(L-1)$ matrix of edge vectors, and $R_\ell=\|X_\ell^T\|_\infty\,\|(X_\ell X_\ell^T)^{-1}\|_\infty$ with $\|\cdot\|_\infty$ the maximum-row-sum norm.
--
--   These objects carry every statement of the mission: the goal is that $E_{\theta^k}$ converges to $\mathcal F$ in Hausdorff distance for patient $(\theta^k)$.
--
--   **Formalization Note.** Stages are 0-based: Lean stage $s\in\mathbb N$ is the paper's $t=s+1$, so `θ s` is $\theta_{s+1}$, a `History A n` of $n$ played stages is an element of the paper's $\mathcal H_{n+1}$, and `cont θ n` is the paper's $\theta[n+1]$ (the subgame after $n$ played stages). `cont w n s = w (n+s) / ∑' r, w (n+r)` returns $0$ when the tail sum is $0$; for a patient sequence this cannot happen once $k$ is large, and a zero-weight subgame imposes only $0\le0$. In `IsPatient`, Lean's $x/0=0$ makes the ratio $0$ when $\theta^k_{t+1}=0$, so uniform convergence to $1$ forces $\theta^k_t>0$ for all $t$ once $k$ is large, as the page implicitly assumes. With finite action sets there is no measure theory: $\mathbb E_\sigma[g^i(a_s)]$ is a finite sum over histories of length $s+1$, and the payoff is the series $\sum_s w_s\,\mathbb E_\sigma[g^i(a_s)]$, equal to $\mathbb E_\sigma[\sum_t\theta_tg(a_t)]$ by dominated convergence (payoffs are bounded and $\sum\theta=1$). Mixed actions are `AGT.IsLottery` weight functions and the expected stage payoff is `AGT.expectedPayoff` from `agt_games`. `minmax` is an infimum over the nonempty set of lottery profiles (component $i$ is overwritten by a point mass, so only the others' mixed actions matter) of a finite maximum; the set is bounded below by $-\max|g|$, so the real infimum is the paper's minimum and not a junk value. `IsSPE` quantifies over every history of every length, the empty one included (the paper's $T=1$, $\mathcal H_1=\{\emptyset\}$), and deviations range over all behavior strategies, not only one-shot ones. Payoff vectors live in `I → ℝ`, whose Mathlib norm is the sup norm $\|\cdot\|_\infty$ of the paper. `diamond`, `avgPay` and `zvec` divide by $1-\sum w_t$ and $\sum w_t$; they are used only under (5.1), where $0<\sum w_t<1/2$. `rowSumNorm` is $\sup_r\sum_c|M_{rc}|$ (taken as $0$ for a matrix with no rows), and `Rcoef` uses Mathlib's matrix inverse, which is the true inverse whenever $X_\ell X_\ell^T$ is invertible.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), pp. 8–12, Definitions 2.1–2.4, Notation pp. 11–12; §5.1 Part A–C, pp. 17–20, (5.1), z^j_i; §7.1, p. 33, X_ℓ and R_ℓ

import Mathlib
import Definitions.Def_agt_games

namespace TimeDepFolk.Asymptotic

open Finset

/-- Definition 2.1 (p. 9): an evaluation, a nonnegative decreasing sequence with sum `1`.
Stages are 0-based: `θ 0` is the paper's `θ_1`. -/
structure Evaluation where
  θ : ℕ → ℝ
  nonneg : ∀ t, 0 ≤ θ t
  antitone : Antitone θ
  hasSum : HasSum θ 1

/-- Definition 2.2 (p. 9): `θ^k_t / θ^k_{t+1} → 1` as `k → ∞`, uniformly in `t`. -/
def IsPatient (θ : ℕ → Evaluation) : Prop :=
  TendstoUniformly (fun k t => (θ k).θ t / (θ k).θ (t + 1)) (fun _ => (1 : ℝ)) Filter.atTop

/-- The weights `θ[n+1]` of the paper (Notation, p. 11): the continuation of `w` after `n` played
stages, `s ↦ w (n + s) / ∑_r w (n + r)`. It is `0` when the tail sum is `0`. -/
noncomputable def cont (w : ℕ → ℝ) (n : ℕ) : ℕ → ℝ :=
  fun s => w (n + s) / ∑' r, w (n + r)

section Game

variable {I : Type*} [Fintype I] [DecidableEq I] {A : I → Type*}
  [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- A history of `t` played stages, `(a_1, …, a_t)`: the paper's `H_{t+1}`. -/
abbrev History (A : I → Type*) (t : ℕ) := Fin t → (∀ i, A i)

/-- The first `s` stages of a history of `t ≥ s` stages. -/
def History.take {t : ℕ} (h : History A t) (s : ℕ) (hs : s ≤ t) : History A s :=
  fun r => h (Fin.castLE hs r)

/-- A behavior strategy of player `i` (p. 10): a mixed action (a lottery on `A i`) after every
finite history. -/
structure Strategy (A : I → Type*) [∀ i, Fintype (A i)] (i : I) where
  act : (t : ℕ) → History A t → A i → ℝ
  act_mem : ∀ t h, AGT.IsLottery (act t h)

/-- A behavior strategy profile `σ ∈ Σ`. -/
abbrev Profile (A : I → Type*) [∀ i, Fintype (A i)] := ∀ i, Strategy A i

/-- `P_σ` of the first `T` stages being `h`: the players mix independently at every stage. -/
noncomputable def histProb (σ : Profile A) {T : ℕ} (h : History A T) : ℝ :=
  ∏ s : Fin T, ∏ i, (σ i).act s (h.take s (Nat.le_of_lt s.isLt)) (h s i)

/-- `E_σ[g^i(a_s)]`, the expected payoff of player `i` at stage `s` (the paper's stage `s + 1`). -/
noncomputable def stageExp (g : I → (∀ i, A i) → ℝ) (σ : Profile A) (i : I) (s : ℕ) : ℝ :=
  ∑ h : History A (s + 1), histProb σ h * g i (h (Fin.last s))

/-- `γ^i_w(σ) = ∑_s w_s E_σ[g^i(a_s)]` (p. 11). -/
noncomputable def payoff (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (σ : Profile A) (i : I) : ℝ :=
  ∑' s, w s * stageExp g σ i s

/-- `σ|h`: the profile induced in the subgame after the history `h` of `n` played stages
(p. 11): `(σ|h)_s(h') = σ_{n+s}(h h')`. -/
def restrict (σ : Profile A) {n : ℕ} (h : History A n) : Profile A :=
  fun i => ⟨fun s h' => (σ i).act (n + s) (Fin.append h h'), fun _ _ => (σ i).act_mem _ _⟩

/-- Definition 2.3 (p. 11): `σ` is a Nash equilibrium of the repeated game with weights `w`;
deviations range over all behavior strategies. -/
def IsNash (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (σ : Profile A) : Prop :=
  ∀ i (τ : Strategy A i), payoff g w (Function.update σ i τ) i ≤ payoff g w σ i

/-- Definition 2.4 (p. 12): `σ|h` is a Nash equilibrium of the subgame `Γ_{θ[n+1]}(h)` for every
history `h` of every length `n` (the empty history included). -/
def IsSPE (g : I → (∀ i, A i) → ℝ) (θ : Evaluation) (σ : Profile A) : Prop :=
  ∀ (n : ℕ) (h : History A n), IsNash g (cont θ.θ n) (restrict σ h)

/-- `E_θ` (p. 12): the set of subgame perfect equilibrium payoff vectors. -/
def eqPayoffs (g : I → (∀ i, A i) → ℝ) (θ : Evaluation) : Set (I → ℝ) :=
  {x | ∃ σ : Profile A, IsSPE g θ σ ∧ ∀ i, payoff g θ.θ σ i = x i}

omit [DecidableEq I] [∀ i, DecidableEq (A i)] in
/-- A profile of lotteries for all players (component `i` is ignored where the others' mixed
actions are meant). -/
def IsMixed (μ : ∀ j, A j → ℝ) : Prop := ∀ j, AGT.IsLottery (μ j)

/-- `v^i` (p. 12): the minimum over independent mixed actions of the others of the maximum over
the pure actions `a^i` of player `i`'s expected payoff. Component `i` of `μ` is overwritten. -/
noncomputable def minmax (g : I → (∀ i, A i) → ℝ) (i : I) : ℝ :=
  ⨅ μ : {μ : ∀ j, A j → ℝ // IsMixed μ},
    ⨆ ai : A i, AGT.expectedPayoff g (Function.update μ.1 i (Pi.single ai 1)) i

omit [DecidableEq I] [∀ i, DecidableEq (A i)] in
/-- `S = co{g(a) | a ∈ A}` (p. 12). -/
def feasible (g : I → (∀ i, A i) → ℝ) : Set (I → ℝ) :=
  convexHull ℝ (Set.range fun a : (∀ j, A j) => fun i => g i a)

/-- `F = {x ∈ S | x^i ≥ v^i ∀ i}` (p. 12). -/
def F (g : I → (∀ i, A i) → ℝ) : Set (I → ℝ) :=
  {x | x ∈ feasible g ∧ ∀ i, minmax g i ≤ x i}

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] in
/-- `γ_w(h_∞) = ∑_s w_s g(a_s)` for a pure action sequence (p. 11). -/
noncomputable def purePayoff (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ) (h : ℕ → ∀ i, A i) :
    I → ℝ :=
  fun i => ∑' s, w s * g i (h s)

omit [Fintype I] [DecidableEq I] in
/-- The point mass on a pure action is a lottery. -/
theorem isLottery_pure {i : I} (a : A i) : AGT.IsLottery (Pi.single a (1 : ℝ) : A i → ℝ) := by
  refine ⟨fun b => ?_, ?_⟩
  · by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  · simp

/-- The one-shot deviation of player `i` to the pure action `a` at the first stage of the
(sub)game, followed by `σ^i` (§5.1 Part C, p. 20). -/
def oneShot (σ : Profile A) (i : I) (a : A i) : Profile A :=
  Function.update σ i
    ⟨fun t h => if t = 0 then Pi.single a 1 else (σ i).act t h, fun t h => by
      by_cases ht : t = 0
      · simp only [ht, if_true]; exact isLottery_pure a
      · simp only [ht, if_false]; exact (σ i).act_mem t h⟩

end Game

section Punish

/-- (5.1), p. 17: `L` is a punishment length at the subgame after `n` played stages (the paper's
`T = n + 1`): `L ≥ 1` and `3η/κ ≤ ∑_{t=1}^{L+1} θ_t[T] < 4η/κ`. -/
def IsPunLength (θ : Evaluation) (κ η : ℝ) (n L : ℕ) : Prop :=
  0 < L ∧ 3 * η / κ ≤ ∑ t ∈ range (L + 1), cont θ.θ n t ∧
    ∑ t ∈ range (L + 1), cont θ.θ n t < 4 * η / κ

/-- `♦` of p. 18: `∑_{t=1}^{L} w_t / (1 − ∑_{t=1}^{L} w_t)`. -/
noncomputable def diamond (w : ℕ → ℝ) (L : ℕ) : ℝ :=
  (∑ t ∈ range L, w t) / (1 - ∑ t ∈ range L, w t)

/-- `p^j(a_1, …, a_L)` of p. 18: the `w`-weighted average payoff of player `j` over `L` stages. -/
noncomputable def avgPay {I : Type*} {A : I → Type*} (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ)
    {L : ℕ} (a : Fin L → ∀ i, A i) (j : I) : ℝ :=
  (∑ t : Fin L, w t * g j (a t)) / ∑ t ∈ range L, w t

/-- `z^j(a_1, …, a_L) = ♦ × p^j(a_1, …, a_L)` of p. 18. -/
noncomputable def zvec {I : Type*} {A : I → Type*} (g : I → (∀ i, A i) → ℝ) (w : ℕ → ℝ)
    {L : ℕ} (a : Fin L → ∀ i, A i) (j : I) : ℝ :=
  diamond w L * avgPay g w a j

end Punish

section Matrix

/-- The max-row-sum norm `‖M‖_∞` of a real matrix (`0` for a matrix with no rows). -/
noncomputable def rowSumNorm {m n : Type*} [Fintype n] (M : Matrix m n ℝ) : ℝ :=
  ⨆ r, ∑ c, |M r c|

/-- `X_ℓ = (x_s − x_ℓ)_{s ≠ ℓ}` (p. 33), the `ι × (L − 1)` matrix of edge vectors at `x_ℓ`. -/
def edgeMatrix {ι : Type*} {L : ℕ} (x : Fin L → ι → ℝ) (ℓ : Fin L) :
    Matrix ι {s : Fin L // s ≠ ℓ} ℝ :=
  Matrix.of fun i s => x s.1 i - x ℓ i

/-- `R_ℓ = ‖X_ℓ^T‖_∞ ‖(X_ℓ X_ℓ^T)^{-1}‖_∞` (p. 33). -/
noncomputable def Rcoef {ι : Type*} [Fintype ι] [DecidableEq ι] {L : ℕ} (x : Fin L → ι → ℝ)
    (ℓ : Fin L) : ℝ :=
  rowSumNorm (edgeMatrix x ℓ).transpose *
    rowSumNorm ((edgeMatrix x ℓ * (edgeMatrix x ℓ).transpose)⁻¹)

end Matrix

end TimeDepFolk.Asymptotic


