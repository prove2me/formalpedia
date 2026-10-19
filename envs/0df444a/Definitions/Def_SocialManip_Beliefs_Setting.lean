-- Prove2me | Definitions.Def_SocialManip_Beliefs_Setting
-- name    : SocialManip_Beliefs_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:32.074548+00:00
-- url     : https://prove2.me/theorems/0fe746f8-1fff-4d77-b5a1-8153e0de25da
-- title:
--   §2–§3.2, pp. 5–11 — states, signal law (1) with the principal's news, counts, personal experience BU_i, influence matrix W, θ = (1_B, θ_D), the DeGroot belief path
-- statement:
--   The model of a social network of $n$ agents, some Bayesian (stubborn) and some DeGroot, learning a binary state while a principal injects news, from Mostagir, Ozdaglar and Siderius, §2 and §3.2.
--
--   1. **States.** The state of the world is $y\in\{S,R\}$.
--   2. **Organic news, display (1).** An organic signal of agent $i$, whose signal quality is $p_i\in[1/2,1)$, equals the realized state with probability $p_i$:
--   $$\mathbb P(s_{i,\tau}=S\mid y=S)=\mathbb P(s_{i,\tau}=R\mid y=R)=p_i .$$
--   The definition `organicProbS p y` is $\mathbb P(s=S\mid y)$, i.e. $p$ if $y=S$ and $1-p$ if $y=R$.
--   3. **The principal's news (p. 5).** The principal picks an influence state $\hat y$ and an influence strategy $x_i\in\{0,1\}$ for every agent. An agent with $x_i=1$ receives the principal's message, which always equals $\hat y$, with probability $\lambda^*/(\lambda+\lambda^*)$, and organic news with probability $\lambda/(\lambda+\lambda^*)$; an agent with $x_i=0$ always receives organic news. Hence the probability that agent $i$'s signal equals $S$ is
--   $$\frac{\lambda^*\,\mathbf 1[\hat y=S]+\lambda\,\mathbb P(s=S\mid y)}{\lambda+\lambda^*}\quad(x_i=1),\qquad \mathbb P(s=S\mid y)\quad(x_i=0).$$
--   4. **Counts and personal experience (p. 6).** For a signal sequence $h=(h_1,h_2,\dots)$, $z^S_t$ and $z^R_t$ are the numbers of $S$ and $R$ signals among $h_1,\dots,h_t$. The personal experience of an agent with signal quality $p_i$ and prior $q=\mathbb P(y=S)$ is
--   $$\mathrm{BU}_i(S\mid h_{i,t})=\frac{p_i^{z^S_{t}}(1-p_i)^{z^R_{t}}q}{p_i^{z^S_{t}}(1-p_i)^{z^R_{t}}q+p_i^{z^R_{t}}(1-p_i)^{z^S_{t}}(1-q)},\qquad \mathrm{BU}_i(R\mid h_{i,t})=1-\mathrm{BU}_i(S\mid h_{i,t}),$$
--   the face-value Bayesian posterior that ignores the principal.
--   5. **Bayesian belief.** A Bayesian agent knows the realized state $y$: its belief in a state $y'$ is $1$ if $y'=y$ and $0$ otherwise.
--   6. **Influence matrix (p. 7).** Given the set $B$ of Bayesian agents and the weights $\alpha_{ij}$, the matrix $\mathbf W$ has zero rows for the Bayesian agents and row $(\alpha_{ij})_j$ for each DeGroot agent $i\notin B$; in block form $\mathbf W=\begin{pmatrix}0&0\\ \mathbf A_{DB}&\mathbf A_{DD}\end{pmatrix}$. The vector $\boldsymbol\theta=(\mathbf 1_B,\theta_{m+1},\dots,\theta_n)$ (p. 11) has entry $1$ on Bayesian agents and $\theta_i$ on DeGroot agents.
--   7. **Belief path (p. 7).** The belief $\pi_{i,t}(y'\mid y)$ of agent $i$ in state $y'$ at time $t$: a Bayesian agent always holds the correct belief; a DeGroot agent starts at an arbitrary initial value $\pi_{i,0}$ and follows the DeGroot update
--   $$\pi_{i,t+1}=\theta_i\,\mathrm{BU}_i(y'\mid h_{i,t+1})+\sum_{j=1}^n\alpha_{ij}\,\pi_{j,t}.$$
--
--   These objects are shared by every statement of the mission: the goal (Theorem 2) is the almost-sure limit of the belief path, expressed through $\mathbf W$, $\boldsymbol\theta$ and the limit of $\mathrm{BU}_i$.
--
--   **Formalization Note** Agents are `Fin n` and the Bayesian set is a `Finset`; the page's "first $m$ agents are Bayesian" is notation only. Time is discrete ($t\in\mathbb N$): the history at time $t$ is the signals $h_1,\dots,h_t$, and $h_0$ is never read. Bayesian rows of $\mathbf W$ are zero by construction, whatever $\alpha$ holds there. The DeGroot initial belief is a free parameter because the page does not specify it. The weights' nonnegativity and the row sums $\theta_i+\sum_j\alpha_{ij}=1$ are hypotheses of the theorems, not built into these definitions. The division in $\mathrm{BU}_i$ has a positive denominator whenever $0<q<1$ and $0<p_i<1$, and the one in the signal law whenever $\lambda+\lambda^*>0$; the theorems assume both.
-- source:
--   Mostagir, Ozdaglar & Siderius, When Is Society Susceptible to Manipulation?, SSRN preprint 3474643 (version of 2020-06-08; Manag. Sci. 2022, doi:10.1287/mnsc.2021.4265), §2 (display (1) and the principal, p. 5; Agents and BU_i, p. 6; DeGroot update, Network Structure and W, p. 7) and §3.2 (θ = (1_B, θ_{m+1}, …, θ_n), p. 11)

import Mathlib

namespace SocialManip.Beliefs

/-- The binary state of the world `y ∈ {S, R}` (§2, p. 4). -/
inductive State
  | S
  | R
  deriving DecidableEq, Inhabited

instance : Fintype State :=
  ⟨{State.S, State.R}, fun x => by cases x <;> simp⟩

instance : MeasurableSpace State := ⊤

instance : MeasurableSingletonClass State := ⟨fun _ => trivial⟩

instance : DiscreteMeasurableSpace State := ⟨fun _ => trivial⟩

/-- Organic news, display (1), p. 5: the probability that an organic signal equals `S` when the
realized state is `y`, for an agent of signal quality `p`:
`P(s = S | y = S) = p` and `P(s = S | y = R) = 1 - p`. -/
noncomputable def organicProbS (p : ℝ) (y : State) : ℝ :=
  if y = State.S then p else 1 - p

/-- The law of agent `i`'s signal, p. 5: the probability that a signal equals `S`.
A targeted agent (`xi = true`, the page's `x_i = 1`) receives the principal's message, which is
always `yhat`, with probability `λ*/(λ + λ*)`, and organic news, distributed as in (1), with
probability `λ/(λ + λ*)`. An untargeted agent (`xi = false`) always receives organic news. -/
noncomputable def signalProbS (p lam lamStar : ℝ) (y yhat : State) (xi : Bool) : ℝ :=
  if xi then
    (lamStar * (if yhat = State.S then 1 else 0) + lam * organicProbS p y) / (lam + lamStar)
  else organicProbS p y

/-- `z^S_t`: the number of `S` signals among `h 1, …, h t` (p. 6). -/
def countS (h : ℕ → State) (t : ℕ) : ℕ :=
  ((Finset.Icc 1 t).filter (fun τ => h τ = State.S)).card

/-- `z^R_t`: the number of `R` signals among `h 1, …, h t` (p. 6). -/
def countR (h : ℕ → State) (t : ℕ) : ℕ :=
  ((Finset.Icc 1 t).filter (fun τ => h τ = State.R)).card

/-- The personal experience `BU_i(S | h)` of p. 6, as a function of the signal quality `p`, the
prior `q = P(y = S)` and the counts `zS`, `zR`:
`p^{zS} (1-p)^{zR} q / (p^{zS} (1-p)^{zR} q + p^{zR} (1-p)^{zS} (1-q))`. -/
noncomputable def BUS (p q : ℝ) (zS zR : ℕ) : ℝ :=
  p ^ zS * (1 - p) ^ zR * q / (p ^ zS * (1 - p) ^ zR * q + p ^ zR * (1 - p) ^ zS * (1 - q))

/-- `BU_i(y' | h_{i,t})`, p. 6: the personal experience of an agent with signal quality `p` and
signal sequence `h` about state `y'` after the signals `h 1, …, h t`;
`BU_i(R | h) = 1 - BU_i(S | h)`. -/
noncomputable def BU (p q : ℝ) (h : ℕ → State) (t : ℕ) (y' : State) : ℝ :=
  if y' = State.S then BUS p q (countS h t) (countR h t)
  else 1 - BUS p q (countS h t) (countR h t)

/-- The belief in `y'` of an agent who knows the realized state `y`: `1` if `y' = y`, else `0`
(a Bayesian agent, p. 6). -/
noncomputable def truth (y y' : State) : ℝ :=
  if y' = y then 1 else 0

/-- The influence matrix `W` of p. 7: Bayesian rows (`i ∈ B`) are zero, and the DeGroot row `i`
carries the weights `α i j`. -/
def W {n : ℕ} (B : Finset (Fin n)) (α : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if i ∈ B then 0 else α i j

/-- The vector `θ = (1_B, θ_{m+1}, …, θ_n)` of p. 11: `1` on Bayesian agents, `θ i` on DeGroot
agents. -/
def thetaVec {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => if i ∈ B then 1 else θ i

/-- The belief path `π_t(y' | y)` (DeGroot update process, p. 7, with stubborn Bayesians, p. 6).
A Bayesian agent always holds `truth y y'`. A DeGroot agent starts from the arbitrary initial
belief `π₀ i` and updates `π_{i,t+1} = θ_i BU_i(h_{i,t+1}) + ∑_j α_ij π_{j,t}`, where `h i` is
agent `i`'s signal sequence. -/
noncomputable def belief {n : ℕ} (B : Finset (Fin n)) (θ : Fin n → ℝ)
    (α : Matrix (Fin n) (Fin n) ℝ) (p : Fin n → ℝ) (q : ℝ) (h : Fin n → ℕ → State)
    (y y' : State) (π₀ : Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => fun i => if i ∈ B then truth y y' else π₀ i
  | t + 1 => fun i =>
      if i ∈ B then truth y y'
      else θ i * BU (p i) q (h i) (t + 1) y' + ∑ j, α i j * belief B θ α p q h y y' π₀ t j

end SocialManip.Beliefs


