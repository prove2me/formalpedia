-- Prove2me | Definitions.Def_FoundationsRL_RLBasics_Core
-- name    : FoundationsRL_RLBasics_Core
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-18T05:01:08.575064+00:00
-- url     : https://prove2.me/theorems/fcef4acd-8e20-4431-a276-ae7e6c592311
-- title:
--   Finite-horizon episodic MDPs and their value functions
-- statement:
--   This file sets up the finite-horizon episodic MDP framework of Chapter 5 ("Reinforcement Learning: Basics") and the value functions built on top of it.
--
--   An `EpisodicMDP S A H` bundles a finite state space $S$, a finite action space $A$, a horizon $H$, layer-indexed transition kernels `P : ℕ → S → A → S → ℝ` (`P h s a s'` is $P_h(s' \mid s,a)$) and mean rewards `R : ℕ → S → A → ℝ` (`R h s a` is $\mathbb E[r_h(s,a)]$), together with proofs that `P h s a` and the initial state distribution `d1` are genuine probability distributions. Layers are indexed $0,\dots,H-1$ throughout (the book's layer $h$ is `h - 1` here), so `V M π h s` denotes the book's $V^{M,\pi}_{h+1}(s)$ and the terminal convention $V_{H+1} \equiv 0$ becomes `V M π H s = 0`.
--
--   A `Policy S A H` is an (unbundled) function `ℕ → S → A → ℝ`; `IsPolicy H π` asserts membership in $\Pi^{\mathrm{rns}}$, the randomized non-stationary policies of Definition (5.1)–(5.2): at every layer $h<H$ and state, `π h s` is a probability distribution over actions. `detPolicy πdet` is the Dirac policy playing `πdet h s` deterministically.
--
--   For a fixed `M` and `π`, `V M π h s` and `Q M π h s a` are $V^{M,\pi}_h(s)$ and $Q^{M,\pi}_h(s,a)$ (p. 82), computed by backward induction — the Bellman *expectation* equation for a fixed policy, equivalent by the tower property of conditional expectation to the trajectory-sum definition $Q^{M,\pi}_h(s,a) = \mathbb E^{M,\pi}\!\big[\sum_{h'\ge h} r_{h'} \mid s_h=s, a_h=a\big]$ of Eq. (5.1). `stateDist M π s0 h` is the marginal law of the layer-$h$ state when the process starts at `s0` at layer $0$ and follows $\pi$; `stateExp` is the corresponding expectation operator, used to state the roll-in expectations of Lemmas 13–15.
--
--   `bellmanOp M h Qnext` is the Bellman operator $[T^M_h Q_{h+1}](s,a) = \mathbb E\big[r_h(s,a) + \max_{a'} Q_{h+1}(s_{h+1},a') \mid s_h=s,a_h=a\big]$ of Eq. (5.10). Finally, `Qstar` and `Vstar` are the *optimal* value functions of Eq. (5.4), defined as the literal supremum over **all** of $\Pi^{\mathrm{rns}}$ (an infinite-dimensional space, since $|A|\ge 2$ makes `Policy S A H` a continuum) — not via any recursive shortcut — so that Proposition 25 (a separate item) is a genuine theorem about this supremum, not a restatement of a recursive definition.
--
--   **Formalization Note** Since every formula in this chapter uses the reward distribution $R_h(s,a) \in \Delta(\mathbb R)$ of the book's Definition (5.1) only through its mean (by linearity of expectation), `EpisodicMDP.R` records that mean directly rather than carrying the full distribution; this changes no theorem's content. `IsArgmax f a` formalizes "$a \in \arg\max_{a'} f(a')$" as $\forall a', f(a') \le f(a)$.
--
--   **Moderator's note.** (i) $Q^{M,\star}_h$ is the supremum over *valid* policies $\pi \in \Pi^{\mathrm{rns}}$ (those satisfying `IsPolicy`), as in Eq. (5.4); over all real-valued weight functions the set is unbounded and Lean's real supremum would return $0$. (ii) $Q^{M,\pi}_h \equiv 0$ for $h \ge H$, the book's $Q_{H+1} \equiv 0$, so the Bellman recursion of Proposition 25 is exact at the last layer.
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, p. 81–82, §5.1–5.2 and Eqs. (5.1)–(5.4), (5.10)

import Mathlib

/-!
Finite-horizon episodic MDPs (Foster & Rakhlin, §5.1), the layer-`h` state/state-action
value functions for a fixed randomized non-stationary policy, the optimal (sup-over-all-
policies) value functions of Eq. (5.4), and the Bellman operator of Eq. (5.10).

Layers are indexed `0`-based throughout this file (`ℓ = 0, …, H-1` corresponds to the
book's `h = ℓ+1 = 1, …, H`); `V _ _ H _ = 0` matches the book's terminal convention
`V_{H+1} ≡ 0`. Since every value/expectation formula in this chapter uses the reward
distribution `R_h(s,a) ∈ Δ(ℝ)` only through its mean, `EpisodicMDP.R` records that mean
directly (equivalent by linearity of expectation to carrying the full distribution).
-/

namespace FoundationsRL.RLBasics

/-- A finite-horizon episodic MDP `(S, A, {P_h}, {R_h}, d1)` with horizon `H`
(Foster–Rakhlin, arXiv:2312.16730v1, p. 81, §5.1). `R h s a` is the mean of the reward
distribution `R_h(s,a)`; `P h s a s'` is the transition probability `P_h(s'∣s,a)`. -/
structure EpisodicMDP (S A : Type*) [Fintype S] [Fintype A] (H : ℕ) where
  P : ℕ → S → A → S → ℝ
  R : ℕ → S → A → ℝ
  d1 : S → ℝ
  P_nonneg : ∀ h s a s', 0 ≤ P h s a s'
  P_sum_one : ∀ h s a, ∑ s' : S, P h s a s' = 1
  d1_nonneg : ∀ s, 0 ≤ d1 s
  d1_sum_one : ∑ s : S, d1 s = 1

/-- A randomized, non-stationary policy `π ∈ Π^{rns}`: `π h s a` is the probability of
action `a` in state `s` at layer `h`. -/
def Policy (S A : Type*) (H : ℕ) := ℕ → S → A → ℝ

/-- `π ∈ Π^{rns}`: at every layer `h < H` and state, `π h s` is a probability distribution
over actions. -/
def IsPolicy {S A : Type*} [Fintype A] (H : ℕ) (π : Policy S A H) : Prop :=
  ∀ h, h < H → ∀ s : S, (∀ a : A, 0 ≤ π h s a) ∧ ∑ a : A, π h s a = 1

/-- `a` maximizes `f`, i.e. `a ∈ argmax f` (Foster–Rakhlin write `a ∈ arg max_a f(a)`). -/
def IsArgmax {A : Type*} (f : A → ℝ) (a : A) : Prop := ∀ a', f a' ≤ f a

/-- The Dirac policy that plays `πdet h s` deterministically. -/
def detPolicy {S A : Type*} [DecidableEq A] {H : ℕ} (πdet : ℕ → S → A) : Policy S A H :=
  fun h s a => if a = πdet h s then 1 else 0

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] [DecidableEq S] {H : ℕ}

/-- `valueAux M π k s = V^{M,π}_{H-k}(s)`: the value with `k` layers remaining
(base case `k = 0` is the book's `V_{H+1} ≡ 0`). -/
noncomputable def valueAux (M : EpisodicMDP S A H) (π : Policy S A H) : ℕ → S → ℝ
  | 0, _ => 0
  | (k + 1), s =>
      let ℓ := H - 1 - k
      ∑ a : A, π ℓ s a * (M.R ℓ s a + ∑ s' : S, M.P ℓ s a s' * valueAux M π k s')

/-- `V^{M,π}_h(s)` (Foster–Rakhlin, p. 82), `0`-indexed: `V M π h s` is the book's
`V^{M,π}_{h+1}(s)`. `V M π H s = 0` is the terminal convention. -/
noncomputable def V (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (s : S) : ℝ :=
  valueAux M π (H - h) s

/-- `Q^{M,π}_h(s,a)` (Foster–Rakhlin, p. 82), `0`-indexed for `h < H`; `0` at and beyond the
horizon, the book's `Q_{H+1} ≡ 0`. -/
noncomputable def Q (M : EpisodicMDP S A H) (π : Policy S A H) (h : ℕ) (s : S) (a : A) : ℝ :=
  if h < H then M.R h s a + ∑ s' : S, M.P h s a s' * V M π (h + 1) s' else 0

/-- Marginal law of the layer-`h` state, starting from `s0` at layer `0` and following `π`
thereafter (`0`-indexed: `stateDist M π s0 h` is the law of the book's `s_{h+1}`). -/
noncomputable def stateDist (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S) : ℕ → S → ℝ
  | 0, s => if s = s0 then 1 else 0
  | (h + 1), s =>
      ∑ sp : S, stateDist M π s0 h sp * ∑ a : A, π h sp a * M.P h sp a s

/-- Expectation of `f` under the layer-`h` state marginal `stateDist M π s0 h`. -/
noncomputable def stateExp (M : EpisodicMDP S A H) (π : Policy S A H) (s0 : S) (h : ℕ)
    (f : S → ℝ) : ℝ :=
  ∑ s : S, stateDist M π s0 h s * f s

/-- The Bellman operator `T^M_h` (Eq. (5.10)) applied to a `Q`-function `Qnext : S → A → ℝ`
representing `Q_{h+1}`. -/
noncomputable def bellmanOp (M : EpisodicMDP S A H) (h : ℕ) (Qnext : S → A → ℝ) (s : S)
    (a : A) : ℝ :=
  M.R h s a + ∑ s' : S, M.P h s a s' * ⨆ a' : A, Qnext s' a'

/-- `Q^{M,⋆}_h(s,a) = max_{π ∈ Π^{rns}} E^{M,π}[· ∣ s_h = s, a_h = a]` (Eq. (5.4)): the supremum
over *valid* randomized non-stationary policies (`IsPolicy`), a bounded set, so this is a
genuine maximum (attained by a deterministic policy). -/
noncomputable def Qstar (M : EpisodicMDP S A H) (h : ℕ) (s : S) (a : A) : ℝ :=
  ⨆ π : {π : Policy S A H // IsPolicy H π}, Q M π.1 h s a

/-- `V^{M,⋆}_h(s) = max_a Q^{M,⋆}_h(s,a)` (Eq. (5.4)). -/
noncomputable def Vstar (M : EpisodicMDP S A H) (h : ℕ) (s : S) : ℝ :=
  ⨆ a : A, Qstar M h s a

end FoundationsRL.RLBasics


