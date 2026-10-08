-- Prove2me | Definitions.Def_RobustDP_FiniteHorizon_Value
-- name    : RobustDP_FiniteHorizon_Value
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:51.704852+00:00
-- url     : https://prove2.me/theorems/c5825aa1-cbd8-43ba-ae78-b036734c8156
-- title:
--   Policies, the rectangular adversary, and the robust values $V^\pi_n$, $V^*_n$ (and optimistic $\bar V^\pi_n$, $\bar V^*_n$)
-- statement:
--   Fix a finite horizon AMDP with horizon $N$, admissible actions $\mathcal A_t(s)$, ambiguity sets $\mathcal P_t(s,a)$ and rewards $r_t$, $r_N$.
--
--   **Policies.** A (history dependent, randomized) decision rule at epoch $t$ maps each history $h_t$ to a probability measure $d_t(h_t)$ on actions supported on $\mathcal A_t(s_t)$. A policy is a sequence $\pi=(d_t)_{t}$ of decision rules; $\Pi$ is the set of all policies. A policy is *deterministic* ($\pi\in\Pi_D$) if every $d_t(h_t)$, $t<N$, is a point mass, and *deterministic Markov* ($\pi\in\Pi_{MD}$) if moreover $d_t(h_t)$ is the point mass at an action $f_t(s_t)$ that depends on the current state alone.
--
--   **The adversary.** Under Rectangularity (Assumption 1), the set $\mathcal T^\pi$ of path measures consistent with $\pi$ is the product $\mathcal T^{d_0}\times\cdots\times\mathcal T^{d_{N-1}}$ of (2)–(3): an element is a choice, for every epoch $t<N$, every history $h_t$ and every admissible action $a$, of a measure $p_{h_t,a}\in\mathcal P_t(s_t,a)$. A *one-epoch selection* at epoch $t$ in state $s$ is a family $(p_{sa})_{a\in\mathcal A_t(s)}$ with $p_{sa}\in\mathcal P_t(s,a)$. For a measure $p$ on states, $E^p[f]=\sum_{s}p(s)f(s)$.
--
--   **Expected reward.** Under the path measure $\mathbf P(h_N)=\prod_t q_{d_t(h_t)}(a_t)\,p_{h_t,a_t}(s_{t+1})$, the expected reward from history $h_n$ is
--   $$
--   E^{\mathbf P}\Big[\sum_{t=n}^{N-1} r_t(s_t,a_t,s_{t+1})+r_N(s_N)\Big],
--   $$
--   computed epoch by epoch: with no epochs left it is $r_N(s_n)$, and otherwise it is $\sum_a d_n(h_n)(a)\sum_{s}p_{h_n,a}(s)\big[r_n(s_n,a,s)+(\text{expected reward from }(h_n,a,s))\big]$.
--
--   **Values.** The robust value of a policy (8) and the robust value function (10) are
--   $$
--   V^\pi_n(h_n)=\inf_{\mathbf P\in\mathcal T^\pi_n}E^{\mathbf P}\Big[\sum_{t=n}^{N-1} r_t+r_N(s_N)\Big],\qquad V^*_n(h_n)=\sup_{\pi\in\Pi_n}V^\pi_n(h_n),
--   $$
--   and the optimistic values (6)–(7) replace the infimum over $\mathcal T^\pi_n$ by a supremum: $\bar V^\pi_n(h_n)=\sup_{\mathbf P\in\mathcal T^\pi_n}E^{\mathbf P}[\cdots]$ and $\bar V^*_n(h_n)=\sup_{\pi\in\Pi_n}\bar V^\pi_n(h_n)$.
--
--   These are the objects of Theorems 1–3 and Corollary 1.
--
--   **Formalization Note** A policy is a decision rule for every epoch $t\in\mathbb N$; the admissibility constraint is imposed for $t<N$ only, and $V^\pi_n$ uses only $d_n,\dots,d_{N-1}$, so the supremum over $\Pi$ equals the supremum over the page's $\Pi_n$ (policies for epochs $t\ge n$). Likewise one adversary is a choice for every epoch, and only the choices at histories extending $h_n$ matter. The expectation is written as iterated sums over the countable action and state sets (the product structure (3)); with bounded rewards every sum converges absolutely and all values lie in $[-(N-n+1)R,(N-n+1)R]$, so the real infima and suprema are of nonempty bounded families. For $n\ge N$ the expected reward is $r_N(s_n)$.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), pp. 4–5, Section 2, eqs. (1)–(10) and Assumption 1 (Rectangularity)

import Mathlib
import Definitions.Def_RobustDP_FiniteHorizon_AMDP

namespace RobustDP.FiniteHorizon

variable {S A : Type*} [Countable S] [Countable A]

/-- A history dependent randomized decision rule sequence: at every epoch `t` and history
`h_t`, a probability measure `d_t(h_t) ∈ M(A)`; it is admissible if, for `t < N`, it puts all its
mass on `A_t(s_t)`. -/
def IsPolicy (M : AMDP S A) (d : (t : ℕ) → History S A t → PMF A) : Prop :=
  ∀ t < M.N, ∀ h : History S A t, ∀ a ∈ (d t h).support, a ∈ M.Aset t h.cur

/-- The set `Π` of all history dependent randomized policies `π = (d_t : t ∈ T)`. -/
def Policy (M : AMDP S A) := {d : (t : ℕ) → History S A t → PMF A // IsPolicy M d}

/-- `π ∈ Π_D`: every decision rule `d_t`, `t < N`, is deterministic (a point mass). -/
def IsDeterministic {M : AMDP S A} (π : Policy M) : Prop :=
  ∀ t < M.N, ∀ h : History S A t, ∃ a : A, π.1 t h = PMF.pure a

/-- `π ∈ Π_{MD}`: every decision rule `d_t`, `t < N`, is deterministic and Markovian (a point mass
at an action depending on the current state `s_t` alone). -/
def IsDetMarkov {M : AMDP S A} (π : Policy M) : Prop :=
  ∃ f : ℕ → S → A, ∀ t < M.N, ∀ h : History S A t, π.1 t h = PMF.pure (f t h.cur)

/-- The adversary's choices, i.e. one element of `T^π = T^{d_0} × ⋯ × T^{d_{N-1}}` (Assumption 1,
(2)–(3)): for every epoch `t < N`, every history `h_t` and every admissible action `a`, a
conditional measure `p_{h_t, a} ∈ P_t(s_t, a)` for the next state. -/
def Adversary (M : AMDP S A) :=
  {σ : (t : ℕ) → History S A t → A → PMF S //
    ∀ t < M.N, ∀ h : History S A t, ∀ a ∈ M.Aset t h.cur, σ t h a ∈ M.P t h.cur a}

/-- One-epoch selection at epoch `t` in state `s`: a family `(p_{s a})_{a ∈ A_t(s)}` with
`p_{s a} ∈ P_t(s, a)` (the epoch-`t` factor of (2) at a fixed history). -/
def Selection (M : AMDP S A) (t : ℕ) (s : S) :=
  {p : A → PMF S // ∀ a ∈ M.Aset t s, p a ∈ M.P t s a}

/-- `E^p[f] = Σ_s p(s) f(s)` for a probability measure `p` on the countable set `S`. -/
noncomputable def expect (p : PMF S) (f : S → ℝ) : ℝ :=
  ∑' s, (p s).toReal * f s

/-- Expected total reward `E^P[Σ_{t=n}^{N-1} r_t(s_t, a_t, s_{t+1}) + r_N(s_N)]` from history
`h_n` when `k` epochs remain, under the decision rules `d` and the adversary's choices `σ`. The
path measure is the product `P(h_N) = ∏_t q_{d_t(h_t)}(a_t) p_{h_t a_t}(s_{t+1})` of (2)–(3),
and the expectation is computed epoch by epoch. -/
noncomputable def expTail (M : AMDP S A) (d : (t : ℕ) → History S A t → PMF A)
    (σ : (t : ℕ) → History S A t → A → PMF S) : (k n : ℕ) → History S A n → ℝ
  | 0, _, h => M.rN h.cur
  | k + 1, n, h =>
      ∑' a, (d n h a).toReal *
        expect (σ n h a) (fun s => M.r n h.cur a s + expTail M d σ k (n + 1) (h.extend a s))

/-- `E^P[Σ_{t=n}^{N-1} r_t(s_t, d_t(h_t), s_{t+1}) + r_N(s_N)]` for the policy `π` and the
adversary `σ ∈ T^π_n`, starting from the history `h_n` (for `n ≥ N` it is `r_N(s_n)`). -/
noncomputable def expectedReward (M : AMDP S A) (π : Policy M) (σ : Adversary M) (n : ℕ)
    (h : History S A n) : ℝ :=
  expTail M π.1 σ.1 (M.N - n) n h

/-- The robust value of a policy, (8): `V^π_n(h_n) = inf_{P ∈ T^π_n} E^P[⋯]`. -/
noncomputable def V (M : AMDP S A) (π : Policy M) (n : ℕ) (h : History S A n) : ℝ :=
  ⨅ σ : Adversary M, expectedReward M π σ n h

/-- The robust value function, (10): `V*_n(h_n) = sup_{π ∈ Π_n} V^π_n(h_n)`. -/
noncomputable def Vstar (M : AMDP S A) (n : ℕ) (h : History S A n) : ℝ :=
  ⨆ π : Policy M, V M π n h

/-- The optimistic value of a policy, (6) at epoch `n`: `V̄^π_n(h_n) = sup_{P ∈ T^π_n} E^P[⋯]`. -/
noncomputable def Vbar (M : AMDP S A) (π : Policy M) (n : ℕ) (h : History S A n) : ℝ :=
  ⨆ σ : Adversary M, expectedReward M π σ n h

/-- The optimistic value function, (7) at epoch `n`: `V̄*_n(h_n) = sup_{π ∈ Π_n} V̄^π_n(h_n)`. -/
noncomputable def VbarStar (M : AMDP S A) (n : ℕ) (h : History S A n) : ℝ :=
  ⨆ π : Policy M, Vbar M π n h

end RobustDP.FiniteHorizon


