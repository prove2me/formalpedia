-- Prove2me | Definitions.Def_AstromPOMDP_Reduction_Belief
-- name    : AstromPOMDP_Reduction_Belief
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:19:08.109341+00:00
-- url     : https://prove2.me/theorems/8f7cc81f-f393-40ab-9d87-3dcd69f11029
-- title:
--   §III, pp. 180–185 — z^j(u, w), the ℓ¹ norm, the update (3.25), the right-hand side of (3.28), the cost-to-go V_k(w) of (3.11), the Markov law c⁰(w(t), t)
-- statement:
--   This module defines the objects of Åström's dynamic programming solution (§III).
--
--   1. **The vectors $z^j$** (3.22)–(3.23): for a control $u$, a time $t$ and a distribution $w$ of $x_t$, $z^j(u,w)_i=\sum_s q_{ij}\,p_{si}(u,t+1)\,w_s$; and the norm (3.24) $\|z\|=\sum_i|z_i|$, the $\ell^1$ norm.
--   2. **The update** (3.25): after the output $\eta_{t+1}=j$ the new distribution is $z^j(u,w)/\|z^j(u,w)\|$. The first distribution is $w_i(1)=p^1_i q_{i\eta_1}/\sum_s p^1_s q_{s\eta_1}$, and $P(y_1=j)=\sum_s p^1_s q_{sj}$.
--   3. **The right-hand side of (3.28)** at time $k$, for a function $V$ standing for $V_{k+1}$:
--   $$
--   \sum_i g(u,i,k)\,w_i+\sum_j V\!\left(\frac{z^j(u,w)}{\|z^j(u,w)\|}\right)\|z^j(u,w)\|.
--   $$
--   4. **The cost-to-go** $V_k(w)$ (3.11): the infimum, over admissible tail laws (controls at times $k,\dots,N$ depending on the outputs observed after time $k$), of the expected cost $E\sum_{t=k}^N g(u(t),x_t,t)$ when $x_k$ has distribution $w$; and $V_{N+1}\equiv0$.
--   5. **Solutions of (3.28)**: pairs $(V,c^0)$ with $V_{N+1}=0$ on the probability simplex, $c^0(w,k)\in U$, and, for $1\le k\le N$ and every probability vector $w$, $V_k(w)$ equal to the right-hand side at $u=c^0(w,k)$ and at most the right-hand side at every $u\in U$.
--   6. **The Markov law** $u(t)=c^0(w(t),t)$, where $w(t)$ is computed from the outputs by (3.25) under this same law (one joint recursion: $w(t)$ gives $u(t)$, which gives $w(t+1)$).
--
--   The theorems of the mission compare these objects with the conditional probabilities and expected costs of §II.
--
--   **Formalization Note** The paper writes $V_k$ as a function of $\eta(k)$ and observes that it depends on $\eta(k)$ only through $w(k)$; the tail problem started from the distribution $w$ makes this a definition. The infimum is over a nonempty set and is bounded below ($g$ is continuous on the compact $U$), so it is not a junk value. When $\|z^j\|=0$ the update is the zero vector, and it is always multiplied by $\|z^j\|=0$. The time argument of $p$ that (3.22) suppresses is explicit.
-- source:
--   Åström, Optimal Control of Markov Processes with Incomplete State Information, J. Math. Anal. Appl. 10(1):174–205 (1965), DOI 10.1016/0022-247X(65)90154-X, pp. 180–185, §III, (3.6), (3.11), (3.22)–(3.25), (3.28)

import Mathlib
import Definitions.Def_AstromPOMDP_Reduction_Model

namespace AstromPOMDP.Reduction

variable {St Obs : Type*} [Fintype St] [DecidableEq St] [Fintype Obs] {r : ℕ}

/-- (3.24): the norm `‖x‖ = Σ_i |x_i|`, the ℓ¹ norm. (Mathlib's `‖·‖` on `St → ℝ` is the sup norm
and is not used.) -/
noncomputable def l1 (z : St → ℝ) : ℝ := ∑ i, |z i|

/-- (3.22)–(3.23): `z^j(u, w(t))`, the vector with components
`z_ij(u, w(t)) = Σ_s q_ij p_si(u) w_s(t)`, where `j` is the next output `η_{t+1}`.

**Formalization Note.** `t` is the time of the current distribution `w(t)`; the transition to
`x_{t+1}` uses `p(u, t + 1)` by (2.1). The paper suppresses this time argument. -/
noncomputable def zvec (M : Model St Obs r) (u : Fin r → ℝ) (t : ℕ) (w : St → ℝ) (j : Obs) :
    St → ℝ :=
  fun i => ∑ s, M.q i j * M.P u (t + 1) s i * w s

/-- (3.25): the updated distribution `z^j(u, w(t)) / ‖z^j(u, w(t))‖` after the output
`η_{t+1} = j`. When `‖z^j‖ = 0` (an output of conditional probability zero) Lean's `0⁻¹ = 0` makes
this the zero vector; it is then always multiplied by `‖z^j‖ = 0`. -/
noncomputable def bayesNext (M : Model St Obs r) (u : Fin r → ℝ) (t : ℕ) (w : St → ℝ) (j : Obs) :
    St → ℝ :=
  (l1 (zvec M u t w j))⁻¹ • zvec M u t w j

/-- `P(y₁ = j) = Σ_s p₁(s) q_sj`. -/
noncomputable def prob1 (M : Model St Obs r) (j : Obs) : ℝ := ∑ s, M.p₁ s * M.q s j

/-- `w(1)` after the first output `η₁ = j`: `w_i(1) = p₁(i) q_ij / Σ_s p₁(s) q_sj` (the zero vector
when `P(y₁ = j) = 0`). -/
noncomputable def bayes1 (M : Model St Obs r) (j : Obs) : St → ℝ :=
  (prob1 M j)⁻¹ • fun i => M.p₁ i * M.q i j

/-- The expression minimized in (3.28) at time `k`, with `V` standing for `V_{k+1}`:
`Σ_i g(u, i, k) w_i + Σ_j V(z^j(u, w)/‖z^j(u, w)‖) ‖z^j(u, w)‖`. -/
noncomputable def bellmanRHS (M : Model St Obs r) (k : ℕ) (V : (St → ℝ) → ℝ) (w : St → ℝ)
    (u : Fin r → ℝ) : ℝ :=
  ∑ i, M.g u i k * w i + ∑ j, V (bayesNext M u k w j) * l1 (zvec M u k w j)

/-- A tail control law from time `k` (an element of `ControlLaw`, reinterpreted): `d m η'` is the
control used at time `k + m` after the `m` outputs `y_{k+1}, …, y_{k+m}` observed after time `k`.
It is admissible if every control used at a time `k + m ≤ N` lies in `U`. -/
def TailAdmissible (M : Model St Obs r) (k : ℕ) (d : ControlLaw Obs r) : Prop :=
  ∀ m : ℕ, k + m ≤ M.N → ∀ η : Fin m → Obs, d m η ∈ M.U

/-- The joint weight of the tail problem started at time `k` with `x_k` distributed as `w`:
states `x 0, …, x m` at times `k, …, k + m` and outputs `y 0, …, y (m−1)` at times
`k + 1, …, k + m`, under the tail law `d`:
`w(x_k) ∏_{l=0}^{m−1} p_{x_{k+l} x_{k+l+1}}(d(l, y_{k+1..k+l}), k + l + 1) q(x_{k+l+1}, y_{k+l+1})`.
The output `y_k` is already accounted for in `w`. -/
noncomputable def tailProb (M : Model St Obs r) (k : ℕ) (w : St → ℝ) (d : ControlLaw Obs r) :
    (m : ℕ) → (Fin (m + 1) → St) → (Fin m → Obs) → ℝ
  | 0, x, _ => w (x 0)
  | m + 1, x, y =>
      tailProb M k w d m (Fin.init x) (Fin.init y) *
        M.P (d m (Fin.init y)) (k + m + 1) (x (Fin.last m).castSucc) (x (Fin.last (m + 1))) *
        M.q (x (Fin.last (m + 1))) (y (Fin.last m))

/-- The expected cost `E Σ_{t=k}^N g(u(t), x_t, t)` of the steps `k, …, N` under the tail law
`d`, when `x_k` is distributed as `w`. -/
noncomputable def tailCost (M : Model St Obs r) (k : ℕ) (w : St → ℝ) (d : ControlLaw Obs r) : ℝ :=
  ∑ x : Fin (M.N - k + 1) → St, ∑ y : Fin (M.N - k) → Obs,
    tailProb M k w d (M.N - k) x y *
      ∑ i : Fin (M.N - k + 1),
        M.g (d i.val (Fin.take i.val (Nat.lt_succ_iff.mp i.isLt) y)) (x i) (k + i.val)

/-- (3.11): the minimal expected cost `V_k(w)` of the last `N − k + 1` steps when the conditional
distribution of `x_k` is `w`: the infimum of `tailCost` over admissible tail laws, and
`V_{N+1} ≡ 0` (the convention under which (3.5) is (3.28) at `k = N`).

**Formalization Note.** The paper writes `V_k` as a function of `η(k)` and observes (p. 180) that
it depends on `η(k)` only through `w(k)`; taking the tail problem started from the distribution
`w` makes this a definition. The index set of the infimum is nonempty (constant laws with value in
the nonempty `U`) and `tailCost` is bounded below on it (`g` is continuous on the compact `U`,
hence bounded, and the weights are bounded), so the real `⨅` is not a junk value. Only
`1 ≤ k ≤ N + 1` is meaningful. -/
noncomputable def costToGo (M : Model St Obs r) (k : ℕ) (w : St → ℝ) : ℝ :=
  if M.N < k then 0 else ⨅ d : {d : ControlLaw Obs r // TailAdmissible M k d}, tailCost M k w d.1

/-- `(V, c⁰)` solves the functional equation (3.28): `V_{N+1} = 0` on the probability simplex,
`c⁰(w, k) ∈ U` for every `w` and `k`, and for `1 ≤ k ≤ N` and every probability vector `w`,
`V_k(w)` equals the right-hand side of (3.28) at `u = c⁰(w, k)` and is at most the right-hand side
at every `u ∈ U` (so the minimum over `U` is attained at `c⁰(w, k)`). -/
def IsSolution328 (M : Model St Obs r) (V : ℕ → (St → ℝ) → ℝ) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) :
    Prop :=
  (∀ w ∈ stdSimplex ℝ St, V (M.N + 1) w = 0) ∧ (∀ w t, c₀ w t ∈ M.U) ∧
    ∀ k : ℕ, 1 ≤ k → k ≤ M.N → ∀ w ∈ stdSimplex ℝ St,
      V k w = bellmanRHS M k (V (k + 1)) w (c₀ w k) ∧
        ∀ u ∈ M.U, V k w ≤ bellmanRHS M k (V (k + 1)) w u

/-- The conditional distributions `w(t)` generated by (3.25) under the Markov control law
`u(t) = c⁰(w(t), t)`, as a function of the outputs `η(t)`: `w(1) = bayes1 η₁` and
`w(t + 1) = z^j(u(t), w(t))/‖z^j(u(t), w(t))‖` with `j = η_{t+1}` and `u(t) = c⁰(w(t), t)`
(one joint recursion: `w(t)` gives `u(t)` gives `w(t + 1)`). At `t = 0` (no output yet) the value
is the law `p₁` of `x₁`; it is never used by the control law at a time `t ≥ 1`. -/
noncomputable def markovBelief (M : Model St Obs r) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) :
    (t : ℕ) → (Fin t → Obs) → St → ℝ
  | 0, _ => M.p₁
  | 1, η => bayes1 M (η 0)
  | t + 2, η =>
      bayesNext M (c₀ (markovBelief M c₀ (t + 1) (Fin.init η)) (t + 1)) (t + 1)
        (markovBelief M c₀ (t + 1) (Fin.init η)) (η (Fin.last (t + 1)))

/-- The control law of P.1 induced by `c⁰`: `c(η(t), t) = c⁰(w(t), t)` with `w(t)` the
conditional distribution computed by (3.25) along the outputs `η(t)` under this same law. -/
noncomputable def markovLaw (M : Model St Obs r) (c₀ : (St → ℝ) → ℕ → (Fin r → ℝ)) :
    ControlLaw Obs r :=
  fun t η => c₀ (markovBelief M c₀ t η) t

end AstromPOMDP.Reduction


