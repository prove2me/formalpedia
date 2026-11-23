-- Prove2me | Definitions.Def_StableDispatch_Markov_Supplement_Policy
-- name    : StableDispatch_Markov_Supplement_Policy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:43:07.974674+00:00
-- url     : https://prove2.me/theorems/36deafad-dc51-4bd8-b0ff-da91c972c212
-- title:
--   §2.3, pp. 7–11 — memory-based dispatching policies (f1, f2, f3, g1, g2, g3, h1, h2) and weak symmetry (Assumption 2.1)
-- statement:
--   **Queue states.** The state of a server is a sequence $q=(q_0,q_1,\dots)$ of nonnegative remaining workloads, the job in service first; an idle server is the zero sequence (the paper's $\mathcal Q=\mathbb R_+^{\mathbb Z_+}$, p. 7).
--
--   **Policies.** A memory-based dispatching policy for $n$ servers (§2.3.2, pp. 8–10) consists of a finite set of memory states $\mathcal M_n$, a rate $\beta_n>0$ for the spontaneous-message process, and measurable maps
--
--   1. $f_1(m,w,u)\subseteq\{1,\dots,n\}$: the servers sampled at an arrival of size $w$;
--   2. $f_2(m,w,\{(q_i,\mu_i,i):i\in S\},u)\in\{1,\dots,n\}$: the destination of the job, from the states and rates of the sampled servers;
--   3. $f_3(m,w,\{\dots\},D,u)\in\mathcal M_n$: the new memory state after dispatching to $D$;
--   4. $g_1(\mathbf q,\mu,u)\in\{0,1,\dots,n\}$: the server sending a spontaneous message ($0$ = none);
--   5. $g_2(m,i,q_i,\mu_i,u)$ and $g_3(m,i,q_i,\mu_i,\{(q_j,\mu_j,j):j\in S\},u)$: the servers then sampled and the new memory state;
--   6. $h_1(q_i,\mu_i,u)\in\{0,1\}$ and $h_2(m,i,q_i,\mu_i,u)$: whether server $i$ messages at a departure, and the new memory state.
--
--   **Weak symmetry (Assumption 2.1).** For every permutation $\sigma$ of the servers there is a permutation $\sigma_M$ of $\mathcal M_n$ such that, with $U,V$ uniform on $[0,1]$,
--
--   $$\sigma\big(f_1(m,w,U)\big)\overset{d}{=}f_1(\sigma_M(m),w,U),\qquad \sigma\Big(f_2\big(m,w,\{(q_i,\mu_i,i):i\in S\},V\big)\Big)\overset{d}{=}f_2\Big(\sigma_M(m),w,\{(q_i,\mu_i,\sigma(i)):i\in S\},V\Big)$$
--
--   for every $m$, every $w\ge0$, every $S$, every $\mathbf q\in\mathcal Q^n$ and every $\mu\in\mathbb R^n_+$. Only $f_1$ and $f_2$ are constrained.
--
--   These objects describe the class of policies to which Theorem 2.2 and Propositions B.1–B.3 apply; the single-ID policy of §2.2.1 belongs to it (Remark 2.4).
--
--   **Formalization Note** Memory states are `Fin memSize`. Servers are `Fin n` (0-based). The set of triples $\{(q_i,\mu_i,i):i\in S\}$, an element of the paper's $B_n$, is the partial map $i\mapsto(q_i,\mu_i)$ (`info S q μ`). The maps take real arguments; only their values at nonnegative sizes and rates and at $u\in[0,1]$ matter. Measurability is required on each fiber of the discrete arguments, with product σ-algebras on sequences. $g_1$ returns `Option (Fin n)` (`none` for $0$) and $h_1$ returns `Bool`. Equality in distribution of finitely-valued variables is equality of the probability of each value under the uniform law.
-- source:
--   Gamarnik, Tsitsiklis, Zubeldia, Stability, Memory, and Messaging Trade-Offs in Heterogeneous Service Systems, arXiv:2007.07219v1, pp. 7–11, §2.3, §2.3.2, Assumption 2.1

import Mathlib

namespace StableDispatch.Markov.Supplement

open MeasureTheory Set

noncomputable section

/-- The state of one server (§2.3, p. 7): a sequence `q : ℕ → ℝ` of remaining workloads, the job
in service first (`q 0`); an idle server is the zero sequence. The paper's `Q = ℝ₊^{ℤ₊}`. -/
abbrev Queue := ℕ → ℝ

/-- The information the dispatcher receives from a set of queried servers (§2.3.2, p. 9): an
element of `B_n`, a set of triples `(q_i, μ_i, i)` with pairwise distinct third coordinates,
encoded as the partial map `i ↦ (q_i, μ_i)` (`none` for an unqueried server). -/
abbrev Info (n : ℕ) := Fin n → Option (Queue × ℝ)

/-- The set `{(q_i, μ_i, i) : i ∈ S}` as an element of `Info n`. -/
def info {n : ℕ} (S : Finset (Fin n)) (q : Fin n → Queue) (μ : Fin n → ℝ) : Info n :=
  fun i => if i ∈ S then some (q i, μ i) else none

/-- The law of a uniform random variable on `[0, 1]`. -/
def unif : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

/-- A memory-based dispatching policy for `n` servers (§2.3, pp. 7–10). Memory states are
`Fin memSize` (the paper's `M_n = {1, …, 2^{c_n}}`); `beta` is the rate `β_n` of the spontaneous
message process; the eight maps are those of §2.3.2, with `[0, 1]`-valued randomization
arguments, job sizes and rates in `ℝ` (only their values at the arguments the paper allows
matter), `g1`'s value `0` ("no message") encoded as `none`, and `h1` valued in `Bool`.
Each map is measurable: for every value of the discrete arguments (memory state, server index,
queried set, destination) and every output value, the set of continuous arguments producing that
output is measurable (product σ-algebras; sequences carry the product σ-algebra). -/
structure Policy (n : ℕ) where
  memSize : ℕ
  memSize_pos : 0 < memSize
  beta : ℝ
  beta_pos : 0 < beta
  /-- `S_k = f1(M(T_k^-), W_k, U_{1,k})`. -/
  f1 : Fin memSize → ℝ → ℝ → Finset (Fin n)
  /-- `D_k = f2(M(T_k^-), W_k, {(Q_i(T_k^-), μ_i, i) : i ∈ S_k}, U_{2,k})`. -/
  f2 : Fin memSize → ℝ → Info n → ℝ → Fin n
  /-- `M(T_k) = f3(M(T_k^-), W_k, {…}, D_k, U_{3,k})`. -/
  f3 : Fin memSize → ℝ → Info n → Fin n → ℝ → Fin memSize
  /-- `g1(Q(T^s_k), μ, U_{4,k})`: the server sending a spontaneous message, if any. -/
  g1 : (Fin n → Queue) → (Fin n → ℝ) → ℝ → Option (Fin n)
  /-- `S^s_k = g2(M, i, Q_i(T^s_k), μ_i, U_{5,k})`. -/
  g2 : Fin memSize → Fin n → Queue → ℝ → ℝ → Finset (Fin n)
  /-- `M(T^s_k) = g3(M(T^s_k^-), i, Q_i(T^s_k), μ_i, {(Q_j, μ_j, j) : j ∈ S^s_k}, U_{6,k})`. -/
  g3 : Fin memSize → Fin n → Queue → ℝ → Info n → ℝ → Fin memSize
  /-- `h1(Q_i(T^d_k(i)), μ_i, U_{7,k}) = 1` iff server `i` messages at its `k`-th departure. -/
  h1 : Queue → ℝ → ℝ → Bool
  /-- `M(T^d_k(i)) = h2(M(T^d_k(i)^-), i, Q_i(T^d_k(i)), μ_i, U_{8,k})`. -/
  h2 : Fin memSize → Fin n → Queue → ℝ → ℝ → Fin memSize
  measurable_f1 : ∀ m S, MeasurableSet {p : ℝ × ℝ | f1 m p.1 p.2 = S}
  measurable_f2 : ∀ m (S : Finset (Fin n)) j,
    MeasurableSet {p : ℝ × ((Fin n → Queue) × (Fin n → ℝ)) × ℝ |
      f2 m p.1 (info S p.2.1.1 p.2.1.2) p.2.2 = j}
  measurable_f3 : ∀ m (S : Finset (Fin n)) d m',
    MeasurableSet {p : ℝ × ((Fin n → Queue) × (Fin n → ℝ)) × ℝ |
      f3 m p.1 (info S p.2.1.1 p.2.1.2) d p.2.2 = m'}
  measurable_g1 : ∀ o,
    MeasurableSet {p : (Fin n → Queue) × (Fin n → ℝ) × ℝ | g1 p.1 p.2.1 p.2.2 = o}
  measurable_g2 : ∀ m i S,
    MeasurableSet {p : Queue × ℝ × ℝ | g2 m i p.1 p.2.1 p.2.2 = S}
  measurable_g3 : ∀ m i (S : Finset (Fin n)) m',
    MeasurableSet {p : Queue × ℝ × ((Fin n → Queue) × (Fin n → ℝ)) × ℝ |
      g3 m i p.1 p.2.1 (info S p.2.2.1.1 p.2.2.1.2) p.2.2.2 = m'}
  measurable_h1 : ∀ b, MeasurableSet {p : Queue × ℝ × ℝ | h1 p.1 p.2.1 p.2.2 = b}
  measurable_h2 : ∀ m i m',
    MeasurableSet {p : Queue × ℝ × ℝ | h2 m i p.1 p.2.1 p.2.2 = m'}

/-- Weak symmetry, Assumption 2.1 (pp. 10–11): for every permutation `σ` of the servers there is
a permutation `σ_M` of the memory states such that, with `U, V` uniform on `[0, 1]`,
1. `σ(f1(m, w, U)) =ᵈ f1(σ_M(m), w, U)` for every `m` and `w ≥ 0`;
2. `σ(f2(m, w, {(q_i, μ_i, i) : i ∈ S}, V)) =ᵈ f2(σ_M(m), w, {(q_i, μ_i, σ(i)) : i ∈ S}, V)` for
   every `m`, `w ≥ 0`, `S`, `q ∈ Qⁿ` (nonnegative sequences) and `μ ∈ ℝⁿ₊`.

Both random variables take finitely many values, so equality in distribution is equality of the
probability of every value. -/
def WeaklySymmetric {n : ℕ} (P : Policy n) : Prop :=
  ∀ σ : Equiv.Perm (Fin n), ∃ σM : Equiv.Perm (Fin P.memSize),
    (∀ (m : Fin P.memSize) (w : ℝ), 0 ≤ w → ∀ T : Finset (Fin n),
      unif {u | (P.f1 m w u).map σ.toEmbedding = T} = unif {u | P.f1 (σM m) w u = T}) ∧
    (∀ (m : Fin P.memSize) (w : ℝ), 0 ≤ w → ∀ (S : Finset (Fin n)) (q : Fin n → Queue)
      (μ : Fin n → ℝ), (∀ i k, 0 ≤ q i k) → (∀ i, 0 ≤ μ i) → ∀ j : Fin n,
      unif {v | σ (P.f2 m w (info S q μ) v) = j} =
        unif {v | P.f2 (σM m) w (info (S.map σ.toEmbedding) (q ∘ σ.symm) (μ ∘ σ.symm)) v = j})

end

end StableDispatch.Markov.Supplement


