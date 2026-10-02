-- Prove2me | Definitions.Def_SennottDP_FiniteHorizon_ApproxSeq
-- name    : SennottDP_FiniteHorizon_ApproxSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T06:18:26.1172+00:00
-- url     : https://prove2.me/theorems/0dc02da3-e6c4-4f34-8596-dfc5e934f7d6
-- title:
--   Approximating sequences, augmentation type approximating sequences and Assumption FH(α, n)
-- statement:
--   Let $\Delta$ be an MDC with countable state space $S$. An **approximating sequence** (AS) $(\Delta_N)_{N \ge N_0}$ for $\Delta$ (Definition 2.5.1) is given by an increasing sequence $(S_N)_{N \ge N_0}$ of finite nonempty subsets of $S$ with $\bigcup_N S_N = S$, and, for $N \ge N_0$, $i \in S_N$ and $a \in A_i$, a probability distribution $(P_{ij}(a;N))_{j \in S_N}$ on $S_N$ such that
--   $$
--   \lim_{N\to\infty} P_{ij}(a;N) = P_{ij}(a), \qquad j \in S. \tag{2.17}
--   $$
--   $\Delta_N$ is the MDC with state space $S_N$, the same action sets $A_i$ and costs $C(i,a)$, and transitions $P_{ij}(a;N)$; it carries the same terminal cost $F$. Its $n$ horizon value function is written $v^N_{\alpha,n}$ and its minimizing sets $B^N_i(\alpha,n)$.
--
--   The AS is an **augmentation type approximating sequence** (ATAS, Definition 2.5.3) if for $i \in S_N$, $a \in A_i$ and each $r \notin S_N$ there is a probability distribution $(q_j(i,a,r,N))_{j \in S_N}$, the augmentation distribution, such that
--   $$
--   P_{ij}(a;N) = P_{ij}(a) + \sum_{r \in S - S_N} P_{ir}(a)\, q_j(i,a,r,N), \qquad j \in S_N. \tag{2.19}
--   $$
--   It **sends excess probability to** a set $G$ if $\sum_{j \in G} q_j(i,a,r,N) = 1$ always.
--
--   **Assumption FH($\alpha$, $n$)** (p. 43): for every $i \in S$,
--   $$
--   w_{\alpha,n}(i) := \limsup_{N\to\infty} v^N_{\alpha,n}(i) < \infty \quad\text{and}\quad w_{\alpha,n}(i) \le v_{\alpha,n}(i).
--   $$
--
--   If $e^N$ is a stationary policy for $\Delta_N$ for each $N$, a stationary policy $e$ for $\Delta$ is a **limit point** of $(e^N)$ (Definition B.4) if there is a subsequence $(N_r)$ with $e^{N_r}(i) = e(i)$ for $N_r$ sufficiently large, for each $i \in S$.
--
--   These definitions set up the approximating sequence method, which computes finite horizon value functions and optimal policies of a countable-state MDC through finite-state truncations.
--
--   **Formalization Note** The sets $S_N$ and the probabilities $P_{ij}(a;N)$ are given for every $N$, but only $N \ge N_0$, $i,j \in S_N$, $a \in A_i$ are part of the model; for fixed $i,a,j$ the remaining values occur for finitely many $N$ only, so (2.17) is unaffected. `valueN F α n N i` is $v^N_{\alpha,n}(i)$ for $N \ge N_0$, $i \in S_N$, and $0$ otherwise (again finitely many $N$ for each $i$, so limits, $\liminf$ and $\limsup$ are the book's). A stationary policy $e^N$ of $\Delta_N$ is a function on $S$ whose values on $S_N$ lie in $A_i$. The augmentation distributions $q$ are indexed as `q N i a r j`; "sends excess probability to $G$" sums over $j \in G \cap S_N$, where $q$ is defined.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 28, Definition 2.5.1 and Eq. (2.17); pp. 29–30, Definition 2.5.3, Eq. (2.19), 'sends excess probability to G'; p. 43, Assumption FH(α, n); p. 290, Definition B.4

import Mathlib
import Definitions.Def_SennottDP_FiniteHorizon_MDC
import Definitions.Def_SennottDP_FiniteHorizon_Criterion

open scoped ENNReal NNReal Topology
open Classical Filter

namespace SennottDP.FiniteHorizon

namespace MDC

variable {S Act : Type}

/-- The state spaces of an approximating sequence (Definition 2.5.1, p. 28): starting from the
approximation level `N₀`, the sets `S_N` (`N ≥ N₀`) are finite nonempty subsets of `S`, increasing
in `N`, with `⋃_N S_N = S`. -/
def IsStateApprox (N₀ : ℕ) (SN : ℕ → Finset S) : Prop :=
  (∀ N, N₀ ≤ N → (SN N).Nonempty) ∧
  (∀ N N', N₀ ≤ N → N ≤ N' → SN N ⊆ SN N') ∧
  (∀ i, ∃ N, N₀ ≤ N ∧ i ∈ SN N)

/-- An approximating sequence (AS) `(Δ_N)_{N ≥ N₀}` for `Δ` (Definition 2.5.1, p. 28). `Δ_N` has
state space `S_N`, the same action sets `A_i` and costs `C(i, a)` as `Δ` for `i ∈ S_N`, and
transition probabilities `P_ij(a; N)`: for `i ∈ S_N` and `a ∈ A_i` a probability distribution on
`S_N`, converging to the original ones, `lim_{N → ∞} P_ij(a; N) = P_ij(a)` for `j ∈ S` (2.17).
The values `PN N i a j` with `N < N₀`, `i ∉ S_N` or `j ∉ S_N` are not part of the model; for
fixed `i, j` they occur for only finitely many `N`, so they do not affect the limit (2.17). -/
structure ApproxSeq (M : MDC S Act) where
  N₀ : ℕ
  SN : ℕ → Finset S
  SN_spec : IsStateApprox N₀ SN
  PN : ℕ → S → Act → S → ℝ≥0∞
  PN_sum : ∀ N, N₀ ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, PN N i a j = 1
  PN_tendsto : ∀ i, ∀ a ∈ M.A i, ∀ j, Tendsto (fun N => PN N i a j) atTop (𝓝 (M.P i a j))

namespace ApproxSeq

variable {M : MDC S Act} (AS : M.ApproxSeq)

/-- The MDC `Δ_N` (`N ≥ N₀`) on the finite state space `S_N` (Definition 2.5.1). -/
noncomputable def toMDC (N : ℕ) (hN : AS.N₀ ≤ N) : MDC (AS.SN N) Act where
  A i := M.A i.1
  A_nonempty i := M.A_nonempty i.1
  C i a := M.C i.1 a
  P i a j := AS.PN N i.1 a j.1
  P_sum i a ha := by
    rw [Finset.tsum_subtype (AS.SN N) (fun j => AS.PN N i.1 a j)]
    exact AS.PN_sum N hN i.1 i.2 a ha

/-- The `n` horizon value function `v^N_{α,n}(i)` of `Δ_N` (with the same terminal cost `F`,
p. 28) at a state `i ∈ S_N`, for `N ≥ N₀`. Convention: for `N < N₀` or `i ∉ S_N`, where
`v^N_{α,n}(i)` is undefined, the value is `0`; for each fixed `i` this happens for only finitely
many `N`, so limits, `lim inf` and `lim sup` as `N → ∞` are those of the book. -/
noncomputable def valueN (F : S → ℝ≥0) (α : ℝ≥0) (n N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : AS.N₀ ≤ N ∧ i ∈ AS.SN N then
    (AS.toMDC N h.1).value (fun j => F j.1) α n ⟨i, h.2⟩
  else 0

/-- The minimizing set `B^N_i(α, n)` of `Δ_N` at `i ∈ S_N` (p. 36 applied to `Δ_N`). -/
noncomputable def minSetN (F : S → ℝ≥0) (α : ℝ≥0) (n N : ℕ) (hN : AS.N₀ ≤ N)
    (i : AS.SN N) : Finset Act :=
  (AS.toMDC N hN).minSet (fun j => F j.1) α n i

/-- Assumption FH(α, n), p. 43: for `i ∈ S`,
`lim sup_{N → ∞} v^N_{α,n}(i) =: w_{α,n}(i) < ∞` and `w_{α,n}(i) ≤ v_{α,n}(i)`. -/
def FH (F : S → ℝ≥0) (α : ℝ≥0) (n : ℕ) : Prop :=
  ∀ i, limsup (fun N => AS.valueN F α n N i) atTop < ⊤ ∧
    limsup (fun N => AS.valueN F α n N i) atTop ≤ M.value F α n i

/-- `e N` is a stationary policy for `Δ_N` for every `N ≥ N₀`: `e N i ∈ A_i` for `i ∈ S_N`
(only these values of `e N` are part of the policy). -/
def IsStationarySeq (e : ℕ → S → Act) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, e N i ∈ M.A i

end ApproxSeq

variable (M : MDC S Act)

/-- Definition B.4, p. 290: for an AS `(Δ_N)`, and `e^N` a stationary policy for `Δ_N` for each
`N` (defined on `S_N`), the stationary policy `f` for `Δ` is a limit point of the sequence `(e^N)`
if there is a subsequence `e^{N_r}` such that, given `i ∈ S`, `e^{N_r}(i) = f(i)` for sufficiently
large index `N_r`. (The definition involves the AS only through the domains `S_N` of the `e^N`;
for fixed `i`, `i ∈ S_{N_r}` for `N_r` large.) -/
def IsApproxLimitPoint (e : ℕ → S → Act) (f : M.Stationary) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ᶠ k in atTop, e (φ k) i = f.1 i

/-- `q` is a family of augmentation distributions for the state sets `S_N` (Definition 2.5.3,
p. 29): for `N ≥ N₀`, `i ∈ S_N`, `a ∈ A_i` and `r ∉ S_N`, `(q N i a r j)_{j ∈ S_N}` is a probability
distribution on `S_N` (the book's `q_j(i, a, r, N)`). -/
def IsAugmentation (N₀ : ℕ) (SN : ℕ → Finset S) (q : ℕ → S → Act → S → S → ℝ≥0∞) : Prop :=
  ∀ N, N₀ ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∀ r, r ∉ SN N → ∑ j ∈ SN N, q N i a r j = 1

/-- The augmented transition probabilities (2.19), p. 29:
`P_ij(a; N) = P_ij(a) + ∑_{r ∈ S − S_N} P_ir(a) q_j(i, a, r, N)` for `j ∈ S_N`. -/
noncomputable def augProb (SN : ℕ → Finset S) (q : ℕ → S → Act → S → S → ℝ≥0∞)
    (N : ℕ) (i : S) (a : Act) (j : S) : ℝ≥0∞ :=
  M.P i a j + ∑' r : {r : S // r ∉ SN N}, M.P i a r.1 * q N i a r.1 j

variable {M}

/-- The AS `(Δ_N)` is an augmentation type approximating sequence (ATAS) with augmentation
distributions `q` (Definition 2.5.3, p. 29): its approximating distributions are given by (2.19)
for `N ≥ N₀`, `i, j ∈ S_N`, `a ∈ A_i`. -/
def ApproxSeq.IsATASWith (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞) : Prop :=
  M.IsAugmentation AS.N₀ AS.SN q ∧
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ j ∈ AS.SN N,
    AS.PN N i a j = M.augProb AS.SN q N i a j

/-- The ATAS with augmentation distributions `q` sends excess probability to the set `G`
(p. 29–30): `∑_{j ∈ G} q_j(i, a, r, N) = 1` always (the sum runs over `j ∈ G ∩ S_N`, where `q` is
defined). -/
def ApproxSeq.SendsExcessTo (AS : M.ApproxSeq) (q : ℕ → S → Act → S → S → ℝ≥0∞)
    (G : Set S) : Prop :=
  ∀ N, AS.N₀ ≤ N → ∀ i ∈ AS.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ AS.SN N →
    ∑ j ∈ (AS.SN N).filter (· ∈ G), q N i a r j = 1

end MDC

end SennottDP.FiniteHorizon


