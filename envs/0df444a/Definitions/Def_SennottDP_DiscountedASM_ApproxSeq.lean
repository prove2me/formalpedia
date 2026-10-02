-- Prove2me | Definitions.Def_SennottDP_DiscountedASM_ApproxSeq
-- name    : SennottDP_DiscountedASM_ApproxSeq
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-01T07:28:34.636206+00:00
-- url     : https://prove2.me/theorems/b2c174be-a718-4f55-b46a-4a2c0b6939a2
-- title:
--   Approximating sequences, ATAS, Assumption DC($\alpha$), and limit points of policies
-- statement:
--   Let $\Delta$ be an MDC with state space $S$. An **approximating sequence** (AS) $(\Delta_N)_{N\ge N_0}$ for $\Delta$ is given by an increasing sequence $(S_N)_{N\ge N_0}$ of finite nonempty subsets of $S$ with $\bigcup_N S_N=S$, and, for each $N\ge N_0$, $i\in S_N$ and $a\in A_i$, a probability distribution $(P_{ij}(a;N))_{j\in S_N}$ on $S_N$ such that
--   $$
--   \lim_{N\to\infty}P_{ij}(a;N)=P_{ij}(a),\qquad j\in S.
--   $$
--   The MDC $\Delta_N$ has state space $S_N$, the action sets $A_i$ and costs $C(i,a)$ of $\Delta$, and transition probabilities $P_{ij}(a;N)$. Its discounted value function is written $V^N_\alpha$.
--
--   **Assumption DC($\alpha$).** For $i\in S$,
--   $$
--   \limsup_{N\to\infty}V^N_\alpha(i)=:W_\alpha(i)<\infty\quad\text{and}\quad W_\alpha(i)\le V_\alpha(i).
--   $$
--
--   **Limit points.** If $e^N$ is a stationary policy of $\Delta_N$ for each $N$, a stationary policy $e$ of $\Delta$ is a limit point of $(e^N)$ if there is a subsequence $N_r$ such that, for each $i\in S$, $e^{N_r}(i)=e(i)$ for all sufficiently large $r$.
--
--   **Augmentation type approximating sequence** (ATAS). The AS is an ATAS if for $N\ge N_0$, $i\in S_N$, $a\in A_i$ and each $r\notin S_N$ there is a probability distribution $(q_j(i,a,r,N))_{j\in S_N}$, the augmentation distribution, such that
--   $$
--   P_{ij}(a;N)=P_{ij}(a)+\sum_{r\in S-S_N}P_{ir}(a)\,q_j(i,a,r,N),\qquad j\in S_N.
--   $$
--   The ATAS **sends excess probability to the finite set** $G$ if every augmentation distribution puts all its mass on $G$: $\sum_{j\in G}q_j(i,a,r,N)=1$.
--
--   These are the objects of the approximating sequence method: $\Delta_N$ is a finite MDC whose optimal policy can be computed, and the results of Sections 4.6–4.7 say when its value function and optimal policies converge to those of $\Delta$.
--
--   **Formalization Note** $V^N_\alpha(i)$ is the discounted value function of the MDC $\Delta_N$ built on the subtype $S_N$ (the general definition applied to $\Delta_N$), extended to all $N$ and $i$ by the value $0$ when $N<N_0$ or $i\notin S_N$. Since the $S_N$ increase to $S$, for each fixed $i$ this convention affects only finitely many $N$ and so no limit, lim sup or lim inf in $N$. A subsequence in a limit point is a strictly increasing map $r\mapsto N_r$ with $N_r\ge N_0$. The augmentation distributions are a function `q N i a r j` whose values for $j\notin S_N$ are not used; "sends excess probability to $G$" sums over $j\in S_N\cap G$.
-- source:
--   Sennott, Stochastic Dynamic Programming and the Control of Queueing Systems (Wiley, 1999), p. 28 Definition 2.5.1 (2.17); p. 29 Definition 2.5.3 (2.19); pp. 29–30; p. 76 Assumption DC(α); p. 290 Definition B.4

import Mathlib
import Definitions.Def_SennottDP_DiscountedASM_MDC

open scoped ENNReal NNReal
open Classical Filter Topology

namespace SennottDP.DiscountedASM

variable {S Act : Type}

/-- An approximating sequence (AS) `(Δ_N)_{N ≥ N₀}` for the MDC `M` (Definition 2.5.1, p. 28):
an increasing sequence `(S_N)_{N ≥ N₀}` of finite nonempty subsets of `S` with union `S`, and for
each `N ≥ N₀`, `i ∈ S_N`, `a ∈ A i` a probability distribution `P_{i·}(a; N)` on `S_N` with
`lim_{N→∞} P_{ij}(a; N) = P_{ij}(a)` for every `j ∈ S` (2.17). The action sets and costs of
`Δ_N` are those of `M` (see `ApproxSeq.truncMDC`). The fields `SN N`, `PN N` for `N < N₀`, and
`PN N i a j` for `i ∉ S_N` or `j ∉ S_N`, carry no meaning and enter no statement except through
limits in `N`, which do not see them. -/
structure ApproxSeq (M : MDC S Act) where
  N0 : ℕ
  SN : ℕ → Finset S
  SN_nonempty : ∀ N, N0 ≤ N → (SN N).Nonempty
  SN_mono : ∀ N N', N0 ≤ N → N ≤ N' → SN N ⊆ SN N'
  SN_cover : ∀ i, ∃ N, N0 ≤ N ∧ i ∈ SN N
  PN : ℕ → S → Act → S → ℝ≥0∞
  PN_sum : ∀ N, N0 ≤ N → ∀ i ∈ SN N, ∀ a ∈ M.A i, ∑ j ∈ SN N, PN N i a j = 1
  PN_lim : ∀ i, ∀ a ∈ M.A i, ∀ j, Tendsto (fun N => PN N i a j) atTop (𝓝 (M.P i a j))

namespace ApproxSeq

variable {M : MDC S Act} (Δs : ApproxSeq M)

/-- The approximating MDC `Δ_N` (`N ≥ N₀`): state space `S_N`, action sets `A i`, costs
`C(i,a)`, transition probabilities `P_{ij}(a; N)`, `i, j ∈ S_N`. -/
noncomputable def truncMDC (N : ℕ) (hN : Δs.N0 ≤ N) : MDC (Δs.SN N) Act where
  A i := M.A i.1
  A_nonempty i := M.A_nonempty i.1
  C i a := M.C i.1 a
  P i a j := Δs.PN N i.1 a j.1
  P_sum i a ha := by
    rw [Finset.tsum_subtype (Δs.SN N) (fun j => Δs.PN N i.1 a j)]
    exact Δs.PN_sum N hN i.1 i.2 a ha

/-- `V^N_α(i)`, the discounted value function of `Δ_N` at `i ∈ S_N` (`N ≥ N₀`), extended by the
convention `0` when `N < N₀` or `i ∉ S_N`. For a fixed `i` the convention applies to finitely
many `N` only (the `S_N` increase to `S`), so it does not affect any limit in `N`. -/
noncomputable def VN (α : ℝ≥0) (N : ℕ) (i : S) : ℝ≥0∞ :=
  if h : Δs.N0 ≤ N ∧ i ∈ Δs.SN N then (Δs.truncMDC N h.1).value α ⟨i, h.2⟩ else 0

/-- Assumption DC(α) (p. 76): for every `i ∈ S`,
`W_α(i) := limsup_{N→∞} V^N_α(i) < ∞` and `W_α(i) ≤ V_α(i)` (limsup in `[0, ∞]`). -/
def DC (α : ℝ≥0) : Prop :=
  ∀ i : S, limsup (fun N => Δs.VN α N i) atTop < ⊤ ∧
    limsup (fun N => Δs.VN α N i) atTop ≤ M.value α i

/-- Definition B.4 (p. 290): the stationary policy `e` of `M` is a limit point of the sequence
`(e^N)_{N ≥ N₀}` of stationary policies of the `Δ_N` (with `e^N` meaningful on `S_N`) if there is
a subsequence `N_r ≥ N₀` such that for each `i ∈ S`, `e^{N_r}(i) = e(i)` for all large `r`. -/
def IsLimitPoint (eN : ℕ → S → Act) (e : S → Act) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ r, Δs.N0 ≤ φ r) ∧ ∀ i, ∀ᶠ r in atTop, eN (φ r) i = e i

/-- Definition 2.5.3 (p. 29): `Δs` is an augmentation type approximating sequence (ATAS) with
augmentation distributions `q N i a r ·` if, for `N ≥ N₀`, `i ∈ S_N`, `a ∈ A i` and every
`r ∉ S_N`, `(q_j(i,a,r,N))_{j ∈ S_N}` is a probability distribution on `S_N`, and
`P_{ij}(a; N) = P_{ij}(a) + Σ_{r ∈ S - S_N} P_{ir}(a) q_j(i,a,r,N)` for `j ∈ S_N` (2.19).
The values `q N i a r j` for `j ∉ S_N` are not used. -/
def IsATAS (q : ℕ → S → Act → S → S → ℝ≥0∞) : Prop :=
  ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, ∀ a ∈ M.A i,
    (∀ r, r ∉ Δs.SN N → ∑ j ∈ Δs.SN N, q N i a r j = 1) ∧
    ∀ j ∈ Δs.SN N, Δs.PN N i a j =
      M.P i a j + ∑' r : S, (if r ∈ Δs.SN N then 0 else M.P i a r * q N i a r j)

/-- The ATAS with augmentation distributions `q` sends excess probability to the finite set
`G` (p. 29–30): every augmentation distribution puts all its mass on `G`,
`Σ_{j ∈ G} q_j(i,a,r,N) = 1` (the sum over `j ∈ S_N ∩ G`, `q` being a distribution on `S_N`). -/
def SendsExcessTo (q : ℕ → S → Act → S → S → ℝ≥0∞) (G : Finset S) : Prop :=
  ∀ N, Δs.N0 ≤ N → ∀ i ∈ Δs.SN N, ∀ a ∈ M.A i, ∀ r, r ∉ Δs.SN N →
    ∑ j ∈ (Δs.SN N).filter (· ∈ G), q N i a r j = 1

end ApproxSeq

end SennottDP.DiscountedASM


