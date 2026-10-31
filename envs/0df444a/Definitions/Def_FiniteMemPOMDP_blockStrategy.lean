-- Prove2me | Definitions.Def_FiniteMemPOMDP_blockStrategy
-- name    : FiniteMemPOMDP_blockStrategy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:33:51.093671+00:00
-- url     : https://prove2.me/theorems/54e9144d-dd5b-4462-ba51-3e68e4a6b2ac
-- title:
--   The block strategy $\sigma'$ of §6.4
-- statement:
--   Fix $n_0\ge1$. The strategy $\sigma'$ plays in blocks of $n_0$ stages; block $\ell$ is the stages $\ell n_0+1,\dots,(\ell+1)n_0$. Each block carries a super-support $\mathcal D^{J_\ell}$:
--
--   1. $\mathcal D^{J_0}=\mathcal B_1=(\mathcal K_1,\dots,\mathcal K_I)$;
--   2. if $h$ is the history recorded during block $\ell-1$, then $\mathcal D^{J_\ell}_i=\mathcal B^i(h^{J_{\ell-1}},h)$ for every $i$.
--
--   During block $\ell$, after the history $h$ recorded since the block started, $\sigma'$ plays $\sigma(h^{J_\ell},h)$: it plays as if it were playing $\sigma$ from the representative history $h^{J_\ell}$.
--
--   `blockTuple` computes $\mathcal D^{J_\ell}$ from the history, and `blockStrategy Γ p σ rep n0` is $\sigma'$.
--
--   **Formalization Note** $J_\ell$ is encoded by the tuple $\mathcal D^{J_\ell}$ and $h^j$ by `rep`. The paper leaves $J_\ell$ undefined after histories of probability zero; the definition uses the same formula there.
-- source:
--   Chatterjee, Saona & Ziliotto, Finite-memory strategies in POMDPs with Long-run Average Objectives, arXiv:1904.13360v2, §6.4, pp.18–19

import Mathlib
import Definitions.Def_FiniteMemPOMDP_superSupp

namespace FiniteMemPOMDP

variable {K A S : Type} [Fintype K] [DecidableEq K] [Fintype A] [Fintype S] [Nonempty A]
  [Nonempty S]

/-- The super-support `D^{J_ℓ}` in force during block `ℓ`, computed from the history `h`:
`D^{J_0} = B_1 = (K_1, …, K_I)`, and `D^{J_{ℓ+1}} = B(h^{J_ℓ}, h_ℓ)` where `h^{J_ℓ} = rep D^{J_ℓ}` and
`h_ℓ` is the part of `h` recorded during block `ℓ` (its pairs `ℓ n0 + 1, …, (ℓ+1) n0`). -/
noncomputable def blockTuple (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (rep : (ℝ → Set K) → List (A × S)) (n0 : ℕ) (h : List (A × S)) : ℕ → ℝ → Set K
  | 0 => superSuppTuple Γ p σ []
  | ℓ + 1 =>
      superSuppTuple Γ p σ (rep (blockTuple Γ p σ rep n0 h ℓ) ++ (h.drop (ℓ * n0)).take n0)

/-- **The block strategy `σ′` of §6.4.**
Chatterjee, Saona & Ziliotto, arXiv:1904.13360v2, §6.4, pp.18–19: "For each ℓ ≥ 0, the block
number ℓ consists in the stages m such that ℓn0 + 1 ≤ m ≤ (ℓ + 1)n0. … Consider ℓ = 0 … there
exists j ∈ [1 .. J] such that B1 = Dj. Set J0 = j, and define σ′(h, J0) := σ(h^{J0}, h) for all
h ∈ Hm and m ≤ n0. … Consider ℓ ≥ 1 … Denote the history between stages (ℓ − 1)n0 + 1 and ℓn0 + 1
by h ∈ Hn0+1 and define Jℓ such that, for all i ∈ [1 .. I],
D^{Jℓ}_i = B^i_{m_{J(ℓ−1)}+n0+1}(h^{J(ℓ−1)}, h). Then, extend σ′ for n0 additional stages as
before: σ′(h, Jℓ) := σ(h^{Jℓ}, h) for all h ∈ Hm and m ≤ n0." (p.19) "during stages ℓn0 + 1,
ℓn0 + 2, . . . , (ℓ + 1)n0, the decision-maker plays as if he was playing σ from history h^{Jℓ}."

`blockStrategy Γ p σ rep n0` plays, after a history `h` of length `t` (stage `t + 1`, in block
`ℓ = ⌊t / n0⌋`), the action `σ(rep D ++ h_{>ℓ n0})`, where `D = blockTuple … h ℓ` is the
super-support in force in block `ℓ` and `h_{>ℓ n0}` is the part of `h` recorded since the start of
the block.

**Formalization Note** The index `J_ℓ ∈ [1 .. J]` is replaced by the super-support tuple
`D^{J_ℓ}` itself and `h^j` by `rep D^j` (see `IsRepresentative`). The paper leaves `J_ℓ` undefined
after histories of probability zero; this definition extends it by the same formula. `n0 ≥ 1`
is a hypothesis of every statement using the block strategy. -/
noncomputable def blockStrategy (Γ : POMDP K A S) (p : stdSimplex ℝ K) (σ : List (A × S) → A)
    (rep : (ℝ → Set K) → List (A × S)) (n0 : ℕ) : List (A × S) → A :=
  fun h => σ (rep (blockTuple Γ p σ rep n0 h (h.length / n0)) ++ h.drop (h.length / n0 * n0))

end FiniteMemPOMDP


