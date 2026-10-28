-- Prove2me | Definitions.Def_WildeQIT_channelCode
-- name    : WildeQIT_channelCode
-- status  : Definition
-- author  : @nonlocally
-- created : 2026-09-07T07:44:39.994108+00:00
-- url     : https://prove2.me/theorems/cd22cbb4-1a78-427f-bfab-fa1f9f6ba30d
-- title:
--   Channel codes, achievable rates, capacity $C(\mathcal N)$ and $I(\mathcal N)$ (§14.10, for Theorem 14.10.1)
-- statement:
--   The notions behind Theorem 14.10.1 (Shannon channel capacity), reconstructed from Wilde §14.10 (they are not roster items). An $(n,M)$ **channel code** for the classical channel $\mathcal{N} = p_{Y|X}$ consists of codewords $x^n(m)$, $m\in\{1,\dots,M\}$, and a decoder $D:\mathcal{Y}^n\to\{1,\dots,M\}$. The **error probability of message $m$** is $\Pr\{D(Y^n)\ne m \mid X^n = x^n(m)\} = \sum_{y^n : D(y^n)\ne m}\prod_i p_{Y|X}(y_i|x_i(m))$. A rate $R$ is **achievable** if for every $\varepsilon\in(0,1)$, $\delta>0$ and all sufficiently large $n$ there is a code with at least $2^{n(R-\delta)}$ messages whose maximal error probability is at most $\varepsilon$. The **capacity** $C(\mathcal N)$ is the supremum of the achievable rates, and $I(\mathcal N) \equiv \max_{p_X} I(X;Y)$ is the mutual information of $p_X(x)p_{Y|X}(y|x)$ maximized over input distributions.
--
--   **Formalization Note.** `ChannelCode α β n M` bundles `enc : Fin M → (Fin n → α)` and `dec : (Fin n → β) → Fin M`; `ChannelCode.errorProb N c m`; `IsAchievableChannelRate N R`; `channelCapacity N = sSup {R | IsAchievableChannelRate N R}`; `channelMaxMutualInfo N = sSup {I | ∃ p, I = mutualInfo (N.joint p)}` (the maximum is attained by compactness, but the definition uses the supremum). Maximal (not average) error probability is used.
-- source:
--   Wilde, Quantum Information Theory 2nd ed. (Cambridge 2017; arXiv:1106.1445v8), Theorem 14.10.1, §Application:\ Channel Capacity Theorem (roster-items.csv line 26887); the notions '(n,M) channel code', 'error probability', 'achievable rate', 'capacity' and I(𝒩) from the prose of §14.10 preceding it.

import Definitions.Def_WildeQIT_mutualInfo
import Definitions.Def_WildeQIT_weakCondTypicalSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
Wilde, *Quantum Information Theory* (2nd ed.), §14.10 (Application: Channel capacity theorem),
the notions used by Theorem 14.10.1 (Shannon channel capacity): an `(n, M)` channel code for the
classical channel `N = p_{Y|X}` consists of `M` codewords `xⁿ(m)` and a decoder; the error
probability of message `m` is `Pr{ D(Yⁿ) ≠ m | Xⁿ = xⁿ(m) }`; a rate `R` is achievable if for
every `ε ∈ (0,1)`, `δ > 0` and all sufficiently large `n` there is a code with at least
`2^{n(R−δ)}` messages whose maximal error probability is at most `ε`; the capacity `C(𝒩)` is the
supremum of the achievable rates; `I(𝒩) ≡ max_{p_X} I(X;Y)` is the maximal mutual information.
-/

namespace WildeQIT

/-- A channel code of block length `n` with `M` messages: codewords and a decoder. -/
structure ChannelCode (α β : Type) (n M : ℕ) where
  /-- The codeword `xⁿ(m)` of message `m`. -/
  enc : Fin M → (Fin n → α)
  /-- The decoder `D : 𝒴ⁿ → {1, …, M}`. -/
  dec : (Fin n → β) → Fin M

variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]

/-- The error probability of message `m`: `∑_{yⁿ : D(yⁿ) ≠ m} ∏ᵢ N(yᵢ | xᵢ(m))`. -/
noncomputable def ChannelCode.errorProb {n M : ℕ} (N : Channel α β) (c : ChannelCode α β n M)
    (m : Fin M) : ℝ :=
  ∑ y, if c.dec y = m then 0 else N.seqProb (c.enc m) y

/-- A rate `R` is achievable for the channel `N`: for every `ε ∈ (0,1)` and `δ > 0`, for all
sufficiently large `n` there is a code with at least `2^{n(R−δ)}` messages, every message having
error probability at most `ε`. -/
def IsAchievableChannelRate (N : Channel α β) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ n ≥ N₀,
    ∃ M : ℕ, (2 : ℝ) ^ ((n : ℝ) * (R - δ)) ≤ M ∧
      ∃ c : ChannelCode α β n M, ∀ m, c.errorProb N m ≤ ε

/-- The capacity `C(𝒩)`: the supremum of the achievable rates. -/
noncomputable def channelCapacity (N : Channel α β) : ℝ :=
  sSup {R : ℝ | IsAchievableChannelRate N R}

/-- The maximal mutual information `I(𝒩) ≡ max_{p_X} I(X;Y)`, the mutual information of the joint
distribution `p_X(x) N(y|x)` maximised over input distributions (as a supremum). -/
noncomputable def channelMaxMutualInfo (N : Channel α β) : ℝ :=
  sSup {I : ℝ | ∃ p : FinDist α, I = mutualInfo (N.joint p)}

end WildeQIT


