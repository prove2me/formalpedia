-- Prove2me | Definitions.Def_EFXCounterex_Submodular_Setting
-- name    : EFXCounterex_Submodular_Setting
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T00:44:44.933979+00:00
-- url     : https://prove2.me/theorems/ca32fe0d-b78e-4d4b-b4b1-9c9adf7fcde4
-- title:
--   Complete allocations, normalized, monotone, strictly increasing and weighted-coverage valuations, relabelling symmetries, and the strictification $v^\varepsilon$
-- statement:
--   General notions of §2 (p. 6) and §3.2.2 (p. 13), for agents `Fin n` and goods `Fin m`. EFX itself is the published `LittleCharity.EFX.IsEFX` ($v_i(X_i)\ge v_i(X_j\setminus\{g\})$ for all $i,j$ and all $g\in X_j$, Definition 2.1 with $\alpha=1$).
--
--   - **Allocation** (`IsAllocation X`): the bundles $X_1,\dots,X_n$ are pairwise disjoint (`LittleCharity.EFX.IsPartialAllocation`) and no good is unallocated (`LittleCharity.EFX.pool X = ∅`), i.e. their union is $M$. Empty bundles are allowed.
--   - **Normalized** $v(\emptyset)=0$; **monotone** $S\subseteq T\Rightarrow v(S)\le v(T)$; **strictly increasing under inclusion** $S\subsetneq T\Rightarrow v(S)<v(T)$.
--   - **Weighted coverage** (`IsWeightedCoverage v`): there are finitely many features $f\in\{0,\dots,k-1\}$ with nonnegative weights $w_f$ and, for each good $g$, a set $F_g$ of covered features, such that $v(S)=\sum_{f\in\bigcup_{g\in S}F_g}w_f$ for every bundle $S$.
--   - **Relabelling**: a permutation $\pi$ of the goods maps a bundle $S$ to its image $\pi(S)$ (`relabelBundle`); a pair $(\sigma,\pi)$ of permutations of agents and goods is a **symmetry** of the profile $v$ if $v_{\sigma(i)}(\pi(S))=v_i(S)$ for all $i,S$ (`IsProfileSymmetry`).
--   - **Strictification** (`perturb ε v`): $v^\varepsilon_i(S)=v_i(S)+\varepsilon|S|$, with the same $\varepsilon$ for every agent.
-- source:
--   Akrami, Mackenzie, Mayorov, Mehlhorn, Srinivas, Suzuki, Weidenbach 2026, Counterexamples to EFX for Submodular and Subadditive Valuations, arXiv:2605.06451 (supplied manuscript, sha256 700243a1…), §2 (Definition 2.1 and weighted coverage), p. 6; §3.2.2, p. 13

import Mathlib
import Definitions.Def_LittleCharity_EFX_Setting

namespace EFXCounterex.Submodular

/-- §2, p. 6: an allocation `X = (X_1, …, X_n)` of the goods `Fin m` to the agents `Fin n` is an
`n`-tuple of pairwise disjoint bundles whose union is all of `M` (empty bundles are allowed,
unallocated goods are not). Built on the published `LittleCharity.EFX.IsPartialAllocation`
(pairwise disjoint) and `LittleCharity.EFX.pool` (the unallocated goods), with completeness
`pool X = ∅`. -/
def IsAllocation {n m : ℕ} (X : Fin n → Finset (Fin m)) : Prop :=
  LittleCharity.EFX.IsPartialAllocation X ∧ LittleCharity.EFX.pool X = ∅

/-- §2, p. 6: a valuation is normalized, `v(∅) = 0`. -/
def IsNormalized {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  v ∅ = 0

/-- §2, p. 6: a valuation is monotone, `v(S) ≤ v(T)` whenever `S ⊆ T`. -/
def IsMonotone {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), S ⊆ T → v S ≤ v T

/-- §2, p. 6: a valuation is strictly increasing under inclusion, `v(S) < v(T)` whenever
`S ⊊ T`. -/
def IsStrictlyIncreasing {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∀ S T : Finset (Fin m), S ⊂ T → v S < v T

/-- §2, p. 6: a weighted-coverage valuation. There is a finite set of features (indexed by
`Fin k`), each feature `f` has a nonnegative weight `w f`, and each good `g` covers a set of
features `cov g`; the value of a bundle `S` is the total weight of the features covered by its
goods, `v(S) = ∑_{f ∈ ⋃_{g ∈ S} F_g} w_f`. -/
def IsWeightedCoverage {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ (k : ℕ) (w : Fin k → ℝ) (cov : Fin m → Finset (Fin k)),
    (∀ f, 0 ≤ w f) ∧ ∀ S : Finset (Fin m), v S = ∑ f ∈ S.biUnion cov, w f

/-- A permutation `π` of the goods relabels a bundle `S` to its image `π(S)`. -/
def relabelBundle {m : ℕ} (π : Equiv.Perm (Fin m)) (S : Finset (Fin m)) : Finset (Fin m) :=
  S.map π.toEmbedding

/-- A simultaneous relabelling of agents by `σ` and goods by `π` is a symmetry of the valuation
profile `v` when agent `σ i` values the relabelled bundle `π(S)` exactly as agent `i` values `S`. -/
def IsProfileSymmetry {n m : ℕ} (v : Fin n → Finset (Fin m) → ℝ)
    (σ : Equiv.Perm (Fin n)) (π : Equiv.Perm (Fin m)) : Prop :=
  ∀ (i : Fin n) (S : Finset (Fin m)), v (σ i) (relabelBundle π S) = v i S

/-- §3.2.2, p. 13: the strictification `v^ε_i(S) = v_i(S) + ε|S|`, with the same `ε` for every
agent. -/
def perturb {n m : ℕ} (ε : ℝ) (v : Fin n → Finset (Fin m) → ℝ) :
    Fin n → Finset (Fin m) → ℝ :=
  fun i S => v i S + ε * (S.card : ℝ)

end EFXCounterex.Submodular


