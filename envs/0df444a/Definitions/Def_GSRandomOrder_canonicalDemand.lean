-- Prove2me | Definitions.Def_GSRandomOrder_canonicalDemand
-- name    : GSRandomOrder_canonicalDemand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:46.571376+00:00
-- url     : https://prove2.me/theorems/98241d72-d315-473b-b96c-d1bf5bd60efe
-- title:
--   Canonical demand $D_v(T)$: the lexicographic maximizer of $(v(X),\psi(X))$
-- statement:
--   Label the items $N=\{1,\dots,n\}$ and put
--   $$
--   \psi(X)=\sum_{g\in X}\bigl(1+2^{-g}\bigr)=|X|+\sum_{g\in X}2^{-g}.
--   $$
--   For $T\subseteq N$, the **canonical demand** $D_v(T)$ is the lexicographic maximizer of $(v(X),\psi(X))$ over $X\subseteq T$. Since $\sum_{g\in X}2^{-g}<1$, comparing $\psi$ compares cardinalities first and then prefers the set containing the smallest item of the symmetric difference; $\psi$ is injective, so the maximizer is unique, and it lies in $\operatorname{dom}v$ because $v(\emptyset)=0$. An item $g$ is **chosen** from $T$ if $g\in D_v(T)$.
--
--   The canonical demand is the choice rule that replaces the greedy basis of a matroid in the paper's algorithm.
--
--   **Formalization Note** The item $g\in$ `Fin n` carries the label $g+1$, so its weight is $2^{-(g+1)}$; $\psi$ is computed in $\mathbb Q$. Keys are compared lexicographically in `WithBot ℝ × ℚ`. The definition selects a maximizer of the key; uniqueness (from the injectivity of $\psi$) is a provable fact, not an assumption. The two helper facts $D_v(T)\subseteq T$ and maximality are proved in the module.
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), §2.2, pp.6–7

import Mathlib

set_option autoImplicit false

namespace GSRandomOrder

/-- The tie-breaking weight `ψ(X) = Σ_{g ∈ X} (1 + 2^{−g}) = |X| + Σ_{g ∈ X} 2^{−g}`
(Paes Leme, Pál, Patel, STOC 2027 submission, manuscript sha256 69787f50…, §2.2, p.6).

**Formalization Note.** Items are `Fin n`; the item `g` carries the paper's label `g.val + 1`, so
the weight of `g` is `2^{−(g.val + 1)}` and `Σ_{g ∈ X} 2^{−(g.val+1)} < 1`, as the paper uses
(comparing `ψ` compares cardinalities first). `ψ` takes dyadic rational values, so it is computed
in `ℚ`. -/
def psi {n : ℕ} (X : Finset (Fin n)) : ℚ :=
  (X.card : ℚ) + ∑ g ∈ X, (1 / 2 : ℚ) ^ (g.val + 1)

/-- The lexicographic key `(v(X), ψ(X))` of a set `X`. -/
def demandKey {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (X : Finset (Fin n)) :
    WithBot ℝ ×ₗ ℚ :=
  toLex (v X, psi X)

/-- A lexicographic maximizer of the key over the subsets of `T` exists (`∅ ⊆ T`). -/
theorem exists_max_demandKey {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (T : Finset (Fin n)) :
    ∃ X ∈ T.powerset, ∀ Y ∈ T.powerset, demandKey v Y ≤ demandKey v X :=
  T.powerset.exists_max_image (demandKey v) ⟨∅, Finset.empty_mem_powerset T⟩

/-- **Canonical demand** `D_v(T)` (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.2, pp.6–7): for `T ⊆ N`, the
lexicographic maximizer of `(v(X), ψ(X))` over `X ⊆ T`. "`g` is chosen from `T`" means
`g ∈ D_v(T)`.

**Formalization Note.** The key `(v X, psi X)` is compared in the lexicographic order of
`WithBot ℝ × ℚ` (`⊥ = −∞` is the least value). The definition picks a maximizer of this key over
`T.powerset`; since `ψ` is injective on `2^N` (p.7) the maximizer is unique, so this is the
paper's `D_v(T)` (uniqueness is a provable fact, not part of the definition). `D_v(T) ⊆ T` and
the maximality are `canonicalDemand_spec`. -/
noncomputable def canonicalDemand {n : ℕ} (v : Finset (Fin n) → WithBot ℝ)
    (T : Finset (Fin n)) : Finset (Fin n) :=
  Classical.choose (exists_max_demandKey v T)

/-- `D_v(T) ⊆ T`, and every `Y ⊆ T` has key at most that of `D_v(T)`. -/
theorem canonicalDemand_spec {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (T : Finset (Fin n)) :
    canonicalDemand v T ⊆ T ∧
      ∀ Y ⊆ T, demandKey v Y ≤ demandKey v (canonicalDemand v T) := by
  obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_max_demandKey v T)
  exact ⟨Finset.mem_powerset.mp h1, fun Y hY => h2 Y (Finset.mem_powerset.mpr hY)⟩

end GSRandomOrder


