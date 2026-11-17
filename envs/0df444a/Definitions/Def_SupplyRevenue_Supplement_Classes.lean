-- Prove2me | Definitions.Def_SupplyRevenue_Supplement_Classes
-- name    : SupplyRevenue_Supplement_Classes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:31:52.175441+00:00
-- url     : https://prove2.me/theorems/b2df4dae-e2fa-4a37-901a-79c3aef5d87f
-- title:
--   The constructive class $\mathcal H_2$ and rational sources
-- statement:
--   Let $M=[m]$ be the items. A value $v$ on bundles has **at most two nonnegative additive clauses** if there are $a,c\in\mathbb R_{\ge 0}^M$ with
--
--   $$v(T)=\max\Bigl\{\sum_{j\in T}a_j,\ \sum_{j\in T}c_j\Bigr\}\qquad\text{for all }T\subseteq M$$
--
--   ($a=c$ gives a single clause). The value is **additive on a block** $B\subseteq M$ if $v(T)=\sum_{j\in T}v(\{j\})$ for every $T\subseteq B$.
--
--   A buyer belongs to the **constructive class** $\mathcal H_2$ if there is one partition $M=B_1\sqcup B_2$, either block possibly empty, fixed for the buyer and shared by all of its supported types (types of positive mass), such that every supported type has at most two nonnegative additive clauses and is additive on $B_1$ and on $B_2$. An instance is in $\mathcal H_2$ when every buyer is, each buyer with its own partition. The partition is part of the promise only; it is never given to an algorithm.
--
--   A **rational source** is an item-pricing source whose every mixture weight, and every price of an item in the assortment of every atom, is a rational number.
--
--   These are the promises of the $\mathcal H_2$ rows of Theorem 1.2 and of its sampled interface.
--
--   **Formalization Note** $B_2$ is the complement of $B_1$. Values are already normalized and monotone in the base model. Prices of items outside an assortment are never read and are unrestricted. The helper `toRat x` returns the rational equal to a real $x$ when one exists (else $0$); it is exact on rational sources and is how sampled offers are reported as rational data. Subadditivity is not redefined here: Theorem 1.2 uses the published `SubmodOrder.Subadditive`.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.3 (class H₂; sampled interface: rational source)

import Mathlib
import Definitions.Def_SupplyRevenue_Classes
import Definitions.Def_SupplyRevenue_CapRev

namespace SupplyRevenue
namespace Supplement

/-!
# The constructive class `𝓗₂` and rational sources

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
p.3: "The constructive class H₂ has at most two nonnegative
additive clauses per type. For each buyer there exists an unknown fixed partition M = B_{i1} ⊔ B_{i2}, allowing an empty
block, such that every supported type satisfies v_i(T) = Σ_{j∈T} v_i({j}) on either block. The partition is
buyer-specific and persistent across types, not supplied"; p.3: "a rational source … supplied".

**Formalization Note** Subadditivity (p.2) is not defined here: the theorems use the published
`SubmodOrder.Subadditive`, the same predicate `v(S ∪ T) ≤ v(S) + v(T)`. Values are already normalized and monotone (`SupplyRevenue.Buyer`). Class membership of a buyer
concerns supported types only (mass `> 0`), as in the published `Buyer.InClass`. In `𝓗₂` the block `B₁` is chosen once
per buyer, before the type, and `B₂` is its complement; either block may be empty. "On either block" is read as: on each
of the two blocks the value is additive over subsets of that block. A two-clause value is `max` of two nonnegative
additive functions; equal clauses give a single clause. A rational source has rational weights and rational prices on
every assortment item; the prices of items outside an assortment are never read and are unrestricted. `toRat x` is the
rational equal to `x` when there is one (and `0` otherwise); it is exact on rational sources.
-/

/-- A value with at most two nonnegative additive clauses: `v(T) = max{a(T), c(T)}` with `a, c ≥ 0` (p.3). -/
def IsTwoClause {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  ∃ a c : Fin m → ℝ, (∀ j, 0 ≤ a j) ∧ (∀ j, 0 ≤ c j) ∧
    ∀ T : Finset (Fin m), v T = max (∑ j ∈ T, a j) (∑ j ∈ T, c j)

/-- `v` is additive on the block `B`: `v(T) = Σ_{j∈T} v({j})` for every `T ⊆ B` (p.3). -/
def AdditiveOn {m : ℕ} (v : Finset (Fin m) → ℝ) (B : Finset (Fin m)) : Prop :=
  ∀ T ⊆ B, v T = ∑ j ∈ T, v {j}

/-- A buyer is in `𝓗₂` (p.3): one partition `M = B₁ ⊔ B₂` (`B₂ = B₁ᶜ`, either block possibly empty), fixed for the
buyer and shared by all its supported types, such that every supported type has at most two nonnegative additive clauses
and is additive on each block. -/
def BuyerInH2 {m : ℕ} (b : Buyer m) : Prop :=
  ∃ B₁ : Finset (Fin m), ∀ θ, 0 < b.mass θ →
    IsTwoClause (b.val θ) ∧ AdditiveOn (b.val θ) B₁ ∧ AdditiveOn (b.val θ) B₁ᶜ

/-- Every buyer of the instance is in `𝓗₂` (each with its own partition). -/
def InstanceInH2 {n m : ℕ} (D : Instance n m) : Prop :=
  ∀ i, BuyerInH2 (D i)

/-- A rational source (p.3): every weight, and every price of an item in the assortment of every atom, is rational. -/
def IsRationalSource {n m : ℕ} (σ : Source n m) : Prop :=
  ∀ i, (∀ a, ∃ q : ℚ, (σ i).weight a = q) ∧
    ∀ a, ∀ j ∈ ((σ i).atom a).assort, ∃ q : ℚ, ((σ i).atom a).price j = q

open Classical in
/-- The rational equal to a real number, when there is one; `0` otherwise. -/
noncomputable def toRat (x : ℝ) : ℚ :=
  if h : ∃ q : ℚ, (q : ℝ) = x then h.choose else 0

theorem toRat_cast (q : ℚ) : toRat (q : ℝ) = q := by
  have h : ∃ q' : ℚ, (q' : ℝ) = q := ⟨q, rfl⟩
  classical
  unfold toRat
  rw [dif_pos h]
  exact_mod_cast h.choose_spec

end Supplement
end SupplyRevenue


