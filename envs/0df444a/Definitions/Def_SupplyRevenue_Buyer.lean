-- Prove2me | Definitions.Def_SupplyRevenue_Buyer
-- name    : SupplyRevenue_Buyer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:45:37.763137+00:00
-- url     : https://prove2.me/theorems/cf573eb4-d568-41dc-936d-f1ded34df8fc
-- title:
--   Finite mixtures, lotteries, buyers and instances
-- statement:
--   A **finite mixture** of elements of a set is a finite family of atoms with nonnegative weights summing to one, and its expectation is the weighted sum. A **lottery** is a mass function on whole bundles; the same object serves as a law of the remaining stock. Its inclusion marginal is $x_j(L)=\Pr_{T\sim L}[j\in T]$.
--
--   A **buyer** has finitely many types, a mass function and a normalized monotone value per type. An **independent instance** $D=\prod_i D_i$ is a family of $n$ buyers, whose types are drawn independently.
--
--   These objects are finite sums throughout, so that every benchmark is an elementary expression with no measure theory.
--
--   **Formalization Note** Types are `Fin numTypes`. Atoms of a mixture may repeat.
-- source:
--   Mahboub, Rahgoshay, Supply-Sensitive Revenue Recovery under Unknown Buyer Order (manuscript, sha256 c04de641…), §1.1, p.2

import Mathlib
import Definitions.Def_SupplyRevenue_Demand

namespace SupplyRevenue

/-!
# Finite mixtures, lotteries, buyers and instances

Mahboub, Rahgoshay, *Supply-Sensitive Revenue Recovery under Unknown Buyer Order* (manuscript, sha256 c04de641…),
§1.1, p.2: "Let M = [m], n, m ≥ 1, and D = ∏_i D_i with finite D_i."

**Formalization Note** Everything is a finite sum; there is no `Measure` and no Bochner integral. A buyer's types are
`Fin numTypes`, with a mass function. Independence across buyers is the product mass in `Instance`-level expectations
(`Def_SupplyRevenue_Revenue`). Every type carries a normalized monotone value; class membership looks at supported types
only (`Def_SupplyRevenue_Classes`). `Mix α` is a finite mixture: a finite index, nonnegative weights summing to one and
atoms; atoms may repeat.
-/

/-- A finite mixture of elements of `α`. -/
structure Mix (α : Type) where
  N : ℕ
  weight : Fin N → ℝ
  atom : Fin N → α
  weight_nonneg : ∀ a, 0 ≤ weight a
  weight_sum : ∑ a, weight a = 1

/-- The expectation of `f` under a finite mixture. -/
noncomputable def Mix.E {α : Type} (μ : Mix α) (f : α → ℝ) : ℝ := ∑ a, μ.weight a * f (μ.atom a)

/-- The point mass at `x`, as a finite mixture. -/
noncomputable def Mix.pure {α : Type} (x : α) : Mix α where
  N := 1
  weight := fun _ => 1
  atom := fun _ => x
  weight_nonneg := fun _ => zero_le_one
  weight_sum := by simp

/-- A lottery: a mass function on whole bundles (p.2: "Lotteries over whole subsets"). The same object is a stock law. -/
structure Lottery (m : ℕ) where
  mass : Finset (Fin m) → ℝ
  mass_nonneg : ∀ T, 0 ≤ mass T
  mass_sum : ∑ T, mass T = 1

/-- The expectation of a function of the realized bundle. -/
noncomputable def Lottery.E {m : ℕ} (L : Lottery m) (f : Finset (Fin m) → ℝ) : ℝ :=
  ∑ T, L.mass T * f T

/-- The inclusion marginal `x_j(L) = P[j ∈ T]` of a lottery (p.2). -/
noncomputable def Lottery.incl {m : ℕ} (L : Lottery m) (j : Fin m) : ℝ :=
  L.E fun T => if j ∈ T then 1 else 0

/-- The point mass at a bundle. -/
def Lottery.dirac {m : ℕ} (T₀ : Finset (Fin m)) : Lottery m where
  mass := fun T => if T = T₀ then 1 else 0
  mass_nonneg := fun T => by split_ifs <;> norm_num
  mass_sum := by simp

/-- A buyer: finitely many types, a mass function, a normalized monotone value per type. -/
structure Buyer (m : ℕ) where
  numTypes : ℕ
  mass : Fin numTypes → ℝ
  val : Fin numTypes → Finset (Fin m) → ℝ
  mass_nonneg : ∀ θ, 0 ≤ mass θ
  mass_sum : ∑ θ, mass θ = 1
  val_valuation : ∀ θ, IsValuation (val θ)

/-- The expectation over one buyer's type. -/
noncomputable def Buyer.E {m : ℕ} (b : Buyer m) (f : Fin b.numTypes → ℝ) : ℝ :=
  ∑ θ, b.mass θ * f θ

/-- An independent finite instance: one buyer distribution per buyer `i : Fin n`. -/
abbrev Instance (n m : ℕ) := Fin n → Buyer m

/-- The buyer with types indexed by a finite type `Θ`. -/
noncomputable def Buyer.ofFintype {m : ℕ} {Θ : Type} [Fintype Θ] (mass : Θ → ℝ)
    (val : Θ → Finset (Fin m) → ℝ) (h0 : ∀ θ, 0 ≤ mass θ) (h1 : ∑ θ, mass θ = 1)
    (hv : ∀ θ, IsValuation (val θ)) : Buyer m where
  numTypes := Fintype.card Θ
  mass := fun i => mass ((Fintype.equivFin Θ).symm i)
  val := fun i => val ((Fintype.equivFin Θ).symm i)
  mass_nonneg := fun _ => h0 _
  mass_sum := by rw [← h1]; exact Equiv.sum_comp (Fintype.equivFin Θ).symm mass
  val_valuation := fun _ => hv _

end SupplyRevenue


