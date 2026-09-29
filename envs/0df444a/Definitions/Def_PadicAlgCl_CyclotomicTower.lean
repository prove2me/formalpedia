-- Prove2me | Definitions.Def_PadicAlgCl_CyclotomicTower
-- name    : PadicAlgCl_CyclotomicTower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/21f848bd-b133-5b19-9365-777c5848a8e7
-- title:
--   The p-power cyclotomic tower over Qp​
-- statement:
--   For a prime $p$ and a natural number $n$, [`PadicAlgCl.cyclotomicTower p n`](../def/PadicAlgCl_CyclotomicTower.html#L9) is the intermediate field of the extension $\mathbb{Q}_p \subseteq$ `PadicAlgCl p` obtained by adjoining to $\mathbb{Q}_p$ the full set $\{\zeta : \zeta^{p^n} = 1\}$ of $p^n$-th roots of unity in `PadicAlgCl p`; that is, it is the subfield $\mathbb{Q}_p(\mu_{p^n})$, presented as an element of `IntermediateField ℚ_[p] (PadicAlgCl p)` rather than as an abstract extension field. No primitive root of unity is chosen: the generating set is the solution set of $X^{p^n} = 1$, so for $n = 0$ the definition gives the trivial level $\mathbb{Q}_p$ itself. The whole family is indexed by $n$, giving a tower of subfields of a single fixed algebraic closure, so that the levels are literally nested subsets and may be compared and united without transition maps.
--
--   Two elementary facts about the family are recorded. First, `mem_cyclotomicTower_of_pow_eq_one`: any $\zeta$ in `PadicAlgCl p` with $\zeta^{p^n} = 1$ belongs to `cyclotomicTower p n`, since such $\zeta$ lie in the generating set. Second, `cyclotomicTower_mono`: the map $n \mapsto$ `cyclotomicTower p n` is monotone for the inclusion ordering on intermediate fields, because $\zeta^{p^m} = 1$ implies $\zeta^{p^n} = 1$ whenever $m \le n$, so the generating set at level $m$ is contained in that at level $n$.
--
--   **Relation to Mathlib.** Built from Mathlib's `IntermediateField.adjoin`, with the subset relation on `IntermediateField`; Mathlib supplies the general theory of cyclotomic extensions but no named $p$-power cyclotomic tower inside a fixed algebraic closure of $\mathbb{Q}_p$, which is what is introduced here.
--
--   **Where it is used.** The levels $\mathbb{Q}_p(\mu_{p^n})$ and their union $\mathbb{Q}_p(\mu_{p^\infty})$ form the ramified tower over $\mathbb{Q}_p$ on which the local $p$-adic Hodge theory input of the argument is set up, the Galois group of the union being identified with $\mathbb{Z}_p^\times$ via the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_PadicAlgCl_CyclotomicTower.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace PadicAlgCl

def cyclotomicTower (p : ℕ) [Fact p.Prime] (n : ℕ) : IntermediateField ℚ_[p] (PadicAlgCl p) :=
  IntermediateField.adjoin ℚ_[p] {ζ : PadicAlgCl p | ζ ^ (p ^ n) = 1}

theorem mem_cyclotomicTower_of_pow_eq_one (p : ℕ) [Fact p.Prime] {n : ℕ} {ζ : PadicAlgCl p}
    (h : ζ ^ (p ^ n) = 1) : ζ ∈ cyclotomicTower p n :=
  IntermediateField.subset_adjoin ℚ_[p] _ h

theorem cyclotomicTower_mono (p : ℕ) [Fact p.Prime] : Monotone (cyclotomicTower p) := by
  intro m n hmn
  refine IntermediateField.adjoin.mono ℚ_[p] _ _ fun ζ (hζ : ζ ^ (p ^ m) = 1) => ?_
  show ζ ^ (p ^ n) = 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [pow_add, pow_mul, hζ, one_pow]

end PadicAlgCl

end


