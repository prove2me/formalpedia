-- Prove2me | Definitions.Def_AvgValueAlloc_expServiceR
-- name    : AvgValueAlloc_expServiceR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:38:22.117418+00:00
-- url     : https://prove2.me/theorems/d28e5d82-49d6-4e87-b657-022005e0362b
-- title:
--   Expected physical service welfare $\mathbb E R$ of the service kernel
-- statement:
--   For service contents $Z$ of length $z$ in uniform order: no negative proposal in the first $\lfloor z/2\rfloor$ positions; afterwards each occupied group $J$ takes the canonical per-copy mass of the current copy in the small-edge LP of the observed prefix (current copy included), rounded down to a power-of-two grid, and fresh coins propose at most one buyer of the group with these probabilities. $\mathbb E R$ is the expected final physical service welfare over the order and the proposal coins.
--
--   Proposals read only the prefix multiset, the current copy and fresh coins, never earlier private checks or physical winners.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.2, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec
import Definitions.Def_AvgValueAlloc_svcRun

namespace AvgValueAlloc

/-- The proposal probability of buyer `j` at service position `a`: no negative proposal in the
first `⌊z/2⌋` positions; afterwards the canonical per-copy mass of the current copy on `j` in the
prefix LP of `j`'s group, rounded down to the grid `2^{-grid g}`. -/
noncomputable def propRate {n z : ℕ} (grp : Fin n → ℤ)
    (opt : Finset (Fin n) → Multiset (Vec n) → Vec n → Fin n → ℝ) (grid : ℤ → ℕ)
    (Z : Fin z → Vec n) (τ : Equiv.Perm (Fin z)) (a : Fin z) (j : Fin n) : ℝ :=
  if z / 2 ≤ a.val then
    (⌊opt (Finset.univ.filter fun k => grp k = grp j)
        ((Finset.univ.filter fun b : Fin z => b ≤ a).val.map fun b => Z (τ b)) (Z (τ a)) j *
          2 ^ grid (grp j)⌋ : ℝ) / 2 ^ grid (grp j)
  else 0

open scoped Classical in
/-- The probability of a proposal profile (the set of proposed buyers at each position): fresh
coins at each position and in each occupied group propose at most one buyer of the group, buyer
`j` with probability `propRate … j`, nobody with the remaining mass. -/
noncomputable def propProfileProb {n z : ℕ} (grp : Fin n → ℤ)
    (opt : Finset (Fin n) → Multiset (Vec n) → Vec n → Fin n → ℝ) (grid : ℤ → ℕ)
    (Z : Fin z → Vec n) (τ : Equiv.Perm (Fin z)) (prop : Fin z → Fin n → Bool) : ℝ :=
  ∏ a, ∏ g ∈ Finset.univ.image grp,
    let J := Finset.univ.filter fun j => grp j = g
    let Pg := J.filter fun j => prop a j = true
    if Pg = ∅ then 1 - ∑ j ∈ J, propRate grp opt grid Z τ a j
    else if Pg.card = 1 then ∑ j ∈ Pg, propRate grp opt grid Z τ a j else 0

/-- **Expected original physical service welfare `E R` of the service kernel.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.2, p.5: "With service length z, make no
negative proposal in the first ⌊z/2⌋ positions. Thereafter each occupied group J solves its
canonical observed-prefix LP … Round per-copy probabilities downward on a power-of-two grid with at
least 100|J|z subdivisions. Fresh finite coins propose at most one buyer per group. Proposals do
not read earlier private checks or physical winners."; Lemma 2.3: "fixed service contents in
conditional uniform order".

`expServiceR ρ grp opt grid B C₀ Z` is the expectation of the final physical service welfare `R`
over a uniform order `τ` of the service contents `Z` and the proposal coins, for the group
partition `grp`, canonical optimum chooser `opt`, rounding grids `grid` and earned bank `B`.

**Formalization Note.** Given the order, proposals at different positions are independent (they
read only the prefix multiset, the current copy and fresh coins), so the proposal law is a product
over positions and groups. The observed prefix at position `a` includes the current copy. -/
noncomputable def expServiceR {n z : ℕ} (ρ : Fin n → ℚ) (grp : Fin n → ℤ)
    (opt : Finset (Fin n) → Multiset (Vec n) → Vec n → Fin n → ℝ) (grid : ℤ → ℕ)
    (B C₀ : Fin n → ℝ) (Z : Fin z → Vec n) : ℝ :=
  (∑ τ : Equiv.Perm (Fin z), ∑ prop : Fin z → Fin n → Bool,
      propProfileProb grp opt grid Z τ prop * (svcRun ρ Z τ prop B C₀ z).R) /
    (z.factorial : ℝ)

end AvgValueAlloc


