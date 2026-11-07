-- Prove2me | Definitions.Def_MinrankTW_relJoin
-- name    : MinrankTW_relJoin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:51.000203+00:00
-- url     : https://prove2.me/theorems/51110675-2fc0-457a-b611-e309c1cc0adf
-- title:
--   Join $R_1\boxplus R_2$ of linear relations
-- statement:
--   The **join** of two linear relations $R_1,R_2\le\mathbb F^a\oplus\mathbb F^c$ is
--   $$
--   R_1\boxplus R_2=\{(x,y_1+y_2) : (x,y_1)\in R_1,\ (x,y_2)\in R_2\}.
--   $$
--   Two subgraphs sharing a separator use the same boundary vector $x$ and add their partial sums $y$; the join is their combined relation, and the dynamic program's join step is a convolution over it.
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Section 2.1, p.6, Eq. (7)

import Mathlib

namespace MinrankTW

/-- The **join** of two linear relations (Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), §2.1, p.6, Eq. (7)):
`R₁ ⊞ R₂ = {(x, y₁ + y₂) : (x, y₁) ∈ R₁, (x, y₂) ∈ R₂}`. -/
def relJoin {F : Type*} [Field F] {α γ : Type*} (R₁ R₂ : Submodule F ((α → F) × (γ → F))) :
    Submodule F ((α → F) × (γ → F)) where
  carrier := {p | ∃ y₁ y₂, (p.1, y₁) ∈ R₁ ∧ (p.1, y₂) ∈ R₂ ∧ p.2 = y₁ + y₂}
  zero_mem' := ⟨0, 0, R₁.zero_mem, R₂.zero_mem, by simp⟩
  add_mem' := by
    rintro ⟨x, y⟩ ⟨x', y'⟩ ⟨a, b, ha, hb, h⟩ ⟨a', b', ha', hb', h'⟩
    dsimp only at ha hb h ha' hb' h'
    refine ⟨a + a', b + b', ?_, ?_, ?_⟩
    · simpa using R₁.add_mem ha ha'
    · simpa using R₂.add_mem hb hb'
    · simp only [Prod.snd_add, h, h']
      abel
  smul_mem' := by
    rintro r ⟨x, y⟩ ⟨a, b, ha, hb, h⟩
    dsimp only at ha hb h
    refine ⟨r • a, r • b, ?_, ?_, ?_⟩
    · simpa using R₁.smul_mem r ha
    · simpa using R₂.smul_mem r hb
    · simp only [Prod.smul_snd, h, smul_add]

end MinrankTW


