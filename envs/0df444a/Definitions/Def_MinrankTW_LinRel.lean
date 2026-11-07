-- Prove2me | Definitions.Def_MinrankTW_LinRel
-- name    : MinrankTW_LinRel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:31:47.546381+00:00
-- url     : https://prove2.me/theorems/7d313609-d440-4592-bc6c-01b06dcb73bb
-- title:
--   Linear relations: $\mathrm{dom}\,R$, $R(0)$ and $K(R)$
-- statement:
--   A **linear relation** between $\mathbb F^a$ and $\mathbb F^c$ is a subspace $R\le\mathbb F^a\oplus\mathbb F^c$; its elements are pairs $(x,y)$, and a given $x$ may be paired with several $y$ or with none. Attached to it are
--   $$
--   \mathrm{dom}\,R=\{x:\exists y,\ (x,y)\in R\},\qquad R(0)=\{y:(0,y)\in R\},\qquad K(R)=\{x:(x,0)\in R\}.
--   $$
--   If $(x,y)\in R$, the vectors paired with $x$ form $y+R(0)$.
--
--   **Formalization Note** Relations are submodules of $(\alpha\to\mathbb F)\times(\gamma\to\mathbb F)$ for finite index types $\alpha$ ($a=|\alpha|$) and $\gamma$ ($c=|\gamma|$).
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), Definition 1, p.6; Section 3.1, p.9; Section 2.1, p.7

import Mathlib

namespace MinrankTW

/-!
# Linear relations: domain, zero fibre, kernel part

Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), Definition 1, p.6: a **linear relation** between `F^a` and `F^c` is a subspace
`R ≤ F^a ⊕ F^c`; its elements are pairs `(x, y)`. §3.1, p.9: `dom R = {x : ∃ y, (x, y) ∈ R}`
and `R(0) = {y : (0, y) ∈ R}`; §2.1, p.7 (and Lemma 1, p.10): `K(R) = {x : (x, 0) ∈ R}`.

**Formalization Note** A linear relation is any `Submodule F ((α → F) × (γ → F))` for finite
index types `α` (the `x`-coordinates, `a = |α|`) and `γ` (the `y`-coordinates,
`c = |γ|`); no separate structure is introduced. The three spaces are the image under the first
projection, the preimage under `y ↦ (0, y)` and the preimage under `x ↦ (x, 0)`.
-/

variable {F : Type*} [Field F] {α γ : Type*}

/-- `dom R = {x : ∃ y, (x, y) ∈ R}` (p.9). -/
def relDom (R : Submodule F ((α → F) × (γ → F))) : Submodule F (α → F) :=
  R.map (LinearMap.fst F (α → F) (γ → F))

/-- `R(0) = {y : (0, y) ∈ R}` (p.9). -/
def relZero (R : Submodule F ((α → F) × (γ → F))) : Submodule F (γ → F) :=
  R.comap (LinearMap.inr F (α → F) (γ → F))

/-- `K(R) = {x : (x, 0) ∈ R}` (p.7, p.10). -/
def relKer (R : Submodule F ((α → F) × (γ → F))) : Submodule F (α → F) :=
  R.comap (LinearMap.inl F (α → F) (γ → F))

end MinrankTW


