-- Prove2me | Definitions.Def_TangleStructTree_StronglyEfficient
-- name    : TangleStructTree_StronglyEfficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:21.28123+00:00
-- url     : https://prove2.me/theorems/0c8114d1-abbc-44d3-b170-2fecaf8b7dca
-- title:
--   Efficient and strongly efficient subsets
-- statement:
--   Let $\vec S$ be an ordered separation system. An oriented separation $\vec s$ is **weakly eclipsed** by $\vec r$ if $\vec r<\vec s$ and $|r|\le|s|$, and **eclipsed** by $\vec r$ if $\vec r<\vec s$ and $|r|<|s|$.
--
--   Given any set $\tau\subseteq\vec S$, a subset $\sigma\subseteq\tau$ is
--
--   1. **efficient** (in $\tau$) if no element of $\sigma$ is eclipsed by any other element of $\tau$;
--   2. **strongly efficient** (in $\tau$) if no element of $\sigma$ is weakly eclipsed by any other element of $\tau$.
--
--   Efficiency of the witnesses in $\mathcal F$ is what allows them to be found among the edge labels of a tree, not only in closures; it enters the definition of rich sets $\mathcal F$.
--
--   **Formalization Note** Both predicates include $\sigma\subseteq\tau$. "Any other element" is $y\ne x$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §4, p.8 (PDF 19)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- `σ` is **efficient** in `τ` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §4, p.8 (PDF 19)):
`σ ⊆ τ` and no element `s⃗` of `σ` is *eclipsed* by any other element `r⃗` of `τ`, where `s⃗` is
eclipsed by `r⃗` if `r⃗ < s⃗` and `|r| < |s|`. -/
def Efficient (ord : E → ℝ) (σ τ : Set E) : Prop :=
  σ ⊆ τ ∧ ∀ x ∈ σ, ∀ y ∈ τ, y ≠ x → ¬ (y < x ∧ ord y < ord x)

/-- `σ` is **strongly efficient** in `τ` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §4, p.8
(PDF 19)): `σ ⊆ τ` and no element `s⃗` of `σ` is *weakly eclipsed* by any other element `r⃗` of
`τ`, where `s⃗` is weakly eclipsed by `r⃗` if `r⃗ < s⃗` and `|r| ≤ |s|`. -/
def StronglyEfficient (ord : E → ℝ) (σ τ : Set E) : Prop :=
  σ ⊆ τ ∧ ∀ x ∈ σ, ∀ y ∈ τ, y ≠ x → ¬ (y < x ∧ ord y ≤ ord x)

end TangleStructTree


