-- Prove2me | Definitions.Def_TangleStructTree_IsOrientation
-- name    : TangleStructTree_IsOrientation
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:52:07.189887+00:00
-- url     : https://prove2.me/theorems/81660069-2bc3-49ff-88b1-0fa9505d5f14
-- title:
--   Orientations and partial orientations of $S$
-- statement:
--   Let $(\vec S,\le,{}^*)$ be a separation system with unoriented separations $S$. A set $\sigma\subseteq\vec S$ **orients** $s\in S$ if it contains $\vec s$ or $\overleftarrow{s}$.
--
--   1. An **orientation of $S$** is a set $\tau\subseteq\vec S$ that contains exactly one orientation of every $s\in S$.
--   2. A **partial orientation of $S$** is an orientation of a subset of $S$, that is, a set $\tau\subseteq\vec S$ that never contains both orientations of a separation.
--
--   Tangles are particular orientations of $S$, and the structure trees of the mission store orientations along their root–leaf paths.
--
--   **Formalization Note** "Exactly one orientation of $s$" is encoded as: $x\in\tau$ or $x^*\in\tau$, and if both lie in $\tau$ then $x^*=x$. A degenerate separation has a single orientation, which therefore lies in every orientation of $S$.
-- source:
--   von Bergen, Diestel, Tangle structure trees, arXiv:2601.15870 (STOC 2027 submission build of 2026-10-31, sha256 7670745285d0070c890a0203dfe9e72ef24717b9e9d824274becd54ce276803b), journal version (Part I), §2, p.4 (PDF 15)

import Mathlib
import Definitions.Def_TangleStructTree_SepSystem

namespace TangleStructTree

open SepSystem

variable {E : Type*} [PartialOrder E] [SepSystem E]

/-- A set `σ ⊆ S⃗` **orients** the separation `s` underlying `x` if it contains one of its two
orientations `x`, `x∗` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.4 (PDF 15)). -/
def Orients (σ : Set E) (x : E) : Prop :=
  x ∈ σ ∨ rev x ∈ σ

/-- A **partial orientation** of `S` (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.4
(PDF 15)): an orientation of a subset of `S`, i.e. a set `τ ⊆ S⃗` that never contains both
orientations of a non-degenerate separation.

**Formalization Note** `τ` contains at most one orientation of each `s ∈ S`: if `x ∈ τ` and
`x∗ ∈ τ` then `x∗ = x` (`s` is degenerate, so it has only one orientation). -/
def IsPartialOrientation (τ : Set E) : Prop :=
  ∀ x, x ∈ τ → rev x ∈ τ → rev x = x

/-- An **orientation of `S`** (von Bergen, Diestel, *Tangle structure trees*, arXiv:2601.15870 (STOC 2027 submission build, sha256 7670745…), journal version, §2, p.4 (PDF 15)):
a set `τ ⊆ S⃗` that contains exactly one orientation of every `s ∈ S`.

**Formalization Note** "Exactly one orientation of `s`": `τ` contains `x` or `x∗`, and if it
contains both then `x∗ = x`. A degenerate separation (`x∗ = x`) has a single orientation, which
must lie in every orientation of `S`. -/
def IsOrientation (τ : Set E) : Prop :=
  ∀ x, Orients τ x ∧ (x ∈ τ → rev x ∈ τ → rev x = x)

end TangleStructTree


