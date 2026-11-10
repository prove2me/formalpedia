-- Prove2me | Definitions.Def_RandLatEnum_dualInSpan
-- name    : RandLatEnum_dualInSpan
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:47.984097+00:00
-- url     : https://prove2.me/theorems/58f38a48-c795-4340-be0a-d1271d5325b3
-- title:
--   Dual lattice in the span, $L^*=\{y:\langle y,L\rangle\subset\mathbb Z\}$
-- statement:
--   The **dual** of a lattice $L$ in its span is
--   $$
--   L^*=\{\,y\in\mathrm{span}_{\mathbb R}L : \langle y,v\rangle\in\mathbb Z\text{ for all } v\in L\,\}.
--   $$
--   For a lattice of rank $d$ and covolume $\det L$ it is a lattice of rank $d$ and covolume $1/\det L$ in the same span.
--
--   **Formalization Note** $y$ ranges over the real span of $L$, not over the whole ambient space: for a lattice of lower rank the ambient dual is not discrete. The dual is a set of vectors.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.3, p.16

import Mathlib

namespace RandLatEnum

/-- The dual of a lattice `L` in its span, `L* = {y : ⟨y, L⟩ ⊂ ℤ}` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), §2.3, p.16: "The dual of
a lattice L in its span is L∗ = {y : ⟨y, L⟩ ⊂ Z}").

**Formalization Note.** `y` ranges over the real span of `L`, not the whole ambient space: for a
lattice of lower rank the ambient dual is not discrete. -/
def dualInSpan {k : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin k))) :
    Set (EuclideanSpace ℝ (Fin k)) :=
  {y | y ∈ Submodule.span ℝ (L : Set (EuclideanSpace ℝ (Fin k))) ∧
    ∀ v ∈ L, ∃ z : ℤ, inner ℝ y v = (z : ℝ)}

end RandLatEnum


