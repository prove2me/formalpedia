-- Prove2me | Definitions.Def_ZKSheafPCP_CodedSpace
-- name    : ZKSheafPCP_CodedSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:09:39.53819+00:00
-- url     : https://prove2.me/theorems/82ba4118-a0f3-4204-8b4f-d62bad90146a
-- title:
--   Coded spaces, upper sets and covers
-- statement:
--   A **coded space** over a finite domain $D$ is a poset whose maximal elements are the points of $D$, with $\rho\le\tau$ if and only if $P_\rho\supseteq P_\tau$, where $P_\rho$ is the set of maximal elements above $\rho$. Since $\rho$ is determined by $P_\rho$, a coded space is a family of nonempty subsets of $D$ containing all singletons, ordered by reverse inclusion. An **upper set** is a subfamily closed under passing to subsets in the family. $U_S$ is the upper closure of $S$, $P_{\ge\sigma}$ the primitive upper set of $\sigma$, $P_U=\bigcup U$, and a **cover** is a subfamily whose union is $D$.
--
--   This is the combinatorial layer of sheaf codes [PK24].
--
--   **Formalization Note** Each element is represented by its set $P_\rho$. Restrictions are zero-padded (Definition 3.9), so words are functions on all of $D$.
-- source:
--   Zeilberger, O'Connor, Gur, Spooner, Zero-Knowledge PCPs of Quasilinear Size via Locally Simulatable Sheaf Codes, STOC 2027 submission (manuscript sha256 ac5e528f…), Definitions 4.2, 4.4, 4.6, 4.12, 4.13, pp.14–15

import Mathlib

namespace ZKSheafPCP

open Classical

/-- A coded space over a finite domain `D` (Zeilberger, O'Connor, Gur, Spooner, STOC 2027 submission, manuscript
sha256 ac5e528f…, Definitions 4.4–4.6, pp.14–15), as a family of nonempty subsets of `D` containing all
singletons.

**Formalization Note** By Definition 4.6 an element `ρ` of a coded space is determined by `P_ρ`, the maximal
elements above it, and `ρ ⩽ τ` if and only if `P_ρ ⊇ P_τ`. So a coded space is a set family with
`ρ ⩽ τ ⟺ τ ⊆ ρ` and `P_ρ = ρ`; the maximal elements are the singletons, identified with `D` (`P∗ = D`). -/
structure CodedSpace (D : Type) where
  /-- the elements, each given by its set `P_ρ` -/
  P : Finset (Finset D)
  /-- the maximal elements are the points of `D` -/
  singleton_mem : ∀ x : D, {x} ∈ P
  /-- `P_ρ` is nonempty -/
  nonempty_of_mem : ∀ ρ ∈ P, ρ.Nonempty

namespace CodedSpace

variable {D : Type} (PP : CodedSpace D)

/-- An upper set of the coded space (Definition 4.2, p.14): a subfamily of `P`, closed under passing to larger
elements of the poset, i.e. to subsets in `P`. -/
def IsUpper (U : Finset (Finset D)) : Prop :=
  U ⊆ PP.P ∧ ∀ ρ ∈ U, ∀ τ ∈ PP.P, τ ⊆ ρ → τ ∈ U

/-- The upper set closure `U_S` (Definition 4.13, p.15). -/
noncomputable def closure (S : Finset (Finset D)) : Finset (Finset D) :=
  PP.P.filter fun τ => ∃ σ ∈ S, τ ⊆ σ

/-- The primitive upper set `P⩾σ` (Definition 4.2, p.14). -/
noncomputable def geq (σ : Finset D) : Finset (Finset D) :=
  PP.P.filter fun τ => τ ⊆ σ

/-- A cover of the coded space (Definition 4.12, p.15). -/
def IsCover (S : Finset (Finset D)) : Prop :=
  S ⊆ PP.P ∧ ∀ x : D, ∃ ρ ∈ S, x ∈ ρ

end CodedSpace

/-- `P_U`, the maximal elements of an upper set (Definition 4.4, p.14), as a subset of `D`. -/
noncomputable def supp {D : Type} (U : Finset (Finset D)) : Finset D :=
  U.biUnion id

/-- The restriction `c|_S`, zero-padded (Definition 3.9, p.11): it agrees with `c` on `S` and vanishes
elsewhere. -/
noncomputable def restr {D F : Type} [Zero F] (S : Finset D) (c : D → F) : D → F :=
  fun x => if x ∈ S then c x else 0

end ZKSheafPCP


