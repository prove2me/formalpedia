-- Prove2me | Definitions.Def_UncrowdedColoring_IsCompatible
-- name    : UncrowdedColoring_IsCompatible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:12:28.733944+00:00
-- url     : https://prove2.me/theorems/3629308e-fb88-4cf1-a7e4-ee883e02c700
-- title:
--   Partial color assignments, their union, and $(L,F)$-compatibility
-- statement:
--   A **partial color assignment** for $U$ is a function $\psi:S\to\mathbb N$ on a subset $S=\mathrm{supp}(\psi)\subseteq U$. It is **$(L,F)$-compatible** if
--
--   1. $\psi(v)\in L(v)$ for every $v\in\mathrm{supp}(\psi)$, and
--   2. for every $c\in L(U)$ there is no edge $e\in E(F_c)$ with $e\subseteq\mathrm{supp}(\psi)$ and $\psi(v)=c$ for all $v\in e$.
--
--   Assignments with disjoint supports are combined by taking their union. Compatibility is the notion of partial proper coloring that the iteration preserves.
--
--   **Formalization Note** $\psi$ is `V → Option ℕ` with `none` off the support; the union takes the first assignment where it is defined.
-- source:
--   Dhawan, Methuku, Vo, List Coloring Uncrowded Hypergraphs at the Shattering Threshold, STOC 2027 submission (manuscript sha256 2e7243ce…), Definitions 4.3, 4.4, p.17

import Mathlib
import Definitions.Def_UncrowdedColoring_IsRestrictionFamily

open scoped Classical

namespace UncrowdedColoring

/-- **Partial color assignment for `U`** (Definition 4.3, p.17): "a function ψ : S → N, defined on
some subset S ⊆ U." (Dhawan, Methuku, Vo, manuscript sha256 2e7243ce…, p.17.)

**Formalization Note.** `ψ : V → Option ℕ` with `ψ v = none` off the support `S`; the predicate says
the support lies in `U`. -/
def IsPartialAssignment {V : Type*} (U : Finset V) (ψ : V → Option ℕ) : Prop :=
  ∀ v, ψ v ≠ none → v ∈ U

/-- The union `ψ₁ ∪ ψ₂` of two partial color assignments (Definition 4.3, p.17): it agrees with `ψ₁`
on `supp(ψ₁)` and with `ψ₂` on `supp(ψ₂)`.

**Formalization Note.** The paper takes the union for pairwise disjoint supports, where the order
is immaterial; the mission only applies it to `ψ` and `ψ̃` with `supp(ψ̃) ⊆ U \ supp(ψ)`. -/
def unionAssign {V : Type*} (ψ₁ ψ₂ : V → Option ℕ) : V → Option ℕ :=
  fun v => (ψ₁ v).orElse fun _ => ψ₂ v

/-- **Compatible coloring** (Definition 4.4, p.17): "A partial color assignment ψ for U is
(L, F)-compatible if: (i) ψ(v) ∈ L(v) for every v ∈ supp(ψ); and (ii) for every c ∈ L(U), there is no
edge e ∈ E(F_c) with e ⊆ supp(ψ) and ψ(v) = c for every v ∈ e." (Dhawan, Methuku, Vo, manuscript
sha256 2e7243ce…, p.17.)

**Formalization Note.** `∀ v ∈ e, ψ v = some c` contains both `e ⊆ supp(ψ)` and the color condition.
That `ψ` is for `U` is the separate predicate `IsPartialAssignment U ψ`. -/
def IsCompatible {V : Type*} (U : Finset V) (L : V → Finset ℕ) (F : ℕ → Finset (Finset V))
    (ψ : V → Option ℕ) : Prop :=
  (∀ v c, ψ v = some c → c ∈ L v) ∧
    ∀ c ∈ colours U L, ∀ e ∈ F c, ¬ ∀ v ∈ e, ψ v = some c

end UncrowdedColoring


