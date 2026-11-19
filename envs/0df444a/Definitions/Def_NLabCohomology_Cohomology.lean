-- Prove2me | Definitions.Def_NLabCohomology_Cohomology
-- name    : NLabCohomology_Cohomology
-- status  : Definition
-- author  : @LG
-- created : 2026-11-18T20:45:03.10788+00:00
-- url     : https://prove2.me/theorems/91e91b96-90e8-4fd5-ad1b-e967ca84db8a
-- title:
--   Cocycles, coboundaries, cohomology sets, characteristic and trivial cocycles
-- statement:
--   This definition file formalizes the general definition of cohomology from the nLab entry "cohomology", section "Definition / General definition". Let $\mathbf{H}$ be an (∞,1)-category (as fixed in the companion definition file), and let $X$ and $A$ be objects of $\mathbf{H}$, with $A$ the **coefficient object**.
--
--   - A **cocycle** on $X$ with coefficients in $A$ is an object of the hom ∞-groupoid $\mathbf{H}(X,A)$: a $0$-simplex, i.e. a morphism $c : X \to A$ in $\mathbf{H}$ (`Cocycle`).
--   - A **coboundary** between cocycles $c_1$ and $c_2$ is a morphism $\lambda : c_1 \to c_2$ in $\mathbf{H}(X,A)$: an edge from $c_1$ to $c_2$ (`Coboundary`). Two cocycles connected by a coboundary are **cohomologous** (`Cohomologous`).
--   - The **cohomology class** $[c]$ of a cocycle is its class in the set of connected components (`cohomologyClass`), and the **cohomology set** of $X$ with coefficients in $A$ is
--   $$H(X,A) \coloneqq \pi_0\,\mathbf{H}(X,A)$$
--   (`Cohomology`).
--   - For a cocycle $c$ on $X$ and a cocycle $k : A \to B$ on the coefficient object, `charCocycle` is the composite cocycle $k(c) : X \xrightarrow{c} A \xrightarrow{k} B$; its cohomology class $[k(c)] \in H(X,B)$ is the **characteristic class** of $c$ with respect to $k$ (well-definedness on cohomology is the mission's characteristic-class milestone).
--   - If $A$ is pointed by $* \to A$, the **trivial cocycle** on $X$ is the composite $X \to * \to A$ (`trivialCocycle`), where $X \to *$ is any cocycle into the terminal object; any two such are cohomologous by the trivial-cocycle milestone, so its class is canonical. A cocycle cohomologous to the trivial cocycle is called a **coboundary** (`IsCoboundary`).
--
--   As the source remarks, there is no notion of cochain in this general setup: cochains are components of specific models of $\mathbf{H}(X,A)$.
--
--   **Formalization Note.** Cocycles are $0$-simplices, coboundaries are `SSet.Edge`s, and the cohomology set is Mathlib's `SSet.π₀` of the hom Kan complex; `Cohomologous` is Mathlib's `SSet.π₀Rel` (existence of an edge). The trivial cocycle uses `Classical.choice` of a cocycle into the terminal object, whose existence is part of contractibility.
-- source:
--   nLab, 'cohomology', section 3 (Definition), subsection 'General definition'; https://ncatlab.org/nlab/show/cohomology#Definition (page last revised August 11, 2026). Bullets: cocycles; trivial cocycle; coboundaries and cohomologous cocycles; cohomology classes; the cohomology set H(X,A) = π₀𝐇(X,A); characteristic class [k(c)].

import Definitions.Def_NLabCohomology_Ambient
import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# The general definition of cohomology (nLab, "cohomology", Definition)

Cocycles, coboundaries, cohomologous cocycles, cohomology classes, the
cohomology set `H(X, A) = π₀ 𝐇(X, A)`, the composite (characteristic) cocycle,
and the trivial cocycle of a pointed coefficient object, following the
"General definition" subsection of the nLab entry "cohomology".
-/

universe u

open CategoryTheory Simplicial Opposite

namespace NLabCohomology

variable (H : InfinityOneCategory.{u})

/-- A **cocycle** on `X` with coefficients in `A`: an object of the hom
∞-groupoid `𝐇(X, A)`, i.e. a `0`-simplex, a morphism `c : X ⟶ A` in `𝐇`. -/
abbrev Cocycle (X A : H.Obj) : Type u := H.hom X A _⦋0⦌

/-- A **coboundary** between cocycles `c₁` and `c₂`: a morphism `λ : c₁ ⟶ c₂`
in the hom ∞-groupoid `𝐇(X, A)`, i.e. an edge from `c₁` to `c₂`. -/
abbrev Coboundary {X A : H.Obj} (c₁ c₂ : Cocycle H X A) : Type u :=
  (H.hom X A).Edge c₁ c₂

/-- Two cocycles are **cohomologous** when they are connected by a coboundary. -/
def Cohomologous {X A : H.Obj} (c₁ c₂ : Cocycle H X A) : Prop :=
  SSet.π₀Rel c₁ c₂

/-- The **cohomology set** `H(X, A) ≔ π₀ 𝐇(X, A)`: the type of cohomology
classes of `A`-valued cocycles on `X`. -/
def Cohomology (X A : H.Obj) : Type u := SSet.π₀ (H.hom X A)

/-- The cohomology class `[c]` of a cocycle `c`. -/
def cohomologyClass {X A : H.Obj} (c : Cocycle H X A) : Cohomology H X A :=
  SSet.π₀.mk c

/-- The composite cocycle `k(c) : X ⟶ B` of a cocycle `c : X ⟶ A` on `X` and a
cocycle `k : A ⟶ B` on the coefficient object. Its cohomology class is the
characteristic class of `c` with respect to `k`. -/
def charCocycle {X A B : H.Obj} (c : Cocycle H X A) (k : Cocycle H A B) :
    Cocycle H X B :=
  H.comp c k

/-- The **trivial cocycle** on `X` with coefficients in a pointed object `A`:
the composite `X ⟶ * ⟶ A`, where `X ⟶ *` is any cocycle into the terminal
object. All cocycles into the terminal object are cohomologous (see
`NLabCohomology.trivialCocycle_cohomologous`), so the cohomology class of the
trivial cocycle is canonical. -/
noncomputable def trivialCocycle (T : TerminalObject H) (A : PointedObject H T)
    (X : H.Obj) : Cocycle H X A.A :=
  H.comp (Classical.choice (T.contractible X).1) A.pt

/-- A cocycle cohomologous to the trivial cocycle is called a **coboundary**
(the terminological specialization noted in the nLab general definition). -/
def IsCoboundary (T : TerminalObject H) (A : PointedObject H T) {X : H.Obj}
    (c : Cocycle H X A.A) : Prop :=
  Cohomologous H c (trivialCocycle H T A X)

end NLabCohomology


