-- Prove2me | Definitions.Def_ZerothLawThermo_Defs
-- name    : ZerothLawThermo_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:24:21.773366+00:00
-- url     : https://prove2.me/theorems/f29fc959-d99d-4d04-9416-a49597e9ee43
-- title:
--   Zeroth law of thermodynamics: thermal equilibrium vocabulary
-- statement:
--   This definition file fixes the vocabulary for the mission. Throughout, $S$ is a type of thermodynamic systems and $\mathrm{TE}$ is a binary relation on $S$, with $\mathrm{TE}(A,B)$ read as "$A$ is in thermal equilibrium with $B$".
--
--   1. **Zeroth law** (right-Euclidean form): $\mathrm{TE}$ satisfies the zeroth law if
--   $$\forall A,B,C\in S,\quad \mathrm{TE}(A,C)\wedge \mathrm{TE}(B,C)\Longrightarrow \mathrm{TE}(A,B),$$
--   i.e. two systems both in thermal equilibrium with a third are in thermal equilibrium with each other.
--   2. **Planck's form** (left-Euclidean form):
--   $$\forall A,B,C\in S,\quad \mathrm{TE}(C,A)\wedge \mathrm{TE}(C,B)\Longrightarrow \mathrm{TE}(A,B),$$
--   i.e. if a body $C$ is in thermal equilibrium with two bodies $A$ and $B$, then $A$ and $B$ are in thermal equilibrium with one another.
--   3. **Empirical temperature**: a map $t:S\to T$ into an arbitrary type $T$ is an empirical temperature for $\mathrm{TE}$ if
--   $$\forall A,B\in S,\quad \mathrm{TE}(A,B)\iff t(A)=t(B).$$
--
--   These are the objects in terms of which all theorems of the mission are stated.
--
--   **Formalization Note** Reflexivity of $\mathrm{TE}$ is deliberately not built into these definitions; theorems that need it state it as a hypothesis.
-- source:
--   Wikipedia, "Zeroth law of thermodynamics", revision oldid=1328026962, https://en.wikipedia.org/w/index.php?title=Zeroth_law_of_thermodynamics&oldid=1328026962; sections "Equivalence relation" and "Foundation of temperature"

import Mathlib

namespace ZerothLawThermo

/-- The zeroth law of thermodynamics in its usual ("right-Euclidean") form, for a relation
`TE` of thermal equilibrium on a type `S` of thermodynamic systems: if two systems `A` and `B`
are both in thermal equilibrium with a third system `C`, then `A` and `B` are in thermal
equilibrium with each other. -/
def ZerothLaw {S : Type*} (TE : S → S → Prop) : Prop :=
  ∀ A B C : S, TE A C → TE B C → TE A B

/-- Planck's ("left-Euclidean") form of the zeroth law: if a system `C` is in thermal
equilibrium with two other systems `A` and `B`, then `A` and `B` are in thermal equilibrium
with one another. -/
def ZerothLawPlanck {S : Type*} (TE : S → S → Prop) : Prop :=
  ∀ A B C : S, TE C A → TE C B → TE A B

/-- A tagging `t : S → T` of systems is an empirical temperature scale for the thermal
equilibrium relation `TE` if two systems are in thermal equilibrium exactly when they carry
the same tag. -/
def IsEmpiricalTemperature {S T : Type*} (TE : S → S → Prop) (t : S → T) : Prop :=
  ∀ A B : S, TE A B ↔ t A = t B

end ZerothLawThermo


