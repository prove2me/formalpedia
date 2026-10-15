-- Prove2me | Definitions.Def_OAI_Combinatorics_Sensitivity_RecursiveProfiles
-- name    : OAI_Combinatorics_Sensitivity_RecursiveProfiles
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T01:19:58.658633+00:00
-- url     : https://prove2.me/theorems/6e9c137c-777c-445c-abdb-ac63a4af26c5
-- title:
--   Nested predicate families and their side and joint sensitivity profiles
-- statement:
--   Throughout, $I$ is a finite set, Boolean values are identified with $\{0,1\}$, and $x^{\{i\}}$ is the input $x \in \{0,1\}^I$ with coordinate $i$ flipped. The sensitivity of a Boolean function $f$ at $x$ is $s(f,x) = |\{ i \in I : f(x^{\{i\}}) \ne f(x) \}|$. A family is a tuple $F = (F_0, \dots, F_{h-1})$ of Boolean functions on $\{0,1\}^I$.
--
--   1. **Nested family.** $F$ is nested if acceptance by a member with a larger index implies acceptance by every member with a smaller index: for all $q \le q'$ and all $x$, $F_{q'}(x) = 1$ implies $F_q(x) = 1$. Equivalently the acceptance sets decrease, $F_0^{-1}(1) \supseteq F_1^{-1}(1) \supseteq \dots \supseteq F_{h-1}^{-1}(1)$.
--
--   2. **Joint sensitivity at a point.** For Boolean functions $f, g$ on $\{0,1\}^I$ and an input $x$, the number of coordinates whose flip changes both functions:
--   $$
--   s(f,g;x) = \big|\{ i \in I : f(x^{\{i\}}) \ne f(x) \text{ and } g(x^{\{i\}}) \ne g(x) \}\big| .
--   $$
--
--   3. **Side sensitivity.** For $b \in \{0,1\}$, the largest sensitivity of a member at an input where that member outputs $b$:
--   $$
--   S_b(F) = \max\{ s(F_q, x) : 0 \le q < h,\ x \in \{0,1\}^I,\ F_q(x) = b \}.
--   $$
--
--   4. **Joint sensitivity profile.** For $b \in \{0,1\}$, the largest joint sensitivity of two distinct members at a common input where both output $b$:
--   $$
--   J_b(F) = \max\{ s(F_q, F_{q'}; x) : 0 \le q < q' < h,\ F_q(x) = F_{q'}(x) = b \}.
--   $$
--
--   In both maxima an empty range gives the value $0$.
--
--   The four numbers $S_0(F), S_1(F), J_0(F), J_1(F)$ form the profile of a family. They are tracked level by level through the recursive construction of Boolean functions with small sensitivity and large block sensitivity, where they satisfy linear recurrences that eventually bound the sensitivity of the final function.
--
--   **Formalization Note** A family is a function `Fin h → (I → Bool) → Bool`, and `NestedFamily F` is a structure with the single field `accepts_of_le`. The definitions are `jointSensitivityAt`, `sideSensitivity` and `jointSensitivity`; the maxima are `Finset.sup` over natural numbers of an expression that is `0` outside the admissible range. Sensitivity `sensitivityAt` and the flip operation `flip` come from the base definitions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/Sensitivity/RecursiveProfiles.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/Sensitivity/RecursiveProfiles.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SensitivitySeparation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SensitivitySeparation
import Definitions.Def_OAI_Combinatorics_Sensitivity_HammingBase

namespace OAI

/-! The side and joint profiles count literal flips of the same raw input. -/

noncomputable section
open scoped Classical

namespace Paper320

/-- Acceptance at a stronger index implies acceptance at every weaker index. -/
structure NestedFamily {h : ℕ} {I : Type}
    (F : Fin h → (I → Bool) → Bool) : Prop where
  accepts_of_le : ∀ {q q' : Fin h} {x}, q ≤ q' → F q' x = true → F q x = true

/-- The number of coordinates whose one-bit flip changes both predicates. -/
def jointSensitivityAt {I : Type} [Fintype I]
    (f g : (I → Bool) → Bool) (x : I → Bool) : ℕ :=
  (Finset.univ.filter fun i =>
    f (flip x {i}) ≠ f x ∧ g (flip x {i}) ≠ g x).card

/-- Maximum sensitivity over all indices and inputs with the indicated output. -/
def sideSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) : ℕ :=
  Finset.univ.sup fun q => Finset.univ.sup fun x =>
    if F q x = b then sensitivityAt (F q) x else 0

/-- Maximum same-input, same-bit joint sensitivity over two distinct ordered indices. -/
def jointSensitivity {h : ℕ} {I : Type} [Fintype I]
    (F : Fin h → (I → Bool) → Bool) (b : Bool) : ℕ :=
  Finset.univ.sup fun q => Finset.univ.sup fun q' => Finset.univ.sup fun x =>
    if q < q' ∧ F q x = b ∧ F q' x = b then
      jointSensitivityAt (F q) (F q') x else 0

end Paper320

end

end OAI


