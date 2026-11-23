-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Supplement_Types
-- name    : ProcureAssort_Hotelling_Supplement_Types
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T12:23:30.63385+00:00
-- url     : https://prove2.me/theorems/c406caf5-5875-480b-872c-0470de7516a8
-- title:
--   Supported probability laws, regularity, consecutive types and genuine optimal values
-- statement:
--   Suppliers have independent, finite supported types. Each support $\Theta_i$ is nonempty and consists of strictly positive real numbers; its probabilities $f_i(c)$ are positive and sum to one. The published definitions supply profiles, product probabilities, expectations and the virtual cost $v_i$. Regularity means that $v_i$ is strictly increasing on $\Theta_i$.
--
--   $$\sum_{c\in\Theta_i}f_i(c)=1,\qquad v_i(c)<v_i(c')\quad(c<c',\ c,c'\in\Theta_i).$$
--
--   Two costs are consecutive if both belong to the support and no supported cost lies strictly between them. `ValuesWellDefined` asserts nonempty, bounded-above objective sets for both mechanisms, using the published IC, IR and demand definitions. It prevents real supremum defaults from representing optimal values.
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), §2 and Assumption 3.1, pp. 7, 13

import Mathlib
import Definitions.Def_ProcureAssort_Hotelling_Setting

namespace ProcureAssort.Hotelling.Supplement

/-- The supported finite independent probability laws of §2, p. 7. -/
def ValidTypes {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) : Prop :=
  (∀ i, (Θ i).Nonempty) ∧ (∀ i, ∀ c ∈ Θ i, 0 < c) ∧
  (∀ i, ∀ c ∈ Θ i, 0 < f i c) ∧ (∀ i, ∑ c ∈ Θ i, f i c = 1)

/-- Assumption 3.1 applies only to supported types. -/
def Regular {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) : Prop :=
  ∀ i, StrictMonoOn (virtualCost Θ f i) (↑(Θ i) : Set ℝ)

/-- Consecutive supported costs, not natural-number subtraction. -/
def Consecutive (S : Finset ℝ) (a b : ℝ) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a < b ∧ ∀ c ∈ S, ¬ (a < c ∧ c < b)

/-- Nonempty bounded objective sets: the real suprema have their intended meaning. -/
def ValuesWellDefined {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (G : (Fin n → ℝ) → ℝ) : Prop :=
  let C := {r | ∃ x t : Profile Θ → Fin n → ℝ,
    IsCentFeasible f (simplex n) x t ∧ r = centObj f G x t}
  let D := {r | ∃ (q : Profile Θ → Finset (Fin n)) (p x : Profile Θ → Fin n → ℝ),
    IsDecLinFeasible f G (simplex n) q p x ∧ r = decLinObj f G p x}
  C.Nonempty ∧ BddAbove C ∧ D.Nonempty ∧ BddAbove D

end ProcureAssort.Hotelling.Supplement


