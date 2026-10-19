-- Prove2me | Definitions.Def_FairProxy_ClosedFormDD_Model
-- name    : FairProxy_ClosedFormDD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:17.198356+00:00
-- url     : https://prove2.me/theorems/13156598-7a35-4bf9-a0e4-06fd02338d6f
-- title:
--   §2 and §§4–5 — observed marginals, consistent joints, demographic disparity and weights
-- statement:
--   The model contains a binary decision $\hat Y$, binary true outcome $Y$, a two-class protected attribute $A\in\{a,b\}$, and a proxy $Z$ in an arbitrary measurable space. The observed primary and auxiliary marginals share $P(Z)$ and are represented by measurable conditional vectors $P(\hat Y,Y\mid Z)$ and $P(A\mid Z)$.
--
--   A compatible joint in $\mathcal P_D$ is a measurable conditional coupling of those two vectors. For each compatible joint $P'$, demographic disparity is
--
--   $$
--   \delta_{DD}(a,b;P')=P'(\hat Y=1\mid A=a)-P'(\hat Y=1\mid A=b),\qquad
--   \Delta_{DD}(\mathcal P_D)=\{\delta_{DD}(a,b;P'):P'\in\mathcal P_D\}.
--   $$
--
--   The file also defines the weighted expectation $\mu(\alpha;w)$, the induced weight set $\mathcal W(\mathcal P_D)$, and the two Fréchet–Hoeffding weight functions $w^L,w^U$ used by Proposition 7. These definitions keep the identification set tied to full compatible joints.
--
--   **Formalization Note** The class probabilities and conditional positive-decision rates are integrals over $P(Z)$; the denominator of a candidate joint's rate is computed from that joint. Weight identities are imposed only on positive-probability decision cells. A measurable conditional coupling is required for every proxy value, choosing a version of the paper's almost-everywhere conditional law.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, pp. 5–15, §2.1, Definition 1, Eqs. (1), (3), (4), (7), (9), Proposition 7

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Coupling

namespace FairProxy.ClosedFormDD
open MeasureTheory

/-- The two protected groups in Section 5. -/
inductive Cls | a | b
  deriving DecidableEq

instance : Fintype Cls where
  elems := {.a, .b}
  complete := by
    intro x
    cases x <;> simp

/-- The observed primary and auxiliary marginals, expressed as a shared proxy law and
conditional probability vectors. -/
structure Marginals (Z : Type*) [MeasurableSpace Z] where
  PZ : Measure Z
  etaAux : Cls → Z → ℝ
  etaPriT : Fin 2 → Fin 2 → Z → ℝ

variable {Z : Type*} [MeasurableSpace Z]

/-- Each conditional vector is measurable, nonnegative, and normalized; the proxy law is a probability measure. -/
def Marginals.Valid (M : Marginals Z) : Prop :=
  IsProbabilityMeasure M.PZ ∧
  (∀ α, Measurable (M.etaAux α)) ∧
  (∀ ŷ y, Measurable (M.etaPriT ŷ y)) ∧
  (∀ α z, 0 ≤ M.etaAux α z) ∧
  (∀ z, ∑ α, M.etaAux α z = 1) ∧
  (∀ ŷ y z, 0 ≤ M.etaPriT ŷ y z) ∧
  (∀ z, ∑ ŷ, ∑ y, M.etaPriT ŷ y z = 1)

/-- The primary conditional probability of the decision alone. -/
def etaPri (M : Marginals Z) (ŷ : Fin 2) (z : Z) : ℝ :=
  ∑ y, M.etaPriT ŷ y z

/-- The protected-group probability from the auxiliary marginal. -/
noncomputable def probA (M : Marginals Z) (α : Cls) : ℝ :=
  ∫ z, M.etaAux α z ∂M.PZ

/-- Equation (3): a measurable conditional joint law coupling the two observed conditionals at every proxy value. -/
def IsInPD (M : Marginals Z) (π : Cls → Fin 2 → Fin 2 → Z → ℝ) : Prop :=
  (∀ α ŷ y, Measurable (π α ŷ y)) ∧
  ∀ z, (fun (p : Fin 2 × Fin 2) (α : Cls) => π α p.1 p.2 z) ∈
    couplingSet (fun p : Fin 2 × Fin 2 => M.etaPriT p.1 p.2 z)
      (fun α => M.etaAux α z)

/-- The positive-decision rate conditional on a protected group in the candidate joint law. -/
noncomputable def condPosRate (M : Marginals Z)
    (π : Cls → Fin 2 → Fin 2 → Z → ℝ) (α : Cls) : ℝ :=
  (∫ z, ∑ y, π α 1 y z ∂M.PZ) /
    (∫ z, ∑ ŷ, ∑ y, π α ŷ y z ∂M.PZ)

/-- Demographic disparity of the candidate joint law, Section 2.1. -/
noncomputable def deltaDD (M : Marginals Z)
    (π : Cls → Fin 2 → Fin 2 → Z → ℝ) : ℝ :=
  condPosRate M π .a - condPosRate M π .b

/-- The partial identification set of demographic disparity, equations (3) and (4), with no extra restrictions. -/
def PIsetDD (M : Marginals Z) : Set ℝ :=
  {d | ∃ π, IsInPD M π ∧ deltaDD M π = d}

/-- Equation (7): weighted positive-decision probability divided by the group's observed mass. -/
noncomputable def mu (M : Marginals Z) (α : Cls)
    (w : Cls → Fin 2 → Z → ℝ) : ℝ :=
  (∫ z, ∑ ŷ : Fin 2, w α ŷ z * ((ŷ : ℕ) : ℝ) * etaPri M ŷ z ∂M.PZ) /
    probA M α

/-- The lower weight in Proposition 7. -/
noncomputable def wL (M : Marginals Z) (α : Cls) (ŷ : Fin 2) (z : Z) : ℝ :=
  max 0 (1 + (M.etaAux α z - 1) / etaPri M ŷ z)

/-- The upper weight in Proposition 7. -/
noncomputable def wU (M : Marginals Z) (α : Cls) (ŷ : Fin 2) (z : Z) : ℝ :=
  min 1 (M.etaAux α z / etaPri M ŷ z)

/-- Equation (9): conditional protected-class weights induced by a consistent joint,
identified only when the conditioning cell has positive probability. -/
def WPD (M : Marginals Z) : Set (Cls → Fin 2 → Z → ℝ) :=
  {w | (∀ α ŷ, Measurable (w α ŷ)) ∧
    ∃ π, IsInPD M π ∧
      ∀ α ŷ z, 0 < etaPri M ŷ z →
        w α ŷ z = (∑ y, π α ŷ y z) / etaPri M ŷ z}

end FairProxy.ClosedFormDD


