-- Prove2me | Definitions.Def_SmartPTO_Fisher_Setting
-- name    : SmartPTO_Fisher_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:26.019485+00:00
-- url     : https://prove2.me/theorems/fa66bdd3-0ce0-4c9a-839b-455631b2c0df
-- title:
--   The SPO and SPO+ losses, population risks, symmetry and continuous full-support laws
-- statement:
--   Let $S\subseteq\mathbb R^d$ be the feasible region and let $c,\hat c\in\mathbb R^d$ be cost vectors. The nominal value, optimal-decision set, and support function are
--
--   $$z^*(c)=\min_{w\in S}c^\top w,\qquad W^*(c)=\arg\min_{w\in S}c^\top w,\qquad \xi_S(c)=\max_{w\in S}c^\top w.$$
--
--   For any optimization oracle $w^*$ with $w^*(c)\in W^*(c)$, Definition 2's unambiguous loss and Definition 3's surrogate loss are
--
--   $$\ell_{\mathrm{SPO}}(\hat c,c)=\max_{w\in W^*(\hat c)}c^\top w-z^*(c),\qquad \ell_{\mathrm{SPO+}}(\hat c,c)=\xi_S(c-2\hat c)+2\hat c^\top w^*(c)-z^*(c).$$
--
--   The second formula is the support-function form of $\max_{w\in S}(c^\top w-2\hat c^\top w)+2\hat c^\top w^*(c)-z^*(c)$. For a cost law $P$, $R_{\mathrm{SPO}}$ and $R_{\mathrm{SPO+}}$ are the expected respective losses. For a joint feature-cost law $D$ and predictor $f$, the two population risks integrate the losses at $(f(x),c)$ over $D$ as in (11)–(12).
--
--   A cost law is centrally symmetric when it equals its image under $c\mapsto2\mathbb E_P[c]-c$. The formal reading of a law “continuous on all of $\mathbb R^d$” is absolute continuity with respect to Lebesgue measure together with positive mass on every nonempty open set.
--
--   These definitions provide the common objects for the consistency theorem and its supporting propositions.
--
--   **Formalization Note** All risks are extended nonnegative integrals of the nonnegative losses. The real infima and suprema represent the paper's extrema under the theorems' nonempty compact-set assumptions. Full support is an explicit pin on Assumption 1.3; absolute continuity alone does not imply uniqueness in Proposition 6(b).
-- source:
--   Elmachtoub & Grigas, Smart "Predict, then Optimize", arXiv:1710.08005v5, pp. 8–10, 12, 17, 20–23: (2), Definitions 2–3, (11)–(12), Assumption 1

import Mathlib
import Definitions.Def_SPOBounds_Natarajan_Model

open scoped InnerProductSpace
open MeasureTheory ProbabilityTheory

namespace SmartPTO.Fisher

/-- The nominal minimum value `z*(c)` in (2), p. 8. -/
noncomputable def zstar {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sInf ((fun w => ⟪c, w⟫_ℝ) '' S)

/-- The set `W*(c)` of nominal optimal decisions, p. 10. -/
def Wstar {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) : Set (EuclideanSpace ℝ (Fin d)) :=
  {w | w ∈ S ∧ ∀ v ∈ S, ⟪c, w⟫_ℝ ≤ ⟪c, v⟫_ℝ}

/-- The support function `ξ_S(c)`, p. 10. -/
noncomputable def xi {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun w => ⟪c, w⟫_ℝ) '' S)

/-- The unambiguous SPO loss of Definition 2, p. 12. -/
noncomputable def spoLoss {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (chat c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  sSup ((fun w => ⟪c, w⟫_ℝ) '' Wstar S chat) - zstar S c

/-- The equivalent support-function expression for the SPO+ loss in Definition 3, p. 17. -/
noncomputable def spoPlusLoss {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (chat c : EuclideanSpace ℝ (Fin d)) : ℝ :=
  xi S (c - (2 : ℝ) • chat) + 2 * ⟪chat, wstar c⟫_ℝ - zstar S c

/-- The true SPO risk `R_SPO` in §4.1, p. 22. -/
noncomputable def spoRisk {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (P : Measure (EuclideanSpace ℝ (Fin d))) (chat : EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ∫⁻ c, ENNReal.ofReal (spoLoss S chat c) ∂P

/-- The SPO+ risk `R_SPO+` in §4.1, p. 22. -/
noncomputable def spoPlusRisk {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d)))
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : Measure (EuclideanSpace ℝ (Fin d))) (chat : EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ∫⁻ c, ENNReal.ofReal (spoPlusLoss S wstar chat c) ∂P

/-- The true SPO population risk (11), p. 20. -/
noncomputable def spoRiskJoint {X : Type*} [MeasurableSpace X] {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (f : X → EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (spoLoss S (f p.1) p.2) ∂D

/-- The SPO+ population risk (12), p. 20. -/
noncomputable def spoPlusRiskJoint {X : Type*} [MeasurableSpace X] {d : ℕ}
    (S : Set (EuclideanSpace ℝ (Fin d)))
    (wstar : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (D : Measure (X × EuclideanSpace ℝ (Fin d)))
    (f : X → EuclideanSpace ℝ (Fin d)) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (spoPlusLoss S wstar (f p.1) p.2) ∂D

/-- A law equal to its reflection about its own mean, p. 21. -/
noncomputable def CentrallySymmetric {d : ℕ}
    (P : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  P.map (fun c => (2 : ℝ) • (∫ c', c' ∂P) - c) = P

/-- The full-support continuous-law reading of Assumption 1.3, p. 21. -/
def ContinuousOnAll {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d))) : Prop :=
  P ≪ volume ∧ ∀ U : Set (EuclideanSpace ℝ (Fin d)), IsOpen U → U.Nonempty → 0 < P U

end SmartPTO.Fisher


