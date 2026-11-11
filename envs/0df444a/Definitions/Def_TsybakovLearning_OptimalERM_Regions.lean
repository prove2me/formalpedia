-- Prove2me | Definitions.Def_TsybakovLearning_OptimalERM_Regions
-- name    : TsybakovLearning_OptimalERM_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:50:29.376011+00:00
-- url     : https://prove2.me/theorems/43b00520-f12d-42fd-9dff-77654fc6d044
-- title:
--   Binary classification, restricted regions, and the original ERM
-- statement:
--   Let $X$ be an arbitrary measurable instance space, let $D$ be a probability law on $X\times\{0,1\}$, and let $D_X$ be its first marginal. A classifier is a function $h:X\to\{0,1\}$. Its error region is $\mathrm{ER}(h)=\{(x,y):h(x)\ne y\}$. Its risk and empirical risk on a sample $S=((X_i,Y_i))_{i=1}^m$ are
--
--   $$\mathrm{er}_D(h)=\mathbb E_D\mathbf1\{h(X)\ne Y\},\qquad \widehat{\mathrm{er}}_S(h)=\frac1m\sum_{i=1}^m\mathbf1\{h(X_i)\ne Y_i\}.$$
--
--   For a measurable region $\Delta\subseteq X$, write $p=D_X(\Delta)$, $q=D_X(\{f\ne g\}\cap\Delta)$, and $\mathrm{er}_{D,\Delta}(h)=D(\mathrm{ER}(h)\cap(\Delta\times\{0,1\}))$. Restricted empirical risk and disagreement count observations in $\Delta$ but retain the original denominator $m$. Piecewise prediction uses $f$ on $\Delta$ and $g$ elsewhere. The empirical minimizers are exactly
--
--   $$\mathrm{ERM}(H;S)=\{h\in H:\forall g\in H,\ \widehat{\mathrm{er}}_S(h)\le\widehat{\mathrm{er}}_S(g)\}.$$
--
--   These definitions supply the region notation used by both concentration statements while keeping the classical learning rule unchanged. Measurable bounded loss makes the expectation equal to the error probability.
--
--   **Formalization Note** Labels use Bool, false for 0 and true for 1. Samples are functions on Fin m, preserving repetitions. The product law, 0–1 loss, risk, empirical risk, and IsERM are reused from UnderstandingML. Probability values are ENNReal; finite probabilities are converted to real numbers in risk and disagreement formulas. Definitions of empirical means are used only for positive sample sizes.
-- source:
--   Steve Hanneke, Hongao Wang, Mingyue Xu, STOC 2027 submission #1413 (October 2026), §2, p. 5 (PDF p. 5); ERM definition, p. 4 (PDF p. 4)

import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_UnderstandingML_VC
import Mathlib

open MeasureTheory

namespace TsybakovLearning.OptimalERM

variable {X : Type*} [MeasurableSpace X]

/-- The instance marginal; the projection is measurable on every measurable space. -/
noncomputable def marginal (D : Measure (X × Bool)) : Measure X := D.map Prod.fst

def errorRegion (h : X → Bool) : Set (X × Bool) := {z | h z.1 ≠ z.2}

def restrictedError (h : X → Bool) (Δ : Set X) : Set (X × Bool) :=
  {z | h z.1 ≠ z.2 ∧ z.1 ∈ Δ}

noncomputable def regionMass (D : Measure (X × Bool)) (Δ : Set X) : ℝ :=
  (marginal D Δ).toReal

noncomputable def disagreement (D : Measure (X × Bool)) (Δ : Set X)
    (f g : X → Bool) : ℝ := (marginal D {x | f x ≠ g x ∧ x ∈ Δ}).toReal

noncomputable def restrictedRisk (D : Measure (X × Bool)) (Δ : Set X)
    (h : X → Bool) : ℝ := (D (restrictedError h Δ)).toReal

noncomputable def restrictedLoss (Δ : Set X) (h : X → Bool) (z : X × Bool) : ℝ := by
  classical
  exact if z.1 ∈ Δ then UnderstandingML.loss01 h z else 0

noncomputable def restrictedEmpRisk {m : ℕ} (Δ : Set X) (S : Fin m → X × Bool)
    (h : X → Bool) : ℝ := UnderstandingML.empRisk (restrictedLoss Δ) S h

noncomputable def empiricalDisagreement {m : ℕ} (Δ : Set X) (S : Fin m → X × Bool)
    (f g : X → Bool) : ℝ := by
  classical
  exact (∑ i, if (S i).1 ∈ Δ ∧ f (S i).1 ≠ g (S i).1 then (1 : ℝ) else 0) / m

noncomputable def decisionList (Δ : Set X) (f g : X → Bool) : X → Bool := by
  classical
  exact fun x => if x ∈ Δ then f x else g x

noncomputable abbrev risk (D : Measure (X × Bool)) (h : X → Bool) : ℝ :=
  UnderstandingML.risk UnderstandingML.loss01 D h

noncomputable abbrev empRisk {m : ℕ} (S : Fin m → X × Bool) (h : X → Bool) : ℝ :=
  UnderstandingML.empRisk UnderstandingML.loss01 S h

abbrev IsERM (H : Set (X → Bool)) {m : ℕ} (S : Fin m → X × Bool) (h : X → Bool) : Prop :=
  UnderstandingML.IsERM UnderstandingML.loss01 H S h

end TsybakovLearning.OptimalERM


