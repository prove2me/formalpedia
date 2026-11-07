-- Prove2me | Definitions.Def_LDPSelect_Values
-- name    : LDPSelect_Values
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:57:13.13979+00:00
-- url     : https://prove2.me/theorems/681c5051-67bc-46c2-a9c6-3f29e47efc0a
-- title:
--   The optimal rewards $W^{\mathrm I}_{\mathcal F}$, $W^{\mathrm N}_{\mathcal F}$, uselessness of interaction, and the prophet value
-- statement:
--   For a downward-closed family $\mathcal F$, a privacy level $a$ and laws $P_1,\dots,P_n$ of independent values:
--
--   1. $W^{\mathrm I}_{\mathcal F}$ is the supremum of the expected reward over all measurable output spaces and all $a$-locally private mechanisms that respect $\mathcal F$ (sequentially interactive model);
--   2. $W^{\mathrm N}_{\mathcal F}$ is the same supremum over non-interactive mechanisms;
--   3. a prior is **integrable** if every $X_i$ has finite mean, and **bounded** if some constant bounds every $X_i$ almost surely;
--   4. **interaction is useless** for $\mathcal F$ if $W^{\mathrm I}=W^{\mathrm N}$ for the relabelled family $\mathcal F^\sigma$, every arrival order $\sigma$ and every integrable product prior;
--   5. $\mathcal F$ **has a gap** if for some arrival order and some bounded product prior $W^{\mathrm N}<W^{\mathrm I}$;
--   6. the prophet's reward is $M_{\mathcal F}=\mathbb E\max_{S\in\mathcal F}\sum_{i\in S}X_i$.
--
--   **Formalization Note** The suprema are taken in $[0,\infty]$ over every output type, so no boundedness is needed for them to be meaningful; for integrable priors $W^{\mathrm I}<\infty$ (sanity file), so uselessness is not the trivial equation $\infty=\infty$. The prior is indexed by arrival position.
-- source:
--   Chen, Wang, When Does Private Data Collection Need Interaction? Online Selection under Local Differential Privacy, STOC 2027 submission (manuscript sha256 2e2d6157…), §1.1, p.1 (pdf p.2); §2, p.5 (pdf p.6), Definition 8

import Mathlib
import Definitions.Def_LDPSelect_law

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LDPSelect

/-!
# The values `W^I`, `W^N`, uselessness, the prophet

Chen, Wang, *When Does Private Data Collection Need Interaction? Online Selection under Local
Differential Privacy*, STOC 2027 submission (manuscript sha256 2e2d6157…), §1.1, p.1; Definition 8, p.5.

**Formalization Note.** `W^I` and `W^N` are suprema in `ℝ≥0∞` over every output type `Z : Type`, so
no boundedness is needed for them to mean what they say; for integrable priors they are finite (sanity
file). A prior is a function `P : Fin n → Measure ℝ≥0`, indexed by arrival position; users' values are
independent by construction of the law. An arrival order is a permutation `σ` relabelling `F`:
quantifying over `σ` and over `P` at positions covers every prior on users in every order. The
integrability hypothesis in `Useless` is the standing assumption of §2.
-/

variable {n : ℕ}

/-- The optimal expected reward under sequentially interactive mechanisms (Definition 8, p.5). -/
noncomputable def WI (a : ℝ) (F : Family n) (P : Fin n → Measure ℝ≥0) : ℝ≥0∞ :=
  ⨆ (Z : Type) (_ : MeasurableSpace Z) (M : Mechanism n Z) (_ : M.Private a) (_ : M.Respects F),
    M.reward P

/-- The optimal expected reward under non-interactive mechanisms (Definition 8, p.5). -/
noncomputable def WN (a : ℝ) (F : Family n) (P : Fin n → Measure ℝ≥0) : ℝ≥0∞ :=
  ⨆ (Z : Type) (_ : MeasurableSpace Z) (M : Mechanism n Z) (_ : M.Private a) (_ : M.Respects F)
    (_ : M.NonInteractive), M.reward P

/-- Each value has finite mean (§2, p.5). -/
def IsIntegrablePrior (P : Fin n → Measure ℝ≥0) : Prop :=
  ∀ i, ∫⁻ x, (x : ℝ≥0∞) ∂P i ≠ ⊤

/-- All values are bounded by one constant almost surely. -/
def IsBoundedPrior (P : Fin n → Measure ℝ≥0) : Prop :=
  ∃ B : ℝ≥0, ∀ i, P i {x | B < x} = 0

/-- "Interaction is useless for `F`": `W^I_F = W^N_F` for every product prior and every arrival order
(§1.1, p.1). -/
def Useless (a : ℝ) (F : Family n) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (P : Fin n → Measure ℝ≥0), (∀ i, IsProbabilityMeasure (P i)) →
    IsIntegrablePrior P → WI a (relabel σ F) P = WN a (relabel σ F) P

/-- There is a bounded prior and an arrival order with `W^I_F > W^N_F` (Theorem 1, p.2). -/
def HasGap (a : ℝ) (F : Family n) : Prop :=
  ∃ (σ : Equiv.Perm (Fin n)) (P : Fin n → Measure ℝ≥0), (∀ i, IsProbabilityMeasure (P i)) ∧
    IsBoundedPrior P ∧ WN a (relabel σ F) P < WI a (relabel σ F) P

/-- The prophet's reward `M_F = E max_{S ∈ F} X(S)` (Definition 8, p.5). -/
noncomputable def prophet (F : Family n) (P : Fin n → Measure ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ x, ⨆ S ∈ F, ∑ i ∈ S, (x i : ℝ≥0∞) ∂Measure.pi P

end LDPSelect


