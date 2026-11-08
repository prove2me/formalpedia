-- Prove2me | Definitions.Def_DPVerify_IsDPAlg
-- name    : DPVerify_IsDPAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:12.643193+00:00
-- url     : https://prove2.me/theorems/4d510b65-13e2-4668-a73e-bc306a9f3a2f
-- title:
--   $(\varepsilon,\delta)$-differentially private algorithm
-- statement:
--   Two samples $S,S'\in\mathcal X^m$ are **neighbouring** if they differ in exactly one coordinate. A randomized algorithm $\mathcal A:\mathcal X^m\to\mathcal Y$ is **$(\varepsilon,\delta)$-differentially private** if for every pair of neighbouring samples $S,S'$ and every measurable set $O\subseteq\mathcal Y$ of outputs,
--
--   $$
--   \Pr[\mathcal A(S)\in O]\;\le\;e^{\varepsilon}\,\Pr[\mathcal A(S')\in O]+\delta .
--   $$
--
--   This is Definition 2.2 of the paper for an algorithm that interacts with nobody; Lemma 4.2 assumes it.
--
--   **Formalization Note** Neighbouring samples are the published `PrivLearn.Generic.Neighbors`, and the inequality is the published `ContinualCounting.IsApproxDP` applied to the output laws. Definition 2.1 speaks of adding or removing one element; all algorithms of the paper read samples of a fixed size, and §6 proves privacy for samples "which differ on the $i$th coordinate", so substitution is the adjacency used.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definitions 2.1–2.2, p.4 (PDF p.7); Lemma 4.2, p.18 (PDF p.21)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_ContinualCounting_IsApproxDP
import Definitions.Def_DPVerify_RandAlg

set_option autoImplicit false

open MeasureTheory

namespace DPVerify

/-- An `(ε, δ)`-differentially private algorithm `A : X^m → Y` (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), Definition 2.2, p.4 = PDF p.7,
specialized to a non-interactive algorithm, as used in Lemma 4.2, p.18): for every pair of
neighbouring samples `S, S′` and every measurable output set `O`,
`Pr[A(S) ∈ O] ≤ e^ε · Pr[A(S′) ∈ O] + δ`.

**Formalization Note** Neighbouring samples are the published `PrivLearn.Generic.Neighbors`
(substitution of one entry of `S ∈ X^m`). Definition 2.1 says "addition or removal of one
element", but every algorithm of the paper reads a sample of fixed size, and §6 (p.33) proves
privacy for "neighboring datasets which differ on the ith coordinate". The inequality is the
published `ContinualCounting.IsApproxDP` applied to the output laws, in `ℝ≥0∞`, with `e^ε` and
`δ` embedded by `ENNReal.ofReal`. -/
def IsDPAlg {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {m : ℕ} (A : RandAlg X Y m)
    (ε δ : ℝ) : Prop :=
  ContinualCounting.IsApproxDP PrivLearn.Generic.Neighbors A.law ε δ

end DPVerify


