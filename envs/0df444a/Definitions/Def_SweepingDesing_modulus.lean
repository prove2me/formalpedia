-- Prove2me | Definitions.Def_SweepingDesing_modulus
-- name    : SweepingDesing_modulus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:10.510257+00:00
-- url     : https://prove2.me/theorems/fdd2a4e4-a927-4b2d-88dc-c6cc3b1667e6
-- title:
--   Definition 3 — modulus $\|D^*S(t,x)\|^+$ of the coderivative
-- statement:
--   Throughout, $S:\mathbb R\rightrightarrows\mathbb R^n$ is a set-valued map with graph $\mathcal S=\operatorname{gph}S=\{(t,x)\in\mathbb R\times\mathbb R^n: x\in S(t)\}$, and $N_C$ denotes the limiting (Mordukhovich) normal cone of §2: the outer limit of Fréchet normal cones $\hat N_C(y)$ as $y\to x$ within $C$.
--
--   With $D^*S(t,x)(u)=\{a\in\mathbb R:(a,-u)\in N_{\mathcal S}(t,x)\}$ the limiting coderivative, its (symmetric) **modulus** is
--
--   $$
--   \|D^*S(t,x)\|^+=\sup_{\|u\|\le1}\{|a| : a\in D^*S(t,x)(u)\}\in[0,+\infty].
--   $$
--
--   It is the classical quantity tied to the Lipschitz (Aubin) behaviour of $S$; the oriented modulus never exceeds it.
--
--   **Formalization Note** Values in `ℝ≥0∞`, empty supremum $0$.
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 3, p.5

import Mathlib
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 3, p.5: the (symmetric) *modulus* of the limiting coderivative,
`‖D*S(t, x)‖⁺ = sup_{‖u‖ ≤ 1} {|a| : a ∈ D*S(t, x)(u)}`, where
`D*S(t, x)(u) = {a ∈ ℝ : (a, -u) ∈ N_𝒮(t, x)}` is `GenNewtonSubgrad.ProxReg.coderiv S t x u`.

**Formalization Note** The value lies in `[0, +∞]` (`ℝ≥0∞`); the empty supremum is `0`. -/
noncomputable def modulus {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (u : EuclideanSpace ℝ (Fin n)) (_ : ‖u‖ ≤ 1)
    (a : ℝ) (_ : a ∈ GenNewtonSubgrad.ProxReg.coderiv S t x u), ENNReal.ofReal |a|

end SweepingDesing


