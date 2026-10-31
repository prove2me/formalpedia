-- Prove2me | Definitions.Def_SweepingDesing_orientedModulus
-- name    : SweepingDesing_orientedModulus
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:15:17.753737+00:00
-- url     : https://prove2.me/theorems/bc17d003-df63-4fb3-8739-d84fefe85751
-- title:
--   Definition 4 — oriented modulus $\|D^*S(t,x)|^+$ of the coderivative
-- statement:
--   Throughout, $S:\mathbb R\rightrightarrows\mathbb R^n$ is a set-valued map with graph $\mathcal S=\operatorname{gph}S=\{(t,x)\in\mathbb R\times\mathbb R^n: x\in S(t)\}$, and $N_C$ denotes the limiting (Mordukhovich) normal cone of §2: the outer limit of Fréchet normal cones $\hat N_C(y)$ as $y\to x$ within $C$.
--
--   The limiting coderivative of $S$ at $(t,x)\in\mathcal S$ is the set-valued map $u\mapsto D^*S(t,x)(u)=\{a\in\mathbb R:(a,-u)\in N_{\mathcal S}(t,x)\}$ (Definition 3). The **oriented (asymmetric) modulus** of the coderivative is
--
--   $$
--   \|D^*S(t,x)|^+=\sup\{a^+ : a\in D^*S(t,x)(u),\ \|u\|\le 1\},\qquad a^+=\max\{0,a\},
--   $$
--
--   with the convention $\sup\emptyset=0$. It takes values in $[0,+\infty]$.
--
--   Replacing $|a|$ by $a^+$ makes the modulus sensitive to the direction of time: it measures how fast the sets $S(t)$ recede, which is what pushes an orbit of the sweeping process.
--
--   **Formalization Note** The coderivative is the published `GenNewtonSubgrad.ProxReg.coderiv` on $\mathbb R\times\mathbb R^n$; the value is in `ℝ≥0∞`, and it is $0$ off the graph (empty normal cone).
-- source:
--   Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 4, p.5 (with Definition 3, p.5)

import Mathlib
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
open Filter Topology MeasureTheory Set
open scoped ENNReal

namespace SweepingDesing

/-- Daniilidis, Tapia-García, Desingularization of the Sweeping Process Mapping, arXiv:2110.08686v1, Definition 4, p.5: the *asymmetric (oriented) modulus* of the limiting coderivative,
`‖D*S(t, x)|⁺ = sup {a⁺ : a ∈ D*S(t, x)(u), ‖u‖ ≤ 1}`, with `sup ∅ = 0`.

Here `D*S(t, x)(u) = {a ∈ ℝ : (a, -u) ∈ N_𝒮(t, x)}` (Definition 3, p.5) is the published
`GenNewtonSubgrad.ProxReg.coderiv S t x u`, with `N_𝒮` the limiting normal cone to the graph
`𝒮 = gph S ⊂ ℝ × ℝⁿ`.

**Formalization Note** ℝⁿ is `EuclideanSpace ℝ (Fin n)`; the value lies in `[0, +∞]`
(`ℝ≥0∞`), where `ENNReal.ofReal a = a⁺` and the empty supremum is `0`, the paper's convention.
Off the graph the limiting normal cone is empty, so the modulus is `0` there. -/
noncomputable def orientedModulus {n : ℕ} (S : ℝ → Set (EuclideanSpace ℝ (Fin n))) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ≥0∞ :=
  ⨆ (u : EuclideanSpace ℝ (Fin n)) (_ : ‖u‖ ≤ 1)
    (a : ℝ) (_ : a ∈ GenNewtonSubgrad.ProxReg.coderiv S t x u), ENNReal.ofReal a

end SweepingDesing


