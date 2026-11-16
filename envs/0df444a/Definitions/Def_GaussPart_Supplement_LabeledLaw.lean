-- Prove2me | Definitions.Def_GaussPart_Supplement_LabeledLaw
-- name    : GaussPart_Supplement_LabeledLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:01:57.180832+00:00
-- url     : https://prove2.me/theorems/f5ac075f-7c45-434e-ad23-3c6576dc9af0
-- title:
--   Labeled distributions, $\mathrm{err}_D$, $\mathrm{opt}_D$, positive and negative reliable learning
-- statement:
--   A **distribution on $\mathbb R^d\times\{\pm1\}$** is a probability measure on $\mathbb R^d\times\mathbb R$ whose label is $\pm1$ almost surely; its x-marginal is $D_x$. For a hypothesis $h$,
--   $$
--   \mathrm{err}_D(h)=\Pr_{(x,y)\sim D}[h(x)\neq y],\qquad \mathrm{opt}_D(\mathcal F)=\inf_{f\in\mathcal F}\mathrm{err}_D(f).
--   $$
--   **Positive reliable learning** (for $\mathcal F\ni -1$): with $G_D=\{f\in\mathcal F:\Pr_D[f(x)=1,y=-1]=0\}$, the hypothesis satisfies $\Pr_D[h(x)=1,y=-1]\le\epsilon$ and
--   $$
--   \Pr_D[h(x)=-1,y=1]\le\inf_{f\in G_D}\Pr_D[f(x)=-1,y=1]+\epsilon .
--   $$
--   **Negative reliable learning** (for $\mathcal F\ni 1$) interchanges the labels $1$ and $-1$.
--
--   These are the error notions of the semi-agnostic (Definition 1.4) and reliable (Definitions 1.10, 6.1) learning results.
--
--   **Formalization Note** Errors are values in $[0,\infty]$; a hypothesis value other than $\pm1$ counts as an error.
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Definition 1.4, p.3 (PDF p.5); Definition 1.10, p.6 (PDF p.8); Definition 6.1, p.60 (PDF p.62)

import Mathlib
import Definitions.Def_GaussPart_Cell

open MeasureTheory

namespace GaussPart

namespace Supplement

/-- A distribution `D` on `ℝᵈ × {±1}`: a probability measure on `ℝᵈ × ℝ` whose label is `1` or `-1`
almost surely. Its x-marginal is `D.map Prod.fst`. -/
def IsLabeledLaw {d : ℕ} (D : Measure (Vec d × ℝ)) : Prop :=
  IsProbabilityMeasure D ∧ ∀ᵐ p ∂D, p.2 = 1 ∨ p.2 = -1

/-- **Definition 1.4**, arXiv:2611.05264 (sha256 7e0ca6d4…), p.3 (PDF p.5):
`err_D(h) := Pr_{(x,y)∼D}[h(x) ≠ y]`, in `[0, 1] ⊆ [0, ∞]`. A value of `h` other than `±1` is an
error. -/
noncomputable def err {d : ℕ} (D : Measure (Vec d × ℝ)) (h : Vec d → ℝ) : ENNReal :=
  D {p | h p.1 ≠ p.2}

/-- `opt_D(F) := inf_{f ∈ F} err_D(f)` (Definition 1.4). -/
noncomputable def opt {d : ℕ} (D : Measure (Vec d × ℝ)) (F : Set (Vec d → ℝ)) : ENNReal :=
  ⨅ f ∈ F, err D f

/-- **Negative reliable learning** (Definition 6.1, p.60, PDF p.62, Definition 1.10, p.6): the
hypothesis `h` satisfies `Pr_D[h(x) = −1, y = 1] ≤ ϵ` and
`Pr_D[h(x) = 1, y = −1] ≤ inf_{f ∈ G_D} Pr_D[f(x) = 1, y = −1] + ϵ`, where
`G_D = {f ∈ F : Pr_D[f(x) = −1, y = 1] = 0}` (labels `1` and `−1` of Definition 6.1 interchanged). -/
def NegReliable {d : ℕ} (F : Set (Vec d → ℝ)) (D : Measure (Vec d × ℝ)) (ε : ℝ)
    (h : Vec d → ℝ) : Prop :=
  D {p | h p.1 = -1 ∧ p.2 = 1} ≤ ENNReal.ofReal ε ∧
  D {p | h p.1 = 1 ∧ p.2 = -1} ≤
    (⨅ f ∈ {f ∈ F | D {p | f p.1 = -1 ∧ p.2 = 1} = 0}, D {p | f p.1 = 1 ∧ p.2 = -1}) +
      ENNReal.ofReal ε

/-- **Positive reliable learning** (Definition 6.1, p.60): `Pr_D[h(x) = 1, y = −1] ≤ ϵ` and
`Pr_D[h(x) = −1, y = 1] ≤ inf_{f ∈ G_D} Pr_D[f(x) = −1, y = 1] + ϵ`, where
`G_D = {f ∈ F : Pr_D[f(x) = 1, y = −1] = 0}`. -/
def PosReliable {d : ℕ} (F : Set (Vec d → ℝ)) (D : Measure (Vec d × ℝ)) (ε : ℝ)
    (h : Vec d → ℝ) : Prop :=
  D {p | h p.1 = 1 ∧ p.2 = -1} ≤ ENNReal.ofReal ε ∧
  D {p | h p.1 = -1 ∧ p.2 = 1} ≤
    (⨅ f ∈ {f ∈ F | D {p | f p.1 = 1 ∧ p.2 = -1} = 0}, D {p | f p.1 = -1 ∧ p.2 = 1}) +
      ENNReal.ofReal ε

end Supplement

end GaussPart


