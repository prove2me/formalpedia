-- Prove2me | Definitions.Def_SupportVectorMachines_Classification_RiskBasics_v2
-- name    : SupportVectorMachines_Classification_RiskBasics_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:18:59.775704+00:00
-- url     : https://prove2.me/theorems/f127d221-2510-4091-b07c-78b5757fccd3
-- title:
--   Loss function, $L$-risk and Bayes risk (Definitions 2.1–2.3, Chapter 8 draft) — measurable bundled loss, $[0,\infty]$-valued risks
-- statement:
--   A **loss function** on a measurable space $X$ (Definition 2.1, p. 22) is a measurable map $L : X \times Y \times \mathbb R \to [0,\infty)$, where $Y \subset \mathbb R$ is the closed label set. It is represented by a curried function $X \to \mathbb R \to \mathbb R \to \mathbb R$ (labels embedded in $\mathbb R$; a distribution on $X \times Y$ is a distribution on $X \times \mathbb R$ supported on $X \times Y$) **bundled with** the two defining properties of Definition 2.1: measurability with respect to the product $\sigma$-algebra of $X \times \mathbb R \times \mathbb R$, and nonnegativity. A loss is applied as a function, $L\,x\,y\,t = L(x,y,t)$.
--
--   The **$L$-risk** of $f : X \to \mathbb R$ with respect to a distribution $P$ on $X \times Y$ is $R_{L,P}(f) := \int_{X \times Y} L(x,y,f(x))\,dP(x,y) \in [0,\infty]$ (Definition 2.2), which always exists but need not be finite (p. 23); the **Bayes $L$-risk** is $R^*_{L,P} := \inf\{R_{L,P}(f) : f \text{ measurable}\} \in [0,\infty]$ (Definition 2.3).
--
--   **Formalization Note.** The retired module used the bare function type for losses, a real-valued Bochner integral for the risk (junk value $0$ for a non-integrable integrand) and an unguarded real infimum for the Bayes risk, which let a measurable function with infinite hinge risk collapse the Bayes risk to $0$ (the accepted disproof of the Theorem 5.31 instance). The corrected module bundles measurability and nonnegativity into `Loss X` and renders risks as Lebesgue integrals into $[0,\infty]$.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, Definitions 2.1-2.3

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.Classification

/-- A **loss function** (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9): given a measurable space `X` and a
closed label set `Y ⊂ ℝ`, a loss is a **measurable** map `L : X × Y × ℝ → [0,∞)`. It is
represented as a curried function `toFun : X → ℝ → ℝ → ℝ` (labels embedded in `ℝ`; a
distribution on `X × Y` is a distribution on `X × ℝ` supported on `X × Y`), bundled with
measurability for the product σ-algebra of `X × ℝ × ℝ` and nonnegativity, the two defining
properties of Definition 2.1. (The retired module
`Def_SupportVectorMachines_Classification_RiskBasics` used the bare function type.) -/
structure Loss (X : Type*) [MeasurableSpace X] where
  /-- The loss as a curried function `L(x, y, t)`. -/
  toFun : X → ℝ → ℝ → ℝ
  /-- `L` is measurable as a map on `X × ℝ × ℝ` (Definition 2.1). -/
  measurable : Measurable (fun p : X × ℝ × ℝ => toFun p.1 p.2.1 p.2.2)
  /-- `L` takes values in `[0,∞)` (Definition 2.1). -/
  nonneg : ∀ x y t, 0 ≤ toFun x y t

/-- A loss is applied as a function: `L x y t` denotes `L(x, y, t)`. -/
instance {X : Type*} [MeasurableSpace X] : CoeFun (Loss X) (fun _ => X → ℝ → ℝ → ℝ) :=
  ⟨Loss.toFun⟩

/-- The **`L`-risk** of `f` with respect to a distribution `P` on `X × ℝ` (Definition 2.2,
p. 22): `R_{L,P}(f) := ∫_{X×Y} L(x,y,f(x)) dP(x,y)`, which "always exists, although it is not
necessarily finite" (p. 23). It is the Lebesgue integral of the nonnegative measurable integrand
into `[0,∞]`, so a function with infinite risk has risk `∞` exactly as in the book (the retired
version was a real-valued Bochner integral, equal to the junk value `0` for a non-integrable
integrand, which falsified the Theorem 5.31 instance). -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ))
    (f : X → ℝ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (L p.1 p.2 (f p.1)) ∂P

/-- The **Bayes (minimal) `L`-risk** with respect to `P` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`, an infimum in `[0,∞]`. -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    ENNReal :=
  ⨅ (f : X → ℝ) (_ : Measurable f), risk L P f

end SupportVectorMachines.Classification


