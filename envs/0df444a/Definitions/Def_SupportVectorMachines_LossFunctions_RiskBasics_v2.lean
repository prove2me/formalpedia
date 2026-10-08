-- Prove2me | Definitions.Def_SupportVectorMachines_LossFunctions_RiskBasics_v2
-- name    : SupportVectorMachines_LossFunctions_RiskBasics_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:19:16.50527+00:00
-- url     : https://prove2.me/theorems/f140b27d-a45a-46e0-b0ee-24cffa530318
-- title:
--   Loss function, $L$-risk and Bayes risk (Definitions 2.1–2.3) — measurable bundled loss, $[0,\infty]$-valued risks
-- statement:
--   A **loss function** on a measurable space $X$ (Definition 2.1, p. 22) is a measurable map $L : X \times Y \times \mathbb R \to [0,\infty)$, where $Y \subset \mathbb R$ is the closed label set. It is represented by a curried function $X \to \mathbb R \to \mathbb R \to \mathbb R$ (labels embedded in $\mathbb R$; a distribution on $X \times Y$ is a distribution on $X \times \mathbb R$ supported on $X \times Y$) **bundled with** the two defining properties of Definition 2.1: measurability with respect to the product $\sigma$-algebra of $X \times \mathbb R \times \mathbb R$, and nonnegativity. A loss is applied as a function, $L\,x\,y\,t = L(x,y,t)$.
--
--   The **$L$-risk** of $f : X \to \mathbb R$ with respect to a distribution $P$ on $X \times Y$ is $R_{L,P}(f) := \int_{X \times Y} L(x,y,f(x))\,dP(x,y) \in [0,\infty]$ (Definition 2.2), which always exists but need not be finite (p. 23); the **Bayes $L$-risk** is $R^*_{L,P} := \inf\{R_{L,P}(f) : f : X \to \mathbb R \text{ measurable}\} \in [0,\infty]$ (Definition 2.3).
--
--   **Formalization Note.** The retired module used the bare function type for losses and a real-valued Bochner integral for the risk (junk value $0$ for a non-integrable integrand) with an `Integrable` guard inside the Bayes infimum (junk $\inf\emptyset = 0$ when every risk is infinite). The corrected module bundles measurability and nonnegativity into `Loss X` and renders risks as Lebesgue integrals into $[0,\infty]$, exactly as the book does.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, pp. 22-23, Definitions 2.1-2.3

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.LossFunctions

/-- A **loss function** (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22): given a measurable space `X` and a closed label set `Y ⊂ ℝ`, a loss is a
**measurable** map `L : X × Y × ℝ → [0,∞)`. It is represented as a curried function
`toFun : X → ℝ → ℝ → ℝ` (the middle argument ranges over the ambient reals, so the label set
`Y` is embedded in `ℝ`; a distribution on `X × Y` is a distribution on `X × ℝ` supported on
`X × Y`), bundled with the two defining properties of Definition 2.1 — measurability for the
product σ-algebra of `X × ℝ × ℝ` and nonnegativity — so that every statement about an
`L : Loss X` carries the book's standing assumptions on a loss. (The retired module
`Def_SupportVectorMachines_LossFunctions_RiskBasics` used the bare function type.) -/
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
necessarily finite" (p. 23). It is rendered as the Lebesgue integral of the nonnegative
measurable integrand into `[0,∞]`, so that a function with infinite risk has risk `∞` exactly
as in the book (the retired version was a real-valued Bochner integral, equal to the junk value
`0` for a non-integrable integrand). -/
noncomputable def risk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ))
    (f : X → ℝ) : ENNReal :=
  ∫⁻ p, ENNReal.ofReal (L p.1 p.2 (f p.1)) ∂P

/-- The **Bayes (minimal) `L`-risk** with respect to `P` (Definition 2.3, p. 22-23):
`R*_{L,P} := inf { R_{L,P}(f) : f : X → ℝ measurable }`, an infimum in `[0,∞]` (equal to `∞`
when every measurable `f` has infinite risk, as in the book). -/
noncomputable def bayesRisk {X : Type*} [MeasurableSpace X] (L : Loss X) (P : Measure (X × ℝ)) :
    ENNReal :=
  ⨅ (f : X → ℝ) (_ : Measurable f), risk L P f

end SupportVectorMachines.LossFunctions


