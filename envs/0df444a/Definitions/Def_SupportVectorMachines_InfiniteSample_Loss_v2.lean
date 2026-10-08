-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_Loss_v2
-- name    : SupportVectorMachines_InfiniteSample_Loss_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:19:02.423912+00:00
-- url     : https://prove2.me/theorems/3d86b255-2d3a-46c9-add6-80e3027c788e
-- title:
--   Loss function (Definition 2.1, Chapter 5 draft): a measurable, nonnegative map on $X \times Y \times \mathbb R$ — corrected
-- statement:
--   A **loss function** on a measurable space $X$ (Definition 2.1, p. 22) is a measurable map $L : X \times Y \times \mathbb R \to [0,\infty)$, where $Y \subset \mathbb R$ is the closed label set. It is represented by a curried function $X \to \mathbb R \to \mathbb R \to \mathbb R$ (labels embedded in $\mathbb R$; a distribution on $X \times Y$ is a distribution on $X \times \mathbb R$ supported on $X \times Y$) **bundled with** the two defining properties of Definition 2.1: measurability with respect to the product $\sigma$-algebra of $X \times \mathbb R \times \mathbb R$, and nonnegativity. A loss is applied as a function, $L\,x\,y\,t = L(x,y,t)$.
--
--   **Formalization Note.** The retired definition was the bare function type, with a docstring deferring measurability and nonnegativity to the theorems; no theorem supplied them, which made four milestones of this series refutable with non-measurable "losses". Bundling them makes every statement over `L : Loss X` carry the book's standing assumptions.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 22, Definition 2.1

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.InfiniteSample

/-- A **loss function** (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
Definition 2.1, p. 22, restated locally per Hard Rule 9 rather than imported from the
`LossFunctions` chapter draft): given a measurable space `X` and a closed label set `Y ⊂ ℝ`, a
loss is a **measurable** map `L : X × Y × ℝ → [0,∞)`. It is represented as a curried function
`toFun : X → ℝ → ℝ → ℝ` (labels embedded in `ℝ`; a distribution on `X × Y` is a distribution
on `X × ℝ` supported on `X × Y`), bundled with measurability for the product σ-algebra of
`X × ℝ × ℝ` and nonnegativity, the two defining properties of Definition 2.1, so that every
theorem quantifying over `L : Loss X` carries the book's standing assumptions on a loss. (The
retired module `Def_SupportVectorMachines_InfiniteSample_Loss` used the bare function type,
which let non-measurable "losses" falsify Lemma 5.1 and Theorems 5.2 and 5.6.) -/
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

end SupportVectorMachines.InfiniteSample


