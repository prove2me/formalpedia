-- Prove2me | Definitions.Def_GraphonCheeger_IsGraphon
-- name    : GraphonCheeger_IsGraphon
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:39:23.201723+00:00
-- url     : https://prove2.me/theorems/9e98e20e-6b4d-4910-89dd-414b9c5d1184
-- title:
--   Graphons on a general probability space; degree function $k_W$, edge density $\rho_W$, pullback $W^\varphi$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space. A **graphon** on $\Omega$ is a measurable symmetric function $W:\Omega^2\to[0,1]$, measurable for the product $\sigma$-algebra $\mathcal F\otimes\mathcal F$.
--
--   Its **degree function** and **edge density** are
--
--   $$k_W(x)=\int_\Omega W(x,y)\,d\mu(y)\quad(x\in\Omega),\qquad \rho_W=\iint_{\Omega^2}W(x,y)\,d\mu(x)\,d\mu(y).$$
--
--   For a map $\varphi:\Omega_1\to\Omega_2$ and a function $W$ on $\Omega_2^2$, the **pullback** is the function $W^\varphi(x,y)=W(\varphi(x),\varphi(y))$ on $\Omega_1^2$.
--
--   These are the basic objects of every statement in the mission. The paper works on arbitrary probability spaces, not only on $[0,1]$, and pullbacks along measure-preserving maps are how graphons on different spaces are compared.
--
--   **Formalization Note** A graphon is a plain function `W : Ω → Ω → ℝ` together with the predicate `IsGraphon W` (measurable on `Ω × Ω`, symmetric and `[0,1]`-valued at every point). The measure `μ` is an explicit argument of `degFun` and `density`, because a pullback changes the measure. `density` integrates against the product measure `μ.prod μ`.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Definition 2.1, p.6; (4.1)–(4.2), p.30; (A.2), p.81

import Mathlib

open MeasureTheory

namespace GraphonCheeger

/-!
# Graphons on a general probability space, degree function, edge density, pullback

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…): Definition 2.1 (p.6), the setup of §4
((4.1)–(4.2), p.30) and (A.2) (p.81).

**Formalization Note.**
* Graphons are unbundled: `IsGraphon W` is a predicate on a plain function `W : Ω → Ω → ℝ`
  ("a measurable symmetric function `Ω² → [0, 1]`"); measurability is for the product
  σ-algebra on `Ω × Ω`, and symmetry and the range `[0, 1]` hold at every point.
* The probability measure `μ` is an explicit argument (not a `MeasureSpace` instance), because
  pullbacks change the measure. The definitions below are total; they are used only for graphons
  on probability spaces, where every integral involved is of a bounded measurable function.
-/

universe u v

/-- A **graphon** on a measurable space `Ω` (Def. 2.1, p.6): a function `W : Ω → Ω → ℝ` that is
measurable on `Ω × Ω` (product σ-algebra), symmetric, and takes values in `[0, 1]`. -/
def IsGraphon {Ω : Type u} [MeasurableSpace Ω] (W : Ω → Ω → ℝ) : Prop :=
  Measurable (Function.uncurry W) ∧ (∀ x y, W x y = W y x) ∧ (∀ x y, W x y ∈ Set.Icc (0 : ℝ) 1)

/-- The **degree function** `k_W(x) = ∫_Ω W(x, y) dµ(y)` ((4.1), p.30). -/
noncomputable def degFun {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → Ω → ℝ)
    (x : Ω) : ℝ :=
  ∫ y, W x y ∂μ

/-- The **edge density** `ρ_W = ∬_{Ω²} W(x, y) dµ(x) dµ(y)` ((4.2), p.30), as an integral over
the product measure `µ ⊗ µ`. -/
noncomputable def density {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  ∫ p, W p.1 p.2 ∂(μ.prod μ)

/-- The **pullback** `W^φ(x, y) = W(φ(x), φ(y))` of `W` along `φ : Ω₁ → Ω₂` ((A.2), p.81). -/
def pullback {Ω₁ : Type u} {Ω₂ : Type v} (φ : Ω₁ → Ω₂) (W : Ω₂ → Ω₂ → ℝ) : Ω₁ → Ω₁ → ℝ :=
  fun x y => W (φ x) (φ y)

end GraphonCheeger


