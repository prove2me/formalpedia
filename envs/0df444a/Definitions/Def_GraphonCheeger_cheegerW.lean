-- Prove2me | Definitions.Def_GraphonCheeger_cheegerW
-- name    : GraphonCheeger_cheegerW
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:44:21.39575+00:00
-- url     : https://prove2.me/theorems/ccf7a274-e920-4815-8f5e-10afea78581f
-- title:
--   Mixed and pure Cheeger constants $h(W)$, $h_{\mathrm{pure}}(W)$ of a graphon
-- statement:
--   Let $W$ be a graphon on a probability space $(\Omega,\mathcal F,\mu)$. A **mixed 2-colouring** is $\Psi=(\psi,1-\psi)$ with $\psi:\Omega\to[0,1]$ measurable; it is **pure** if $\psi$ takes only the values $0$ and $1$. Define
--
--   $$C(W,\psi)=\iint_{\Omega^2}W(x,y)\,\psi(x)\,(1-\psi(y))\,d\mu(x)\,d\mu(y),\qquad m(W,\psi)=\int_\Omega k_W(x)\,\psi(x)\,d\mu(x),$$
--
--   $$D(W,\psi)=\min\{m(W,\psi),\ \rho_W-m(W,\psi)\},$$
--
--   and, whenever $D(W,\psi)>0$, the **coloured Cheeger ratio** $H(W,\Psi)=C(W,\psi)/D(W,\psi)$. When $\rho_W>0$, the (mixed) **Cheeger constant** of $W$ is
--
--   $$h(W)=\inf\bigl\{H(W,\Psi):\ \Psi=(\psi,1-\psi)\text{ a mixed 2-colouring},\ D(W,\psi)>0\bigr\},$$
--
--   and the **pure Cheeger constant** $h_{\mathrm{pure}}(W)$ is the same infimum over pure colourings only.
--
--   $C$ is the edge mass crossing between the two colour classes and $m$, $\rho_W-m$ are their degree volumes, so $h(W)$ is the graphon analogue of the Cheeger constant of a graph.
--
--   **Formalization Note** A colouring $\Psi$ is identified with $\psi$. The infimum ranges only over colourings with $D(W,\psi)>0$. When $\rho_W>0$ the constant colouring $\psi\equiv1/2$ is admissible, so the set is nonempty and bounded below by $0$; for $\rho_W=0$, where the paper leaves $h(W)$ undefined, the value is the junk $0$.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), (4.79)–(4.83), pp.42–43

import Mathlib
import Definitions.Def_GraphonCheeger_IsGraphon

open MeasureTheory

namespace GraphonCheeger

/-!
# Mixed and pure Cheeger constants of a graphon

Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…), (4.79)–(4.83), pp.42–43.

**Formalization Note.**
* A mixed 2-colouring `Ψ = (ψ, 1 − ψ) ∈ Λ₂` is identified with its first coordinate, a measurable
  `ψ : Ω → [0, 1]` (`IsColouring`); a pure one has `ψ` with values in `{0, 1}`
  (`IsPureColouring`, `ψ = 1_{χ = 1}` for a measurable `χ : Ω → [2]`).
* `cutVal = C(W, ψ)` (4.79), `mass = m(W, ψ)` (4.80), `denom = D(W, ψ)` (4.81),
  `ratio = H(W, Ψ) = C/D` (4.82).
* `cheegerW μ W` is the **mixed** Cheeger constant (4.83): the infimum of `H(W, Ψ)` over the
  colourings with `D(W, ψ) > 0` only. The paper defines it when `ρ_W > 0`; then `ψ ≡ 1/2` is
  admissible and the set is nonempty and bounded below by `0`. For `ρ_W = 0` the value is the
  junk `sInf ∅ = 0`. `cheegerPure` is the same infimum over pure colourings.
-/

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A (mixed) 2-colouring `Ψ = (ψ, 1 − ψ)`, given by a measurable `ψ : Ω → [0, 1]`. -/
def IsColouring (ψ : Ω → ℝ) : Prop :=
  Measurable ψ ∧ ∀ x, ψ x ∈ Set.Icc (0 : ℝ) 1

/-- A pure 2-colouring: a measurable `ψ : Ω → {0, 1}`. -/
def IsPureColouring (ψ : Ω → ℝ) : Prop :=
  Measurable ψ ∧ ∀ x, ψ x = 0 ∨ ψ x = 1

/-- `C(W, ψ) = ∬ W(x, y) ψ(x) (1 − ψ(y)) dµ(x) dµ(y)` ((4.79), p.42). -/
noncomputable def cutVal (μ : Measure Ω) (W : Ω → Ω → ℝ) (ψ : Ω → ℝ) : ℝ :=
  ∫ p, W p.1 p.2 * ψ p.1 * (1 - ψ p.2) ∂(μ.prod μ)

/-- `m(W, ψ) = ∫ k_W(x) ψ(x) dµ(x)` ((4.80), p.42). -/
noncomputable def mass (μ : Measure Ω) (W : Ω → Ω → ℝ) (ψ : Ω → ℝ) : ℝ :=
  ∫ x, degFun μ W x * ψ x ∂μ

/-- `D(W, ψ) = min{m(W, ψ), ρ_W − m(W, ψ)}` ((4.81), p.42). -/
noncomputable def denom (μ : Measure Ω) (W : Ω → Ω → ℝ) (ψ : Ω → ℝ) : ℝ :=
  min (mass μ W ψ) (density μ W - mass μ W ψ)

/-- The coloured Cheeger ratio `H(W, Ψ) = C(W, ψ) / D(W, ψ)` ((4.82), p.42); used only where
`D(W, ψ) > 0`. -/
noncomputable def ratio (μ : Measure Ω) (W : Ω → Ω → ℝ) (ψ : Ω → ℝ) : ℝ :=
  cutVal μ W ψ / denom μ W ψ

/-- The (mixed) **Cheeger constant** of a graphon,
`h(W) = inf { H(W, Ψ) : Ψ = (ψ, 1 − ψ) ∈ Λ₂, D(W, ψ) > 0 }` ((4.83), p.42). -/
noncomputable def cheegerW (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ ψ : Ω → ℝ, IsColouring ψ ∧ 0 < denom μ W ψ ∧ r = ratio μ W ψ}

/-- The **pure** Cheeger constant `h_pure(W)` (p.43): the infimum in (4.83) over pure colourings
only. -/
noncomputable def cheegerPure (μ : Measure Ω) (W : Ω → Ω → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ ψ : Ω → ℝ, IsPureColouring ψ ∧ 0 < denom μ W ψ ∧ r = ratio μ W ψ}

end GraphonCheeger


