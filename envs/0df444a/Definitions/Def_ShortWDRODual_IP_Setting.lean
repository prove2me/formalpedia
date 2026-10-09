-- Prove2me | Definitions.Def_ShortWDRODual_IP_Setting
-- name    : ShortWDRODual_IP_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:30:33.62709+00:00
-- url     : https://prove2.me/theorems/d242d437-d1e1-46b9-a5fc-4a8a725a96a0
-- title:
--   §3 Definition 1, Proposition 1, p. 6 — Graph(E), diagonally dominant functions, sets and set functions, (Proj), (Sel*)
-- statement:
--   Let $(\mathcal X,\mathcal F,\widehat{\mathbb P})$ be a probability space, and let $\mathcal F_{\widehat{\mathbb P}}$ denote the completion of $\mathcal F$ under $\widehat{\mathbb P}$. A set or function is called $\widehat{\mathbb P}$-measurable when it is measurable with respect to $\mathcal F_{\widehat{\mathbb P}}$. Write $\Gamma_{\widehat{\mathbb P}}$ for the set of probability measures on $(\mathcal X\times\mathcal X,\mathcal F\otimes\mathcal F)$ whose first marginal is $\widehat{\mathbb P}$.
--
--   1. **Graph** of a set-valued map $E:\mathcal X\to 2^{\mathcal X}$:
--   $$\mathrm{Graph}(E)=\{(\widehat x,x)\in\mathcal X\times\mathcal X:\ x\in E(\widehat x)\}.$$
--   2. **Diagonally dominant function (Definition 1).** An $(\mathcal F\otimes\mathcal F)$-measurable $\phi:\mathcal X\times\mathcal X\to\bar{\mathbb R}$ is diagonally dominant if $\phi(\widehat x,x)\le\phi(x,x)$ for every $\widehat x,x\in\mathcal X$.
--   3. **Diagonally dominant set (Definition 1).** An $(\mathcal F\otimes\mathcal F)$-measurable set $A\subset\mathcal X\times\mathcal X$ is diagonally dominant if $(\widehat x,x)\in A$ implies $(x,x)\in A$.
--   4. **Diagonally dominant set function (Definition 1).** A set function $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$ (every value a nonempty measurable set) with $(\mathcal F\otimes\mathcal F)$-measurable graph is diagonally dominant if $x\in E(\widehat x)$ implies $x\in E(x)$.
--   5. **(Proj), measurable projection.** For every diagonally dominant set $A\in\mathcal F\otimes\mathcal F$,
--   $$\mathrm{Proj}_{\widehat x}(A)=\{\widehat x\in\mathcal X:\ (\widehat x,x)\in A\text{ for some }x\in\mathcal X\}\in\mathcal F_{\widehat{\mathbb P}}.$$
--   6. **(Sel\*), weak measurable selection.** For every diagonally dominant set-valued function $E:\mathcal X\to\mathcal F\setminus\{\emptyset\}$ with measurable graph there is a probability measure $\gamma\in\Gamma_{\widehat{\mathbb P}}$ with $\operatorname{supp}\gamma\subset\mathrm{Graph}(E)$.
--
--   These are the objects of Proposition 1, which shows that the interchangeability principle holds for every diagonally dominant function $\phi:\mathcal X\times\mathcal X\to\mathbb R\cup\{-\infty\}$ exactly when (Proj) and (Sel\*) hold. The couplings $\Gamma_{\widehat{\mathbb P}}$, the pointwise supremum and the interchangeability principle itself are defined in the companion module `ShortWDRODual.Legendre.Setting`, which this module imports.
--
--   **Formalization Note** Functions into $\bar{\mathbb R}$ are `EReal`-valued; Definition 1 speaks of functions into $\mathbb R\cup\{-\infty\}$, and the theorems that use diagonal dominance add the side condition "never $+\infty$" explicitly. $\widehat{\mathbb P}$-measurability of a set is `NullMeasurableSet` (membership in the completion). Since $\mathcal X$ carries no topology, "$\operatorname{supp}\gamma\subset\mathrm{Graph}(E)$" is read as $\gamma(\mathrm{Graph}(E)^{c})=0$, which is how the proof of Proposition 1 uses it. The requirement that the graph be measurable is part of the definition of a diagonally dominant set function, as in Definition 1, so (Sel\*)'s "with a measurable graph" adds nothing further.
-- source:
--   Zhang, Yang & Gao, A Short and General Duality Proof for Wasserstein Distributionally Robust Optimization, arXiv:2205.00362v4, §2.1 notations (ℙ̂-measurable), p. 2 (PDF p. 2); §2.1 (IP) (Γ_ℙ̂), p. 3 (PDF p. 3); §3 Definition 1 and Proposition 1 (Proj), (Sel*), p. 6 (PDF p. 6)

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_Legendre_Setting

namespace ShortWDRODual.IP

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]

/-- `Graph(E) = {(x̂, x) : x ∈ E(x̂)}` of a set-valued map `E : 𝒳 → 2^𝒳`. -/
def graph (E : X → Set X) : Set (X × X) :=
  {p | p.2 ∈ E p.1}

/-- Definition 1 (p. 6), functions: `φ` is `(ℱ ⊗ ℱ)`-measurable and `φ(x̂, x) ≤ φ(x, x)` for all
`x̂, x`. -/
def DiagDomFun (φ : X × X → EReal) : Prop :=
  Measurable φ ∧ ∀ xh x, φ (xh, x) ≤ φ (x, x)

/-- Definition 1 (p. 6), sets: `A` is `(ℱ ⊗ ℱ)`-measurable and `(x̂, x) ∈ A` implies
`(x, x) ∈ A`. -/
def DiagDomSet (A : Set (X × X)) : Prop :=
  MeasurableSet A ∧ ∀ xh x, (xh, x) ∈ A → (x, x) ∈ A

/-- Definition 1 (p. 6), set functions: `E : 𝒳 → ℱ ∖ {∅}` (measurable, nonempty values) with an
`(ℱ ⊗ ℱ)`-measurable graph, such that `x ∈ E(x̂)` implies `x ∈ E(x)`. -/
def DiagDomSetFun (E : X → Set X) : Prop :=
  (∀ xh, MeasurableSet (E xh) ∧ (E xh).Nonempty) ∧ MeasurableSet (graph E) ∧
    ∀ xh x, x ∈ E xh → x ∈ E x

/-- (Proj) Measurable Projection (p. 6): for every diagonally dominant `A ∈ ℱ ⊗ ℱ`,
`Proj_x̂(A) = {x̂ : (x̂, x) ∈ A for some x}` lies in the completion `ℱ_ℙ̂`. -/
def Proj (Phat : Measure X) : Prop :=
  ∀ A : Set (X × X), DiagDomSet A → NullMeasurableSet (Prod.fst '' A) Phat

/-- (Sel*) Weak Measurable Selection (p. 6): for every diagonally dominant set-valued
`E : 𝒳 → ℱ ∖ {∅}` with measurable graph there is `γ ∈ Γ_ℙ̂` concentrated on `Graph(E)`
(`γ(Graph(E)ᶜ) = 0`; this is how "supp γ ⊂ Graph(E)" is read on a space without topology). -/
def SelStar (Phat : Measure X) : Prop :=
  ∀ E : X → Set X, DiagDomSetFun E → ∃ γ ∈ ShortWDRODual.Legendre.couplingsFst Phat, γ (graph E)ᶜ = 0

end ShortWDRODual.IP


