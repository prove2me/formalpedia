-- Prove2me | Definitions.Def_AffinePSD_Existence_Generator
-- name    : AffinePSD_Existence_Generator
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:22.963558+00:00
-- url     : https://prove2.me/theorems/b3ed7e63-ee23-4c34-af22-dca4c8e4e3b9
-- title:
--   The generator formula (2.12) on rapidly decreasing functions, with the paper's symmetrized partial derivatives
-- statement:
--   Following §1.2, a function $f$ on $S_d$ is read as $x\mapsto g((x+x^\top)/2)$, so $\partial f/\partial x_{ij}$ is the derivative in the direction $\tfrac12(E^{ij}+E^{ji})$. For a rapidly decreasing smooth function $f$ (the restriction to $S_d^+$ of a Schwartz function on $M_d$) and $x\in S_d^+$, the operator (2.12) is
--   $$\mathcal Af(x)=\frac12\sum_{i,j,k,l}A_{ijkl}(x)\frac{\partial^2f(x)}{\partial x_{ij}\partial x_{kl}}+\sum_{i,j}\big(b_{ij}+B_{ij}(x)\big)\frac{\partial f(x)}{\partial x_{ij}}-(c+\langle\gamma,x\rangle)f(x)$$
--   $$\quad+\int_{S_d^+\setminus\{0\}}\big(f(x+\xi)-f(x)\big)\,m(d\xi)+\int_{S_d^+\setminus\{0\}}\big(f(x+\xi)-f(x)-\langle\chi(\xi),\nabla f(x)\rangle\big)\,M(x,d\xi).$$
--
--   The predicate `GeneratorIntegrable` states that both integrands are integrable for every such $f$ and every $x\in S_d^+$. The operator (2.12) is the generator of the process whose existence and uniqueness the mission establishes.
--
--   **Formalization Note** The space $\mathcal S_+$ of (B.1) is represented by Schwartz functions $F$ on $M_d$, restricted to the cone. Every restriction is in $\mathcal S_+$, and every element of $\mathcal S_+$ arises this way: extend a Schwartz function $h$ on $S_d$ by $x\mapsto h(\operatorname{sym}x)\,e^{-\|x-x^\top\|^2}$. Because $A_{ijkl}$ is symmetric in $i\leftrightarrow j$ and in $k\leftrightarrow l$, the formula does not depend on the symmetric extension.
-- source:
--   Cuchiero, Filipović, Mayerhofer, Teichmann, Affine processes on positive semidefinite matrices, arXiv:0910.0137v3 (2011), §1.2 p. 6; Theorem 2.4, (2.12), p. 9; (B.1), p. 65

import Mathlib
import Definitions.Def_AffinePSD_Existence_Params
import Definitions.Def_AffinePSD_Necessity_Generator

open MeasureTheory
open scoped SchwartzMap

namespace AffinePSD.Existence

/-- The two integrands of (2.12) are integrable for every Schwartz `F` and every `x ∈ S_d^+`:
`ξ ↦ F(x+ξ) − F(x)` against `m` and `ξ ↦ F(x+ξ) − F(x) − ⟨χ(ξ), ∇F(x)⟩` against `M(x, ·)`.
Formalization Note: concluded alongside every statement about the generator (2.12), so that the
Bochner integrals in `Asharp` are the page's integrals and not Lean's junk value `0`. -/
def GeneratorIntegrable {d : ℕ} (χ : AffinePSD.Necessity.Trunc d) (P : AffinePSD.Necessity.Params d) : Prop :=
  ∀ (F : 𝓢(Mat d, ℝ)) (x : Cone d),
    Integrable (fun ξ : Cone d => F ((x : Mat d) + (ξ : Mat d)) - F x) P.m ∧
    Integrable (fun ξ : Cone d =>
      F ((x : Mat d) + (ξ : Mat d)) - F x - tr (χ.χ ξ) (AffinePSD.Necessity.grad F x)) (AffinePSD.Necessity.Mker P x)

end AffinePSD.Existence


