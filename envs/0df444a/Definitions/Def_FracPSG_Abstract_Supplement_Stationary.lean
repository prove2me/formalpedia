-- Prove2me | Definitions.Def_FracPSG_Abstract_Supplement_Stationary
-- name    : FracPSG_Abstract_Supplement_Stationary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:56:09.300805+00:00
-- url     : https://prove2.me/theorems/41b1490b-8523-4109-ad06-5bcba959e81d
-- title:
--   Definition 3.1(i) — stationary points of $\min_{x\in S} f(x)/g(x)$, with set regularity, local Lipschitz continuity and strict differentiability (pp. 4, 7)
-- statement:
--   Let $\mathcal H$ be a finite-dimensional real Hilbert space, $S\subseteq\mathcal H$, $f:\mathcal H\to(-\infty,+\infty]$ and $g:\mathcal H\to\mathbb R$. This file fixes the objects that Lemma 3.2, Assumption 3 and Theorem 5.5 of Boţ, Dao and Li use beyond those already published for this paper.
--
--   1. **The quotient.** $f/g$ is the extended-real function equal to $+\infty$ where $f(x)=+\infty$ and to the real number $f(x)/g(x)$ elsewhere.
--   2. **Stationary point (Definition 3.1(i)).** A point $\bar x\in S$ is a (limiting) stationary point of $\min_{x\in S} f(x)/g(x)$ if
--   $$0\in\partial_L\Big(\frac fg+\iota_S\Big)(\bar x),$$
--   where $\partial_L$ is the limiting subdifferential and $\iota_S$ the indicator of $S$.
--   3. **Regular set (p. 4).** $A$ is regular at $x\in A$ if its limiting normal cone $N_A(x)=\partial_L\iota_A(x)$ equals its Fréchet normal cone $\widehat N_A(x)=\widehat\partial\iota_A(x)$.
--   4. **Lipschitz continuity around a point.** An extended-real function $h$ is Lipschitz continuous around $x$ if it is finite on a neighbourhood of $x$ and Lipschitz there.
--   5. **Strict differentiability (p. 4, footnote 1).** $h$ is strictly differentiable at $x$ if it is finite near $x$ and there is $u$ with
--   $$\lim_{y,z\to x}\frac{h(y)-h(z)-\langle u,y-z\rangle}{\|y-z\|}=0 .$$
--
--   Stationary points are the first-order notion in which Corollary 4.6 and Theorem 5.5 state their limits; local minimizers of $f/g$ on $S$ are stationary.
--
--   **Formalization Note** $\mathcal H$ is any real inner-product space here and `EuclideanSpace ℝ (Fin N)` in the theorems. Where $f=+\infty$ the quotient is $+\infty$, so $\operatorname{dom}(f/g+\iota_S)=S\cap\operatorname{dom} f$. Where $g(x)=0$ and $f(x)$ is finite, the value $f(x)/g(x)$ is Lean's $0$; every statement that uses the quotient has $g>0$ near the points involved. Strict differentiability is Mathlib's `HasStrictFDerivAt` applied to the real values of $h$ on the neighbourhood where it is finite. The lifted stationary points of Definition 3.1(ii) are the published `FracPSG.Subseq.IsLiftedStationary`.
-- source:
--   Boţ, Dao, Li, Extrapolated Proximal Subgradient Algorithms for Nonconvex and Nonsmooth Fractional Programs, arXiv:2003.04124v2, p. 7, Definition 3.1(i); p. 4 (regularity of sets, strict differentiability, footnote 1)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_FracPSG_Subseq_Basic

open Filter Topology
open scoped InnerProductSpace

namespace FracPSG.Abstract.Supplement

open NonconvexSplitting.Shared FracPSG.Subseq

/-- The quotient `f/g` of problem (P) (Boţ–Dao–Li, arXiv:2003.04124v2, p. 1) as an extended-real
function: `+∞` where `f = +∞`, and the real number `f(x)/g(x)` elsewhere. Only its values on `S`
(where `g > 0` in every use) enter the statements, through `f/g + ι_S`. -/
noncomputable def quotient {X : Type*} (f : X → EReal) (g : X → ℝ) : X → EReal :=
  fun x => if f x = ⊤ then ⊤ else (((f x).toReal / g x : ℝ) : EReal)

/-- Definition 3.1(i) (p. 7): `xbar ∈ S` is a (limiting) stationary point of
`min_{x ∈ S} f(x)/g(x)` when `0 ∈ ∂_L(f/g + ι_S)(xbar)`. -/
def IsStationary {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → EReal) (g : X → ℝ) (S : Set X) (xbar : X) : Prop :=
  xbar ∈ S ∧ (0 : X) ∈ LimitingSubdiff (addInd (quotient f g) S) xbar

/-- Regularity of a set at a point (p. 4): `A` is regular at `x ∈ A` when its limiting normal cone
`N_A(x) = ∂_L ι_A(x)` equals its Fréchet normal cone `N̂_A(x) = ∂̂ ι_A(x)`. -/
def IsSetRegularAt {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (A : Set X) (x : X) : Prop :=
  x ∈ A ∧ {v | IsRegularSubgrad (addInd (fun _ => (0 : EReal)) A) x v} =
    LimitingSubdiff (addInd (fun _ => (0 : EReal)) A) x

/-- An extended-real function `h` is Lipschitz continuous around `x`: on some neighbourhood `U` of
`x` it is finite and its real values are Lipschitz. -/
def IsLipschitzAround {X : Type*} [NormedAddCommGroup X] (h : X → EReal) (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, (∀ y ∈ U, h y ≠ ⊤ ∧ h y ≠ ⊥) ∧ ∃ K : NNReal, LipschitzOnWith K (fun y => (h y).toReal) U

/-- An extended-real function `h` is strictly differentiable at `x` (p. 4, footnote 1): it is
finite near `x` and there is `u` with `(h(y) − h(z) − ⟨u, y − z⟩)/‖y − z‖ → 0` as `y, z → x`,
i.e. its real values have a strict Fréchet derivative at `x`. -/
def IsStrictlyDiffAt {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (h : X → EReal) (x : X) : Prop :=
  ∃ U ∈ 𝓝 x, (∀ y ∈ U, h y ≠ ⊤ ∧ h y ≠ ⊥) ∧
    ∃ L : X →L[ℝ] ℝ, HasStrictFDerivAt (fun y => (h y).toReal) L x

end FracPSG.Abstract.Supplement


