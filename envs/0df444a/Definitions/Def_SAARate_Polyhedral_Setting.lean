-- Prove2me | Definitions.Def_SAARate_Polyhedral_Setting
-- name    : SAARate_Polyhedral_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T02:16:29.988427+00:00
-- url     : https://prove2.me/theorems/320270d2-6795-4cdd-b1f0-827d20ad19f5
-- title:
--   §1–§3, pp. 1–12 — (1.1), (1.2), optimal sets A and A_N, i.i.d. sample, polyhedral sets, piecewise linear convex functions, faces
-- statement:
--   This file fixes the objects of the paper's finite polyhedral setting.
--
--   Let $\Theta\subseteq\mathbb R^m$ be a feasible set, $(\Omega,\mathcal F,P)$ a probability space of scenarios and $h:\mathbb R^m\times\Omega\to\mathbb R$. The **true problem** (1.1) and the **sample average approximation (SAA)** (1.2) are
--   $$
--   \min_{x\in\Theta}\ f(x):=\mathbb E_P\,h(x,\omega),\qquad \min_{x\in\Theta}\ \hat f_N(x):=\frac1N\sum_{j=1}^N h(x,\omega^j),
--   $$
--   where $\omega^1,\omega^2,\dots$ is a sample.
--
--   1. **Expected value function** $f(x)=\int h(x,\omega)\,dP(\omega)$.
--   2. **Sample average function** $\hat f_N(x)=N^{-1}\sum_{j=1}^N h(x,\omega^j)$, computed from the first $N$ terms of a sample path $(\omega^1,\omega^2,\dots)$.
--   3. **Optimal set** of a function $g$ on $\Theta$: $\{x\in\Theta: g(x)\le g(y)\ \forall y\in\Theta\}$. The paper's $A$ is the optimal set of $f$ and $A_N$ that of $\hat f_N$; either may be empty.
--   4. **i.i.d. sample**: a sequence $\omega^1,\omega^2,\dots$ of $\Omega$-valued random variables on an auxiliary probability space $(S,Q)$, measurable, mutually independent, each with law $P$.
--   5. A set $C\subseteq\mathbb R^m$ is **polyhedral** if it is the intersection of finitely many closed half-spaces $\{x:\langle a_i,x\rangle\le b_i\}$ (no half-spaces gives $\mathbb R^m$).
--   6. A function $g:\mathbb R^m\to\mathbb R$ is **piecewise linear and convex** if it is the pointwise maximum of finitely many, and at least one, affine functions $x\mapsto\langle a_i,x\rangle+b_i$.
--   7. A set $F$ **forms a face** of a convex set $A$ if $F$ is convex and is an extreme subset of $A$: $F\subseteq A$ and whenever a point of $F$ lies in the open segment between two points of $A$, both points lie in $F$ (Rockafellar's face). The empty set and $A$ itself are faces.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^m$ is `EuclideanSpace ℝ (Fin m)`. The sample is one sequence `ω : ℕ → S → Ω`; the paper's $\omega^1,\dots,\omega^N$ are its terms $0,\dots,N-1$, so the same sample is extended as $N$ grows. At $N=0$ the sample average is the junk value $0$, which statements "for $N$ large enough" never see. "Piecewise linear" for a finite-valued function on $\mathbb R^m$ is encoded as a maximum of $k+1$ affine pieces, and "face" as `Convex ℝ F ∧ IsExtreme ℝ A F`; both are disclosed encoding choices.
-- source:
--   Shapiro & Homem-de-Mello, On Rate of Convergence of Optimal Solutions of Monte Carlo Approximations of Stochastic Programs, preprint (SPEPS copy, edoc.hu-berlin.de), pp. 1, 3, 6, 12, (1.1), (1.2), (2.1), Theorem 2.3 (i)–(iv), (3.16)

import Mathlib
import Definitions.Def_SAARate_SharpLD_Setting
import Definitions.Def_SAARate_Sharp_Setting

namespace SAARate.Polyhedral

open MeasureTheory ProbabilityTheory

/-- A polyhedral set: the intersection of finitely many closed half-spaces
`{x | ⟪a_i, x⟫ ≤ b_i}` (with `k = 0` this is the whole space). -/
def IsPolyhedral {m : ℕ} (C : Set (SAARate.Sharp.E m)) : Prop :=
  ∃ (k : ℕ) (a : Fin k → SAARate.Sharp.E m) (b : Fin k → ℝ), C = {x | ∀ i, inner ℝ (a i) x ≤ b i}

/-- A finite-valued piecewise linear convex function on `ℝ^m`: the pointwise maximum of
finitely many, and at least one, affine functions `x ↦ ⟪a_i, x⟫ + b_i`, `i = 0, …, k`
(`k + 1` pieces, so the maximum is over a nonempty index set). -/
def IsPLConvex {m : ℕ} (g : SAARate.Sharp.E m → ℝ) : Prop :=
  ∃ (k : ℕ) (a : Fin (k + 1) → SAARate.Sharp.E m) (b : Fin (k + 1) → ℝ), ∀ x,
    g x = Finset.univ.sup' Finset.univ_nonempty (fun i => inner ℝ (a i) x + b i)

/-- `F` forms a face of the convex set `A`: `F` is convex and is an extreme subset of `A`
(Rockafellar's face). The empty set and `A` itself are faces. -/
def IsFace {m : ℕ} (A F : Set (SAARate.Sharp.E m)) : Prop :=
  Convex ℝ F ∧ IsExtreme ℝ A F

end SAARate.Polyhedral


