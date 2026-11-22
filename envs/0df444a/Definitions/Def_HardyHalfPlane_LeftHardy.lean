-- Prove2me | Definitions.Def_HardyHalfPlane_LeftHardy
-- name    : HardyHalfPlane_LeftHardy
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:07.752606+00:00
-- url     : https://prove2.me/theorems/cafc89af-8810-4b28-9ece-122d5ca57c75
-- title:
--   Hardy space $H^p(\mathbf C_{<a})$ of a left half-plane: the Hardy norm and the membership predicate
-- statement:
--   **Hardy spaces $H^p$ of a half-plane.** Fix $a\in\mathbb R$ and write $\mathbf C_{<a}=\{s\in\mathbb C:\operatorname{Re}(s)<a\}$ for the open half-plane to the left of the vertical line $\operatorname{Re}(s)=a$. For an exponent $p\in(0,\infty]$ and a function $\Phi$ on $\mathbf C_{<a}$, the *Hardy norm* of $\Phi$ is the supremum of the $L^p$ norms of $\Phi$ on the vertical lines of the half-plane:
--
--   $$\|\Phi\|_{H^p(\mathbf C_{<a})}:=\sup_{\sigma<a}\ \bigl\|\,y\mapsto\Phi(\sigma+iy)\,\bigr\|_{L^p(\mathbb R,\mathrm dy)}\ \in[0,\infty].$$
--
--   The *Hardy space* $H^p(\mathbf C_{<a})$ is the set of holomorphic functions $\Phi\colon\mathbf C_{<a}\to\mathbb C$ with $\|\Phi\|_{H^p(\mathbf C_{<a})}<\infty$.
--
--   The file provides two declarations.
--
--   1. `HardyHalfPlane.leftHardyNorm Φ a p` is the quantity $\|\Phi\|_{H^p(\mathbf C_{<a})}$, an element of $[0,\infty]$.
--   2. `HardyHalfPlane.MemLeftHardy Φ a p` is the proposition $\Phi\in H^p(\mathbf C_{<a})$: the function $\Phi$ is complex differentiable on $\mathbf C_{<a}$ and $\|\Phi\|_{H^p(\mathbf C_{<a})}<\infty$.
--
--   For example $\Phi(s)=1/(s-c)$ with $\operatorname{Re}(c)>a$ belongs to $H^p(\mathbf C_{<a})$ for every $p>1$, while a non-zero constant belongs only to $H^\infty(\mathbf C_{<a})$.
--
--   These are the classical Hardy spaces of a half-plane; Duren's book works with the upper half-plane $\{\operatorname{Im}(z)>0\}$, which corresponds to $\mathbf C_{<a}$ under $s=a+iz$. The source recalls them at the beginning of §B.2.1 as the model case for its Cauchy integral formulas on vertical lines: functions in $H^p(\mathbf C_{<a})$ have boundary values on $\operatorname{Re}(s)=a$ and, for $p\ge1$, are reproduced by their Cauchy integrals.
--
--   **Formalization Note.** $\Phi$ is a total function `ℂ → ℂ`; both declarations depend only on its values on $\mathbf C_{<a}$. The exponent is `p : ℝ≥0∞` and the $L^p$ norm is Mathlib's `eLpNorm` for Lebesgue measure on $\mathbb R$, so $p=\infty$ gives the essential supremum. For $p=0$ `eLpNorm` is identically $0$, so statements about $H^p$ must assume $p\ne0$. The source considers real exponents $p>0$.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 592, §B.2.1 (recalled definition of the Hardy space $H^p(\mathbf C_{<a})$ and of its norm); classical reference: P. Duren, Theory of $H^p$ Spaces, Academic Press, 1970, Chapter 11 (as cited by the paper at that spot)

import Mathlib

/-!
# Hardy spaces `H^p` of a left half-plane

For a real number `a` let `ℂ_{<a} = {s : ℂ | Re s < a}`.  The Hardy space `H^p(ℂ_{<a})` is the space
of holomorphic functions `Φ` on `ℂ_{<a}` whose `L^p` norms on the vertical lines `Re s = σ`, `σ < a`,
are uniformly bounded:

`‖Φ‖_{H^p(ℂ_{<a})} = sup_{σ < a} ‖y ↦ Φ(σ + i y)‖_{L^p(ℝ, dy)} < ∞`.

This is the classical Hardy space of a half-plane (P. Duren, *Theory of `H^p` spaces*, Chapter 11,
where the upper half-plane is used), in the normalisation of A. M. Masullo, *The Music of the
Primes*, §B.2.1, p. 592.

* `HardyHalfPlane.leftHardyNorm Φ a p` is the quantity `‖Φ‖_{H^p(ℂ_{<a})}`, as an element of
  `[0, ∞]`; it only depends on the values of `Φ` on `ℂ_{<a}`.
* `HardyHalfPlane.MemLeftHardy Φ a p` says that `Φ` is holomorphic on `ℂ_{<a}` and that
  `leftHardyNorm Φ a p` is finite.

The exponent `p` is an extended non-negative real, so that `p = ∞` gives the bounded holomorphic
functions.  For `p = 0` Mathlib's `eLpNorm` is identically `0`; statements about `H^p` should
assume `p ≠ 0`.
-/

open MeasureTheory
open scoped ENNReal

namespace HardyHalfPlane

/-- The Hardy norm `‖Φ‖_{H^p(ℂ_{<a})} = sup_{σ < a} ‖y ↦ Φ(σ + i y)‖_{L^p(ℝ, dy)}` of a function
`Φ : ℂ → ℂ` on the left half-plane `Re s < a`, with values in `[0, ∞]`.  The `L^p` norm is Mathlib's
`eLpNorm` with respect to Lebesgue measure on `ℝ`; no measurability or holomorphy is assumed here. -/
noncomputable def leftHardyNorm (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ σ : ℝ, ⨆ _ : σ < a, eLpNorm (fun y : ℝ => Φ ((σ : ℂ) + (y : ℂ) * Complex.I)) p volume

/-- `Φ` belongs to the Hardy space `H^p(ℂ_{<a})` of the left half-plane `Re s < a`: it is
holomorphic on that open half-plane and its Hardy norm `leftHardyNorm Φ a p` is finite. -/
def MemLeftHardy (Φ : ℂ → ℂ) (a : ℝ) (p : ℝ≥0∞) : Prop :=
  DifferentiableOn ℂ Φ {s : ℂ | s.re < a} ∧ leftHardyNorm Φ a p < ⊤

end HardyHalfPlane


