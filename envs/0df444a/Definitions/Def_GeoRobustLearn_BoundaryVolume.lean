-- Prove2me | Definitions.Def_GeoRobustLearn_BoundaryVolume
-- name    : GeoRobustLearn_BoundaryVolume
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:07:15.276292+00:00
-- url     : https://prove2.me/theorems/c628286c-9de0-4f0b-870a-daf808ff3793
-- title:
--   Boundary volume $\mathrm{Bdry}_r$, the class $\mathcal C_K$, $\mathrm{opt}_K$, binary labels and Gaussian surface area $\Gamma_\gamma$
-- statement:
--   Let $\gamma$ be the standard Gaussian measure $N(0,I_d)$ on $\mathbb R^d$. A **Boolean function** is a function $f:\mathbb R^d\to\{0,1\}$. Its **$r$-boundary volume** is the Gaussian probability of the points within distance $r$ of its decision boundary:
--
--   $$\mathrm{Bdry}_r(f)=\Pr_{x\sim\gamma}\big[\exists z:\ \|z\|_2\le r,\ f(x)\ne f(x+z)\big].$$
--
--   For $K\in\mathbb R$, the class $\mathcal C_K$ consists of the Boolean functions with $\mathrm{Bdry}_r(f)\le Kr$ for every $r>0$; it is empty when $K<0$, since $\mathrm{Bdry}_r(f)\ge0>Kr$. For a distribution $D$ on $\mathbb R^d\times\{0,1\}$,
--
--   $$\mathrm{opt}_K=\inf_{f\in\mathcal C_K}\Pr_{(x,y)\sim D}[f(x)\ne y].$$
--
--   For a Borel set $A\subseteq\mathbb R^d$, the **Gaussian (Minkowski) surface area** is
--
--   $$\Gamma_\gamma(A)=\liminf_{\delta\to0^+}\frac{\gamma(A_\delta\setminus A)}{\delta},\qquad A_\delta=\{x:\operatorname{dist}(x,A)\le\delta\}.$$
--
--   These are the objects of the paper's main theorem: $\mathcal C_K$ is the class of adversarially robust classifiers, $\mathrm{opt}_K$ the agnostic benchmark, and $\Gamma_\gamma$ the complexity measure of [KOS08].
--
--   **Formalization Note** Classifiers are real-valued functions with values $0$ and $1$ (`IsBoolean`); labels are reals equal to $0$ or $1$ almost surely (`BinaryLabels`). No measurability is required of classifiers, and every probability of a set that may fail to be measurable is an outer measure. $\mathrm{Bdry}_r$ is taken under $\gamma$, the data marginal throughout §6. $A_\delta$ is Mathlib's closed thickening (empty for $A=\emptyset$), and the quotient is computed in $[0,\infty]$.
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Definition 1.1, p.2; class C_K, p.3; opt_K, Theorem 6.1, p.30; Definition 3.1, p.13

import Definitions.Def_GeoLipLearn_Agnostic_Gaussian

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-!
# Boundary volume, the class `C_K`, `opt_K`, binary labels and Gaussian surface area

J. Lange, C. Marcussen, A. Vasilyan, *Geometrically Constrained Learning I: Agnostically Learning
Adversarially Robust Classifiers*, manuscript of November 3, 2026 (sha256 8cbf3f52…): Definition 1.1
(p.2), the class `C_K` (p.3), `opt_K` (Theorem 6.1, p.30), Definition 3.1 (p.13).

**Formalization Note.** `ℝ^d` is the published `GeoLipLearn.Agnostic.Space d` and `γ` the published
`GeoLipLearn.Agnostic.gaussian d` (the standard Gaussian). Classifiers are real-valued functions with
values in `{0, 1}` (`IsBoolean`); no measurability is required of them, and every probability of a set
that may fail to be measurable is the outer measure `μ S`. The data marginal is `γ` throughout §6, so
`Bdry_r` is taken under `γ`.
-/

/-- A Boolean function `f : ℝ^d → {0, 1}`, written as a real-valued function with values `0` and `1`. -/
def IsBoolean {d : ℕ} (f : Space d → ℝ) : Prop := ∀ x, f x = 0 ∨ f x = 1

/-- The `r`-boundary volume (Definition 1.1, p.2):
`Bdry_r(f) = Pr_{x∼γ}[∃ z : ‖z‖₂ ≤ r, f(x) ≠ f(x + z)]`.

**Formalization Note.** The (outer) Gaussian measure of the set, with no measurability assumed. -/
noncomputable def bdry {d : ℕ} (r : ℝ) (f : Space d → ℝ) : ℝ≥0∞ :=
  gaussian d {x | ∃ z : Space d, ‖z‖ ≤ r ∧ f x ≠ f (x + z)}

/-- The class `C_K` (p.3): Boolean functions with `Bdry_r(f) ≤ K r` for all `r > 0`.

**Formalization Note.** `r = 0` is automatic (`Bdry_0 = 0`) and a negative radius is not a radius;
no measurability is required of `f`. The conjunct `0 ≤ K` keeps the book's meaning for `K < 0`:
there `Bdry_r(f) ≥ 0 > K r`, so `C_K` is empty, whereas `ENNReal.ofReal (K * r) = 0` alone would
admit the constant functions. -/
def InCK {d : ℕ} (K : ℝ) (f : Space d → ℝ) : Prop :=
  IsBoolean f ∧ 0 ≤ K ∧ ∀ r : ℝ, 0 < r → bdry r f ≤ ENNReal.ofReal (K * r)

/-- `opt_K = inf_{f ∈ C_K} Pr_{(x,y)∼D}[f(x) ≠ y]` (Theorem 6.1, p.30), the infimum over **all** of
`C_K`, with the (outer) `D`-measure of the error set (`⊤`, the infimum of the empty set, when
`K < 0`). -/
noncomputable def optK {d : ℕ} (K : ℝ) (D : Measure (Space d × ℝ)) : ℝ≥0∞ :=
  ⨅ f : {f : Space d → ℝ // InCK K f}, D {z | f.1 z.1 ≠ z.2}

/-- `D` is a distribution on `ℝ^d × {0, 1}`: labels live in `ℝ` and are `0` or `1` almost surely. -/
def BinaryLabels {d : ℕ} (D : Measure (Space d × ℝ)) : Prop :=
  ∀ᵐ z ∂D, z.2 = 0 ∨ z.2 = 1

/-- The Gaussian (Minkowski) surface area of Definition 3.1, p.13:
`Γ_γ(A) = liminf_{δ→0} γ(A_δ \ A)/δ`, `A_δ = {x : dist(x, A) ≤ δ}`.

**Formalization Note.** `A_δ` is Mathlib's closed thickening `Metric.cthickening δ A` (empty for
`A = ∅`), the limit is taken as `δ → 0⁺`, and the quotient is computed in `ℝ≥0∞`. -/
noncomputable def surfaceArea {d : ℕ} (A : Set (Space d)) : ℝ≥0∞ :=
  Filter.liminf (fun δ : ℝ => gaussian d (Metric.cthickening δ A \ A) / ENNReal.ofReal δ)
    (nhdsWithin 0 (Set.Ioi 0))

end GeoRobustLearn


