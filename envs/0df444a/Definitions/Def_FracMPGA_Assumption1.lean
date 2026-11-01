-- Prove2me | Definitions.Def_FracMPGA_Assumption1
-- name    : FracMPGA_Assumption1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:40:56.408879+00:00
-- url     : https://prove2.me/theorems/62018ded-2b74-4b38-8e64-95d85bbb17a4
-- title:
--   Assumption 1 (blanket hypotheses on problem (1))
-- statement:
--   The standing hypotheses of the paper on problem (1):
--
--   1. each $f_i$ is proper, lower semicontinuous and valued in $(-\infty,+\infty]$, and $\Omega$ is nonempty;
--   2. (Assumption 1(i)) $f$ is continuous on $\operatorname{dom}f$ and each $f_i$ is bounded below;
--   3. (Assumption 1(ii)) $h$ is locally Lipschitz differentiable on $\Omega$: every $x\in\Omega$ has a neighbourhood $B(x)$ and a constant $L_x$ with $\|\nabla h(u)-\nabla h(v)\|_2\le L_x\|u-v\|_2$ for all $u,v\in B(x)\cap\Omega$;
--   4. (Assumption 1(iii)) $g$ is convex, real-valued and non-negative;
--   5. (Assumption 1(iv)) $f+h\ge0$ on $\operatorname{dom}f$.
--
--   Every theorem of the mission assumes these.
--
--   **Formalization Note** Properness and lower semicontinuity of $f=\sum_i f_i$ follow from those of the $f_i$, those of the convex real-valued $g$ are automatic, and $h$ is real-valued, so they are not listed. Item 3 includes differentiability of $h$ on $\Omega$.
-- source:
--   Zhou, Zhang, Li, An equivalent reformulation and multi-proximity gradient algorithms for a class of nonsmooth fractional programming, arXiv:2311.00957v2, §1, p.2 (problem (1) and Assumption 1)

import Mathlib
import Definitions.Def_FracMPGA_Problem

open Topology

namespace FracMPGA

/-- The standing hypotheses on problem (1) of Zhou, Zhang, Li, arXiv:2311.00957v2, §1, p.2
("Throughout the paper, we make the following blanket assumptions"):

* each `f_i : ℝ^{n_i} → (−∞, +∞]` is proper and lower semicontinuous (p.2);
* `Ω = {x : g(x) ≠ 0}` is nonempty (p.2);
* **Assumption 1** (i) `f` is continuous on `dom(f)` and each `f_i` is bounded below;
  (ii) `h` is locally Lipschitz differentiable on `Ω`: for any `x ∈ Ω` there are a neighbourhood
  `B(x)` and a constant `L_x` with `‖∇h(u) − ∇h(v)‖₂ ≤ L_x ‖u − v‖₂` for all
  `u, v ∈ B(x) ∩ Ω`; (iii) `g` is convex, real-valued and non-negative on `ℝⁿ`;
  (iv) `f + h` is non-negative on `dom(f)`.

**Formalization Note** "`f_i` has values in `(−∞, +∞]`" is the clause `fb i z ≠ ⊥`. Properness
and lower semicontinuity of `f = Σ f_i` follow from those of the `f_i`, and those of the
real-valued convex `g` are automatic; `h` is real-valued (see `Problem`), so its properness and
lower semicontinuity are not required. (ii) includes differentiability of `h` on `Ω`, and `∇h` is
Mathlib's `gradient`. -/
def Assumption1 {n N : ℕ} (P : Problem n N) : Prop :=
  (∀ i, (∃ z, P.fb i z ≠ ⊤) ∧ (∀ z, P.fb i z ≠ ⊥) ∧ LowerSemicontinuous (P.fb i)) ∧
  P.Omega.Nonempty ∧
  ContinuousOn P.f {x | P.f x ≠ ⊤} ∧
  (∀ i, ∃ m : ℝ, ∀ z, (m : EReal) ≤ P.fb i z) ∧
  DifferentiableOn ℝ P.h P.Omega ∧
  (∀ x ∈ P.Omega, ∃ U ∈ 𝓝 x, ∃ L : ℝ, ∀ u ∈ U ∩ P.Omega, ∀ v ∈ U ∩ P.Omega,
    ‖gradient P.h u - gradient P.h v‖ ≤ L * ‖u - v‖) ∧
  ConvexOn ℝ Set.univ P.g ∧ (∀ x, 0 ≤ P.g x) ∧
  (∀ x, P.f x ≠ ⊤ → 0 ≤ P.zeta x)

end FracMPGA


