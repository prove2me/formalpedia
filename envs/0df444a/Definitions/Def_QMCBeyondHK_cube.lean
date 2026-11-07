-- Prove2me | Definitions.Def_QMCBeyondHK_cube
-- name    : QMCBeyondHK_cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:34:23.781974+00:00
-- url     : https://prove2.me/theorems/b26f6402-a022-4182-aff6-3209125d7b56
-- title:
--   The unit cube $[0,1)^d$, its uniform law, the integral, the $L^2$ inner product, shifts mod 1 and the integration error
-- statement:
--   This module fixes the basic objects of numerical integration on the half-open unit cube.
--
--   1. The **cube** is $[0,1)^d = \prod_{i=1}^d [0,1)$, a set of vectors $x = (x_1,\dots,x_d) \in \mathbb R^d$.
--   2. The **uniform distribution** $\mathrm{Unif}[0,1)^d$ is Lebesgue measure restricted to the cube.
--   3. The **integral** of $f$ is $\bar f = \int_{[0,1)^d} f(z)\,dz$, and the $L^2$ **inner product** is $\langle f, g\rangle = \int_{[0,1)^d} f(x) g(x)\,dx$.
--   4. For a point $x$ and a shift $s \in [0,1)^d$, $x - s \bmod [0,1)^d$ is the vector with coordinates $\operatorname{frac}(x_i - s_i)$, and the **shifted function** is $f_s(x) = f(x + s \bmod [0,1)^d)$, i.e. $f_s(x) = f\big((\operatorname{frac}(x_i + s_i))_i\big)$.
--   5. For an $n$-point set $A = (A_0,\dots,A_{n-1})$ the **integration error** is
--   $$
--   \operatorname{err}(A, f) = \bar f(A) - \bar f, \qquad \bar f(A) = \frac1n \sum_{t<n} f(A_t).
--   $$
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** Points are `Fin d → ℝ`; $\operatorname{frac}$ is `Int.fract`. An $n$-point set is a tuple `Fin n → ℝ^d`, so repeated points are counted with multiplicity; every statement using $\operatorname{err}$ has $n \ge 1$. The integrals are Bochner integrals, applied only to functions in $L^2$ of the cube.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §1, p.1 (PDF p.3): f̄, f̄(A), err(A, f); §2, p.6 (PDF p.8): ⟨f, g⟩ and f_s; §2.1, p.7 (PDF p.9): Unif[0,1)^d; §3.1, p.9 (PDF p.11): shifts modulo [0,1)^d

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK

/-- The half-open unit cube `[0,1)^d` (Ezeunala, Jha, Jiang, *Quasi-Monte Carlo Beyond
Hardy–Krause II*, arXiv:2609.10921, sha256 bc273e88…, §1, printed p.1, PDF p.3).

**Formalization Note** Points of `[0,1)^d` are vectors `Fin d → ℝ`; the cube is the product set
`∏ i, [0,1)`. -/
def cube (d : ℕ) : Set (Fin d → ℝ) := Set.univ.pi (fun _ => Set.Ico (0 : ℝ) 1)

/-- The uniform distribution `Unif[0,1)^d`: Lebesgue measure restricted to the cube
(arXiv:2609.10921, sha256 bc273e88…, §2.1, p.7, PDF p.9). -/
noncomputable def unif (d : ℕ) : Measure (Fin d → ℝ) := volume.restrict (cube d)

/-- The integral `f̄ = ∫_{[0,1)^d} f(z) dz` (arXiv:2609.10921, sha256 bc273e88…, §1, p.1, PDF p.3).

**Formalization Note** A Bochner integral; every statement using it assumes `f ∈ L²` of the cube,
so `f` is integrable and no junk value occurs. -/
noncomputable def cubeMean (d : ℕ) (f : (Fin d → ℝ) → ℝ) : ℝ := ∫ x in cube d, f x

/-- The `L²([0,1)^d)` inner product `⟨f, g⟩ = ∫_{[0,1)^d} f(x) g(x) dx`
(arXiv:2609.10921, sha256 bc273e88…, §2, p.6, PDF p.8). -/
noncomputable def l2inner (d : ℕ) (f g : (Fin d → ℝ) → ℝ) : ℝ := ∫ x in cube d, f x * g x

/-- The shift of a point by `−s` modulo `[0,1)^d`, `x − s mod [0,1)^d`
(arXiv:2609.10921, sha256 bc273e88…, §3.1, p.9, PDF p.11).

**Formalization Note** Reduction modulo `1` in each coordinate is `Int.fract`. -/
noncomputable def fracSub {d : ℕ} (x s : Fin d → ℝ) : Fin d → ℝ := fun i => Int.fract (x i - s i)

/-- The shifted function `f_s(x) = f(x + s mod [0,1)^d)` (arXiv:2609.10921, sha256 bc273e88…,
§2, p.6, PDF p.8).

**Formalization Note** Reduction modulo `1` in each coordinate is `Int.fract`. -/
noncomputable def shiftFun {d : ℕ} (f : (Fin d → ℝ) → ℝ) (s : Fin d → ℝ) : (Fin d → ℝ) → ℝ :=
  fun y => f (fun i => Int.fract (y i + s i))

/-- The integration error `err(A, f) = f̄(A) − f̄`, with `f̄(A) = |A|⁻¹ ∑_{z∈A} f(z)`
(arXiv:2609.10921, sha256 bc273e88…, §1, p.1, PDF p.3).

**Formalization Note** An `n`-point set is a tuple `A : Fin n → [0,1)^d` (a multiset; repeated
points are counted with multiplicity). Every statement using `err` has `n ≥ 1`. -/
noncomputable def err {d n : ℕ} (A : Fin n → Fin d → ℝ) (f : (Fin d → ℝ) → ℝ) : ℝ :=
  (∑ t, f (A t)) / n - cubeMean d f

end QMCBeyondHK


