-- Prove2me | Definitions.Def_ThinShellSampling_piOf
-- name    : ThinShellSampling_piOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:14.852233+00:00
-- url     : https://prove2.me/theorems/c423c4b5-846e-4dd9-873b-8936bf7c4589
-- title:
--   Extended-valued convex potential $V$, ground set $L_g$, target $\pi\propto e^{-V}$
-- statement:
--   Let $V:\mathbb R^n\to\mathbb R\cup\{\infty\}$. It is **convex** if its domain $\{V<\infty\}$ is convex and $V$ is convex there. Its **ground set** is
--
--   $$
--   L_g=\{x\in\mathbb R^n: V(x)-\min V\le 10n\},
--   $$
--
--   and the **target** is the probability measure $\pi\propto e^{-V}$, with Lebesgue density $e^{-V}/\int e^{-V}$ (and $e^{-\infty}=0$). The **standing assumptions** of §6 and Theorem 1.7 are: $V$ convex, $B(0,1)\subseteq L_g$, and $\int e^{-V}<\infty$. Finally $R=(\mathbb E_\pi\|X\|^2)^{1/2}$.
--
--   The case $V=\infty\cdot 1_{K^c}$ is the uniform distribution on a convex body $K\supseteq B(0,1)$; the ball condition is a normalization that any logconcave distribution satisfies after an affine change of variables.
--
--   **Formalization Note** $V$ takes values in `WithTop ℝ`. $x\in L_g$ is encoded as $V(x)<\infty$ and $V(x)-V(y)\le 10n$ for all $y$ in the domain, so $\min V$ is the infimum over the domain and no junk value of a minimum enters. $B(0,1)$ is the open ball. No measurability of $V$ is assumed.
-- source:
--   Kook, Vempala, Thin-Shell Stability and Heat-Adjoint Hypercontractivity: Logconcave Sampling with Sesteric Complexity from a Cold Start, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.7, p.5 (PDF p.7); §6, p.34 (PDF p.36); §1.1, p.4

import Mathlib
import Definitions.Def_ThinShellSampling_covMat

set_option autoImplicit false

namespace ThinShellSampling

open MeasureTheory
open scoped ENNReal

/-- The **effective domain** `{x : V(x) < ∞}` of an extended-valued potential `V : ℝⁿ → ℝ ∪ {∞}`. -/
def dom {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | V x ≠ ⊤}

/-- The real value of `V` at `x`, meaningful on the domain (it is `0` where `V = ∞`, and is only
read on the domain). -/
noncomputable def vr {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (V x).untopD 0

/-- **Convexity of an extended-valued function** `V : ℝⁿ → ℝ ∪ {∞}`: its domain is convex and `V`
is convex on it.

Kook, Vempala, *Thin-Shell Stability and Heat-Adjoint Hypercontractivity*, STOC 2027 submission
(manuscript sha256 25a041a9…), Theorem 1.7, p.5 (PDF p.7): "Let `V : ℝⁿ → ℝ ∪ {∞}` be a convex
function".

**Formalization Note.** `V` takes values in `WithTop ℝ`. No measurability or lower semicontinuity
is assumed (the paper assumes none; a convex function is Borel off the boundary of its domain, a
Lebesgue-null set). -/
def IsConvexPotential {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop :=
  Convex ℝ (dom V) ∧ ConvexOn ℝ (dom V) (vr V)

/-- `e^{−V(x)}` with `e^{−∞} = 0`. -/
noncomputable def expNegV (v : WithTop ℝ) : ℝ≥0∞ :=
  if h : v = ⊤ then 0 else ENNReal.ofReal (Real.exp (-(v.untop h)))

/-- **Ground set** `L_g = {x ∈ ℝⁿ : V(x) − min V ≤ 10n}`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), §1.1, p.5 (PDF p.7) and §6,
p.34 (PDF p.36): "the ground set `L_g := {x ∈ ℝⁿ : V(x) − min V ≤ 10n}`".

**Formalization Note.** `x ∈ L_g` iff `V(x) < ∞` and `V(x) − V(y) ≤ 10n` for every `y` with
`V(y) < ∞`, i.e. `V(x) − inf V ≤ 10n` with `inf V` the infimum over the domain (`min V` in the
paper). If `V` were unbounded below the set would be empty; no junk value of `min V` enters. -/
def Lg {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | V x ≠ ⊤ ∧ ∀ y, V y ≠ ⊤ → vr V x - vr V y ≤ 10 * n}

/-- The normalizing constant `∫ e^{−V} dx ∈ [0, ∞]`. -/
noncomputable def normConst {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : ℝ≥0∞ :=
  ∫⁻ x, expNegV (V x)

/-- **The target** `π ∝ e^{−V}`, the probability measure with Lebesgue density `e^{−V}/∫e^{−V}`.

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.7, p.5 (PDF p.7):
"suppose that `π ∝ e^{−V}`"; §1, p.1 (PDF p.3): "`dπ(x) ∝ e^{−V(x)} dx`".

**Formalization Note.** Under `IsStandardPotential V` the normalizer is positive and finite, so
`piOf V` is a probability measure. -/
noncomputable def piOf {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) :=
  (normConst V)⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin n))).withDensity
    (fun x => expNegV (V x))

/-- **The standing assumptions of §6 and Theorem 1.7** on the potential: `V : ℝⁿ → ℝ ∪ {∞}` is
convex, the ground set contains the open unit ball, and `e^{−V}` is integrable (so that
`π ∝ e^{−V}` is a distribution).

Kook, Vempala, STOC 2027 submission (manuscript sha256 25a041a9…), Theorem 1.7, p.5 (PDF p.7):
"Let `V : ℝⁿ → ℝ ∪ {∞}` be a convex function, and suppose that `π ∝ e^{−V}` satisfies
`B(0, 1) ⊆ L_g`"; §6, p.34 (PDF p.36).

**Formalization Note.** `B(0, 1)` is the open ball (the weaker of the two readings). `∫ e^{−V} < ∞`
is the paper's implicit "π ∝ e^{−V} is a distribution"; `∫ e^{−V} > 0` follows from the ball
condition. -/
structure IsStandardPotential {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : Prop where
  convex : IsConvexPotential V
  ball_subset : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1 ⊆ Lg V
  integrable : normConst V < ⊤

/-- **`R = (E_π‖X‖²)^{1/2}`** for `π ∝ e^{−V}` (Kook, Vempala, STOC 2027 submission, manuscript
sha256 25a041a9…, §1.1, p.4 = PDF p.6). Under `IsStandardPotential V`, `π` is logconcave with
finite moments of all orders, so the Bochner integral is the true second moment. -/
noncomputable def Rrad {n : ℕ} (V : EuclideanSpace ℝ (Fin n) → WithTop ℝ) : ℝ :=
  Real.sqrt (rsq (piOf V))

end ThinShellSampling


