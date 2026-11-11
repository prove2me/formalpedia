-- Prove2me | Definitions.Def_TestableSanitization_Robust_Boundary
-- name    : TestableSanitization_Robust_Boundary
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:00.779682+00:00
-- url     : https://prove2.me/theorems/07a8c07e-be08-4110-9de9-7515fbbf604b
-- title:
--   The r-boundary $D(\partial f_r)$, $(r,\eta)$-robustness, uniform ball laws, local noise sensitivity $\phi_{f,\delta}$, $\mathrm{NS}_{D,\delta}$, $\mathrm{Iso}_{D,\delta}$ and total variation
-- statement:
--   The input space is $\mathbb R^d$ with the Euclidean norm $\|\cdot\|$ (`Pt d`). A **classifier** is a Borel-measurable function $f:\mathbb R^d\to\{\pm1\}$ (`IsClassifier f`).
--
--   **Boundary and robustness (Definition 1).** For $r>0$, the **$r$-boundary** of $f$ is the set of points at which a perturbation of norm strictly less than $r$ changes the label,
--   $$\partial f_r=\{x\in\mathbb R^d:\ \exists z,\ \|z\|<r,\ f(x)\neq f(x+z)\},$$
--   and its **$r$-boundary volume** under a distribution $D$ is $D(\partial f_r)$ (`boundaryMass D r f`). $f$ is **$(r,\eta)$-robust** if $D(\partial f_r)\le\eta$ (`IsRobust`).
--
--   **Uniform laws (§2).** $U=U(B_1)$ is the uniform distribution on the closed unit ball $B_1=\{z:\|z\|\le1\}$ (`U d`, the published `uniformBall`), and $U(B(x,R))$ is the uniform distribution on the closed ball $B(x,R)=\{y:\|y-x\|\le R\}$ (`ballLaw x R`), the law of $x+RZ$ for $Z\sim U$.
--
--   **Noise sensitivity and isolation (Definitions 11–13).** For a noise scale $\delta>0$, the **local noise sensitivity** of $f$ at $x$ is $\phi_{f,\delta}(x)=\Pr_{Z\sim U}[f(x+\delta Z)\neq f(x)]$ (`lns f δ x`); the **noise sensitivity** is $\mathrm{NS}_{D,\delta}(f)=\mathbb E_{x\sim D}\,\phi_{f,\delta}(x)$ (`NS D δ f`); the **isolation probability** at threshold $\theta$ is $\mathrm{Iso}_{D,\delta}(f,\theta)=\Pr_{x\sim D}[\phi_{f,\delta}(x)>\theta]$ (`Iso D δ f θ`, strict inequality).
--
--   **Total variation (§2).** $d_{TV}(P,Q)=\sup_A|P(A)-Q(A)|$ over measurable sets $A$ (`tvDist P Q`). **Unit-ball volume (Lemma 34).** $\kappa_m=\pi^{m/2}/\Gamma(m/2+1)$ (`kappa m`).
--
--   These are the objects every statement of the mission is written in: robustness is the property the sanitizer must certify, and noise sensitivity and isolation are the quantities its test measures.
--
--   **Formalization Note.** The labels $\pm1$ are the reals $1,-1$. $D(\partial f_r)$ is Mathlib's measure of the set (an outer measure, so no measurability of $f$ is needed for it to make sense). `lnsE` is $\phi_{f,\delta}(x)$ in $[0,1]\subset[0,\infty]$ and `lns` its real value; `NS` is a lower Lebesgue integral and `Iso` a measure, both in $[0,\infty]$. `tvDist` takes the supremum in $[0,\infty]$ of $|P(A)-Q(A)|$ (computed from the real values of the two measures). The file proves that `U d` is a probability measure (an instance needed for the stream laws).
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 6 (PDF 8), §2 Notation and Distributions; p. 7 (PDF 9), Definition 1; p. 22 (PDF 24), §4.1; pp. 62–63 (PDF 64–65), Definitions 11–13; p. 64 (PDF 66), Lemma 34 (κ_m)

import Mathlib
import Definitions.Def_RegretBandits_Nonlinear_Smoothing

/-!
# The r-boundary, robustness, uniform ball laws, local noise sensitivity, noise sensitivity,
# isolation and total variation

Cai, Mamali, Sotiraki, Yu, Zampetakis, *Testable Sanitization via Boundary Geometry*, STOC 2027
submission (manuscript sha256 bcf6434f…): §2 p. 6 (notation, balls, uniform laws, total
variation), Definition 1 p. 7, §4.1 p. 22, Definitions 11–13 pp. 62–63, Lemma 34 p. 64 (the
unit-ball volume constant).

Conventions.
* The input space is `Pt d = EuclideanSpace ℝ (Fin d)`, with the Euclidean norm.
* A classifier `f : Pt d → ℝ` takes the values `1` and `-1` only and is Borel measurable
  (`IsClassifier`); the paper's `{±1}` are these two reals.
* `boundarySet r f` is the paper's `∂f_r = {x : ∃ z, ‖z‖ < r, f x ≠ f (x + z)}` (strict radius);
  `boundaryMass D r f = D(∂f_r)` is its `D`-measure (outer measure, so no measurability of `f` is
  needed for the value to make sense).
* `U d` is the uniform law on the closed unit ball (the published `uniformBall`), and
  `ballLaw x R` the uniform law on the closed ball `B(x, R)`, its image under `z ↦ x + R • z`.
* `lnsE f δ x = U{z : f (x + δ z) ≠ f x}` in `[0, 1]`; `lns` is its real value `ϕ_{f,δ}(x)`.
  `NS D δ f = ∫⁻ ϕ_{f,δ} dD` and `Iso D δ f θ = D{x : ϕ_{f,δ}(x) > θ}` (strict), both in `[0, ∞]`.
* `tvDist P Q` is `sup` over measurable sets `A` of `|P(A) − Q(A)|`, in `[0, ∞]`.
* `kappa m = π^{m/2} / Γ(m/2 + 1)`, the volume of the unit ball of `ℝ^m`.
-/

open MeasureTheory

namespace TestableSanitization.Robust

/-- The input space `ℝ^d` with the Euclidean norm. -/
abbrev Pt (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- A classifier `f : ℝ^d → {±1}`: Borel measurable with values `1` and `-1` only (§2, p. 6). -/
def IsClassifier {d : ℕ} (f : Pt d → ℝ) : Prop :=
  Measurable f ∧ ∀ x, f x = 1 ∨ f x = -1

/-- The strict-radius `r`-boundary `∂f_r` (Definition 1, p. 7; p. 22). -/
def boundarySet {d : ℕ} (r : ℝ) (f : Pt d → ℝ) : Set (Pt d) :=
  {x | ∃ z : Pt d, ‖z‖ < r ∧ f x ≠ f (x + z)}

/-- The `r`-boundary volume `D(∂f_r)` (Definition 1, p. 7). -/
noncomputable def boundaryMass {d : ℕ} (D : Measure (Pt d)) (r : ℝ) (f : Pt d → ℝ) :
    ENNReal :=
  D (boundarySet r f)

/-- `f` is `(r, η)`-robust with respect to `D`: `D(∂f_r) ≤ η` (Definition 1, p. 7). -/
def IsRobust {d : ℕ} (D : Measure (Pt d)) (r η : ℝ) (f : Pt d → ℝ) : Prop :=
  boundaryMass D r f ≤ ENNReal.ofReal η

/-- `U = U(B_1)`, the uniform law on the closed unit ball (the published `uniformBall`). -/
noncomputable def U (d : ℕ) : Measure (Pt d) :=
  RegretBandits.Nonlinear.uniformBall d

/-- The uniform law on the closed unit ball is a probability measure. -/
instance U.isProbabilityMeasure (d : ℕ) : IsProbabilityMeasure (U d) := by
  constructor
  have h0 : volume (Metric.closedBall (0 : Pt d) 1) ≠ 0 :=
    (Metric.measure_closedBall_pos volume (0 : Pt d) one_pos).ne'
  have h1 : volume (Metric.closedBall (0 : Pt d) 1) ≠ ⊤ := measure_closedBall_lt_top.ne
  simp only [U, RegretBandits.Nonlinear.uniformBall, Measure.smul_apply,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 h1

/-- `U(B(x, R))`, the uniform law on the closed ball of radius `R` centred at `x` (§2, p. 6):
the image of `U` under `z ↦ x + R • z`. -/
noncomputable def ballLaw {d : ℕ} (x : Pt d) (R : ℝ) : Measure (Pt d) :=
  (U d).map (fun z => x + R • z)

/-- `U{z : f (x + δ z) ≠ f x}`, the local noise sensitivity as a value in `[0, 1]`. -/
noncomputable def lnsE {d : ℕ} (f : Pt d → ℝ) (δ : ℝ) (x : Pt d) : ENNReal :=
  U d {z | f (x + δ • z) ≠ f x}

/-- The local noise sensitivity `ϕ_{f,δ}(x) = Pr_{Z∼U}[f(x + δZ) ≠ f(x)]` (Definition 11, p. 62). -/
noncomputable def lns {d : ℕ} (f : Pt d → ℝ) (δ : ℝ) (x : Pt d) : ℝ :=
  (lnsE f δ x).toReal

/-- The noise sensitivity `NS_{D,δ}(f) = E_{x∼D} ϕ_{f,δ}(x)` (Definition 12, p. 62). -/
noncomputable def NS {d : ℕ} (D : Measure (Pt d)) (δ : ℝ) (f : Pt d → ℝ) : ENNReal :=
  ∫⁻ x, lnsE f δ x ∂D

/-- The isolation probability `Iso_{D,δ}(f, θ) = Pr_{x∼D}[ϕ_{f,δ}(x) > θ]` (Definition 13, p. 63). -/
noncomputable def Iso {d : ℕ} (D : Measure (Pt d)) (δ : ℝ) (f : Pt d → ℝ) (θ : ℝ) : ENNReal :=
  D {x | θ < lns f δ x}

/-- Total variation `d_TV(P, Q) = sup_A |P(A) − Q(A)|` over measurable `A` (§2, p. 6). -/
noncomputable def tvDist {d : ℕ} (P Q : Measure (Pt d)) : ENNReal :=
  ⨆ (A : Set (Pt d)) (_ : MeasurableSet A), ENNReal.ofReal |(P A).toReal - (Q A).toReal|

/-- `κ_m = π^{m/2} / Γ(m/2 + 1)`, the volume of the unit ball in `ℝ^m` (Lemma 34, p. 64). -/
noncomputable def kappa (m : ℕ) : ℝ :=
  Real.pi ^ ((m : ℝ) / 2) / Real.Gamma ((m : ℝ) / 2 + 1)

end TestableSanitization.Robust


