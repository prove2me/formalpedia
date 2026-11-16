-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Supplement_Geometry
-- name    : ZLIPPadding_Padding_Supplement_Geometry
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:14:35.828295+00:00
-- url     : https://prove2.me/theorems/748af5e9-05fa-424d-9c0c-ac377c2295b1
-- title:
--   Shells, finite orbit moments, and spherical four-designs
-- statement:
--   For a dimension $n$, integer vectors have coordinates indexed by $\{0,\ldots,n-1\}$, and real ambient vectors carry the Euclidean norm. Define the standard integer shell $S_m$, its flat subset $F_m$, and the distinct signed-permutation orbit of a profile $a$. In particular,
--
--   $$S_m=\{z\in\mathbb Z^n:\textstyle\sum_i z_i^2=m\},\qquad F_m=S_m\cap\{0,\pm1\}^n.$$
--
--   Finite expectations use actual uniform counting averages or the point masses of a probability mass function. Define the signed coefficients $\alpha_a,\beta_a,\kappa_a$, normalized contrast $\eta_a$, the hidden-axis quartic $P_O$, Euclidean matrix operator norm, and complete coordinate-square multisets. A spherical four-design matches every polynomial of total degree at most four against normalized surface law. That law is constructed by radial projection of uniform volume on the unit ball; polynomial integrability is included explicitly. These interfaces impose no rationality restriction on geometric identities.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 7–14, 24, 38–39 (PDF pp. 8–15, 25, 39–40), Definitions 2.1, 2.3, Sections 2.4, 3.1, 6.1 and Appendix A.2

import Definitions.Def_ZLIPPadding_Padding_Laws

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

abbrev EVec (n : ℕ) := EuclideanSpace ℝ (Fin n)
def liftZ {n : ℕ} (z : ZVec n) : EVec n := WithLp.toLp 2 (fun i => (z i : ℝ))
def rotate {n : ℕ} (O : RMat n) (x : EVec n) : EVec n :=
  WithLp.toLp 2 (O.mulVec (WithLp.ofLp x))
def iznorm {n : ℕ} (z : ZVec n) : ℤ := ∑ i, z i ^ 2
def shell (n m : ℕ) : Finset (ZVec n) :=
  ((Finset.univ : Finset (Fin n → Fin (2*m+1))).image
    (fun v i => (v i : ℤ) - (m : ℤ))).filter (fun z => iznorm z = m)
def flat (n m : ℕ) : Finset (ZVec n) :=
  (shell n m).filter (fun z => ∀ i, z i = 0 ∨ z i = 1 ∨ z i = -1)
def orbit {n : ℕ} (a : ZVec n) : Finset (ZVec n) :=
  ((Finset.univ : Finset (Equiv.Perm (Fin n) × (Fin n → Bool))).image
    (fun ps => signedAction ps.1 ps.2 a))
def average {α : Type} (s : Finset α) (f : α → ℝ) : ℝ :=
  (∑ x ∈ s, f x) / s.card
def UniformOn {α : Type} (μ : PMF α) (s : Finset α) : Prop :=
  s.Nonempty ∧ ∀ x, μ x = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0
def ShellLaw {n : ℕ} (m : ℕ) (μ : PMF (ZVec n)) : Prop :=
  ∀ z, μ z ≠ 0 → z ∈ shell n m
def expectShell {n : ℕ} (m : ℕ) (μ : PMF (ZVec n)) (f : ZVec n → ℝ) : ℝ :=
  ∑ z ∈ shell n m, (μ z).toReal * f z
def normSq {n : ℕ} (a : ZVec n) : ℝ := ∑ i, (a i : ℝ)^2
def fourthSum {n : ℕ} (a : ZVec n) : ℝ := ∑ i, (a i : ℝ)^4
def orbitAlpha {n : ℕ} (a : ZVec n) : ℝ := fourthSum a / n
def orbitBeta {n : ℕ} (a : ZVec n) : ℝ :=
  (normSq a ^ 2 - fourthSum a) / ((n : ℝ)*(n-1))
def orbitKappa {n : ℕ} (a : ZVec n) : ℝ :=
  (((n : ℝ)+2)*fourthSum a - 3*normSq a^2) / ((n : ℝ)*(n-1))
def orbitEta {n : ℕ} (a : ZVec n) : ℝ := |orbitKappa a| / normSq a ^ 2
def axisQuartic {n : ℕ} (O : RMat n) (x : EVec n) : ℝ :=
  ∑ i, (∑ j, O j i * x j)^4
def outer {n : ℕ} (x : EVec n) : RMat n := fun i j => x i*x j
def opNorm {n : ℕ} (A : RMat n) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖
def profile {n : ℕ} (z : ZVec n) : Multiset ℤ := ↑(List.ofFn (fun i => z i^2))

/-- Normalized radial projection of uniform volume on the unit ball is uniform surface law.
The origin has measure zero in the dimensions used below. -/
def sphereLaw (n : ℕ) : Measure (EVec n) :=
  let v : Measure (EVec n) := volume.restrict (Metric.ball 0 1)
  Measure.map (fun x : EVec n => ‖x‖⁻¹ • x) ((v Set.univ)⁻¹ • v)

/-- Tests every polynomial of total degree at most four, not only directional quartics. -/
def SphericalFourDesign {n : ℕ} (O : RMat n) (a : ZVec n) : Prop :=
  (orbit a).Nonempty ∧
  ∀ p : MvPolynomial (Fin n) ℝ, p.totalDegree ≤ 4 →
    Integrable (fun x => MvPolynomial.eval (fun i => x i) p) (sphereLaw n) ∧
    average (orbit a) (fun z => MvPolynomial.eval
      (fun i => (Real.sqrt (normSq a))⁻¹ * (rotate O (liftZ z)) i) p) =
    ∫ x, MvPolynomial.eval (fun i => x i) p ∂sphereLaw n

def momentAlpha {n : ℕ} (m : ℕ) (μ : PMF (ZVec n)) : ℝ :=
  expectShell m μ fourthSum / n
def momentBeta {n : ℕ} (m : ℕ) (μ : PMF (ZVec n)) : ℝ :=
  expectShell m μ (fun z => ∑ i, ∑ j, if i = j then 0 else
    (z i : ℝ)^2*(z j : ℝ)^2) / ((n : ℝ)*(n-1))
def momentKappa {n : ℕ} (m : ℕ) (μ : PMF (ZVec n)) : ℝ :=
  momentAlpha m μ - 3*momentBeta m μ
def shellAlpha (n m : ℕ) : ℝ := average (shell n m) fourthSum / n
def shellBeta (n m : ℕ) : ℝ :=
  average (shell n m) (fun z => ∑ i, ∑ j, if i = j then 0 else
    (z i : ℝ)^2*(z j : ℝ)^2) / ((n : ℝ)*(n-1))
def shellKappa (n m : ℕ) : ℝ := shellAlpha n m - 3*shellBeta n m

end
end ZLIPPadding.Padding.Supplement


