-- Prove2me | Definitions.Def_TFIMPhaseDiagram_Classical_entropy
-- name    : TFIMPhaseDiagram_Classical_entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:02:56.353327+00:00
-- url     : https://prove2.me/theorems/64de7ecd-537e-4691-b0e6-4d0c22164b9c
-- title:
--   Sphere covariance, genuine ATE and block Glauber dynamics
-- statement:
--   A sphere spin is an actual unit vector of $\mathbb R^N$, with its Borel measurable structure. Product measures may be continuous. The interaction is $V(x)=\frac12\sum_{i,j}J_{ij}\langle x_i,x_j\rangle$. The conditional distribution of one coordinate is its base law tilted by $V$ with the other coordinates fixed; a Glauber step averages these conditional replacements uniformly over the $n$ sites.
--
--   For a probability measure $\mu$ and nonnegative integrable $f$, write $m=\mathbb E_\mu f$. Entropy is represented without losing infinite values by
--   $$\operatorname{Ent}_\mu(f)=\int m\,\psi(f/m)\,d\mu,\qquad\psi(t)=t\log t-t+1.$$
--   The zero-mean case has entropy zero. Conditional entropy uses $m(x)=\mathbb E[f\mid X_{-i}](x)$ in the same nonnegative extended integral. ATE is the inequality $\operatorname{Ent}_\mu(f)\le C\sum_i\mathbb E\operatorname{Ent}_{\mu(\cdot\mid X_{-i})}(f)$ for every such $f$.
--
--   This definition does not assume mixing, finite entropy, or a finite support. The covariance norm is the supremum of directional variances over Euclidean unit directions.
-- source:
--   Thuy-Duong (June) Vuong, A computational phase diagram for the transverse field Ising model, STOC 2027 submission #739 (October 2026), canonical source.pdf SHA256 02138c3ee0da2e11c9830e41e823dc009b55592cecb60f77602c2a404f2ecfc7, Theorem 13, p.8; its proof, pp.30–31; block dynamics footnote 8, p.8

import Definitions.Def_TFIMPhaseDiagram_Classical_cycles

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped BigOperators
noncomputable section

namespace TFIMPhaseDiagram.Classical
attribute [local instance] Classical.propDecidable

abbrev Sphere (N : ℕ) := {x : EuclideanSpace ℝ (Fin N) // ‖x‖ = 1}
def dot {N : ℕ} (x y : EuclideanSpace ℝ (Fin N)) : ℝ := ∑ k, x k * y k
def sphereCovNorm {N : ℕ} (μ : Measure (Sphere N)) : ℝ :=
  sSup {r | ∃ u : EuclideanSpace ℝ (Fin N), ‖u‖ = 1 ∧
    r = ∫ x, (dot u x.val - ∫ y, dot u y.val ∂μ)^2 ∂μ}
def realOpNorm {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup {r | ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ = 1 ∧
    r = |∑ i, ∑ j, J i j * x i * x j|}
def sphereInteraction {n N : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → Sphere N) : ℝ := (1/2) * ∑ i, ∑ j, J i j * dot (x i).val (x j).val

/-- Conditional single-coordinate law for an exponential tilt of a product base law. -/
def conditionalLaw {n : ℕ} {A : Type} [MeasurableSpace A]
    (μ : Fin n → Measure A) (V : (Fin n → A) → ℝ) (x : Fin n → A) (i : Fin n) : Measure A :=
  tilt (μ i) (fun y => V (Function.update x i y))
def glauberStep {n : ℕ} {A : Type} [MeasurableSpace A]
    (μ : Fin n → Measure A) (V : (Fin n → A) → ℝ) (ρ : Measure (Fin n → A)) : Measure (Fin n → A) :=
  (ENNReal.ofReal (1/(n : ℝ))) • ∑ i, ρ.bind (fun x =>
    (conditionalLaw μ V x i).map (fun y => Function.update x i y))
def glauberRun {n : ℕ} {A : Type} [MeasurableSpace A]
    (μ : Fin n → Measure A) (V : (Fin n → A) → ℝ) (ρ : Measure (Fin n → A)) : ℕ → Measure (Fin n → A)
  | 0 => ρ
  | t+1 => glauberStep μ V (glauberRun μ V ρ t)

/-- x log x - x + 1, including its continuous value at zero. -/
def klScalar (x : ℝ) : ℝ := x * Real.log x - x + 1
/-- Extended nonnegative entropy; infinite entropy is retained, not replaced by a Bochner default. -/
def entropy {A : Type} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ) : ENNReal :=
  let m := ∫ x, f x ∂μ
  ∫⁻ x, ENNReal.ofReal (m * klScalar (f x / m)) ∂μ

def outsideSigma {n : ℕ} {A : Type} [MeasurableSpace A] (i : Fin n) : MeasurableSpace (Fin n → A) :=
  ⨆ j : {j : Fin n // j ≠ i}, MeasurableSpace.comap (fun x : Fin n → A => x j.val) inferInstance

def conditionalEntropy {n : ℕ} {A : Type} [MeasurableSpace A]
    (μ : Measure (Fin n → A)) (f : (Fin n → A) → ℝ) (i : Fin n) : ENNReal :=
  let m := μ[f | outsideSigma i]
  ∫⁻ x, ENNReal.ofReal (m x * klScalar (f x / m x)) ∂μ

def ATE {n : ℕ} {A : Type} [MeasurableSpace A] (μ : Measure (Fin n → A)) (C : ℝ) : Prop :=
  ∀ f : (Fin n → A) → ℝ, Measurable f → Integrable f μ → (∀ x, 0 ≤ f x) →
    entropy μ f ≤ ENNReal.ofReal C * ∑ i, conditionalEntropy μ f i
end TFIMPhaseDiagram.Classical


