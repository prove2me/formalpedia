-- Prove2me | Definitions.Def_GaussPolyReg_Approx_Chaos
-- name    : GaussPolyReg_Approx_Chaos
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:38:37.900171+00:00
-- url     : https://prove2.me/theorems/b4d7c536-5579-40c3-8457-af9ac496bfd0
-- title:
--   Gaussian chaos, graded Hermite spans, projections and approximation error
-- statement:
--   Let $\gamma_I=N(0,1)^{\otimes I}$ on $\mathbb R^I$. For finitely supported $\alpha:I\to\mathbb N$, put $\mathrm{He}_\alpha(x)=\prod_i\mathrm{He}_{\alpha_i}(x_i)$, $\alpha!=\prod_i\alpha_i!$, and $\psi_\alpha=\mathrm{He}_\alpha/\sqrt{\alpha!}$. For grades $g_i\ge1$, the graded chaos of degree $d$ is
--
--   $$H_d^{\rm gr}=\overline{\operatorname{span}}\{\mathrm{He}_\alpha:\sum_i g_i\alpha_i=d\}\subset L^2(\gamma_I).$$
--
--   The original variables have $I=\mathbb N$ and grade one. This module defines $H_d$, $H_{\le d}$, the first-$n$-coordinate subspaces, the orthogonal projection $\Pi_d$, and the top product $p\diamond q=\Pi_{r+s}(pq)$. Finite graded polynomials are algebraic Hermite spans. The approximation error is the lower integral of $|p-q(Z)|^2$; it cannot vanish through a nonintegrable Bochner integral. Wasserstein distance reuses the published coupling definition on Euclidean space.
--
--   These are shared interfaces for every statement in the mission. L² elements are almost-everywhere classes; generators are identified by equality almost everywhere. The auxiliary conversion to L² returns zero outside L² and is used only for products whose L² membership follows from their finite chaos degrees.
-- source:
--   Chris Jones, Regularity lemma for Gaussian polynomials, STOC 2027 submission #1637 (October 2026), §2, p.3, (2.1); §3.2–3.3, pp.6–7; Theorem 1.1, pp.1–2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1637.pdf

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_wassersteinDistance

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace GaussPolyReg.Approx

/-- Standard Gaussian coordinates, §2, p.3; arbitrary index sets are allowed. -/
def gaussianProduct (I : Type*) : Measure (I → ℝ) :=
  Measure.infinitePi (fun _ : I => gaussianReal 0 1)

instance gaussianProduct_isProbabilityMeasure (I : Type*) :
    IsProbabilityMeasure (gaussianProduct I) := by
  unfold gaussianProduct
  infer_instance

abbrev GaussianL2 (I : Type*) := Lp ℝ 2 (gaussianProduct I)
abbrev Original := GaussianL2 ℕ
abbrev Sample := ℕ → ℝ

/-- Probabilists' Hermite polynomials, §2, p.3. -/
def hermite (a : ℕ) (x : ℝ) : ℝ := Polynomial.aeval x (Polynomial.hermite a)
def multiDegree {I : Type*} (α : I →₀ ℕ) : ℕ := α.sum fun _ a => a
def multiFactorial {I : Type*} (α : I →₀ ℕ) : ℕ := α.prod fun _ a => a.factorial
def grade {I : Type*} (g : I → ℕ) (α : I →₀ ℕ) : ℕ := α.sum fun i a => g i * a

def heMulti {I : Type*} (α : I →₀ ℕ) (x : I → ℝ) : ℝ :=
  α.prod fun i a => hermite a (x i)

def psiMulti {I : Type*} (α : I →₀ ℕ) (x : I → ℝ) : ℝ :=
  heMulti α x / Real.sqrt (multiFactorial α : ℝ)

/-- Closed Hermite span in L². The a.e. relation avoids assuming Hermite L² integrability
in a definition: it identifies precisely its L² representatives. §2, p.3, (2.1). -/
def gradedChaos {I : Type*} (g : I → ℕ) (d : ℕ) : Submodule ℝ (GaussianL2 I) :=
  (Submodule.span ℝ {p : GaussianL2 I | ∃ α : I →₀ ℕ, grade g α = d ∧
    (p : (I → ℝ) → ℝ) =ᵐ[gaussianProduct I] heMulti α}).topologicalClosure

def chaos (d : ℕ) : Submodule ℝ Original := gradedChaos (fun _ => 1) d

def chaosLE (d : ℕ) : Submodule ℝ Original :=
  (Submodule.span ℝ {p : Original | ∃ α : ℕ →₀ ℕ, multiDegree α ≤ d ∧
    (p : Sample → ℝ) =ᵐ[gaussianProduct ℕ] heMulti α}).topologicalClosure

/-- First n coordinates are 0,…,n−1 (the paper's X₁,…,Xₙ). -/
def finiteChaos (n d : ℕ) : Submodule ℝ Original :=
  Submodule.span ℝ {p : Original | ∃ α : ℕ →₀ ℕ, multiDegree α = d ∧
    (∀ i ∈ α.support, i < n) ∧ (p : Sample → ℝ) =ᵐ[gaussianProduct ℕ] heMulti α}

def finiteChaosLE (n d : ℕ) : Submodule ℝ Original :=
  Submodule.span ℝ {p : Original | ∃ α : ℕ →₀ ℕ, multiDegree α ≤ d ∧
    (∀ i ∈ α.support, i < n) ∧ (p : Sample → ℝ) =ᵐ[gaussianProduct ℕ] heMulti α}

/-- Π_d, §2. The closure has the standard complete-space instance. -/
def chaosProjection (d : ℕ) (p : Original) : Original :=
  letI : (chaos d).HasOrthogonalProjection := by
    unfold chaos gradedChaos
    infer_instance
  ((chaos d).orthogonalProjectionOnto p : Original)

/-- Only used on products of fixed-degree chaos elements, which are L² by A.3.
On functions outside L² the extension is zero; no approximation error uses this extension. -/
def toOriginal (f : Sample → ℝ) : Original := by
  classical
  exact if h : MemLp f 2 (gaussianProduct ℕ) then h.toLp f else 0

def topProduct (r s : ℕ) (p q : Original) : Original :=
  chaosProjection (r + s) (toOriginal (fun x => p x * q x))

def iteratedTop {k : ℕ} (d : Fin k → ℕ) (p : Fin k → Original) : Original :=
  chaosProjection (∑ a, d a) (toOriginal (fun x => ∏ a, p a x))

/-- Finite-variable graded polynomial space, (2.1). -/
def hePolynomial {m : ℕ} (α : Fin m →₀ ℕ) : MvPolynomial (Fin m) ℝ :=
  α.prod fun i a => Polynomial.aeval (MvPolynomial.X i) (Polynomial.hermite a)

def gradedPolynomials {m : ℕ} (g : Fin m → ℕ) (d : ℕ) :
    Submodule ℝ (MvPolynomial (Fin m) ℝ) :=
  Submodule.span ℝ {q | ∃ α, grade g α = d ∧ q = hePolynomial α}

def evaluate {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (Z : Fin m → Original)
    (x : Sample) : ℝ := MvPolynomial.eval (fun a => Z a x) q

/-- Squared L² error as a lower integral, never the default Bochner value. -/
def squaredError {m : ℕ} (p : Original) (q : MvPolynomial (Fin m) ℝ)
    (Z : Fin m → Original) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal ((p x - evaluate q Z x) ^ 2) ∂gaussianProduct ℕ

abbrev Vec (k : ℕ) := EuclideanSpace ℝ (Fin k)
def vectorOf {Ω : Type*} {k : ℕ} (p : Fin k → Ω → ℝ) (x : Ω) : Vec k :=
  WithLp.toLp 2 (fun a => p a x)
def vectorLaw {I : Type*} {k : ℕ} (p : Fin k → GaussianL2 I) : Measure (Vec k) :=
  (gaussianProduct I).map (vectorOf (fun a x => p a x))
def wasserstein {k : ℕ} (r : ℝ) (μ ν : Measure (Vec k)) : ℝ≥0∞ :=
  WassersteinDRO.Duality.wassersteinDistance r μ ν

def pairing (p q : Original) : ℝ := ∫ x, p x * q x ∂gaussianProduct ℕ

end GaussPolyReg.Approx


