-- Prove2me | Definitions.Def_RandomIsetThreshold_Degree_RandomOutput
-- name    : RandomIsetThreshold_Degree_RandomOutput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:05:48.075891+00:00
-- url     : https://prove2.me/theorems/a2c788bd-5072-4d68-b557-9de5a5e71239
-- title:
--   Random polynomial outputs, norm, influence, and noise sensitivity
-- statement:
--   Let $R$ have any probability law $\mu$ on a measurable space $\Omega$, independently of $H_{n,p}$, and let $f(G,R)\in\mathbb R^n$ be measurable in $R$ for each graph $G$. Degree at most a real $D$ means that almost every seed gives a cube function whose every coordinate has a polynomial representative of total degree at most $D$. Different syntactic representatives of the same cube function do not change this condition. Set
--
--   $$N(f)=\mathbb E\|f(H,R)\|_2^2,\quad \mathcal I(f)=\frac12\sum_{e\in\mathcal E}\mathbb E\|f(H,R)-f(H^{(e)},R)\|_2^2,$$
--   $$\operatorname{NS}_\tau(f)=\mathbb E\|f(H,R)-f(H^\tau,R)\|_2^2.$$
--
--   Here $H^{(e)}$ independently replaces just bit $e$ by a Bernoulli-$p$ draw; $H^\tau$ uses independent Bernoulli-$\tau$ masks to select independently replaced bits. Both evaluations share $R$. Success probability uses the independent product law of graph and seed. Deterministic versions use a singleton seed or the graph law directly.
--
--   These quantities describe functions by their outputs, with no computational restriction beyond the separately stated degree bound. **Formalization Note** Every nonnegative expectation takes values in $[0,\infty]$, preserving nonintegrable cases; no square-integrability restriction is part of this interface.
-- source:
--   Matthew Cho, Lutz Warnke, STOC 2027 submission #260 (October 2026), p. 2–4, 22–24, §§1.1–1.2, equations (4), (7), Appendix A.1

import Mathlib
import Definitions.Def_RandomIsetThreshold_Degree_Hypergraph

namespace RandomIsetThreshold.Degree

noncomputable section
open MeasureTheory
open scoped ENNReal BigOperators

variable {n r : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The only regularity convention: measurable dependence on the independent seed. -/
def SeedMeasurable (f : Cube n r → Ω → Vector n) : Prop :=
  ∀ G, Measurable (f G)

/-- Degree is a property of the cube function, not of a chosen representative. -/
def DegreeLE (f : Cube n r → Vector n) (D : ℝ) : Prop :=
  ∀ v : Fin n, ∃ q : MvPolynomial (Edge n r) ℝ,
    (q.totalDegree : ℝ) ≤ D ∧
    ∀ G, MvPolynomial.eval (fun e => if G e then (1 : ℝ) else 0) q = f G v

def RandomDegreeLE (μ : Measure Ω) (f : Cube n r → Ω → Vector n) (D : ℝ) : Prop :=
  ∀ᵐ s ∂μ, DegreeLE (fun G => f G s) D

/-- Product sampling makes the graph independent of the seed, for arbitrary seed spaces. -/
def successProbability (p : unitInterval) (μ : Measure Ω)
    (f : Cube n r → Ω → Vector n) (ε γ : ℝ) : ℝ :=
  ((graphLaw n r p).prod μ).real {z | Success ε γ p z.1 (f z.1 z.2)}

def normMoment (p : unitInterval) (μ : Measure Ω)
    (f : Cube n r → Ω → Vector n) : ℝ≥0∞ :=
  ∫⁻ z, ENNReal.ofReal (sqNorm (f z.1 z.2)) ∂((graphLaw n r p).prod μ)

def detSuccessProbability (p : unitInterval) (f : Cube n r → Vector n) (ε γ : ℝ) : ℝ :=
  (graphLaw n r p).real {G | Success ε γ p G (f G)}

def detNormMoment (p : unitInterval) (f : Cube n r → Vector n) : ℝ≥0∞ :=
  ∫⁻ G, ENNReal.ofReal (sqNorm (f G)) ∂(graphLaw n r p)

/-- Masked replacement resamples selected bits; it does not flip them. -/
def resample (G H mask : Cube n r) : Cube n r :=
  fun e => if mask e then H e else G e

def influence (p : unitInterval) (μ : Measure Ω)
    (f : Cube n r → Ω → Vector n) : ℝ≥0∞ :=
  (1 / 2 : ℝ≥0∞) * ∑ e : Edge n r,
    ∫⁻ G, (∫⁻ H, (∫⁻ s,
      ENNReal.ofReal (sqDist (f G s) (f (Function.update G e (H e)) s)) ∂μ)
      ∂(graphLaw n r p)) ∂(graphLaw n r p)

def noiseSensitivity (p τ : unitInterval) (μ : Measure Ω)
    (f : Cube n r → Ω → Vector n) : ℝ≥0∞ :=
  ∫⁻ G, (∫⁻ H, (∫⁻ mask, (∫⁻ s,
      ENNReal.ofReal (sqDist (f G s) (f (resample G H mask) s)) ∂μ)
      ∂(graphLaw n r τ)) ∂(graphLaw n r p)) ∂(graphLaw n r p)

def detInfluence (p : unitInterval) (f : Cube n r → Vector n) : ℝ≥0∞ :=
  influence p (Measure.dirac ()) (fun G (_ : Unit) => f G)

end
end RandomIsetThreshold.Degree


