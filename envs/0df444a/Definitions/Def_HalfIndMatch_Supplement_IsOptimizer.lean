-- Prove2me | Definitions.Def_HalfIndMatch_Supplement_IsOptimizer
-- name    : HalfIndMatch_Supplement_IsOptimizer
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:03:15.111367+00:00
-- url     : https://prove2.me/theorems/0efa7b9d-232f-4e58-a874-fe049d0bb958
-- title:
--   Definition 2.5 — $(k,\delta,\gamma,\eta)$-optimizer for induced matching in $G(n,d/n)$
-- statement:
--   Fix $n$ and a real $d$, and let $G\sim G(n,d/n)$ be the Erdős–Rényi graph in which each of the $m=\binom n2$ pairs is an edge independently with probability $d/n$. A **random polynomial** $f(G;\xi)=(f_e(G;\xi))_{e\in\mathcal E_n}$ of degree at most $D$ has coefficients depending on a random seed $\xi$ sampled independently of $G$, and has degree at most $D$ for every fixed $\xi$; fixing the seed gives a **deterministic** polynomial. Write $\|f(G)\|^2=\sum_{e\in\mathcal E_n}f_e(G)^2$ and $\Phi=(n\log d)/d$.
--
--   Let $k>0$, $\delta\in[0,1]$, $\gamma\ge1$ and $\eta>0$. A random polynomial $f$ is a **$(k,\delta,\gamma,\eta)$-optimizer** for the induced matching problem in $G(n,d/n)$ if, jointly over $G$ and the independent seed,
--
--   $$\mathbb E_{G,f}\big[\|f(G)\|^2\big]\le\gamma k\qquad\text{and}\qquad\mathbb P_{G,f}\big[|\mathcal M^\eta_f(G)|\ge k\big]\ge1-\delta,$$
--
--   with $\mathcal M^\eta_f(G)$ the rounding of Definition 2.4. A deterministic polynomial is an optimizer when the expectation and probability over $G$ alone satisfy the same two bounds.
--
--   The first condition bounds how much the polynomial's output can move when the graph changes; the second says the rounding finds at least $k$ edges with probability $1-\delta$. Theorem 2.6 shows that $k=(\frac12-\varepsilon)\Phi$ is achievable at constant degree and Theorem 2.7 that $k=(\frac12+\varepsilon)\Phi$ is not.
--
--   **Formalization Note** A random polynomial is a seed space `(Ω, μ)` and `f : Ω → Edges n → MvPolynomial (Edges n) ℝ`. The law of $G(n,d/n)$ is the published `LPCommunity.SBMRecovery.edgeWeight G (fun _ _ => d/n)`. The expectation is $\sum_G\mathbb P[G]\int^-\|f_\xi(G)\|^2\,d\mu$ computed in $[0,\infty]$, so a non-integrable seed gives $+\infty$ rather than the junk value $0$ of a Bochner integral; the probability is $\sum_G\mathbb P[G]\,\mu\{\xi:|\mathcal M^\eta_{f_\xi}(G)|\ge k\}$. The deterministic version `IsDetOptimizer` is the case of a one-point seed space with the Dirac measure. The parameter ranges $k>0$, $\delta\in[0,1]$, $\gamma\ge1$, $\eta>0$, the degree bound and the measurability of the seed are stated in the theorems that use the predicate, not inside it. The module also declares `Phi` ($\Phi$) and `sqNorm` ($\|f(G)\|^2$).
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), §2.3, p.10 (PDF p.12): random and deterministic polynomials; Definition 2.5 and the definition of Φ, p.11 (PDF p.13)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_HalfIndMatch_Supplement_roundM

open scoped Classical
open MeasureTheory LPCommunity.SBMRecovery

namespace HalfIndMatch.Supplement

/-- The sparse-regime threshold `Φ = (n log d)/d` (natural logarithm).

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), §2.3,
p.11 (PDF p.13). -/
noncomputable def Phi (n : ℕ) (d : ℝ) : ℝ := (n : ℝ) * Real.log d / d

/-- The squared Euclidean norm `‖f(G)‖² = Σ_{e ∈ 𝓔ₙ} f_e(G)²` (Definition 2.5, p.11, PDF p.13). -/
noncomputable def sqNorm {n : ℕ} (f : Edges n → MvPolynomial (Edges n) ℝ)
    (G : SimpleGraph (Fin n)) : ℝ :=
  ∑ e, (evalPoly f G e) ^ 2

/-- **Definition 2.5** (`(k, δ, γ, η)`-optimizer for the induced matching problem in `G(n, d/n)`).
A random polynomial is a seed space `(Ω, μ)` and a map `f : Ω → (𝓔ₙ → MvPolynomial 𝓔ₙ ℝ)`; the
seed `ξ ∼ μ` is independent of `G ∼ G(n, d/n)`. It is a `(k, δ, γ, η)`-optimizer if
* `E_{G,f}[‖f(G)‖²] ≤ γ k`, and
* `P_{G,f}[|M^η_f(G)| ≥ k] ≥ 1 − δ`,
jointly over `G` and the seed.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…),
Definition 2.5, p.11 (PDF p.13); random polynomials, §2.3, p.10 (PDF p.12).

**Formalization Note** The law of `G(n, d/n)` is the published Erdős–Rényi weight
`LPCommunity.SBMRecovery.edgeWeight G (fun _ _ => d/n)` (its clamp is the identity for
`0 ≤ d ≤ n`). The joint expectation is `Σ_G P[G] · ∫⁻ ξ, ‖f_ξ(G)‖² dμ`, computed in `ℝ≥0∞` so that a
non-integrable seed gives `+∞` rather than a junk `0`; the joint probability is
`Σ_G P[G] · μ{ξ : |M^η_{f_ξ}(G)| ≥ k}`. Measurability of the seed dependence is assumed where the
definition is used. The parameter ranges `k > 0, δ ∈ [0, 1], γ ≥ 1, η > 0` of the definition are
hypotheses (or proved conclusions) of the theorems that use it, not fields of this predicate.
The degree bound is likewise stated separately. -/
def IsOptimizer (n : ℕ) (d k δ γ η : ℝ) (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω)
    (f : Ω → Edges n → MvPolynomial (Edges n) ℝ) : Prop :=
  (∑ G : SimpleGraph (Fin n), ENNReal.ofReal (edgeWeight G (fun _ _ => d / n)) *
      ∫⁻ ξ, ENNReal.ofReal (sqNorm (f ξ) G) ∂μ) ≤ ENNReal.ofReal (γ * k) ∧
  1 - δ ≤ ∑ G : SimpleGraph (Fin n), edgeWeight G (fun _ _ => d / n) *
      μ.real {ξ : Ω | k ≤ ((roundM η (f ξ) G).card : ℝ)}

/-- A **deterministic** polynomial `f` is a `(k, δ, γ, η)`-optimizer when the random polynomial
with a constant seed is one (§2.3, p.10, PDF p.12: "Fixing the seed ξ gives a deterministic
polynomial"); then the expectation and probability are over `G` only. -/
def IsDetOptimizer (n : ℕ) (d k δ γ η : ℝ) (f : Edges n → MvPolynomial (Edges n) ℝ) : Prop :=
  IsOptimizer n d k δ γ η Unit (Measure.dirac ()) (fun _ => f)

end HalfIndMatch.Supplement


