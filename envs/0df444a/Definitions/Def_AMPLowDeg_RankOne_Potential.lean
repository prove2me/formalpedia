-- Prove2me | Definitions.Def_AMPLowDeg_RankOne_Potential
-- name    : AMPLowDeg_RankOne_Potential
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:59:38.660682+00:00
-- url     : https://prove2.me/theorems/20d33fa1-10a8-4986-8caa-eafdfa97b119
-- title:
--   Scalar channel: mutual information $I_\pi(s)$, potential $\Psi$ (1.2), $q_{\mathrm{AMP}}$ (1.3), posterior (4.1) and $F$
-- statement:
--   Let $\Theta\sim\pi$ and $Z\sim\mathcal N(0,1)$ be independent.
--
--   1. **Mutual information.** $I_\pi(s)=I(\Theta;\sqrt s\,\Theta+Z)$ for $s\ge0$, in nats: the Kullback–Leibler divergence (natural logarithm) of the joint law of $(\Theta,\sqrt s\Theta+Z)$ from the product of its two marginals.
--   2. **Potential.** $\Psi(q)=\dfrac{q^2}{4}-\dfrac{m_2q}{2}+I_\pi(q)$ for $q\ge0$ (this is $\Psi(q;0)$ of (1.2)).
--   3. **Bayes-AMP value.**
--   $$
--   q_{\mathrm{AMP}}=\inf\{q\ge0:\Psi'(q)=0,\ \Psi''(q)\ge0\},
--   $$
--   with the derivatives of $\Psi$, a function on $[0,\infty)$, taken within $[0,\infty)$ (one-sided at $q=0$).
--   4. **Scalar posterior.** For $s>0$, $h\in\mathbb R$: $Z_s(h)=\int e^{hx-sx^2/2}\,\pi(dx)$, $\pi_{s,h}(dx)=e^{hx-sx^2/2}\pi(dx)/Z_s(h)$, and the posterior mean $\eta_s(h)=\int x\,\pi_{s,h}(dx)$; derivatives of $\eta_s$ are in $h$.
--   5. **The map $F$.** $F(s)=\mathbb E[\eta_s(H)^2]$ with $H=s\Theta+\sqrt s Z$ for $s>0$, and $F(0)=(\mathbb E\Theta)^2$.
--
--   The AMP error level of the paper is $m_2-q_{\mathrm{AMP}}$, and the auxiliary channel of the proof is run at strength $s=q_{\mathrm{AMP}}$.
--
--   **Formalization Note** The condition defining $q_{\mathrm{AMP}}$ requires that $\Psi$ have derivative $0$ within $[0,\infty)$ at $q$ and that the function $q\mapsto\Psi'(q)$ (Mathlib's `derivWithin` on $[0,\infty)$) have a derivative $c\ge0$ within $[0,\infty)$ at $q$; existence of the derivatives is what $\Psi'(q)=0$, $\Psi''(q)\ge0$ presuppose. The infimum is a real `sInf`; that the set is nonempty, so that the infimum is attained, is Lemma A.7, not part of the definition. $I_\pi(s)$ is the real part (`toReal`) of the divergence, which is finite for priors with finite second moment.
-- source:
--   Zhangsong Li, Almost Sharp Equivalence between Approximate Message Passing and Low-Degree Polynomials, STOC 2027 submission #180 (October 2026), source.pdf SHA-256 9eb368625386c835173a663de76761a4514eda91fb4398b726b5affa824b5a0c, p. 3, (1.2) and (1.3); p. 11, (4.1) and η_s; p. 24, F(s) in §A.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/180.pdf

import Mathlib
import Definitions.Def_AMPLowDeg_RankOne_Model

open MeasureTheory ProbabilityTheory

namespace AMPLowDeg.RankOne

/-- The joint law of `(Θ, √s Θ + Z)` for independent `Θ ∼ π` and `Z ∼ 𝒩(0, 1)` (p. 3). -/
noncomputable def chanJoint (π : Measure ℝ) (s : ℝ) : Measure (ℝ × ℝ) :=
  (π.prod (gaussianReal 0 1)).map (fun p => (p.1, Real.sqrt s * p.1 + p.2))

/-- The scalar-channel mutual information `I_π(s) = I(Θ; √s Θ + Z)` of (1.2), in nats: the
Kullback–Leibler divergence (natural logarithm) of the joint law of `(Θ, √s Θ + Z)` from the
product of its marginals `π ⊗ Law(√s Θ + Z)`. Used for `s ≥ 0`. -/
noncomputable def MI (π : Measure ℝ) (s : ℝ) : ℝ :=
  (InformationTheory.klDiv (chanJoint π s) (π.prod ((chanJoint π s).map Prod.snd))).toReal

/-- The scalar potential `Ψ(q) = Ψ(q; 0) = q²/4 − m₂ q / 2 + I_π(q)` of (1.2), for `q ≥ 0`. -/
noncomputable def Psi (π : Measure ℝ) (q : ℝ) : ℝ :=
  q ^ 2 / 4 - m2 π * q / 2 + MI π q

/-- The set `{q ≥ 0 : Ψ′(q) = 0, Ψ″(q) ≥ 0}` of (1.3). `Ψ` lives on `[0, ∞)`, so both derivatives
are taken within `[0, ∞)` (one-sided at `q = 0`), and their existence is part of the condition. -/
def qAMPSet (π : Measure ℝ) : Set ℝ :=
  {q | 0 ≤ q ∧ HasDerivWithinAt (Psi π) 0 (Set.Ici 0) q ∧
    ∃ c : ℝ, 0 ≤ c ∧ HasDerivWithinAt (derivWithin (Psi π) (Set.Ici 0)) c (Set.Ici 0) q}

/-- `q_AMP = inf{q ≥ 0 : Ψ′(q) = 0, Ψ″(q) ≥ 0}` (1.3), the Bayes-AMP fixed point. -/
noncomputable def qAMP (π : Measure ℝ) : ℝ := sInf (qAMPSet π)

/-- The partition function `Z_s(h) = ∫ e^{hx − s x²/2} π(dx)` of (4.1). -/
noncomputable def Zpart (π : Measure ℝ) (s h : ℝ) : ℝ :=
  ∫ x, Real.exp (h * x - s * x ^ 2 / 2) ∂π

/-- The scalar posterior `π_{s,h}(dx) = e^{hx − s x²/2} π(dx) / Z_s(h)` of (4.1). -/
noncomputable def post (π : Measure ℝ) (s h : ℝ) : Measure ℝ :=
  π.withDensity (fun x => ENNReal.ofReal (Real.exp (h * x - s * x ^ 2 / 2) / Zpart π s h))

/-- The posterior mean `η_s(h) = ∫ x π_{s,h}(dx)` (p. 11). Derivatives `η^{(k)}` are taken in the
field variable `h` with `s` fixed. -/
noncomputable def eta (π : Measure ℝ) (s h : ℝ) : ℝ := ∫ x, x ∂(post π s h)

/-- `F(s) = E[η_s(H)²]` with `H = sΘ + √s Z`, `Θ ∼ π`, `Z ∼ 𝒩(0, 1)` independent, for `s > 0`, and
`F(0) = (E[Θ])²` (§A.4, p. 24). Used for `s ≥ 0`. -/
noncomputable def scalarF (π : Measure ℝ) (s : ℝ) : ℝ :=
  if s = 0 then (mean π) ^ 2
  else ∫ p, (eta π s (s * p.1 + Real.sqrt s * p.2)) ^ 2 ∂(π.prod (gaussianReal 0 1))

end AMPLowDeg.RankOne


