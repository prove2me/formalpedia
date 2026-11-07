-- Prove2me | Definitions.Def_KramerSaglam_Scalars
-- name    : KramerSaglam_Scalars
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:03:33.920587+00:00
-- url     : https://prove2.me/theorems/469704bf-f173-419f-8333-6c11f4390f92
-- title:
--   Tsallis entropy $\bar H$, the constants $I_p,\bar I_p,J_p,\alpha_p$, the factor $c(\mu)$, the binary divergence $D_2$ and $f$
-- statement:
--   Scalar quantities of the progressive entropy, for real arguments.
--
--   1. **Tsallis entropy of a bit.** For a bit with mean $\mu$, $\bar H = 4\mu(1-\mu)$.
--   2. **Noise constants.** With $H_2$ the binary entropy in bits (`GeneralCK.H`),
--   $$
--   I_p = 1 - H_2(p),\qquad \bar I_p = (1-2p)^2,\qquad J_p = \bar I_p - I_p .
--   $$
--   For $0<p<1$, $\alpha_p = J_p\ln 2/(1-\bar I_p)$.
--   3. **The factor $c(\mu)$.** $c(\mu) = \dfrac{\ln(1/\mu)}{4(1-\mu)^2}$ for $1/2\le\mu<1$, extended to $0<\mu<1/2$ by $c(\mu)=c(1-\mu)$.
--   4. **Binary divergence in bits.**
--   $$
--   D_2(a\,\|\,b) = \frac{1}{\ln 2}\Big(a\ln\frac ab + (1-a)\ln\frac{1-a}{1-b}\Big),
--   $$
--   and $f(t) = D_2\big(\tfrac{1+t}{2}\,\|\,\tfrac12\big)$.
--
--   These are the scalars in terms of which the progressive entropy $Q(C)=\bar I_p H(C)-J_p\bar H(C)$ and all the lemmas of the paper are written.
--
--   **Formalization Note** Outside the page's domains the Lean functions return junk values: $\alpha_p$ at $p\in\{0,1\}$ (denominator $0$), $c(\mu)$ at $\mu\in\{0,1\}$. Every statement using them assumes the page's domain. In $D_2$ the terms with $a\in\{0,1\}$ vanish, which is the continuous extension the paper uses ("All endpoint expressions are understood by continuity", p.13).
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), §2 pp.2–3 (H̄, I_p, Ī_p, J_p, c(µ)), p.6 (α_p), p.7 and App. A p.13 (f), App. B p.14 (D₂)

import Mathlib
import Definitions.Def_GeneralCK_statement

namespace KramerSaglam

/-!
# Scalar quantities of the progressive entropy

D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), §2, pp.2–3, and §3.3, p.7, App. A, p.13, App. B, p.14.
-/

/-- Tsallis entropy of a bit with mean `μ`: `H̄ = 4μ(1 − μ)` (§2, p.2). -/
noncomputable def tsallis (μ : ℝ) : ℝ := 4 * μ * (1 - μ)

/-- `I_p = 1 − H₂(p)` (§2, p.3), with `H₂ = GeneralCK.H` the binary entropy in bits. -/
noncomputable def Ip (p : ℝ) : ℝ := 1 - GeneralCK.H p

/-- `Ī_p = (1 − 2p)²` (§2, p.3). -/
noncomputable def IpBar (p : ℝ) : ℝ := (1 - 2 * p) ^ 2

/-- `J_p = Ī_p − I_p` (§2, p.3). -/
noncomputable def Jp (p : ℝ) : ℝ := IpBar p - Ip p

/-- `α_p = J_p ln 2 / (1 − Ī_p)` (p.6). **Formalization Note.** The page defines it for
`0 < p < 1` only; at `p ∈ {0, 1}` the denominator is `0` and Lean returns `0`. Lemma 3.9 assumes
`0 < Ī_p < 1`, which excludes these values. -/
noncomputable def alphaP (p : ℝ) : ℝ := Jp p * Real.log 2 / (1 - IpBar p)

/-- `c(μ) = ln(1/μ) / (4(1 − μ)²)` on `[1/2, 1)`, and `c(μ) = c(1 − μ)` on `(0, 1/2)` (p.3).
**Formalization Note.** The value at `μ ∈ {0, 1}` is not defined on the page and is junk here;
Lemma 2.2 assumes a nonconstant bit. -/
noncomputable def cMu (μ : ℝ) : ℝ :=
  if 1 / 2 ≤ μ then Real.log (1 / μ) / (4 * (1 - μ) ^ 2)
  else Real.log (1 / (1 - μ)) / (4 * μ ^ 2)

/-- Binary divergence in bits, `D₂(a ∥ b)`. **Formalization Note.** At `a ∈ {0, 1}` the vanishing
term is `0`, which is the continuous extension the paper uses (p.13: "All endpoint expressions are
understood by continuity"). -/
noncomputable def D2 (a b : ℝ) : ℝ :=
  (a * Real.log (a / b) + (1 - a) * Real.log ((1 - a) / (1 - b))) / Real.log 2

/-- `f(t) = D₂((1 + t)/2 ∥ 1/2)` (p.7, p.13). -/
noncomputable def f (t : ℝ) : ℝ := D2 ((1 + t) / 2) (1 / 2)

end KramerSaglam


