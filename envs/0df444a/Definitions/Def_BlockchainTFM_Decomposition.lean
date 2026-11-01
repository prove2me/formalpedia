-- Prove2me | Definitions.Def_BlockchainTFM_Decomposition
-- name    : BlockchainTFM_Decomposition
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T14:02:53.930088+00:00
-- url     : https://prove2.me/theorems/e10e527b-2b56-4671-8c12-b7d31fd22e86
-- title:
--   Dominant association (7), auxiliary-variation decomposition (Definition 7) and admissible variation terms (Definition 8)
-- statement:
--   This module defines the objects of §4.1–4.2 used to build U-BNIC and 1-SCP mechanisms.
--
--   1. **Dominant association** (7). For an allocation rule $\mathbf a$,
--   $$p_i(b_i,\mathbf b_{-i})=\begin{cases}\dfrac{\int_0^{b_i}t\,\frac{\partial a_i(t,\mathbf b_{-i})}{\partial t}\,dt}{a_i(b_i,\mathbf b_{-i})}, & a_i(b_i,\mathbf b_{-i})>0,\\[2mm] 0, & a_i(b_i,\mathbf b_{-i})=0.\end{cases}$$
--   2. **Auxiliary-variation decomposition** (Definition 7). For $\tilde M=(\mathbf a,\tilde{\mathbf p},\tilde r)$ with $\mathbf a$ monotone non-decreasing in each user's own bid, the auxiliary mechanism is $M=(\mathbf a,\mathbf p,0)$ with $\mathbf p$ the dominant association of $\mathbf a$, and the variation term is $T=(\boldsymbol\theta,\tilde r)$; $(M,T)$ is a decomposition of $\tilde M$, written $\tilde M=M+T$, when
--   $$\tilde p_i(b_i,\mathbf b_{-i})=p_i(b_i,\mathbf b_{-i})+\frac{\theta_i(b_i,\mathbf b_{-i})}{a_i(b_i,\mathbf b_{-i})},\qquad \theta_i=0\ \text{whenever}\ a_i=0,$$
--   with $0/0$ read as $0$.
--   3. **Admissibility** (Definition 8). $T=(\boldsymbol\theta,\tilde r)$ is admissible if for every $\mathbf b$
--   $$\tilde r(b_i,\mathbf b_{-i})-\tilde r(0,\mathbf b_{-i})=\theta_i(b_i,\mathbf b_{-i})\quad(10),\qquad \mathbb E_{\mathbf b_{-i}\sim V_{-i}}\bigl[\theta_i(b_i,\mathbf b_{-i})\bigr]=0\quad(11).$$
--
--   Theorem 2 shows that an admissible variation term added to an auxiliary mechanism gives a U-BNIC and 1-SCP mechanism; Lemma 2 shows that the quadratic term (19)–(20) is admissible.
--
--   **Formalization Note** $\partial a_i(t,\mathbf b_{-i})/\partial t$ is the derivative of $s\mapsto a_i(s,\mathbf b_{-i})$ within $[0,1]$ (one-sided at the end points). Monotonicity, the decomposition identity and (10) are required for bid vectors in $[0,1]^n$; in (11) the integrand is required to be integrable.
-- source:
--   Chen, Simchi-Levi, Zhao, Zhou, Bayesian Mechanism Design for Blockchain Transaction Fee Allocation, arXiv:2209.13099v7, §4.1 (7) p.21; §4.2 Definition 7 p.22, Definition 8 (10)–(11) p.22

import Mathlib
import Definitions.Def_BlockchainTFM_Model

open MeasureTheory

namespace BlockchainTFM

/-- **Dominant association** of an allocation rule, arXiv:2209.13099v7, (7), p.21:
`p_i(b_i, b_{-i}) = (∫₀^{b_i} t ∂a_i(t, b_{-i})/∂t dt) / a_i(b_i, b_{-i})` if
`a_i(b_i, b_{-i}) > 0`, and `0` if `a_i(b_i, b_{-i}) = 0`.

**Formalization Note.** `∂a_i(t, b_{-i})/∂t` is the derivative of `s ↦ a_i(s, b_{-i})` within
`[0,1]` (`derivWithin`, one-sided at the end points); the theorems that use this definition
assume that `s ↦ a_i(s, b_{-i})` is differentiable on `[0,1]`. -/
noncomputable def domAssoc {n : ℕ} (a : (Fin n → ℝ) → Fin n → ℝ) (b : Fin n → ℝ) (i : Fin n) :
    ℝ :=
  if 0 < a b i then
    (∫ t in (0 : ℝ)..b i,
        t * derivWithin (fun s => a (Function.update b i s) i) (Set.Icc 0 1) t) / a b i
  else 0

/-- **Auxiliary-variation decomposition** `M̃ = M + T`, arXiv:2209.13099v7, Definition 7, p.22.
Given `M̃ = (a, p̃, r̃)` with `a` monotone non-decreasing, the auxiliary mechanism is
`M = (a, p, 0)` and the variation term is `T = (θ, r̃)`; `(M, T)` is an auxiliary-variation
decomposition of `M̃` when
1. `p` is the dominant association of `a` (here built in: `p = domAssoc a`), and
2. `p̃_i = p_i + θ_i / a_i`, where `θ_i = 0` whenever `a_i = 0` (and `0/0` is read as `0`).

**Formalization Note.** "`a` monotone non-decreasing" is: for every `i` and every
`b_{-i} ∈ [0,1]^{n−1}`, `s ↦ a_i(s, b_{-i})` is monotone on `[0,1]`. The conditions are imposed
for bid vectors in `[0,1]ⁿ`. Lean's `x / 0 = 0` is the paper's convention `0/0 = 0`. -/
def IsAuxVarDecomp {n : ℕ} (Mt : TFM n) (θ : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  (∀ i : Fin n, ∀ b ∈ bidBox n,
      MonotoneOn (fun s => Mt.alloc (Function.update b i s) i) (Set.Icc 0 1)) ∧
  (∀ i : Fin n, ∀ b ∈ bidBox n,
      Mt.pay b i = domAssoc Mt.alloc b i + θ b i / Mt.alloc b i ∧
        (Mt.alloc b i = 0 → θ b i = 0))

/-- **Admissible variation term**, arXiv:2209.13099v7, Definition 8, p.22: `T = (θ, r̃)` is
admissible if for every `b`
* (10) `r̃(b_i, b_{-i}) − r̃(0, b_{-i}) = θ_i(b_i, b_{-i})`, and
* (11) `E_{b_{-i}∼V_{-i}}[θ_i(b_i, b_{-i})] = 0`.

**Formalization Note.** Bid vectors range over `[0,1]ⁿ`. In (11) the expectation is over the
other users' truthful bids, i.i.d. `V₀` (`Measure.pi` with coordinate `i` overwritten by `b_i`),
and the integrand is required to be integrable, so that the expectation exists. -/
def IsAdmissible {n : ℕ} (V₀ : Measure ℝ) (θ : (Fin n → ℝ) → Fin n → ℝ)
    (rt : (Fin n → ℝ) → ℝ) : Prop :=
  (∀ i : Fin n, ∀ b ∈ bidBox n, rt b - rt (Function.update b i 0) = θ b i) ∧
  (∀ i : Fin n, ∀ x ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun b => θ (Function.update b i x) i) (Measure.pi fun _ : Fin n => V₀) ∧
        ∫ b, θ (Function.update b i x) i ∂(Measure.pi fun _ : Fin n => V₀) = 0)

end BlockchainTFM


