-- Prove2me | Definitions.Def_CubicPermFPRAS_nuAux
-- name    : CubicPermFPRAS_nuAux
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:56.488111+00:00
-- url     : https://prove2.me/theorems/fa30c2ad-f187-45bc-b799-ac89583645eb
-- title:
--   The auxiliary distributions $\nu_a$, the matching polynomial $F$ and the assignment Glauber dynamics $L_a$
-- statement:
--   For a matrix $B$, $J\ge0$ and an activity $a>0$:
--
--   1. $F(a)=\sum_{M\text{ a matching}}a^{|M|}B(M)$ is the matching partition function.
--   2. The auxiliary distribution of Eq. (12) is
--   $$\nu_a(\sigma)=\frac1{F_{\mathrm{aux}}(a)}\,\frac{a^{\,n-\mathrm{un}(\sigma)}}{(1+J)^{\mathrm{cr}(\sigma)}}\prod_{u:\sigma_u\ne*}B(u,\sigma_u),\qquad\sigma\in\Omega_{\mathrm{aux}},$$
--   with normalizer $F_{\mathrm{aux}}(a)$.
--   3. The rates $\theta_u(\sigma)=1+J$ if $u$ is conflicted in $\sigma$ and $1$ otherwise, and the resampling law $q_u(*)=1/(1+a)$, $q_u(v)=aB(u,v)/(1+a)$, define the **assignment Glauber dynamics** with positive Laplacian (Eq. (14))
--   $$(L_af)(\sigma)=\sum_{u}\theta_u(\sigma)\sum_{x\in V_2\cup\{*\}}q_u(x)\big(f(\sigma)-f(\sigma^{u\to x})\big).$$
--   4. A distribution $\xi$ is a **3-warm start** for $\nu$ if $\sum_\sigma\xi(\sigma)^2/\nu(\sigma)\le3$.
--   5. $\mathbb E[n-|M|]$ for $M$ drawn with probability $a^{|M|}B(M)/F(a)$ is the expected number of unmatched left vertices.
--
--   **Formalization Note** $L_a$ is a matrix indexed by assignments, so that $(L_af)(\sigma)=\sum_\tau L_a(\sigma,\tau)f(\tau)$.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), Eq. (12), p.12 (PDF 14); p.13–14 (PDF 15–16), Eq. (14); §8.1, p.38 (PDF 40); Lemma 42, p.41 (PDF 43)

import Mathlib
import Definitions.Def_CubicPermFPRAS_matchWeight

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

variable {n : ℕ}

/-- The matching partition function `F(a) = ∑_{M a matching} a^{|M|} B(M)`, §8.1, p.38
(PDF 40) (arXiv:2609.20717, held version sha256 9e14f335…). The sum runs over all matchings
of `K_{n,n}`, including the empty one. -/
def Fpoly (B : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : ℝ :=
  ∑ σ ∈ Finset.univ.filter (fun σ : Asg n => IsMatching σ), a ^ size σ * matchWeight B σ

/-- The unnormalized auxiliary weight of Eq. (12), p.12 (PDF 14):
`a^{n−un(σ)} (1+J)^{−cr(σ)} ∏_{u : σ_u ≠ ∗} B(u,σ_u)`. -/
def auxWeight (B : Matrix (Fin n) (Fin n) ℝ) (J a : ℝ) (σ : Asg n) : ℝ :=
  a ^ (n - un σ) / (1 + J) ^ cr σ * matchWeight B σ

/-- The normalizer `F_aux(a) = ∑_σ auxWeight(σ)` of Eq. (12) (p.12; p.38). -/
def Faux (B : Matrix (Fin n) (Fin n) ℝ) (J a : ℝ) : ℝ :=
  ∑ σ, auxWeight B J a σ

/-- The auxiliary distribution `ν_a` on `Ω_aux`, Eq. (12), p.12. -/
def nuAux (B : Matrix (Fin n) (Fin n) ℝ) (J a : ℝ) (σ : Asg n) : ℝ :=
  auxWeight B J a σ / Faux B J a

/-- The resampling rate `θ_u(σ) = 1 + J` if `u` is conflicted in `σ`, else `1` (p.13). -/
def theta (J : ℝ) (σ : Asg n) (u : Fin n) : ℝ :=
  if IsConflicted σ u then 1 + J else 1

/-- The resampling law `q_u(∗) = 1/(1+a)`, `q_u(v) = aB(u,v)/(1+a)` (p.14 (PDF 16)). -/
def qRes (B : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) (u : Fin n) : Option (Fin n) → ℝ
  | none => 1 / (1 + a)
  | some v => a * B u v / (1 + a)

/-- The positive Laplacian `L_a` of the assignment Glauber dynamics, Eq. (14), p.14, as a
matrix: `(L_a f)(σ) = ∑_τ L_a(σ,τ) f(τ) = ∑_u θ_u(σ) ∑_{x ∈ V₂ ∪ {∗}} q_u(x)(f(σ) − f(σ^{u→x}))`. -/
def glauberLap (B : Matrix (Fin n) (Fin n) ℝ) (J a : ℝ) : Matrix (Asg n) (Asg n) ℝ :=
  fun σ τ => ∑ u, theta J σ u * ∑ x : Option (Fin n),
    qRes B a u x * ((if τ = σ then 1 else 0) - (if τ = Function.update σ u x then 1 else 0))

/-- `ξ` is a probability distribution on `Ω_aux` that is a **3-warm start** for `ν`:
`∑_σ ξ(σ)²/ν(σ) ≤ 3` (p.13 (PDF 15)). -/
def IsWarm3 (ξ ν : Asg n → ℝ) : Prop :=
  (∀ σ, 0 ≤ ξ σ) ∧ ∑ σ, ξ σ = 1 ∧ ∑ σ, ξ σ ^ 2 / ν σ ≤ 3

/-- `E[n − |M|]` for a matching `M` drawn with probability `a^{|M|}B(M)/F(a)` (Lemma 42, p.41
(PDF 43)). -/
def meanUnmatched (B : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) : ℝ :=
  (∑ σ ∈ Finset.univ.filter (fun σ : Asg n => IsMatching σ),
      ((n : ℝ) - size σ) * (a ^ size σ * matchWeight B σ)) / Fpoly B a

end

end CubicPermFPRAS


