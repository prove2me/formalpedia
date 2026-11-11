-- Prove2me | Definitions.Def_PreservePast_sourceExp
-- name    : PreservePast_sourceExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:39:32.439704+00:00
-- url     : https://prove2.me/theorems/af9e4474-291d-4937-83fc-58daf87a463f
-- title:
--   Shared-response deficit $J_\lambda$ (1), the event $W_n(b)$ and the source exponent $\mathcal H_n(b;\mu)$ (2)
-- statement:
--   Fix a score $g_h(z)\in\mathbb R$ for histories $h$ and actions $z\in\mathcal B$, with finite value $V(h)=\sup_{z\in\mathcal B}g_h(z)$. For a probability vector $\lambda=(\lambda_1,\dots,\lambda_n)$ the **shared-response deficit** is
--   $$
--   J_\lambda(h_1,\dots,h_n)=\sum_{i=1}^n\lambda_iV(h_i)-\sup_{z\in\mathcal B}\sum_{i=1}^n\lambda_ig_{h_i}(z),
--   $$
--   the value lost when one action must serve all the histories at once. Let $\mu$ be the prior, $\mathcal T$ a domain of histories, $n\ge1$ and $b\ge0$. $W_n(b)\subseteq\mathcal T^n$ is the event that every nonempty subtuple of $(H_1,\dots,H_n)$ has uniform-mixture deficit at most $b$, and the **finite-order source exponent** (in nats) is
--   $$
--   \mathcal H_n(b;\mu)=-\frac1n\ln\Pr_{\mu^n}\{W_n(b)\},
--   $$
--   with the probability taken under the original source $\mu$ even when $\mathcal T$ is a typical subset.
--
--   **Formalization Note** The uniform mixture of the subtuple indexed by $S$ is $J_\lambda$ with weights $1/|S|$ on $S$ and $0$ elsewhere. $\mathcal H_n$ takes values in the extended reals, with $-\ln0=+\infty$. Suprema are real suprema, used for nonempty $\mathcal B$ and scores bounded above.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §1.2.1, p.2 (PDF p.4), (1)–(2)

import Mathlib

open MeasureTheory

namespace PreservePast

/-- The individual optimal value `V(h) = sup_{z∈𝓑} g_h(z)` of the score `g` at history `h`, (1). -/
noncomputable def optVal {Θ 𝓑 : Type*} (g : Θ → 𝓑 → ℝ) (h : Θ) : ℝ := ⨆ z, g h z

/-- **Shared-response deficit** (1). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2.1, p.2 (PDF p.4): "For a probability vector
λ = (λ₁, …, λ_n), define the individual optimal value and the shared-response deficit by
V(h) = sup_{z∈𝓑} g_h(z), J_λ(h₁, …, h_n) = Σ_{i=1}^n λ_i V(h_i) − sup_{z∈𝓑} Σ_{i=1}^n λ_i g_{h_i}(z)."

**Formalization Note.** Suprema are real `⨆`; they are used for nonempty `𝓑` and scores bounded
above in `z` ("the scores and values are finite"), where they are genuine suprema. -/
noncomputable def deficit {Θ 𝓑 : Type*} {k : ℕ} (g : Θ → 𝓑 → ℝ) (lam : Fin k → ℝ)
    (hs : Fin k → Θ) : ℝ :=
  ∑ i, lam i * optVal g (hs i) - ⨆ z, ∑ i, lam i * g (hs i) z

/-- The uniform probability vector on the index set `S` (zero off `S`). -/
noncomputable def unifWeights {k : ℕ} (S : Finset (Fin k)) : Fin k → ℝ :=
  fun i => if i ∈ S then ((S.card : ℕ) : ℝ)⁻¹ else 0

/-- The event `W_n(b) ⊆ 𝒯ⁿ` (p.2): "the event that every nonempty subtuple of (H₁, …, H_n) has
uniform-mixture deficit at most b". The uniform mixture of the subtuple indexed by `S` is the
deficit with weights `1/|S|` on `S` and `0` elsewhere. -/
def Wset {Θ 𝓑 : Type*} (g : Θ → 𝓑 → ℝ) (𝒯 : Set Θ) (n : ℕ) (b : ℝ) : Set (Fin n → Θ) :=
  {hs | (∀ i, hs i ∈ 𝒯) ∧ ∀ S : Finset (Fin n), S.Nonempty → deficit g (unifWeights S) hs ≤ b}

/-- **Finite-order source exponent** (2). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §1.2.1, p.2 (PDF p.4): "Let µ be the prior on
histories, 𝒯 a specified domain of histories, n ≥ 1 an integer, and b ≥ 0. … We define the
finite-order source exponent (in nats) by 𝓗_n(b; µ) = −(1/n) ln Pr_{µⁿ}{W_n(b)}, where the
probability is taken under the original source µ even when 𝒯 is a typical subset."

**Formalization Note.** Valued in `EReal`: `ENNReal.log 0 = ⊥`, so `𝓗_n = +∞` exactly when
`µⁿ(W_n(b)) = 0` (the convention `−ln 0 = +∞`); `µⁿ` is the product measure `Measure.pi`. Used for
`n ≥ 1`. -/
noncomputable def sourceExp {Θ 𝓑 : Type*} [MeasurableSpace Θ] (g : Θ → 𝓑 → ℝ) (𝒯 : Set Θ)
    (μ : Measure Θ) (n : ℕ) (b : ℝ) : EReal :=
  -(((n : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log (Measure.pi (fun _ : Fin n => μ) (Wset g 𝒯 n b))

end PreservePast


