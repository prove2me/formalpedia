-- Prove2me | Definitions.Def_RobertsonSeymour1986_GM5_Params
-- name    : RobertsonSeymour1986_GM5_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T15:55:07.646507+00:00
-- url     : https://prove2.me/theorems/376abd36-64fb-4a72-b52e-328822766613
-- title:
--   The parameters $\alpha,\ \phi_k,\ \psi_k,\ \theta_1,\dots,\theta_9$ of Graph Minors V
-- statement:
--   Fix an even integer $\theta\ge 6$. Graph Minors V defines the following natural numbers depending on $\theta$.
--
--   1. For $k\ge2$, $n\ge0$: $\alpha(2,n)=n+1$ and, for $k\ge 3$,
--   $$\alpha(k,n)=2^{n\theta^4}+\alpha\bigl(k-1,\,2^{n\theta^4}+n+1\bigr).$$
--   2. $\theta_1=2\alpha(\theta^2/2,\theta^2/2)$.
--   3. $\phi_{\theta_1}=\theta^2/2$ and, for $0\le k<\theta_1$, $\phi_k=\phi_{k+1}\,2^{\phi_{k+1}\theta^2}$ (a downward recursion).
--   4. $\psi_{\theta_1}=0$ and, for $0\le k<\theta_1$, $\psi_k=\phi_k+2\phi_{k+1}+\dots+2\phi_{\theta_1-1}+\phi_{\theta_1}$.
--   5. Finally
--   $$\begin{aligned}
--   \theta_2&=\phi_0+2\phi_1+\dots+2\phi_{\theta_1-1}+\phi_{\theta_1}, & \theta_3&=(\theta^2/2)^{\theta_2-1},\\
--   \theta_4&=\theta_2\tbinom{\theta_3}{\theta_2}+\tfrac12\theta^2\tbinom{\theta_3}{\theta^2/2}, & \theta_5&=(\theta^2/2)^{\theta_4-1},\\
--   \theta_6&=\theta_3\tbinom{\theta_5}{\theta_4}+\tfrac12\theta^2\tbinom{\theta_5}{\theta^2/2}, & \theta_7&=\alpha(\theta_5,\theta_6),\\
--   \theta_8&=3\theta_5(3^{\theta_5}-1)/4, & \theta_9&=\theta_7(\theta_8+1)+1.
--   \end{aligned}$$
--
--   The main theorem bounds the tree-width of every graph without a $\theta$-grid minor by $\theta_9(\theta)$. The other parameters are the thresholds of the intermediate lemmas.
--
--   **Formalization Note** All parameters are natural-number functions of $\theta$. $\alpha(k,n)$ at $k=0,1$ (never used) is set to $n+1$; $\phi_k$ for $k>\theta_1$ and $\psi_k$ for $k>\theta_1$ (never used) take junk values. For even $\theta\ge 6$ every division is exact: $\theta^2/2$ is an integer, and $\theta_5$ is even, so $4$ divides $3^{\theta_5}-1$.
-- source:
--   Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986), Sect. 2, pp. 94–95 (PDF pp. 3–4) (α, θ₁, φ_k, θ₂–θ₉) and Sect. 4, p. 99 (PDF p. 8) (ψ_k); DOI 10.1016/0095-8956(86)90030-4

import Mathlib

/-!
# The parameters α, φ, ψ, θ₁, …, θ₉ of Graph Minors V

Robertson–Seymour, Graph Minors. V. Excluding a Planar Graph, J. Combin. Theory Ser. B 41 (1986),
Sect. 2, pp. 94–95 (PDF pp. 3–4), unnumbered, and (for ψ) Sect. 4, p. 99 (PDF p. 8), unnumbered.
All parameters are natural numbers depending on `θ`; the paper takes `θ ≥ 6` even ("Now let θ ≥ 6
be some even number"), and every theorem using them carries `Even θ` and `6 ≤ θ` as hypotheses.
Under that assumption every `/ 2` and `/ 4` below is an exact division (see the individual notes).
-/

namespace RobertsonSeymour1986.GM5

/-- `alpha θ k n` is `α(k, n)` (Sect. 2, p. 94, PDF p. 3): "For k ≥ 2, n ≥ 0, define α(k, n)
inductively by α(2, n) = n + 1, α(k, n) = 2^{nθ⁴} + α(k − 1, 2^{nθ⁴} + n + 1) for k ≥ 3."

**Formalization Note** The paper defines α only for `k ≥ 2`. The last equation also assigns the
value `n + 1` at `k = 0, 1`; those values are never used (every use has `k ≥ 2`). The exponent is
`n * θ ^ 4`. -/
def alpha (θ : ℕ) : ℕ → ℕ → ℕ
  | k + 3, n => 2 ^ (n * θ ^ 4) + alpha θ (k + 2) (2 ^ (n * θ ^ 4) + n + 1)
  | _, n => n + 1

/-- `theta1 θ` is `θ₁ = 2α(θ²/2, θ²/2)` (Sect. 2, p. 94, PDF p. 3).
`θ ^ 2 / 2` is exact for even `θ`. -/
def theta1 (θ : ℕ) : ℕ := 2 * alpha θ (θ ^ 2 / 2) (θ ^ 2 / 2)

/-- Auxiliary downward recursion for φ: `phiAux θ j = φ_{θ₁ − j}`. `phiAux θ 0 = θ²/2` and
`phiAux θ (j + 1) = phiAux θ j · 2^{(phiAux θ j)·θ²}`. -/
def phiAux (θ : ℕ) : ℕ → ℕ
  | 0 => θ ^ 2 / 2
  | j + 1 => phiAux θ j * 2 ^ (phiAux θ j * θ ^ 2)

/-- `phi θ k` is `φ_k` (Sect. 2, p. 94, PDF p. 3): "Define φ_{θ₁} = θ²/2, and for 0 ≤ k < θ₁ define
φ_k inductively by φ_k = φ_{k+1} 2^{φ_{k+1}θ²}."

**Formalization Note** `phi θ k = phiAux θ (θ₁ − k)`; so `phi θ θ₁ = θ²/2` and, for `k < θ₁`,
`phi θ k = phi θ (k+1) * 2 ^ (phi θ (k+1) * θ ^ 2)`. For `k > θ₁` (never used) the truncated
subtraction gives the junk value `θ²/2`. -/
def phi (θ k : ℕ) : ℕ := phiAux θ (theta1 θ - k)

/-- `psi θ k` is `ψ_k` (Sect. 4, p. 99, PDF p. 8): "Define ψ_{θ₁} = 0, and for 0 ≤ k < θ₁, define
ψ_k = φ_k + 2φ_{k+1} + 2φ_{k+2} + ··· + 2φ_{θ₁−1} + φ_{θ₁}."

**Formalization Note** The middle terms are `2 φ_i` for `k < i < θ₁`. For `k ≥ θ₁` the value is `0`
(the paper's `ψ_{θ₁} = 0`; `k > θ₁` is never used). -/
def psi (θ k : ℕ) : ℕ :=
  if k < theta1 θ then
    phi θ k + 2 * ∑ i ∈ Finset.Ioo k (theta1 θ), phi θ i + phi θ (theta1 θ)
  else 0

/-- `theta2 θ` is `θ₂ = φ₀ + 2φ₁ + 2φ₂ + ··· + 2φ_{θ₁−1} + φ_{θ₁}` (Sect. 2, p. 95, PDF p. 4).
The middle terms are `2 φ_i` for `0 < i < θ₁`. (So `θ₂ = ψ₀`, as the paper notes implicitly.) -/
def theta2 (θ : ℕ) : ℕ :=
  phi θ 0 + 2 * ∑ i ∈ Finset.Ioo 0 (theta1 θ), phi θ i + phi θ (theta1 θ)

/-- `theta3 θ` is `θ₃ = (θ²/2)^{θ₂−1}` (Sect. 2, p. 95, PDF p. 4). The subtraction `θ₂ − 1` is
exact since `θ₂ ≥ φ₀ ≥ 1` for `θ ≥ 2`. -/
def theta3 (θ : ℕ) : ℕ := (θ ^ 2 / 2) ^ (theta2 θ - 1)

/-- `theta4 θ` is `θ₄ = θ₂ \binom{θ₃}{θ₂} + ½θ² \binom{θ₃}{θ²/2}` (Sect. 2, p. 95, PDF p. 4).
`½θ²` is `θ ^ 2 / 2`, exact for even `θ`. -/
def theta4 (θ : ℕ) : ℕ :=
  theta2 θ * Nat.choose (theta3 θ) (theta2 θ) + θ ^ 2 / 2 * Nat.choose (theta3 θ) (θ ^ 2 / 2)

/-- `theta5 θ` is `θ₅ = (θ²/2)^{θ₄−1}` (Sect. 2, p. 95, PDF p. 4). -/
def theta5 (θ : ℕ) : ℕ := (θ ^ 2 / 2) ^ (theta4 θ - 1)

/-- `theta6 θ` is `θ₆ = θ₃ \binom{θ₅}{θ₄} + ½θ² \binom{θ₅}{θ²/2}` (Sect. 2, p. 95, PDF p. 4). -/
def theta6 (θ : ℕ) : ℕ :=
  theta3 θ * Nat.choose (theta5 θ) (theta4 θ) + θ ^ 2 / 2 * Nat.choose (theta5 θ) (θ ^ 2 / 2)

/-- `theta7 θ` is `θ₇ = α(θ₅, θ₆)` (Sect. 2, p. 95, PDF p. 4). -/
def theta7 (θ : ℕ) : ℕ := alpha θ (theta5 θ) (theta6 θ)

/-- `theta8 θ` is `θ₈ = 3θ₅(3^{θ₅} − 1)/4` (Sect. 2, p. 95, PDF p. 4).

**Formalization Note** The division is natural-number division; it is exact for even `θ ≥ 6`:
then `θ²/2 = 2(θ/2)²` is even and `θ₄ ≥ 2`, so `θ₅` is even, hence `3^{θ₅} ≡ 1 (mod 8)` and
`4 ∣ 3^{θ₅} − 1`. -/
def theta8 (θ : ℕ) : ℕ := 3 * theta5 θ * (3 ^ theta5 θ - 1) / 4

/-- `theta9 θ` is `θ₉ = θ₇(θ₈ + 1) + 1` (Sect. 2, p. 95, PDF p. 4). -/
def theta9 (θ : ℕ) : ℕ := theta7 θ * (theta8 θ + 1) + 1

end RobertsonSeymour1986.GM5


