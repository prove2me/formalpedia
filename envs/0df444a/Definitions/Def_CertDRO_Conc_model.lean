-- Prove2me | Definitions.Def_CertDRO_Conc_model
-- name    : CertDRO_Conc_model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T19:08:38.900209+00:00
-- url     : https://prove2.me/theorems/df8edce1-2d4c-4c43-ad34-cfa5a212b8f4
-- title:
--   Assumptions A and B, the transportation map T_γ, cases (i)/(ii) of Theorem 4 and the robustness levels
-- statement:
--   This file fixes the model of §3.2 of Sinha, Namkoong, Volpi and Duchi, in which the robustness level achieved by the Wasserstein penalty problem is shown to concentrate uniformly over the parameter set.
--
--   **Spaces.** Parameters live in $\mathbb R^d$ (the parameter set $\Theta\subseteq\mathbb R^d$ is an arbitrary subset, fixed in each theorem) and data in a set $Z\subseteq\mathbb R^m$. Both spaces carry the Euclidean norm $\|\cdot\|_2$, which is its own dual norm.
--
--   **Assumption A** (with the standing conditions on the transportation cost of §2). A cost $c:Z\times Z\to\mathbb R$ satisfies Assumption A when $c\ge0$ on $Z\times Z$, $c(z,z)=0$ for $z\in Z$, $c$ is continuous on $Z\times Z$, and for each $z_0\in Z$ the map $z\mapsto c(z,z_0)$ is $1$-strongly convex on $Z$:
--   $$c(tz+(1-t)z',z_0)\le t\,c(z,z_0)+(1-t)\,c(z',z_0)-\tfrac{t(1-t)}2\|z-z'\|_2^2\qquad(t\in[0,1]).$$
--
--   **Assumption B** (on a parameter set $S$; Theorem 4 takes $S=\Theta$). A loss $\ell$ with partial gradients $g_\theta(\theta,z)=\nabla_\theta\ell(\theta;z)$ and $g_z(\theta,z)=\nabla_z\ell(\theta;z)$ (taken at $\theta\in S$, $z\in Z$) satisfies Assumption B on $S\times Z$ with constants $L_{\theta\theta},L_{zz},L_{\theta z},L_{z\theta}\ge0$ when, for all $\theta,\theta'\in S$ and $z,z'\in Z$,
--   $$\|g_\theta(\theta,z)-g_\theta(\theta',z)\|_2\le L_{\theta\theta}\|\theta-\theta'\|_2,\qquad \|g_z(\theta,z)-g_z(\theta,z')\|_2\le L_{zz}\|z-z'\|_2,$$
--   $$\|g_\theta(\theta,z)-g_\theta(\theta,z')\|_2\le L_{\theta z}\|z-z'\|_2,\qquad \|g_z(\theta,z)-g_z(\theta',z)\|_2\le L_{z\theta}\|\theta-\theta'\|_2 .$$
--
--   **Transportation map** (9). For a penalty $\gamma$ and a parameter set $S$, a map $T:\mathbb R^d\times\mathbb R^m\to\mathbb R^m$ is a transportation (Monge) map on $S$ if, for every $\theta\in S$ and every $z_0\in Z$,
--   $$T(\theta;z_0)\in\operatorname*{argmax}_{z\in Z}\bigl\{\ell(\theta;z)-\gamma c(z,z_0)\bigr\},$$
--   that is, $T(\theta;z_0)\in Z$ and no point of $Z$ has a larger penalized loss.
--
--   **The two cases of Theorem 4.** Let $L_c\ge0$.
--   1. Case (i): $c$ is $L_c$-Lipschitz over $Z$ in each argument, $|c(z_1,z)-c(z_2,z)|\le L_c\|z_1-z_2\|_2$ and $|c(z,z_1)-c(z,z_2)|\le L_c\|z_1-z_2\|_2$ for $z,z_1,z_2\in Z$.
--   2. Case (ii) on a parameter set $S$: for every $\theta\in S$, $\ell(\theta;z)\in[0,M_\ell]$ for $z\in Z$ and $z\mapsto\ell(\theta;z)$ is $\gamma L_c$-Lipschitz on $Z$. Theorem 4 takes $S=\Theta$.
--
--   **Robustness levels** (10). For a sample $\omega=(Z_1,\dots,Z_n)$ with empirical distribution $\widehat P_n$ and a probability measure $P_0$,
--   $$\widehat\rho_n(\theta)=\mathbb E_{\widehat P_n}[c(T(\theta;Z),Z)]=\frac1n\sum_{i=1}^n c(T(\theta;Z_i),Z_i),\qquad \rho(\theta)=\mathbb E_{P_0}[c(T(\theta;Z),Z)],$$
--   and the deviation is $D_n(\theta)=|\widehat\rho_n(\theta)-\rho(\theta)|$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\mathbb R^d$ and $\mathbb R^m$ are `EuclideanSpace ℝ (Fin d)` and `EuclideanSpace ℝ (Fin m)`; the paper's general norm is specialised to $\ell_2$. The cost is real valued and only its values on $Z\times Z$ are constrained. The loss is typed on $\mathbb R^d\times\mathbb R^m$, but Assumption B and the transportation map are parametrised by the parameter set $S$ on which they are required (every statement takes $S=\Theta$, the paper's $\ell:\Theta\times Z\to\mathbb R$); values at parameters outside $S$ enter only through the gradients at points of $S$. Strong convexity uses Mathlib's `StrongConvexOn Z 1`, whose modulus convention $\tfrac m2\|x-y\|^2$ matches the paper's. The transportation map is a function together with its argmax property, not a choice. Case (ii) is parametrised by the set $S$ of parameters it covers, and every statement uses it on $\Theta$, as Theorem 4 does. $\rho(\theta)$ is a Bochner integral (Lean returns $0$ for a non-integrable integrand); the theorems carry the measurability and boundedness that make it integrable. $\frac1n$ is $0$ when $n=0$.
-- source:
--   Sinha, Namkoong, Volpi, Duchi, Certifying Some Distributional Robustness with Principled Adversarial Training, arXiv:1710.10571v5, p. 4 (cost c); p. 5, Assumptions A and B; p. 9, (9) and (10); p. 11, Theorem 4, cases (i) and (ii)

import Mathlib
import Definitions.Def_CertDRO_SGD_model

namespace CertDRO.Conc

open MeasureTheory

/-- Assumption B (p. 5) for the loss `ℓ : Θ × Z → ℝ`, on the parameter set `S` (Theorem 4 takes
`S = Θ`), for the ℓ²-norm (whose dual norm is again the ℓ²-norm): for every `θ ∈ S` and `z ∈ Z`,
`gθ θ z` is the gradient of `ℓ(·, z)` at `θ` and `gz θ z` is the gradient of `ℓ(θ, ·)` at `z`, and
the four Lipschitz conditions hold with nonnegative constants for all `θ, θ' ∈ S` and `z, z' ∈ Z`.
Values of `ℓ` at parameters outside `S` are irrelevant except through the gradients at points of `S`. -/
structure AssumptionB {d m : ℕ} (S : Set (CertDRO.SGD.Param d)) (Z : Set (CertDRO.SGD.Data m))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ)
    (gθ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Param d) (gz : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m)
    (Lθθ Lzz Lθz Lzθ : ℝ) : Prop where
  hasGradient_θ : ∀ θ ∈ S, ∀ z ∈ Z, HasGradientAt (fun θ' => ℓ θ' z) (gθ θ z) θ
  hasGradient_z : ∀ θ ∈ S, ∀ z ∈ Z, HasGradientAt (fun z' => ℓ θ z') (gz θ z) z
  nonneg : 0 ≤ Lθθ ∧ 0 ≤ Lzz ∧ 0 ≤ Lθz ∧ 0 ≤ Lzθ
  lip_θθ : ∀ θ ∈ S, ∀ θ' ∈ S, ∀ z ∈ Z, ‖gθ θ z - gθ θ' z‖ ≤ Lθθ * ‖θ - θ'‖
  lip_zz : ∀ θ ∈ S, ∀ z ∈ Z, ∀ z' ∈ Z, ‖gz θ z - gz θ z'‖ ≤ Lzz * ‖z - z'‖
  lip_θz : ∀ θ ∈ S, ∀ z ∈ Z, ∀ z' ∈ Z, ‖gθ θ z - gθ θ z'‖ ≤ Lθz * ‖z - z'‖
  lip_zθ : ∀ θ ∈ S, ∀ θ' ∈ S, ∀ z ∈ Z, ‖gz θ z - gz θ' z‖ ≤ Lzθ * ‖θ - θ'‖

/-- `T` is a transportation (Monge) map (9), p. 9, on the parameter set `S`: for every `θ ∈ S` and
every `z₀ ∈ Z`, the point `T θ z₀` lies in `Z` and maximizes `z ↦ ℓ(θ; z) − γ c(z, z₀)` over `Z`,
`T_γ(θ; z₀) ∈ argmax_{z ∈ Z} {ℓ(θ; z) − γ c(z, z₀)}`. Values at `θ ∉ S` or `z₀ ∉ Z` are irrelevant. -/
def IsTransportMap {d m : ℕ} (S : Set (CertDRO.SGD.Param d)) (Z : Set (CertDRO.SGD.Data m))
    (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ)
    (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (γ : ℝ) (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) : Prop :=
  ∀ θ ∈ S, ∀ z₀ ∈ Z, T θ z₀ ∈ Z ∧
    ∀ z ∈ Z, ℓ θ z - γ * c z z₀ ≤ ℓ θ (T θ z₀) - γ * c (T θ z₀) z₀

/-- Case (i) of Theorem 4 (p. 11): `c(·, ·)` is `Lc`-Lipschitz over `Z` in each argument with
respect to the ℓ²-norm, with a nonnegative constant `Lc`. -/
structure CaseI {m : ℕ} (Z : Set (CertDRO.SGD.Data m)) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ) (Lc : ℝ) : Prop where
  nonneg : 0 ≤ Lc
  lip_fst : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, ∀ z ∈ Z, |c z₁ z - c z₂ z| ≤ Lc * ‖z₁ - z₂‖
  lip_snd : ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, ∀ z ∈ Z, |c z z₁ - c z z₂| ≤ Lc * ‖z₁ - z₂‖

/-- Case (ii) of Theorem 4 (p. 11), for the parameters in a set `S`: for every `θ ∈ S`,
`ℓ(θ, z) ∈ [0, Mℓ]` for `z ∈ Z` and `z ↦ ℓ(θ, z)` is `γ Lc`-Lipschitz on `Z`, with `Lc ≥ 0`.
(Theorem 4 takes `S = Θ`.) -/
structure CaseII {d m : ℕ} (S : Set (CertDRO.SGD.Param d)) (Z : Set (CertDRO.SGD.Data m)) (ℓ : CertDRO.SGD.Param d → CertDRO.SGD.Data m → ℝ)
    (γ Lc Mℓ : ℝ) : Prop where
  nonneg : 0 ≤ Lc
  range : ∀ θ ∈ S, ∀ z ∈ Z, 0 ≤ ℓ θ z ∧ ℓ θ z ≤ Mℓ
  lip : ∀ θ ∈ S, ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, |ℓ θ z₁ - ℓ θ z₂| ≤ γ * Lc * ‖z₁ - z₂‖

/-- The empirical robustness level (10), p. 9, at the sample `ω = (Z₁, …, Zₙ)`:
`ρ̂ₙ(θ) = E_{P̂ₙ}[c(T(θ; Z), Z)] = (1/n) ∑ᵢ c(T(θ; Zᵢ), Zᵢ)`. -/
noncomputable def empLevel {d m n : ℕ} (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ)
    (ω : Fin n → CertDRO.SGD.Data m) (θ : CertDRO.SGD.Param d) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, c (T θ (ω i)) (ω i)

/-- The population robustness level `E_{P₀}[c(T(θ; Z), Z)]` (a Bochner integral). -/
noncomputable def popLevel {d m : ℕ} (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ)
    (P₀ : Measure (CertDRO.SGD.Data m)) (θ : CertDRO.SGD.Param d) : ℝ :=
  ∫ z, c (T θ z) z ∂P₀

/-- The deviation `|E_{P̂ₙ}[c(T(θ; Z), Z)] − E_{P₀}[c(T(θ; Z), Z)]|` at the sample `ω`. -/
noncomputable def deviation {d m n : ℕ} (T : CertDRO.SGD.Param d → CertDRO.SGD.Data m → CertDRO.SGD.Data m) (c : CertDRO.SGD.Data m → CertDRO.SGD.Data m → ℝ)
    (P₀ : Measure (CertDRO.SGD.Data m)) (ω : Fin n → CertDRO.SGD.Data m) (θ : CertDRO.SGD.Param d) : ℝ :=
  |empLevel T c ω θ - popLevel T c P₀ θ|

end CertDRO.Conc


