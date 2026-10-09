-- Prove2me | Definitions.Def_ImpulsiveISS_SmallGain_Interconnection
-- name    : ImpulsiveISS_SmallGain_Interconnection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:43.058094+00:00
-- url     : https://prove2.me/theorems/40a3196e-a46d-4db5-b4ef-fb93107f3b93
-- title:
--   §4 — interconnection of impulsive systems: subsystem ISS-Lyapunov functions (4.4)–(4.6), gain operator Γ (4.7), small-gain condition (4.9), $V$ (4.10), $\chi$ (4.11), $\tilde\alpha$, $\eta$
-- statement:
--   Consider $n$ interconnected impulsive subsystems (4.1) with Banach state spaces $X_1,\dots,X_n$ and input values in a Banach space $U$, all jumping at the same impulse times (p. 17). They form one impulsive system (4.2) on $X=X_1\times\dots\times X_n$, with transition map $\phi_c$ and jump map $g=(g_1,\dots,g_n)$, endowed with the norm
--   $$\|x\|_X=\|x_1\|_{X_1}+\dots+\|x_n\|_{X_n}.$$
--
--   **Subsystem ISS-Lyapunov functions** (p. 18, items 1–3). Functions $V_i:X_i\to\mathbb R_+$ are ISS-Lyapunov functions for the subsystems with gains $\chi_{ij}$ if for every $i$:
--   1. $V_i$ is continuous and $\psi_{i1}(\|x_i\|)\le V_i(x_i)\le\psi_{i2}(\|x_i\|)$ with $\psi_{i1},\psi_{i2}\in\mathcal K_\infty$;
--   2. $\chi_{ij}\in\mathcal K$ for $j\ne i$, $\chi_{ii}=0$, $\chi_i\in\mathcal K$, $\varphi_i\in\mathcal P$, and for all $x\in X$, $\xi\in U$ and inputs $u\in U_c$ with $u(0)=\xi$,
--   $$V_i(x_i)\ge\max\Big\{\max_{j=1}^n\chi_{ij}(V_j(x_j)),\ \chi_i(\|\xi\|_U)\Big\}\tag{4.4}$$
--   implies
--   $$\overline{\lim_{t\to+0}}\ \frac1t\Big(V_i\big(\phi_c(t,0,x,u)_i\big)-V_i(x_i)\Big)\le-\varphi_i(V_i(x_i));\tag{4.5}$$
--   3. $\alpha_i\in\mathcal P$ and for all $x\in X$, $\xi\in U$,
--   $$V_i(g_i(x,\xi))\le\max\Big\{\alpha_i(V_i(x_i)),\ \max_{j=1}^n\chi_{ij}(V_j(x_j)),\ \chi_i(\|\xi\|_U)\Big\}.\tag{4.6}$$
--
--   **Gain operator** (4.7) and **small-gain condition** (4.9). For $s\in\mathbb R^n_+$,
--   $$\Gamma(s)=\Big(\max_{j=1}^n\chi_{1j}(s_j),\dots,\max_{j=1}^n\chi_{nj}(s_j)\Big),$$
--   and $\Gamma$ satisfies the small-gain condition if $\Gamma(s)\not\ge s$ for every $s\in\mathbb R^n_+\setminus\{0\}$, the order being componentwise.
--
--   **The constructed objects.** Given an $\Omega$-path $\sigma=(\sigma_1,\dots,\sigma_n)$ (Definition 5, from the referenced `Gains` definition) with inverses $\sigma_i^{-1}$:
--   $$V(x)=\max_i\sigma_i^{-1}(V_i(x_i))\ \ (4.10),\qquad \chi(r)=\max_i\sigma_i^{-1}(\chi_i(r))\ \ (4.11),$$
--   $$\tilde\alpha=\max_i\,\sigma_i^{-1}\circ\alpha_i\circ\sigma_i,\qquad \eta=\max_{i,\,j\ne i}\,\sigma_i^{-1}\circ\chi_{ij}\circ\sigma_j\quad(\text{p. }20).$$
--
--   These are the data and the candidate of the small-gain theorem (Theorem 8).
--
--   **Formalization Note** $X$ is the Pi type over `Fin n`; Mathlib's norm on it is the sup norm, so the paper's sum norm is the separate function `sumNorm`. The page states (4.5) for the $i$-th subsystem's own transition map $\phi_{i,c}(t,0,x_i,v)$ for every $v\in PC(\mathbb R_+,\tilde X_i)$ with $v(0)=\tilde x_i$; here it is stated along the $i$-th component of the interconnection's flow, which is the case $v=$ (the other components of the trajectory, $u$) and is exactly what the paper's proof uses. All maxima are `Finset.sup` over `Fin n` in $\mathbb R_{\ge0}$ (value $0$ for an empty index set). The inverses $\sigma_i^{-1}$ are the functions `τ i` carried by `IsOmegaPath`. The page's typo "$\sigma:\mathbb R^n_+\to\mathbb R^n_+$" in Definition 5 is read as $\sigma:\mathbb R_+\to\mathbb R^n_+$.
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, pp. 17–20, §4: norm on X (p. 17), (4.1)–(4.2), items 1–3 and (4.4)–(4.6) (p. 18), (4.7) (p. 18), Definition 5 (pp. 18–19), (4.9), (4.10), (4.11) (p. 19), α̃ and η (p. 20)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_SmallGain_System

open scoped NNReal
open Filter Topology

namespace ImpulsiveISS.SmallGain

open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

/-! Dashkovskiy and Mironchenko, *Input-to-state stability of nonlinear impulsive systems*,
arXiv:1212.5481v1, §4 (pp. 17–20): the interconnection (4.1)/(4.2) as one impulsive system on
`X = X₁ × ⋯ × Xₙ` (subsystems `1, …, n` are `Fin n`), the sum norm on `X`, subsystem ISS-Lyapunov
functions (4.4)–(4.6), the gain operator `Γ` (4.7), the small-gain condition (4.9), the candidate
(4.10), the gain (4.11), and the functions `α̃`, `η` of the proof of Theorem 8 (p. 20). -/

section Interconnection

variable {n : ℕ} {Xi : Fin n → Type*} [∀ i, NormedAddCommGroup (Xi i)]
  [∀ i, NormedSpace ℝ (Xi i)] [∀ i, CompleteSpace (Xi i)]
  {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]

/-- The paper's norm on `X = X₁ × ⋯ × Xₙ` (p. 17): `‖x‖_X = ‖x₁‖ + ⋯ + ‖xₙ‖`. (Mathlib's norm on
the Pi type is the sup norm; it is never used for `‖x‖_X`.) -/
noncomputable def sumNorm (x : (i : Fin n) → Xi i) : ℝ≥0 := ∑ i, ‖x i‖₊

/-- The gain operator `Γ : ℝⁿ₊ → ℝⁿ₊` of (4.7), p. 18: `Γ(s)ᵢ = max_{j=1}^n χᵢⱼ(sⱼ)`. -/
noncomputable def gainOp (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (s : Fin n → ℝ≥0) : Fin n → ℝ≥0 :=
  fun i => Finset.univ.sup fun j => χ i j (s j)

/-- The small-gain condition (4.9), p. 19: `Γ(s) ≱ s` for all `s ∈ ℝⁿ₊ ∖ {0}`, where `≥` is the
componentwise order. -/
def SmallGainCondition (Γ : (Fin n → ℝ≥0) → (Fin n → ℝ≥0)) : Prop :=
  ∀ s : Fin n → ℝ≥0, s ≠ 0 → ¬ (s ≤ Γ s)

/-- The subsystem ISS-Lyapunov functions of §4, items 1–3 on p. 18, for the interconnection (4.1)
written as the impulsive system `S` (4.2) on `X = X₁ × ⋯ × Xₙ`, with jump components
`gᵢ(x, ξ) = (S.jump x ξ)ᵢ`. For every `i`:
1. `Vᵢ : Xᵢ → ℝ₊` is continuous and `ψᵢ₁(‖xᵢ‖) ≤ Vᵢ(xᵢ) ≤ ψᵢ₂(‖xᵢ‖)` with `ψᵢ₁, ψᵢ₂ ∈ 𝒦∞`;
2. `χᵢⱼ ∈ 𝒦` for `j ≠ i`, `χᵢᵢ = 0`, `χᵢ ∈ 𝒦`, `φᵢ ∈ 𝒫`, and for all `x ∈ X`, `ξ ∈ U` and inputs
   `u ∈ U_c` with `u(0) = ξ`, `Vᵢ(xᵢ) ≥ max{max_j χᵢⱼ(Vⱼ(xⱼ)), χᵢ(‖ξ‖)}` (4.4) implies
   `limsup_{t → +0} (Vᵢ((φ_c(t, 0, x, u))ᵢ) − Vᵢ(xᵢ)) / t ≤ −φᵢ(Vᵢ(xᵢ))` (4.5), the Dini derivative
   taken along the `i`-th component of the interconnection's own flow;
3. `αᵢ ∈ 𝒫` and `Vᵢ(gᵢ(x, ξ)) ≤ max{αᵢ(Vᵢ(xᵢ)), max_j χᵢⱼ(Vⱼ(xⱼ)), χᵢ(‖ξ‖)}` (4.6) for all
   `x ∈ X`, `ξ ∈ U`. -/
def IsSubsystemISSLyapunov (S : ImpulsiveSystem ((i : Fin n) → Xi i) U)
    (V : (i : Fin n) → Xi i → ℝ≥0) (ψ₁ ψ₂ : Fin n → ℝ≥0 → ℝ≥0)
    (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (χu : Fin n → ℝ≥0 → ℝ≥0)
    (φ α : Fin n → ℝ≥0 → ℝ≥0) : Prop :=
  (∀ i, Continuous (V i)) ∧
  (∀ i, IsKInf (ψ₁ i) ∧ IsKInf (ψ₂ i)) ∧
  (∀ i (xi : Xi i), ψ₁ i ‖xi‖₊ ≤ V i xi ∧ V i xi ≤ ψ₂ i ‖xi‖₊) ∧
  (∀ i j, i ≠ j → IsK (χ i j)) ∧ (∀ i, χ i i = 0) ∧ (∀ i, IsK (χu i)) ∧
  (∀ i, IsPosDef (φ i)) ∧ (∀ i, IsPosDef (α i)) ∧
  (∀ i (x : (j : Fin n) → Xi j) (ξ : U) (u : ℝ → U), IsPCInput u → u 0 = ξ →
    max (Finset.univ.sup fun j => χ i j (V j (x j))) (χu i ‖ξ‖₊) ≤ V i (x i) →
    diniUpperRight (fun t => (V i (S.flow t x u i) : ℝ)) 0 ≤ ((-(φ i (V i (x i))) : ℝ) : EReal)) ∧
  (∀ i (x : (j : Fin n) → Xi j) (ξ : U),
    V i (S.jump x ξ i) ≤
      max (α i (V i (x i))) (max (Finset.univ.sup fun j => χ i j (V j (x j))) (χu i ‖ξ‖₊)))

/-- The candidate ISS-Lyapunov function (4.10), p. 19: `V(x) = maxᵢ σᵢ⁻¹(Vᵢ(xᵢ))`, with `τᵢ = σᵢ⁻¹`. -/
noncomputable def smallGainV (τ : Fin n → ℝ≥0 → ℝ≥0) (V : (i : Fin n) → Xi i → ℝ≥0)
    (x : (i : Fin n) → Xi i) : ℝ≥0 :=
  Finset.univ.sup fun i => τ i (V i (x i))

/-- The gain of the whole system (4.11), p. 19: `χ(r) = maxᵢ σᵢ⁻¹(χᵢ(r))`, with `τᵢ = σᵢ⁻¹`. -/
noncomputable def smallGainChi (τ : Fin n → ℝ≥0 → ℝ≥0) (χu : Fin n → ℝ≥0 → ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup fun i => τ i (χu i r)

/-- `α̃ = maxᵢ σᵢ⁻¹ ∘ αᵢ ∘ σᵢ` (proof of Theorem 8, p. 20). -/
noncomputable def alphaTilde (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (α : Fin n → ℝ≥0 → ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup fun i => τ i (α i (σ r i))

/-- `η = max_{i, j ≠ i} σᵢ⁻¹ ∘ χᵢⱼ ∘ σⱼ` (proof of Theorem 8, p. 20); `0` when `n ≤ 1`. -/
noncomputable def etaGain (σ : ℝ≥0 → Fin n → ℝ≥0) (τ : Fin n → ℝ≥0 → ℝ≥0)
    (χ : Fin n → Fin n → ℝ≥0 → ℝ≥0) (r : ℝ≥0) : ℝ≥0 :=
  Finset.univ.sup fun i => (Finset.univ.filter fun j => j ≠ i).sup fun j => τ i (χ i j (σ r j))

end Interconnection

end ImpulsiveISS.SmallGain


