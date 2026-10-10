-- Prove2me | Definitions.Def_MasterVisc_Ito_Derivatives
-- name    : MasterVisc_Ito_Derivatives
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T15:36:47.778294+00:00
-- url     : https://prove2.me/theorems/530e00aa-b1aa-4f69-a7aa-3f7b846fa87a
-- title:
--   Definition 2.5 — the classes C^{1,1,1}(Θ̂) and C_b^{1,1,1}(Θ̂), with derivatives (2.7), (2.16), (2.18)
-- statement:
--   This module defines the classes $C^{1,1,1}(\widehat\Theta)$ and $C^{1,1,1}_b(\widehat\Theta)$ of Definition 2.5 of Wu and Zhang, with the derivatives of §2.3.
--
--   A function $f:\widehat\Theta\to\mathbb R$ is given together with candidate derivatives $\partial_tf:\widehat\Theta\to\mathbb R$, $\partial_\mu f:\widehat\Theta\times\widehat\Omega\to\mathbb R^d$ and $\partial_\omega\partial_\mu f:\widehat\Theta\times\widehat\Omega\to\mathbb R^{d\times d}$. Then $f\in C^{1,1,1}(\widehat\Theta)$ with these derivatives when:
--
--   1. $f$ and $\partial_tf$ are continuous on $\widehat\Theta$ for the pseudometric $\mathcal W_2$ of (2.5), and $\partial_\mu f$, $\partial_\omega\partial_\mu f$ are continuous on $\widehat\Theta\times\widehat\Omega$ for $\mathcal W_2+d_{SK}$;
--   2. (2.7) for $t<T$:
--   $$
--   \partial_tf(t,\hat\mu)=\lim_{\delta\downarrow0}\frac{f(t+\delta,\hat\mu_{[0,t]})-f(t,\hat\mu)}{\delta};
--   $$
--   3. (2.16) for every $\widehat{\mathcal F}_t$-measurable, $\hat\mu$-square integrable $\xi:\widehat\Omega\to\mathbb R^d$:
--   $$
--   \mathbb E^{\hat\mu}\big[\partial_\mu f(t,\hat\mu,\widehat X)\cdot\xi\big]=\lim_{\varepsilon\to0}\frac{f\big(t,\hat\mu\circ(\widehat X+\varepsilon\xi\mathbf 1_{[t,T]})^{-1}\big)-f(t,\hat\mu)}{\varepsilon};
--   $$
--   4. (2.18) for every $x\in\mathbb R^d$:
--   $$
--   \partial_\omega\partial_\mu f(t,\hat\mu,\hat\omega)\,x=\lim_{\varepsilon\to0}\frac{\partial_\mu f(t,\hat\mu,\hat\omega+\varepsilon x\mathbf 1_{[t,T]})-\partial_\mu f(t,\hat\mu,\hat\omega)}{\varepsilon};
--   $$
--   5. $\partial_\mu f(t,\hat\mu,\cdot)$ and $\partial_\omega\partial_\mu f(t,\hat\mu,\cdot)$ are $\widehat{\mathcal F}_t$-adapted: they depend on $\hat\omega$ only through $\hat\omega_{t\wedge\cdot}$.
--
--   Moreover $f\in C^{1,1,1}_b(\widehat\Theta)$ if in addition $\partial_tf$ is bounded and (2.19) holds: for some $C$ and all $(t,\hat\mu,\hat\omega)\in\widehat\Theta\times\widehat\Omega$,
--   $$
--   |\partial_\mu f(t,\hat\mu,\hat\omega)|+|\partial_\omega\partial_\mu f(t,\hat\mu,\hat\omega)|\le C\,[1+\|\hat\omega\|].
--   $$
--
--   These are the test functions of the functional Itô formula (Theorem 2.7) and, through it, of the viscosity theory of the paper.
--
--   **Formalization Note** Definition 2.5 says only that continuous $\partial_tf,\partial_\mu f,\partial_\omega\partial_\mu f$ "exist"; that they are the derivatives (2.7), (2.16), (2.18) is implicit in §2.3 and is stated explicitly here. The adaptedness clause 5 is the property the paper's $\partial_\mu f$ inherits from Theorem 2.2 ($\psi$ is $\widehat{\mathcal F}_t$-measurable); (2.16) alone determines only $\mathbb E^{\hat\mu}[\partial_\mu f\mid\widehat{\mathcal F}_t]$. Points of $\widehat\Theta$ are pairs $(t,\hat\mu)$ with $t\le T$ and $\hat\mu\in\widehat{\mathcal P}_2$; every condition is required there only. The time derivative is required for $t<T$ (the right limit needs $f$ after $t$). The matrix norm is the Frobenius norm, which only changes $C$. Adaptedness of $f$ itself is not stated: it follows from continuity for $\mathcal W_2$ (§2.3, "continuous (and thus $\widehat{\mathbb F}$-adapted)").
-- source:
--   Wu, Zhang, Viscosity solutions to parabolic master equations and McKean–Vlasov SDEs with closed-loop controls, Ann. Appl. Probab. 30(2) (2020), §2.3, (2.7), (2.16), (2.18), pp. 941–943; Definition 2.5 and (2.19), p. 944

import Mathlib
import Definitions.Def_MasterVisc_Ito_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MasterVisc.Ito

open EthierKurtz

/-! ### Continuity on Θ̂ = [0, T] × 𝒫̂₂ and on Θ̂ × Ω̂ -/

/-- `f : Θ̂ → ℝ` is continuous for the pseudometric 𝒲₂ of (2.5) at every point of Θ̂. -/
noncomputable def ContOnΘD {d : ℕ} {T : ℝ≥0} (f : ℝ≥0 → Measure (DPath d T) → ℝ) : Prop :=
  ∀ t μ, t ≤ T → IsP2D μ → ∀ ε > 0, ∃ δ > 0, ∀ t' μ', t' ≤ T → IsP2D μ' →
    W2ΘD t μ t' μ' < ENNReal.ofReal δ → |f t' μ' - f t μ| < ε

/-- `g : Θ̂ × Ω̂ → E` is continuous for 𝒲₂ + d_SK at every point of Θ̂ × Ω̂, where the distance
on the target `E` is `dist`. -/
noncomputable def ContOnΘΩD {d : ℕ} {T : ℝ≥0} {E : Type*} (dist : E → E → ℝ)
    (g : ℝ≥0 → Measure (DPath d T) → DPath d T → E) : Prop :=
  ∀ t μ ω, t ≤ T → IsP2D μ → ∀ ε > 0, ∃ δ > 0, ∀ t' μ' ω', t' ≤ T → IsP2D μ' →
    W2ΘD t μ t' μ' + dSK ω ω' < ENNReal.ofReal δ → dist (g t' μ' ω') (g t μ ω) < ε

/-! ### C^{1,1,1}(Θ̂) and C_b^{1,1,1}(Θ̂) (Definition 2.5, p. 944) -/

/-- A function `fn` on Θ̂ together with candidate derivatives `dt` (∂_t f), `dmu` (∂_μ f) and
`dwdmu` (∂_ω∂_μ f). -/
structure C111DataD (d : ℕ) (T : ℝ≥0) where
  /-- f : Θ̂ → ℝ -/
  fn : ℝ≥0 → Measure (DPath d T) → ℝ
  /-- ∂_t f : Θ̂ → ℝ -/
  dt : ℝ≥0 → Measure (DPath d T) → ℝ
  /-- ∂_μ f : Θ̂ × Ω̂ → ℝ^d -/
  dmu : ℝ≥0 → Measure (DPath d T) → DPath d T → SDEState d
  /-- ∂_ω∂_μ f : Θ̂ × Ω̂ → ℝ^{d×d} -/
  dwdmu : ℝ≥0 → Measure (DPath d T) → DPath d T → Matrix (Fin d) (Fin d) ℝ

/-- f ∈ C^{1,1,1}(Θ̂) with derivatives `Φ.dt`, `Φ.dmu`, `Φ.dwdmu` (Definition 2.5):
1. f and ∂_t f are continuous on Θ̂; ∂_μ f and ∂_ω∂_μ f are continuous on Θ̂ × Ω̂
   (matrices with the Frobenius distance);
2. (2.7): ∂_t f(t, μ̂) = lim_{δ↓0} [f(t + δ, μ̂_{[0,t]}) − f(t, μ̂)]/δ for t < T;
3. (2.16): 𝔼^μ̂[∂_μ f(t, μ̂, X̂) · ξ] = lim_{ε→0} [f(t, μ̂ ∘ (X̂ + εξ1_{[t,T]})⁻¹) − f(t, μ̂)]/ε
   for every F̂_t-measurable μ̂-square integrable ξ : Ω̂ → ℝ^d;
4. (2.18): ∂_ω∂_μ f(t, μ̂, ω̂) x = lim_{ε→0} [∂_μ f(t, μ̂, ω̂ + εx1_{[t,T]}) − ∂_μ f(t, μ̂, ω̂)]/ε;
5. ∂_μ f(t, μ̂, ·) and ∂_ω∂_μ f(t, μ̂, ·) are F̂_t-adapted: they depend on ω̂ only through ω̂_{t∧·}. -/
noncomputable def IsC111D {d : ℕ} {T : ℝ≥0} (Φ : C111DataD d T) : Prop :=
  ContOnΘD Φ.fn ∧
  ContOnΘD Φ.dt ∧
  ContOnΘΩD (fun x y => ‖x - y‖) Φ.dmu ∧
  ContOnΘΩD (fun A B => Real.sqrt (MasterVisc.Comparison.frob2 (A - B))) Φ.dwdmu ∧
  (∀ t μ, t < T → IsP2D μ →
    Tendsto (fun δ : ℝ => (Φ.fn (t + δ.toNNReal) (μ.map (stopD t)) - Φ.fn t μ) / δ)
      (𝓝[>] 0) (𝓝 (Φ.dt t μ))) ∧
  (∀ t μ, t ≤ T → IsP2D μ → ∀ ξ : DPath d T → SDEState d, Measurable[FD t] ξ →
    ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 ∂μ < ⊤ →
    HasDerivAt (fun ε : ℝ => Φ.fn t (μ.map (fun ω => bumpD t ω (ε • ξ ω))))
      (∫ ω, inner ℝ (Φ.dmu t μ ω) (ξ ω) ∂μ) 0) ∧
  (∀ t μ ω, t ≤ T → IsP2D μ → ∀ x : SDEState d,
    HasDerivAt (fun ε : ℝ => Φ.dmu t μ (bumpD t ω (ε • x)))
      (Matrix.toEuclideanLin (Φ.dwdmu t μ ω) x) 0) ∧
  (∀ t μ ω, t ≤ T → IsP2D μ →
    Φ.dmu t μ ω = Φ.dmu t μ (stopD t ω) ∧ Φ.dwdmu t μ ω = Φ.dwdmu t μ (stopD t ω))

/-- f ∈ C_b^{1,1,1}(Θ̂): f ∈ C^{1,1,1}(Θ̂), ∂_t f is bounded on Θ̂, and (2.19)
|∂_μ f(t, μ̂, ω̂)| + |∂_ω∂_μ f(t, μ̂, ω̂)| ≤ C[1 + ‖ω̂‖] on Θ̂ × Ω̂ (Frobenius norm on matrices). -/
noncomputable def IsC111bD {d : ℕ} {T : ℝ≥0} (Φ : C111DataD d T) : Prop :=
  IsC111D Φ ∧
  (∃ C : ℝ, ∀ t μ, t ≤ T → IsP2D μ → |Φ.dt t μ| ≤ C) ∧
  ∃ C : ℝ, ∀ t μ ω, t ≤ T → IsP2D μ →
    ‖Φ.dmu t μ ω‖ + Real.sqrt (MasterVisc.Comparison.frob2 (Φ.dwdmu t μ ω)) ≤ C * (1 + (supD ω).toReal)

end MasterVisc.Ito


