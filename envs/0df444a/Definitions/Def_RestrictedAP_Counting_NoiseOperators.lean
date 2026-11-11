-- Prove2me | Definitions.Def_RestrictedAP_Counting_NoiseOperators
-- name    : RestrictedAP_Counting_NoiseOperators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:19:51.844147+00:00
-- url     : https://prove2.me/theorems/3e7c2e26-6232-442e-969f-89ae4b8865a5
-- title:
--   Noise operators $T^{\otimes n}_{\rho,\nu}$, $T_{\nu,\mathcal P,I}$ and $T_{\nu,\mathcal P,1-\varepsilon}$
-- statement:
--   Let $\nu$ be a distribution on a finite alphabet $\Sigma$. For $\rho\in[0,1]$ the **noise operator** $T^{\otimes n}_{\rho,\nu}$ (Definition 2.6) sends $x\in\Sigma^n$ to $y$ with, independently for each $i$, $y_i=x_i$ with probability $\rho$ and $y_i\sim\nu$ otherwise; on functions, $T^{\otimes n}_{\rho,\nu}f(x)=\mathbb E_{y\sim T^{\otimes n}_{\rho,\nu}x}[f(y)]=\sum_y\prod_i\big(\rho\,\mathbf 1[x_i=y_i]+(1-\rho)\nu(y_i)\big)f(y)$. For $\mu$ on $\Sigma^3$ the same construction on the alphabet $\Sigma^3$ is the operator $T^{\otimes n}_{1-\kappa,\mu}$ of p. 20.
--
--   For a collection $\mathcal P$ of functions $\Sigma^n\to\mathbb D$ and $I\subseteq[n]$, $T_{\nu,\mathcal P,I}x$ (Definition 2.21) samples $y\sim\nu^{\otimes n}$ **conditioned on** $y_{\bar I}=x_{\bar I}$ and $P(y)=P(x)$ for all $P\in\mathcal P$; for $\varepsilon>0$, $T_{\nu,\mathcal P,1-\varepsilon}x$ first draws $I\subseteq_\varepsilon[n]$ (each $i$ independently with probability $\varepsilon$) and then $y\sim T_{\nu,\mathcal P,I}x$. On functions,
--   $$T_{\nu,\mathcal P,I}f(x)=\frac{\sum_{y\in C_I(x)}\nu^{\otimes n}(y)f(y)}{\sum_{y\in C_I(x)}\nu^{\otimes n}(y)},\qquad T_{\nu,\mathcal P,1-\varepsilon}f(x)=\sum_{I\subseteq[n]}\varepsilon^{|I|}(1-\varepsilon)^{n-|I|}\,T_{\nu,\mathcal P,I}f(x),$$
--   where $C_I(x)$ is the conditioning set.
--
--   **Formalization Note.** `noiseOp ν ρ n`, `condSet`, `condNoiseI ν 𝒫 I` and `condNoise ν 𝒫 ε` implement the displays. When the conditioning event has $\nu^{\otimes n}$-probability $0$ (possible only at points with $\nu^{\otimes n}(x)=0$, which are null in $L^2(\nu^{\otimes n})$), Lean's division gives the value $0$. The parameter `ε` of `condNoise` is the resampling probability, so `condNoise ν 𝒫 ε` is $T_{\nu,\mathcal P,1-\varepsilon}$.
-- source:
--   Bhangale, Khot, Liu, Minzer, A Counting Lemma for Somewhat Restricted 3-APs, arXiv:2608.17365 (copy sha256 de0b96c1…), p. 8, Definition 2.6; p. 12, Definition 2.21; p. 20

import Mathlib
import Definitions.Def_RestrictedAP_Counting_Distributions

namespace RestrictedAP.Counting

/-!
# Noise operators

Bhangale, Khot, Liu, Minzer, *A Counting Lemma for Somewhat Restricted 3-APs*,
arXiv:2608.17365 (copy sha256 de0b96c1…), p. 8, Definition 2.6; p. 12, Definition 2.21;
p. 20 (the noise operator `T^{⊗n}_{1−κ,μ}` on `(Σ^n)^3`).

* `noiseOp ν ρ n` is `T^{⊗n}_{ρ,ν}` (Definition 2.6), as an operator on functions
  `(Fin n → Ω) → ℂ`: coordinatewise, `y_i = x_i` with probability `ρ`, else `y_i ∼ ν`,
  independently, and `T f(x) = E_{y ∼ T x}[f(y)]`. Its transition weight is
  `∏_i (ρ·[x_i = y_i] + (1 − ρ)·ν(y_i))`. Applied to the alphabet `Sig × Sig × Sig` and a
  distribution `μ` on it, it is the operator `T^{⊗n}_{1−κ,μ}` of p. 20 (with `ρ = 1 − κ`).
* `condNoiseI ν 𝒫 I` is `T_{ν,𝒫,I}` (Definition 2.21): `y ∼ ν^{⊗n}` conditioned on
  `y_{Ī} = x_{Ī}` (the coordinates outside `I` are kept, those in `I` are resampled) and
  `P(y) = P(x)` for every `P ∈ 𝒫`. It is the ratio of two sums over the conditioning set
  `condSet 𝒫 I x`; when the conditioning event has `ν^{⊗n}`-probability `0` (only possible
  when `ν^{⊗n}(x) = 0`, a null point of `L²(ν^{⊗n})`) Lean's division gives the junk value `0`.
* `condNoise ν 𝒫 ε` is `T_{ν,𝒫,1−ε}`: `I ⊆_ε [n]` (each coordinate independently with
  probability `ε`), then `T_{ν,𝒫,I}`; i.e. the average of `T_{ν,𝒫,I}` with weights
  `ε^{|I|}(1−ε)^{n−|I|}`.
-/

open Classical

/-- One-coordinate transition weight of `T_{ρ,ν}` from `a` to `b`: `ρ·[a = b] + (1 − ρ)·ν(b)`. -/
noncomputable def noiseKernel {Ω : Type*} (ν : Ω → ℝ) (ρ : ℝ) (a b : Ω) : ℝ :=
  ρ * (if a = b then 1 else 0) + (1 - ρ) * ν b

/-- `T^{⊗n}_{ρ,ν} f(x) = E_{y ∼ T^{⊗n}_{ρ,ν} x}[f(y)]` (Definition 2.6). -/
noncomputable def noiseOp {Ω : Type*} [Fintype Ω] (ν : Ω → ℝ) (ρ : ℝ) (n : ℕ)
    (f : (Fin n → Ω) → ℂ) : (Fin n → Ω) → ℂ :=
  fun x => ∑ y, ((∏ i, noiseKernel ν ρ (x i) (y i) : ℝ) : ℂ) * f y

/-- The conditioning set of `T_{ν,𝒫,I} x`: the points `y` with `y_i = x_i` for `i ∉ I` and
`P(y) = P(x)` for every `P ∈ 𝒫`. -/
noncomputable def condSet {Ω : Type*} [Fintype Ω] {n : ℕ} (PP : Finset ((Fin n → Ω) → ℂ))
    (I : Finset (Fin n)) (x : Fin n → Ω) : Finset (Fin n → Ω) :=
  Finset.univ.filter (fun y => (∀ i, i ∉ I → y i = x i) ∧ ∀ P ∈ PP, P y = P x)

/-- `T_{ν,𝒫,I} f(x) = E[f(y)]` for `y ∼ ν^{⊗n}` conditioned on `y_{Ī} = x_{Ī}` and
`P(y) = P(x)` for all `P ∈ 𝒫` (Definition 2.21). -/
noncomputable def condNoiseI {Ω : Type*} [Fintype Ω] {n : ℕ} (ν : Ω → ℝ)
    (PP : Finset ((Fin n → Ω) → ℂ)) (I : Finset (Fin n)) (f : (Fin n → Ω) → ℂ)
    (x : Fin n → Ω) : ℂ :=
  (∑ y ∈ condSet PP I x, (tensorPow ν n y : ℂ) * f y) /
    ((∑ y ∈ condSet PP I x, tensorPow ν n y : ℝ) : ℂ)

/-- `T_{ν,𝒫,1−ε} f(x) = E_{I ⊆_ε [n]} [T_{ν,𝒫,I} f(x)]` (Definition 2.21). -/
noncomputable def condNoise {Ω : Type*} [Fintype Ω] {n : ℕ} (ν : Ω → ℝ)
    (PP : Finset ((Fin n → Ω) → ℂ)) (ε : ℝ) (f : (Fin n → Ω) → ℂ) : (Fin n → Ω) → ℂ :=
  fun x => ∑ I : Finset (Fin n),
    ((ε ^ I.card * (1 - ε) ^ (n - I.card) : ℝ) : ℂ) * condNoiseI ν PP I f x

end RestrictedAP.Counting


