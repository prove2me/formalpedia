-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_RSSC
-- name    : ZeroFreeRRG_Hardcore_RSSC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:35:37.312498+00:00
-- url     : https://prove2.me/theorems/2cc7aa19-3f23-4d36-a74e-4ffca4b9cc8f
-- title:
--   Random holomorphic functions in H(D), the product W, and conditions (B0)–(B5) of reinforced small subgraph conditioning
-- statement:
--   For an open connected $D\subseteq\mathbb C$, $H(D)$ is the space of holomorphic functions on $D$ with the topology of locally uniform convergence ($\|f\|_K=\sup_K|f|$ for compact $K\subset D$). A random element $Y_n$ of $H(D)$ has $A_n(z)=\mathbb E[Y_n(z)]$ and $F_n=Y_n/A_n$. With independent $Z_\ell\sim\mathrm{Poisson}(\lambda_\ell)$, $\lambda_\ell>0$ and $\delta_\ell\in H(D)$, the formal product and its partial products are
--   $$W(z)=\prod_{\ell\ge1}(1+\delta_\ell(z))^{Z_\ell}e^{-\lambda_\ell\delta_\ell(z)},\qquad W_N=\prod_{\ell=1}^N(1+\delta_\ell)^{Z_\ell}e^{-\lambda_\ell\delta_\ell}\quad(0^0=1).$$
--   Conditions of Theorem 3.2, for a nonempty open interval $I\subseteq D\cap\mathbb R$: (B0) $A_n$ finite, holomorphic and nowhere zero on $D$ for all large $n$, and $Y_n(t)\ge0$ a.s. for $t\in I$; (B1) $(X_{1,n},\dots,X_{m,n})\to_d(Z_1,\dots,Z_m)$; (B2) $\mathbb E[F_n(t)\prod_\ell(X_{\ell,n})_{j_\ell}]\to\prod_\ell[\lambda_\ell(1+\delta_\ell(t))]^{j_\ell}$ for $t\in I$; (B3) $\sum_\ell\lambda_\ell\sup_K|\delta_\ell|^2<\infty$ for compact $K\subset D$; (B4) $\limsup_n\mathbb E[F_n(t)^2]\le\exp(\sum_\ell\lambda_\ell\delta_\ell(t)^2)$ for $t\in I$; (B5) $\limsup_n\sup_K\mathbb E|F_n|^2<\infty$ for compact $K\subset D$.
--
--   **Formalization Note.** Index $i\in\mathbb N$ stands for $\ell=i+1$. `HFun D` is `ℂ →ᵤ[compacts of D] ℂ` with its Borel σ-algebra; `HSet D` its holomorphic-on-$D$ points (values off $D$ are topologically invisible). `IsRandomHol` = every realization holomorphic on $D$ and measurable into `HFun D`. `Wlim` is the pointwise limit (`limUnder`) of `Wpartial`. In (B0) "finite" is integrability of $Y_n(z)$; $\ge0$ is the order of $\mathbb C$. In (B2) the expectations are required finite for large $n$. In (B4) $F_n(t)^2$ and $\delta_\ell(t)^2$ are written as squared moduli, equal because $F_n(t)\ge0$ and $\delta_\ell(t)$ is real on $I$ (p. 20). (B1) is stated by point probabilities, equivalent for $\mathbb N^m$-valued vectors. Suprema and the series of (B3), (B5) are in $[0,\infty]$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 17 (H(D), random elements, convergence); p. 18 (A_n, F_n, W, Theorem 3.2 (B0)–(B5)); p. 19 (W_N)

import Mathlib

open scoped Classical UniformConvergence ComplexOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

namespace ZeroFreeRRG.Hardcore

/-! Setting of the reinforced small subgraph conditioning theorem (Chen, Wang, Zhang,
arXiv:2610.40510, §2.4 p. 17 and §3 pp. 18–19).

**Index convention.** The cycle data `X_{ℓ,n}`, `Z_ℓ`, `λ_ℓ`, `δ_ℓ` (`ℓ ≥ 1`) are stored at index
`i = ℓ − 1 ∈ ℕ`: `X n i`, `Z i`, `lam i`, `δ i` stand for `X_{i+1,n}`, `Z_{i+1}`, `λ_{i+1}`,
`δ_{i+1}`. -/

/-- The compact subsets of `D`. -/
def compactsIn (D : Set ℂ) : Set (Set ℂ) := {K | IsCompact K ∧ K ⊆ D}

/-- Functions `ℂ → ℂ` with the topology of locally uniform convergence on `D` (uniform convergence on
every compact `K ⊆ D`, `‖f‖_K = sup_K |f|`, §2.4 p. 17). The space `H(D)` of the source is the subset
of functions holomorphic on `D` (`HSet D`); values off `D` play no role (functions agreeing on `D` are
topologically indistinguishable). -/
abbrev HFun (D : Set ℂ) : Type := ℂ →ᵤ[compactsIn D] ℂ

/-- The Borel σ-algebra of the locally uniform topology. -/
noncomputable instance (D : Set ℂ) : MeasurableSpace (HFun D) := borel (HFun D)

/-- A function `ℂ → ℂ` as a point of `HFun D`. -/
def toH (D : Set ℂ) (f : ℂ → ℂ) : HFun D := UniformOnFun.ofFun (compactsIn D) f

/-- `H(D)`: the functions holomorphic on `D`, as a subset of `HFun D`. -/
def HSet (D : Set ℂ) : Set (HFun D) :=
  {f | DifferentiableOn ℂ ((UniformOnFun.toFun (compactsIn D)) f) D}

/-- `Y` is a random element of `H(D)` on `(Ω, P)`: every realization is holomorphic on `D`, and
`ω ↦ Y ω` is measurable for the Borel σ-algebra of the locally uniform topology. -/
def IsRandomHol {Ω : Type*} [MeasurableSpace Ω] (D : Set ℂ) (Y : Ω → ℂ → ℂ) : Prop :=
  (∀ ω, DifferentiableOn ℂ (Y ω) D) ∧ Measurable (fun ω => toH D (Y ω))

/-- `A_n(z) = E[Y_n(z)]` (§3, p. 18). -/
noncomputable def meanFn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℂ → ℂ)
    (z : ℂ) : ℂ :=
  ∫ ω, Y ω z ∂P

/-- `F_n = Y_n / A_n` (§3, p. 18), used where `A_n` is finite and nowhere zero. -/
noncomputable def normalizedFn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → ℂ → ℂ)
    (ω : Ω) (z : ℂ) : ℂ :=
  Y ω z / meanFn P Y z

/-- `(Z_ℓ)_{ℓ ≥ 1}` are independent with `Z_ℓ ∼ Poisson(λ_ℓ)` (index `i = ℓ − 1`). -/
def IsIndepPoisson {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℕ → Ω → ℕ)
    (lam : ℕ → ℝ) : Prop :=
  (∀ i, Measurable (Z i)) ∧ iIndepFun Z P ∧ ∀ i, P.map (Z i) = poissonMeasure (lam i).toNNReal

/-- The partial products `W_N(z) = ∏_{ℓ=1}^N (1 + δ_ℓ(z))^{Z_ℓ} exp{−λ_ℓ δ_ℓ(z)}` (p. 19), with
`0^0 = 1`. -/
noncomputable def Wpartial {Ω : Type*} (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ) (Z : ℕ → Ω → ℕ) (N : ℕ)
    (ω : Ω) (z : ℂ) : ℂ :=
  ∏ i ∈ Finset.range N, (1 + δ i z) ^ (Z i ω) * Complex.exp (-(lam i : ℂ) * δ i z)

/-- The formal product `W(z) = ∏_{ℓ ≥ 1} (1 + δ_ℓ(z))^{Z_ℓ} exp{−λ_ℓ δ_ℓ(z)}` (p. 18), as the
pointwise limit of the partial products (Lean's `limUnder` returns a junk value where the limit does
not exist; the theorems assert where it does). -/
noncomputable def Wlim {Ω : Type*} (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ) (Z : ℕ → Ω → ℕ) (ω : Ω)
    (z : ℂ) : ℂ :=
  limUnder atTop (fun N => Wpartial lam δ Z N ω z)

variable {Ωs : ℕ → Type*} [∀ n, MeasurableSpace (Ωs n)]

/-- (B0): `A_n` is finite, holomorphic and nowhere zero on `D` for all sufficiently large `n`, and
`Y_n(t) ≥ 0` almost surely for every `t ∈ I` (for every `n`). "Finite" is integrability of `Y_n(z)`
for every `z ∈ D`; `Y_n(t) ≥ 0` is the order of `ℂ` (real and nonnegative). -/
def CondB0 (P : ∀ n, Measure (Ωs n)) (Y : ∀ n, Ωs n → ℂ → ℂ) (D : Set ℂ) (I : Set ℝ) : Prop :=
  (∀ᶠ n in atTop, (∀ z ∈ D, Integrable (fun ω => Y n ω z) (P n)) ∧
      DifferentiableOn ℂ (meanFn (P n) (Y n)) D ∧ ∀ z ∈ D, meanFn (P n) (Y n) z ≠ 0) ∧
    ∀ n, ∀ t ∈ I, ∀ᵐ ω ∂(P n), (0 : ℂ) ≤ Y n ω t

/-- (B1): for each fixed `m ≥ 1`, `(X_{1,n}, …, X_{m,n}) →d (Z_1, …, Z_m)`; for `ℕ^m`-valued
vectors this is convergence of every point probability. -/
def CondB1 (P : ∀ n, Measure (Ωs n)) (X : ∀ n, ℕ → Ωs n → ℕ) {Ω₀ : Type*} [MeasurableSpace Ω₀]
    (P₀ : Measure Ω₀) (Z : ℕ → Ω₀ → ℕ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ j : Fin m → ℕ,
    Tendsto (fun n => (P n).real {ω | ∀ i : Fin m, X n i ω = j i}) atTop
      (𝓝 (P₀.real {ω | ∀ i : Fin m, Z i ω = j i}))

/-- (B2) at `t`: for fixed `m ≥ 1` and `j_1, …, j_m ≥ 0`,
`E[F_n(t) ∏_{ℓ=1}^m (X_{ℓ,n})_{j_ℓ}] → ∏_{ℓ=1}^m [λ_ℓ (1 + δ_ℓ(t))]^{j_ℓ}` (falling factorials);
the expectations are finite for all large `n`. -/
def CondB2At (P : ∀ n, Measure (Ωs n)) (Y : ∀ n, Ωs n → ℂ → ℂ) (X : ∀ n, ℕ → Ωs n → ℕ)
    (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ) (t : ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → ∀ j : Fin m → ℕ,
    (∀ᶠ n in atTop, Integrable (fun ω => normalizedFn (P n) (Y n) ω t *
        ∏ i : Fin m, (((X n i ω).descFactorial (j i) : ℕ) : ℂ)) (P n)) ∧
    Tendsto (fun n => ∫ ω, normalizedFn (P n) (Y n) ω t *
        ∏ i : Fin m, (((X n i ω).descFactorial (j i) : ℕ) : ℂ) ∂(P n)) atTop
      (𝓝 (∏ i : Fin m, ((lam i : ℂ) * (1 + δ i t)) ^ (j i)))

/-- (B3): `∑_{ℓ ≥ 1} λ_ℓ sup_{z ∈ K} |δ_ℓ(z)|² < ∞` for every compact `K ⊂ D`. -/
def CondB3 (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ D →
    ∑' i, ENNReal.ofReal (lam i) * (⨆ z ∈ K, ‖δ i z‖ₑ ^ 2) < ∞

/-- (B4) at `t`: `limsup_n E[F_n(t)²] ≤ exp(∑_{ℓ ≥ 1} λ_ℓ δ_ℓ(t)²)`. Since `F_n(t) ≥ 0`,
`F_n(t)² = |F_n(t)|²`; `δ_ℓ(t)` is real under (B0) and (B2) (p. 20), so `δ_ℓ(t)² = |δ_ℓ(t)|²`. -/
def CondB4At (P : ∀ n, Measure (Ωs n)) (Y : ∀ n, Ωs n → ℂ → ℂ) (lam : ℕ → ℝ) (δ : ℕ → ℂ → ℂ)
    (t : ℝ) : Prop :=
  limsup (fun n => ∫⁻ ω, ‖normalizedFn (P n) (Y n) ω t‖ₑ ^ 2 ∂(P n)) atTop ≤
    ENNReal.ofReal (Real.exp (∑' i, lam i * ‖δ i t‖ ^ 2))

/-- (B5): `limsup_n sup_{z ∈ K} E[|F_n(z)|²] < ∞` for every compact `K ⊂ D`. -/
def CondB5 (P : ∀ n, Measure (Ωs n)) (Y : ∀ n, Ωs n → ℂ → ℂ) (D : Set ℂ) : Prop :=
  ∀ K : Set ℂ, IsCompact K → K ⊆ D →
    limsup (fun n => ⨆ z ∈ K, ∫⁻ ω, ‖normalizedFn (P n) (Y n) ω z‖ₑ ^ 2 ∂(P n)) atTop < ∞

end ZeroFreeRRG.Hardcore


