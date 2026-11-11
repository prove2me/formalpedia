-- Prove2me | Definitions.Def_QaryCVP_ent3
-- name    : QaryCVP_ent3
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:21.899691+00:00
-- url     : https://prove2.me/theorems/fdfa0d4f-c1dd-410e-944a-4edaecf9ceb2
-- title:
--   Entropy rates $h_i,r_i,d_i$, the exponents $T_{\rm in},S_{\rm in}$, the parameter conditions (3), (5), (8), theta sums and the high-density profile
-- statement:
--   **Entropy.** $H(p_1,p_2,p_3)=-\sum_i p_i\log_2 p_i$ with $0\log0=0$, and $h(t)=H(t,1-t)$ (Definition 2.1; $h$ is the published `WildeQIT.binaryEntropy`).
--
--   **Rates (4), (5).** For proportions $t_0,\dots,t_k$, $h_i=H(t_i,t_i,1-2t_i)$ and, for $1\le i\le k$,
--
--   $$r_i=2t_{i-1}+(1-2t_{i-1})\,H\Big(\tfrac{t_i-t_{i-1}/2}{1-2t_{i-1}},\tfrac{t_i-t_{i-1}/2}{1-2t_{i-1}},\tfrac{1-t_{i-1}-2t_i}{1-2t_{i-1}}\Big),$$
--
--   $d_0=\rho$, $d_i=r_i-\eta$.
--
--   **Exponents (9).** With $[a]_+=\max\{a,0\}$,
--
--   $$T_{\rm in}=\max\Big\{\tfrac{h_k}{2},\max_{1\le i\le k}\big([h_i-d_i]_++[h_i-d_{i-1}]_+\big)\Big\},\qquad S_{\rm in}=\max\Big\{\tfrac{h_k}{2},\max_{0\le i<k}[h_i-d_i]_+,[h_k-d_{k-1}]_+\Big\}.$$
--
--   **Conditions.** Coordinate conditions: $0<t_i<1/2$ and (3) $t_{i-1}/2\le t_i\le(1-t_{i-1})/2$ (strict version with $<$). Equation conditions (5): $\rho=d_0>d_1>\dots>d_k>0$. Even-modulus conditions (8): $h(2t_0)>\rho/2$, $h(2t_i)>d_{i-1}/2$, $r_i>d_i/2+2t_i-t_{i-1}$. The sign count is $a_0=2^k\lfloor t_0n/2^k\rfloor$ and $T$ is the set of vectors in $\{-1,0,1\}^n$ with exactly $a_0$ entries of each nonzero sign. "$m\log q=\rho n+o(n)$" for sequences $q(n),m(n)$ is $(m\log_2q-\rho n)/n\to0$.
--
--   **Theta sums (48), (10), (24).** $\Theta_u(a)=\sum_{j\in\mathbb Z}e^{-a(j-u)^2}$, $\Theta(a)=\Theta_0(a)$; condition (10) is $\Theta_u(a)\le\Theta(a)e^{-a\tau u^2}$ for $|u|\le1/2$ (with $\tau=\gamma^{-2}$ it is (22)); $e(a,c,\gamma)=(ac/\gamma^2+\ln\Theta(a))/(2\ln2)$.
--
--   **High-density profile (12)–(14), (32).** $u_\delta\in(0,1/3)$ solves $H(u,u,1-2u)=\delta$; $t_i=(u_\delta+10^{-7}+\theta)c_i$ with $(c_0,\dots,c_3)=(1,0.7,0.47,0.24)$; $T_>(\delta)=\max\{T_{\rm in}(\delta),e(a,c(\delta),\gamma)\}$, $S_>(\delta)=\max\{S_{\rm in}(\delta),e(a,c(\delta),\gamma)/2\}$ with $k=3$, $\rho=\delta$, $\eta=10^{-8}$, $c=2t_0+2\cdot10^{-5}$, $a=4.138$, $\gamma=5/3$.
--
--   **Formalization Note** Logarithms are base two except $\ln$ (R11). $u_\delta$ is the infimum of the root set, which for $\delta\in[1,3/2]$ is a singleton. $T_>$ and $S_>$ carry the perturbation $\theta$ of Lemma F.5; (32) is $\theta=0$.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Definition 2.1, p.13; (3)–(5), pp.15–16; (8), p.20; (9), p.24; (10), p.28; (12)–(14), p.34; (24), p.41; (32), p.46; (48), p.62

import Mathlib
import Definitions.Def_WildeQIT_binaryEntropy

open Filter Topology

namespace QaryCVP

/-- Shannon entropy in bits of a three-point distribution, `H(p₁, p₂, p₃) = −Σ pᵢ log₂ pᵢ` with
`0 log 0 = 0` (Definition 2.1, p.13).
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), Definition 2.1, p.13.

**Formalization Note.** `Real.negMulLog x = −x ln x` (zero at `0`), divided by `ln 2` (R11:
`log` is base two). The binary entropy `h(t) = H(t, 1 − t)` is the published
`WildeQIT.binaryEntropy`. -/
noncomputable def ent3 (a b c : ℝ) : ℝ :=
  (Real.negMulLog a + Real.negMulLog b + Real.negMulLog c) / Real.log 2

/-- The binary entropy `h(t) = H(t, 1 − t)` in bits (Definition 2.1, p.13). -/
noncomputable abbrev binEnt (t : ℝ) : ℝ := WildeQIT.binaryEntropy t

/-- `[a]₊ = max{a, 0}` (§2.1, p.12). -/
noncomputable def posPart (a : ℝ) : ℝ := max a 0

/-- The level rate `hᵢ = H(tᵢ, tᵢ, 1 − 2tᵢ)` of (4), p.16. The proportions are a sequence
`t : ℕ → ℝ`, of which only `t 0, …, t k` are used. -/
noncomputable def hRate (t : ℕ → ℝ) (i : ℕ) : ℝ := ent3 (t i) (t i) (1 - 2 * t i)

/-- The decomposition rate `rᵢ` of (4), p.16, for `1 ≤ i ≤ k`:
`rᵢ = 2tᵢ₋₁ + (1 − 2tᵢ₋₁) H(x, x, (1 − tᵢ₋₁ − 2tᵢ)/(1 − 2tᵢ₋₁))`,
`x = (tᵢ − tᵢ₋₁/2)/(1 − 2tᵢ₋₁)`. -/
noncomputable def rRate (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  let s := t (i - 1)
  let x := (t i - s / 2) / (1 - 2 * s)
  2 * s + (1 - 2 * s) * ent3 x x ((1 - s - 2 * t i) / (1 - 2 * s))

/-- The congruence rates of (5), p.16: `d₀ = ρ`, `dᵢ = rᵢ − η` for `i ≥ 1`. -/
noncomputable def dRate (ρ η : ℝ) (t : ℕ → ℝ) (i : ℕ) : ℝ :=
  if i = 0 then ρ else rRate t i - η

/-- The time exponent `T_in` of (9), p.24:
`T_in = max{h_k/2, max_{1≤i≤k}([hᵢ − dᵢ]₊ + [hᵢ − dᵢ₋₁]₊)}`. -/
noncomputable def Tin (k : ℕ) (ρ η : ℝ) (t : ℕ → ℝ) : ℝ :=
  (Finset.Icc 1 k).fold max (hRate t k / 2)
    (fun i => posPart (hRate t i - dRate ρ η t i) + posPart (hRate t i - dRate ρ η t (i - 1)))

/-- The space exponent `S_in` of (9), p.24:
`S_in = max{h_k/2, max_{0≤i<k}[hᵢ − dᵢ]₊, [h_k − d_{k−1}]₊}`. -/
noncomputable def Sin (k : ℕ) (ρ η : ℝ) (t : ℕ → ℝ) : ℝ :=
  max ((Finset.range k).fold max (hRate t k / 2) (fun i => posPart (hRate t i - dRate ρ η t i)))
    (posPart (hRate t k - dRate ρ η t (k - 1)))

/-- The coordinate conditions (p.15): `0 < tᵢ < 1/2` for `0 ≤ i ≤ k` and (3),
`tᵢ₋₁/2 ≤ tᵢ ≤ (1 − tᵢ₋₁)/2` for `1 ≤ i ≤ k`. -/
def CoordCond (k : ℕ) (t : ℕ → ℝ) : Prop :=
  (∀ i ≤ k, 0 < t i ∧ t i < 1 / 2) ∧
    ∀ i, 1 ≤ i → i ≤ k → t (i - 1) / 2 ≤ t i ∧ t i ≤ (1 - t (i - 1)) / 2

/-- The strict coordinate conditions (p.22, "Uniformity over parameter choices"; Appendix F.2,
p.93): `0 < tᵢ < 1/2` and `tᵢ₋₁/2 < tᵢ < (1 − tᵢ₋₁)/2`. -/
def StrictCoordCond (k : ℕ) (t : ℕ → ℝ) : Prop :=
  (∀ i ≤ k, 0 < t i ∧ t i < 1 / 2) ∧
    ∀ i, 1 ≤ i → i ≤ k → t (i - 1) / 2 < t i ∧ t i < (1 - t (i - 1)) / 2

/-- The equation conditions (5), p.16: `ρ = d₀ > d₁ > ⋯ > d_k > 0`. -/
def EqCond (k : ℕ) (ρ η : ℝ) (t : ℕ → ℝ) : Prop :=
  (∀ i, i < k → dRate ρ η t (i + 1) < dRate ρ η t i) ∧ 0 < dRate ρ η t k

/-- The even-modulus (parity) conditions (8), p.20: `h(2t₀) > ρ/2` and, for `1 ≤ i ≤ k`,
`h(2tᵢ) > dᵢ₋₁/2`, `rᵢ > dᵢ/2 + 2tᵢ − tᵢ₋₁`. -/
def ParityCond (k : ℕ) (ρ η : ℝ) (t : ℕ → ℝ) : Prop :=
  ρ / 2 < binEnt (2 * t 0) ∧
    ∀ i, 1 ≤ i → i ≤ k →
      dRate ρ η t (i - 1) / 2 < binEnt (2 * t i) ∧
        dRate ρ η t i / 2 + 2 * t i - t (i - 1) < rRate t i

/-- The integral sign count `a₀ = 2^k ⌊t₀ n / 2^k⌋` (p.15). -/
noncomputable def signCount0 (k : ℕ) (t0 : ℝ) (n : ℕ) : ℕ :=
  2 ^ k * ⌊t0 * n / 2 ^ k⌋₊

/-- `T = T₀` (p.15): vectors of `{−1, 0, 1}ⁿ` with exactly `a` entries equal to `1` and exactly `a`
entries equal to `−1`. -/
def ternarySet (n a : ℕ) : Set (Fin n → ℤ) :=
  {x | (∀ i, x i = -1 ∨ x i = 0 ∨ x i = 1) ∧
    (Finset.univ.filter (fun i => x i = 1)).card = a ∧
    (Finset.univ.filter (fun i => x i = -1)).card = a}

/-- The asymptotic input condition of Lemma 3.2 (p.20): integers `q = qs n` and `m = ms n` depend
on `n` with `m log q = ρn + o(n)`, i.e. `(m log₂ q − ρn)/n → 0`. -/
def RateSeq (ρ : ℝ) (qs ms : ℕ → ℕ) : Prop :=
  Tendsto (fun n : ℕ => ((ms n : ℝ) * Real.logb 2 (qs n) - ρ * n) / n) atTop (𝓝 0)

/-- The theta sums of (48), p.62: `Θ_u(a) = Σ_{j∈Z} e^{−a(j−u)²}`. The series converges for
`a > 0`; every statement using it has `a > 0`. -/
noncomputable def thetaU (a u : ℝ) : ℝ := ∑' j : ℤ, Real.exp (-a * ((j : ℝ) - u) ^ 2)

/-- `Θ(a) = Θ₀(a)` (48), p.62. -/
noncomputable def theta (a : ℝ) : ℝ := thetaU a 0

/-- The shifted-theta condition (10), p.28: `Θ_u(a) ≤ Θ(a) e^{−aτu²}` for `|u| ≤ 1/2`. With
`τ = γ^{−2}` it is (22), p.41. -/
def ThetaCond (τ a : ℝ) : Prop :=
  ∀ u : ℝ, |u| ≤ 1 / 2 → thetaU a u ≤ theta a * Real.exp (-a * τ * u ^ 2)

/-- The exact-search exponent (24), p.41: `e(a, c, γ) = (ac/γ² + ln Θ(a))/(2 ln 2)`. -/
noncomputable def eCost (a c γ : ℝ) : ℝ := (a * c / γ ^ 2 + Real.log (theta a)) / (2 * Real.log 2)

/-- `u_δ`, the solution in `(0, 1/3)` of `H(u, u, 1 − 2u) = δ` (12), p.34.

**Formalization Note.** Defined as the infimum of the solution set; for `δ ∈ [1, 3/2]` the entropy
is strictly increasing on `(0, 1/3)` (p.34), so the set is a singleton and the infimum is the
root. Outside that range the value is not used. -/
noncomputable def uDelta (δ : ℝ) : ℝ :=
  sInf {u : ℝ | 0 < u ∧ u < 1 / 3 ∧ ent3 u u (1 - 2 * u) = δ}

/-- The coordinate ratios `(c₀, c₁, c₂, c₃) = (1, 7/10, 47/100, 6/25)` of (13), p.34. -/
noncomputable def profC (i : ℕ) : ℝ :=
  if i = 0 then 1 else if i = 1 then 7 / 10 else if i = 2 then 47 / 100 else 6 / 25

/-- The proportions of Lemma F.5 (p.102): `tᵢ = (u_δ + 10⁻⁷ + θ) cᵢ`; at `θ = 0` these are the
limiting proportions `tᵢ(δ)` of (13), p.34. -/
noncomputable def profT (δ θ : ℝ) (i : ℕ) : ℝ := (uDelta δ + 1 / 10 ^ 7 + θ) * profC i

/-- The high-density time exponent of (32), p.46, at the proportions `profT δ θ`:
`T_>(δ) = max{T_in(δ), e(a, c(δ), γ)}` with `k = 3`, `ρ = δ`, `η = 10⁻⁸`, `c = 2t₀ + 2·10⁻⁵`,
`a = 4.138`, `γ = 5/3`. At `θ = 0` this is (32) exactly. -/
noncomputable def Tgt (δ θ : ℝ) : ℝ :=
  max (Tin 3 δ (1 / 10 ^ 8) (profT δ θ))
    (eCost (4138 / 1000) (2 * profT δ θ 0 + 2 / 10 ^ 5) (5 / 3))

/-- The high-density space exponent of (32), p.46:
`S_>(δ) = max{S_in(δ), e(a, c(δ), γ)/2}`, same parameters as `Tgt`. -/
noncomputable def Sgt (δ θ : ℝ) : ℝ :=
  max (Sin 3 δ (1 / 10 ^ 8) (profT δ θ))
    (eCost (4138 / 1000) (2 * profT δ θ 0 + 2 / 10 ^ 5) (5 / 3) / 2)

end QaryCVP


