-- Prove2me | Definitions.Def_UnknownLoads_Coxian_NicePaths
-- name    : UnknownLoads_Coxian_NicePaths
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:53.540393+00:00
-- url     : https://prove2.me/theorems/bf6e8ff3-0f34-4504-842a-0af74d8c7aed
-- title:
--   §6.1–§6.2.1 — convergence in ϱ, Proposition 14's relative-compactness property, and the set Ω_T of nice sample paths
-- statement:
--   Let a system of the coupled construction and a horizon $T > 0$ be fixed.
--
--   1. **Convergence with respect to $\varrho$.** A sequence of paths $F_k : [0,T] \to \mathbb R^{X}$ ($X$ countable) converges to $g$ with respect to the metric $\varrho(x,y) = \sup_{t\in[0,T]} \sum_i \min\{|x(t,\nu_i)-y(t,\nu_i)|,1\}2^{-i}$ iff every coordinate $F_k(\cdot,x)$ converges to $g(\cdot,x)$ uniformly over $[0,T]$ (p. 38).
--   2. **Relative compactness with Lipschitz limits.** $\{F_n\}$ is relatively compact with respect to $\varrho$ (every subsequence has a further subsequence converging with respect to $\varrho$), and the limit of every convergent subsequence has Lipschitz coordinates on $[0,T]$.
--   3. **Proposition 14's property at $\omega$** (defining $\Gamma_T$): the sequences $\{\mathcal A_n(\omega)\}$, $\{\mathcal P_n(\omega,m)\}$, $\{\mathcal D_n(\omega,m)\}$ for every phase $m$, and $\{s_n(\omega)\}$ have property 2.
--   4. **Nice sample paths $\Omega_T$ with constant $B_T$** (Proposition 16): $\omega$ is nice if the equations (21a)–(21b) hold at $\omega$ for every $n \ge 1$, Proposition 14's property holds at $\omega$, there is $n_T(\omega)$ with
--   $$q_n(\omega,t,B_T+1) = 0 \quad\text{and}\quad \ell_n(\omega,t) \le B_T \qquad \forall t\in[0,T],\ \forall n \ge n_T(\omega), \tag{23}$$
--   and
--   $$\lim_{n\to\infty} s_n(0) = s(0),\qquad \lim_{n\to\infty}\sup_{t\in[0,T]}\Big|\tfrac1n\mathcal N^\lambda_n(t) - \lambda t\Big| = 0,\qquad \lim_{n\to\infty}\sup_{t\in[0,\mu_i\nu(i)T]}\Big|\tfrac1n\mathcal N_{(\nu,i,j)}(nt) - t\Big| = 0 \tag{24}$$
--   for all $(\nu,i,j) \in \mathbb N^r\times\{1,\dots,r\}\times\{0,1\}$.
--
--   Propositions 17 and 18 are statements about every nice $\omega$; Proposition 16 says that almost every $\omega$ is nice.
--
--   **Formalization Note** The paper's $\Omega_T$ is *some* set of probability one with the properties of Proposition 16. It is rendered as the predicate `IsNicePath sys T B_T ω`, the conjunction of exactly the properties the paper lists; "for each $\omega \in \Omega_T$" becomes "for every $\omega$ and $B_T$ with `IsNicePath sys T B_T ω`". Relative compactness in $D_{\mathbb R^{\mathbb N^r}}[0,T]$ is rendered sequentially through subsequences given by strictly increasing maps $\varphi : \mathbb N \to \mathbb N$; the limit is not required to be càdlàg because a uniform limit of càdlàg paths is càdlàg. Limits in (24) are uniform convergence on the stated intervals; the phase $i$ is `Fin r` index $i-1$ and the Poisson index is $i$.
-- source:
--   Goldsztajn, Borst & van Leeuwaarden, Learning and balancing unknown loads in large-scale systems, arXiv:2012.10142v3, pp. 37–38 (metrics d, ϱ), p. 40 (Proposition 14), p. 41 (Proposition 16, (23), (24a)–(24c))

import Mathlib
import Definitions.Def_UnknownLoads_Coxian_Construction

namespace UnknownLoads.Coxian

/-! Goldsztajn, Borst & van Leeuwaarden, arXiv:2012.10142v3, §6.1 (pp. 37–40) and §6.2.1
(p. 41): convergence with respect to `ϱ` (coordinatewise uniform convergence on `[0, T]`,
p. 38), the relative-compactness property of Proposition 14, and the set `Ω_T` of nice sample
paths of Proposition 16, rendered as a predicate on `ω`. -/

open MeasureTheory Filter Topology

variable {P : Params} {Ω : Type*} [MeasurableSpace Ω] {μP : Measure Ω}

/-- Convergence of a sequence of paths `F k : ℝ → (X → ℝ)` to `g` with respect to `ϱ` on
`[0, T]`, i.e. uniform convergence over `[0, T]` of every coordinate (p. 38). -/
def RhoConverges {X : Type*} (F : ℕ → ℝ → X → ℝ) (g : ℝ → X → ℝ) (T : ℝ) : Prop :=
  ∀ x, TendstoUniformlyOn (fun k t => F k t x) (fun t => g t x) atTop (Set.Icc 0 T)

/-- The sequence `{F n}` is relatively compact with respect to `ϱ` on `[0, T]` (every
subsequence has a further subsequence converging with respect to `ϱ`), and the limit of every
convergent subsequence has Lipschitz coordinates on `[0, T]`. -/
def RelCompactLipLimits {X : Type*} (F : ℕ → ℝ → X → ℝ) (T : ℝ) : Prop :=
  (∀ φ : ℕ → ℕ, StrictMono φ →
      ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ ∃ g : ℝ → X → ℝ, RhoConverges (fun k => F (φ (ψ k))) g T) ∧
  (∀ φ : ℕ → ℕ, StrictMono φ → ∀ g : ℝ → X → ℝ, RhoConverges (fun k => F (φ k)) g T →
      ∀ x, ∃ K : NNReal, LipschitzOnWith K (fun t => g t x) (Set.Icc 0 T))

/-- The property of Proposition 14 at `ω` (the defining property of `Γ_T`): the sequences
`{𝒜_n(ω)}`, `{𝒫_n(ω, m)}`, `{𝒟_n(ω, m)}` (each `m`) and `{s_n(ω)}` are relatively compact with
respect to `ϱ` on `[0, T]`, with Lipschitz subsequential limits. -/
def Prop14Property (sys : System P Ω μP) (T : ℝ) (ω : Ω) : Prop :=
  RelCompactLipLimits (fun n => sys.A n ω) T ∧
  (∀ m : Fin P.r, RelCompactLipLimits (fun n t ν => sys.Ptr n ω t ν m) T) ∧
  (∀ m : Fin P.r, RelCompactLipLimits (fun n t ν => sys.D n ω t ν m) T) ∧
  RelCompactLipLimits (fun n => sys.s n ω) T

/-- `ω ∈ Ω_T` with constant `B_T` (Proposition 16, p. 41): `ω ∈ Γ_0` (the equations hold for
every `n ≥ 1`), `ω ∈ Γ_T` (Proposition 14's property), (23) for some `n_T(ω)`, and the limits
(24a)–(24c). -/
def IsNicePath (sys : System P Ω μP) (T : ℝ) (BT : ℕ) (ω : Ω) : Prop :=
  (∀ n : ℕ, 1 ≤ n → Solves sys.toPrimitives n ω (sys.s n ω) (sys.ℓ n ω)) ∧
  Prop14Property sys T ω ∧
  (∃ nT : ℕ, ∀ n : ℕ, nT ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) T,
      sys.q n ω t (BT + 1) = 0 ∧ sys.ℓ n ω t ≤ BT) ∧
  (∀ ν, Tendsto (fun n => sys.s0 n ω ν) atTop (𝓝 (sys.sLim ν))) ∧
  TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => (arrivalCount sys.toPrimitives n ω t : ℝ) / n)
    (fun t => P.lam * t) atTop (Set.Icc 0 T) ∧
  (∀ (ν : Profile P.r) (i : Fin P.r) (j : Fin 2),
    TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => ((sys.N (ν, i.succ, j)).count ((n : ℝ) * t) ω : ℝ) / n)
      (fun t => t) atTop (Set.Icc 0 (P.μ i * (ν i : ℝ) * T)))

end UnknownLoads.Coxian


