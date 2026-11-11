-- Prove2me | Definitions.Def_ZeroFreeRRG_Hardcore_Moments
-- name    : ZeroFreeRRG_Hardcore_Moments
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:37:41.247833+00:00
-- url     : https://prove2.me/theorems/2c04a407-dee9-41b8-a0dc-2c6d339f2109
-- title:
--   Overlaps, overlap boxes, the local second moment 𝒵^{(2)}_{G,B}, Gibbs replicas, the planted law ℚ_n, the pinned log-likelihood ℓ_s, profiles, KL divergence and Bethe rate functions
-- statement:
--   For $\sigma,\sigma'\in\Omega^{[n]}$, $\rho_a(\sigma)=|\sigma^{-1}(a)|/n$ and the **overlap** $\rho_{ab}(\sigma,\sigma')=|\{v:\sigma_v=a,\sigma'_v=b\}|/n$. An **overlap box** is the preimage of an open axis-aligned box in $|\Omega|^2-1$ coordinates of $\Delta_{\Omega\times\Omega}$, and (30)
--   $$\mathcal Z^{(2)}_{G,B}(z,w)=\sum_{\rho(\sigma,\sigma')\in B}\prod_v\pi_{\sigma_v}(z)\pi_{\sigma'_v}(w)\prod_{uv\in E(G)}M_{\sigma_u\sigma_v}(z)M_{\sigma'_u\sigma'_v}(w).$$
--   At a real $t$ the canonical Gibbs law is $\mu_G(\sigma)=\mathcal Z_G(t)^{-1}\prod_v\pi_{\sigma_v}\prod_{uv}M_{\sigma_u\sigma_v}$, and two independent samples are Gibbs replicas. The **planted law** $\mathbb Q_n$ (Definition 4.19) on pairs $(G,\sigma)$ has density $a_n^{-1}\prod_{uv\in E(G)}M_{\sigma_u\sigma_v}$ with respect to $\mathrm{CM}\otimes\pi^{\otimes n}$. With a reveal set $U$ containing each vertex independently with probability $s$, the **pinned log-likelihood** is $\ell_s=\log\mu_G(\sigma_U)-\sum_{v\in U}\log\pi_{\sigma_v}$.
--
--   The **profile** $(\rho,Q)$ of $(G,\sigma)$ (Definition 5.2) has $\rho=\rho(\sigma)$ and $dnQ_{ab}$ equal to the number of oriented edges from $\sigma^{-1}(a)$ to $\sigma^{-1}(b)$ (a self-loop has two orientations). An edge marginal $Q$ with vertex marginal $\rho$ is a symmetric law on $\Omega\times\Omega$ with $Q\mathbf 1=\rho$; it is **feasible** if $n\rho_a\in\mathbb Z$, $dnQ_{ab}\in\mathbb Z$ ($a\ne b$), $dnQ_{aa}\in2\mathbb Z$. With $D_{\mathrm{KL}}(p\|q)=\sum_xp_x\log(p_x/q_x)$ ($0\log(0/q)=0$, $p\log(p/0)=+\infty$), the **Bethe rate function** (37) and its paired version (Definition 5.4) are
--   $$\Phi_s(\rho,Q)=(d-1)D_{\mathrm{KL}}(\rho\|\pi(s))-\tfrac d2D_{\mathrm{KL}}(Q\|P(s)),\qquad \Phi_{s,u}=\Phi\text{ on }\Omega\times\Omega\text{ with }(\pi(s)\otimes\pi(u),\,P(s)\otimes P(u)).$$
--
--   **Formalization Note.** All laws here are finitely supported, so expectations are finite sums: `plantedE`, `plantedPinnedE` (with reveal weights $s^{|U|}(1-s)^{n-|U|}$), `replicaProb`. `overlapBox c₀ lo hi` constrains every coordinate except the dropped one `c₀`. `klDiv` and `rateFn` are `EReal`-valued, $-\infty=\bot$; with $\pi(s)>0$ the first divergence is finite, so no $\top-\top$ arises. `rateFn` is generic in the alphabet; the paired function is `rateFn d (tensorVec π(s) π(u)) (tensorMat P(s) P(u))`. `profileContribution` is $\mathbb E_{\mathrm{CM}}$ of the total weight of assignments with profile $(\rho,Q)$.
-- source:
--   Chen, Wang, Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, arXiv:2610.40510 (held version, sha256 f1cbb4d9…), p. 14 (overlaps, edge marginals, KL); pp. 31–32, Definition 4.19, ℓ_s, eq. (30), overlap boxes; p. 38, Definitions 5.2 and 5.4

import Mathlib
import Definitions.Def_AFIsingKS_Matching
import Definitions.Def_ZeroFreeRRG_Hardcore_Kernels
import Definitions.Def_ZeroFreeRRG_Hardcore_ConfigModel

open scoped Classical

namespace ZeroFreeRRG.Hardcore

open AFIsingKS

/-! ### Overlaps, overlap boxes and the local second moment (§2.4, §4.3) -/

/-- The empirical vertex marginal `ρ_a(σ) = |σ⁻¹(a)| / n` (§2.4, p. 14). -/
noncomputable def empMarg {n : ℕ} {Ω : Type*} [Fintype Ω] (σ : Fin n → Ω) (a : Ω) : ℝ :=
  ((Finset.univ.filter (fun v => σ v = a)).card : ℝ) / n

/-- The empirical overlap `ρ_{ab}(σ, σ') = |{v : σ_v = a, σ'_v = b}| / n` (§2.4), the empirical
vertex marginal of the pair `(σ, σ')` on the product alphabet `Ω × Ω`. -/
noncomputable def overlap {n : ℕ} {Ω : Type*} [Fintype Ω] (σ σ' : Fin n → Ω) (ab : Ω × Ω) : ℝ :=
  empMarg (fun v => (σ v, σ' v)) ab

/-- An overlap box (§4.3, p. 32): the preimage in `Δ_{Ω×Ω}` of an open axis-aligned box in the
`|Ω|² − 1` coordinates other than a dropped coordinate `c₀`, with lower corner `l` and upper corner
`u`: `{ρ : l_{ab} < ρ_{ab} < u_{ab} for all ab ≠ c₀}`. (Only empirical overlaps, which lie in the
simplex, are ever tested for membership.) -/
def overlapBox {α : Type*} (c₀ : α) (l u : α → ℝ) : Set (α → ℝ) :=
  {ρ | ∀ ab, ab ≠ c₀ → l ab < ρ ab ∧ ρ ab < u ab}

/-- The product `π ⊗ π'` of two vectors on `Ω`, a vector on `Ω × Ω`. -/
def tensorVec {Ω : Type*} {𝕜 : Type*} [Mul 𝕜] (p p' : Ω → 𝕜) : Ω × Ω → 𝕜 :=
  fun ab => p ab.1 * p' ab.2

/-- The Kronecker product `P ⊗ P'` of two `Ω × Ω` matrices, indexed by `(Ω × Ω) × (Ω × Ω)`. -/
def tensorMat {Ω : Type*} {𝕜 : Type*} [Mul 𝕜] (P P' : Ω → Ω → 𝕜) : Ω × Ω → Ω × Ω → 𝕜 :=
  fun ab cd => P ab.1 cd.1 * P' ab.2 cd.2

/-- The local second-moment sum (30), p. 32:
`𝒵^{(2)}_{G,B}(z, w) = ∑_{σ, σ' : ρ(σ, σ') ∈ B} ∏_v π_{σ_v}(z) π_{σ'_v}(w)
  ∏_{uv ∈ E(G)} M_{σ_u σ_v}(z) M_{σ'_u σ'_v}(w)` on the configuration-model multigraph `M`. -/
noncomputable def Z2 (m : Model) (B : Set (m.Spin × m.Spin → ℝ)) (z w : ℂ) {n d : ℕ}
    (M : Matching n d) : ℂ :=
  ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin,
    if overlap σ σ' ∈ B then weight m z M σ * weight m w M σ' else 0

/-! ### Gibbs measure, planted law and pinned log-likelihood (Definition 2.4, Definition 4.19) -/

/-- The canonical Gibbs distribution `µ^{can}_{G,t}(σ) = 𝒵_G(t)⁻¹ ∏_v π_{σ_v}(t) ∏_{uv} M_{σ_uσ_v}(t)`
(Definition 2.4, p. 15) at a real parameter `t`. -/
noncomputable def gibbs (m : Model) (t : ℝ) {n d : ℕ} (M : Matching n d) (σ : Fin n → m.Spin) : ℝ :=
  weight m t M σ / normZ m t M

/-- The planted distribution `ℚ_n` (Definition 4.19, p. 31) as a probability mass function on
pairs `(G, σ)`: its density with respect to `CM ⊗ π^{⊗n}` is `a_n⁻¹ ∏_{uv ∈ E(G)} M_{σ_uσ_v}`, so
`ℚ_n(G, σ) = ∏_v π_{σ_v} ∏_{uv} M_{σ_uσ_v} / (|pairings| · a_n)`. -/
noncomputable def planted (m : Model) (t : ℝ) {n d : ℕ} (M : Matching n d) (σ : Fin n → m.Spin) :
    ℝ :=
  weight m t M σ / ((Fintype.card (Matching n d) : ℝ) * an m d n t)

/-- The Bernoulli(`s`) law of the reveal set `U ⊆ V`: each vertex is included independently with
probability `s`. -/
noncomputable def revealProb {n : ℕ} (s : ℝ) (U : Finset (Fin n)) : ℝ :=
  s ^ U.card * (1 - s) ^ (n - U.card)

/-- `µ_G(σ_U) = ∑_{σ' : σ'_U = σ_U} µ_G(σ')`, the Gibbs marginal probability of the revealed spins. -/
noncomputable def gibbsMarg (m : Model) (t : ℝ) {n d : ℕ} (M : Matching n d) (σ : Fin n → m.Spin)
    (U : Finset (Fin n)) : ℝ :=
  ∑ σ' ∈ Finset.univ.filter (fun σ' : Fin n → m.Spin => ∀ v ∈ U, σ' v = σ v), gibbs m t M σ'

/-- The pinned log-likelihood ratio (§4.3, p. 31): `ℓ_s(σ) = log µ_G(σ_U) − ∑_{v ∈ U} log π_{σ_v}`. -/
noncomputable def pinnedLL (m : Model) (t : ℝ) {n d : ℕ} (M : Matching n d) (σ : Fin n → m.Spin)
    (U : Finset (Fin n)) : ℝ :=
  Real.log (gibbsMarg m t M σ U) - ∑ v ∈ U, Real.log (m.pi t (σ v))

/-- Expectation under `ℚ_n ⊗ Bernoulli(s)^{⊗n}` of a function of `(G, σ, U)`. -/
noncomputable def plantedPinnedE (m : Model) (t s : ℝ) (d n : ℕ)
    (f : Matching n d → (Fin n → m.Spin) → Finset (Fin n) → ℝ) : ℝ :=
  ∑ M : Matching n d, ∑ σ : Fin n → m.Spin, ∑ U : Finset (Fin n),
    planted m t M σ * revealProb s U * f M σ U

/-- Expectation under `ℚ_n` of a function of `(G, σ)`. -/
noncomputable def plantedE (m : Model) (t : ℝ) (d n : ℕ)
    (f : Matching n d → (Fin n → m.Spin) → ℝ) : ℝ :=
  ∑ M : Matching n d, ∑ σ : Fin n → m.Spin, planted m t M σ * f M σ

/-- `µ_G^{⊗2}(A)`, the probability that two independent Gibbs replicas `(σ, σ')` lie in `A`. -/
noncomputable def replicaProb (m : Model) (t : ℝ) {n d : ℕ} (M : Matching n d)
    (A : (Fin n → m.Spin) → (Fin n → m.Spin) → Prop) : ℝ :=
  ∑ σ : Fin n → m.Spin, ∑ σ' : Fin n → m.Spin, if A σ σ' then gibbs m t M σ * gibbs m t M σ' else 0

/-! ### Profiles and Bethe rate functions (Definitions 5.2, 5.4) -/

/-- The empirical edge marginal of a profile (Definition 5.2): `dn Q_{ab}` is the number of
oriented edges from `V_a` to `V_b`, a self-loop contributing two orientations; oriented edges are
half-edges `x` with `σ` of `x`'s vertex `= a` and `σ` of its partner's vertex `= b`. -/
noncomputable def empEdge {n d : ℕ} {Ω : Type*} [Fintype Ω] (M : Matching n d) (σ : Fin n → Ω)
    (a b : Ω) : ℝ :=
  ((Finset.univ.filter (fun x : Fin n × Fin d => σ x.1 = a ∧ σ (M.1 x).1 = b)).card : ℝ) /
    ((d : ℝ) * n)

/-- `Q` is an edge marginal with vertex marginal `ρ` (§2.4, p. 14): a symmetric probability
distribution on `Ω × Ω` with `Q 𝟙 = ρ`. -/
def IsEdgeMarginal {α : Type*} [Fintype α] (ρ : α → ℝ) (Q : α → α → ℝ) : Prop :=
  (∀ a b, 0 ≤ Q a b) ∧ (∀ a b, Q a b = Q b a) ∧ (∑ a, ∑ b, Q a b) = 1 ∧ ∀ a, ∑ b, Q a b = ρ a

/-- A feasible profile on `n` vertices of degree `d` (Definition 5.2): `Q` is an edge marginal with
vertex marginal `ρ`, `nρ_a ∈ ℤ`, `dnQ_{ab} ∈ ℤ` for `a ≠ b`, and `dnQ_{aa} ∈ 2ℤ`. -/
def Feasible {α : Type*} [Fintype α] (n d : ℕ) (ρ : α → ℝ) (Q : α → α → ℝ) : Prop :=
  IsEdgeMarginal ρ Q ∧ (∀ a, ∃ k : ℤ, (n : ℝ) * ρ a = k) ∧
    (∀ a b, a ≠ b → ∃ k : ℤ, (d : ℝ) * n * Q a b = k) ∧ ∀ a, ∃ k : ℤ, (d : ℝ) * n * Q a a = 2 * k

/-- The Kullback–Leibler divergence `D_KL(p ‖ q) = ∑_x p_x log(p_x / q_x)` (§2.4, pp. 14–15) with
`0 log(0/q) = 0` (also at `q = 0`) and `p log(p/0) = +∞` for `p > 0`, valued in `EReal`. -/
noncomputable def klDiv {α : Type*} [Fintype α] (p q : α → ℝ) : EReal :=
  ∑ x, if p x = 0 then (0 : EReal) else if q x = 0 then ⊤ else ((p x * Real.log (p x / q x) : ℝ) : EReal)

/-- The Bethe rate function (37) on an alphabet `α` with reference laws `(π, P)`:
`Φ(ρ, Q) = (d − 1) D_KL(ρ ‖ π) − (d/2) D_KL(Q ‖ P)`, valued in `EReal` (`−∞` when
`D_KL(Q ‖ P) = +∞`; `D_KL(ρ ‖ π)` is finite whenever `π > 0`, as assumed in (37)). The paired rate
function of Definition 5.4 is this on the alphabet `Ω × Ω` with `(π(s) ⊗ π(u), P(s) ⊗ P(u))`. -/
noncomputable def rateFn {α : Type*} [Fintype α] (d : ℕ) (π : α → ℝ) (P : α → α → ℝ)
    (ρ : α → ℝ) (Q : α → α → ℝ) : EReal :=
  (((d : ℝ) - 1 : ℝ) : EReal) * klDiv ρ π -
    (((d : ℝ) / 2 : ℝ) : EReal) * klDiv (fun ab : α × α => Q ab.1 ab.2) (fun ab => P ab.1 ab.2)

/-- `‖ρ − π‖₂² + ‖Q − P‖_F²`. -/
noncomputable def sqDist {α : Type*} [Fintype α] (ρ π : α → ℝ) (Q P : α → α → ℝ) : ℝ :=
  (∑ a, (ρ a - π a) ^ 2) + ∑ a, ∑ b, (Q a b - P a b) ^ 2

/-- The expected contribution to `𝒵_G(s)` from assignments with profile `(ρ, Q)` (Proposition 5.3):
`E_{CM}[∑_{σ : profile(G,σ) = (ρ,Q)} ∏_v π_{σ_v}(s) ∏_{uv} M_{σ_uσ_v}(s)]`. -/
noncomputable def profileContribution (m : Model) (s : ℝ) (d n : ℕ) (ρ : m.Spin → ℝ)
    (Q : m.Spin → m.Spin → ℝ) : ℝ :=
  cmE (fun M : Matching n d =>
    ∑ σ ∈ Finset.univ.filter (fun σ : Fin n → m.Spin => empMarg σ = ρ ∧ empEdge M σ = Q),
      weight m s M σ)

end ZeroFreeRRG.Hardcore


