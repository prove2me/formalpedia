-- Prove2me | Definitions.Def_NCLpModules_Principal_Model
-- name    : NCLpModules_Principal_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:04.093144+00:00
-- url     : https://prove2.me/theorems/e6bb4e34-1aec-4436-814a-4239b4d9e4e5
-- title:
--   Definitions 2.1, 2.3 and (2.4), pp. 8–10 — L^{p/2}-valued inner product, right L^p module and column sum ⊕_c q_α L^p over a finite-dimensional M
-- statement:
--   This file fixes the objects of Junge and Sherman's *Noncommutative $L^p$ modules* for a **finite-dimensional** von Neumann algebra.
--
--   Throughout, $n\in\mathbb N$ and $\mathcal M$ is a unital $*$-subalgebra of the matrix algebra $M_n(\mathbb C)$ (every finite-dimensional von Neumann algebra is of this form). For real $0<p<\infty$, $L^p(\mathcal M)$ is $\mathcal M$ itself with the tracial (quasi)norm
--   $$\|a\|_p=\big(\mathrm{Tr}\,(a^*a)^{p/2}\big)^{1/p},$$
--   which is the published Schatten norm `schattenNorm` at the exponent $p$; likewise $L^{p/2}(\mathcal M)=\mathcal M$ with $\|\cdot\|_{p/2}$.
--
--   1. **Right module.** $\mathfrak X$ is a complex vector space with a right action $(\xi,x)\mapsto \xi x$ of $\mathcal M$: additive in each variable, $\xi 1=\xi$, $(\xi x)y=\xi(xy)$ and $(c\xi)x=c(\xi x)=\xi(cx)$ for $c\in\mathbb C$, $x,y\in\mathcal M$.
--   2. **$L^{p/2}$-valued inner product (Definition 2.1).** A map $\langle\cdot,\cdot\rangle:\mathfrak X\times\mathfrak X\to\mathcal M$, additive in each variable, conjugate linear in the first variable and linear in the second, with
--      (i) $\langle\xi,\eta x\rangle=\langle\xi,\eta\rangle x$ for $x\in\mathcal M$; (ii) $\langle\xi,\eta\rangle=\langle\eta,\xi\rangle^*$; (iii) $\langle\xi,\xi\rangle\ge 0$, and $\langle\xi,\xi\rangle=0\iff\xi=0$.
--   3. **Inherited (quasi)norm.** $\|\xi\|=\|\langle\xi,\xi\rangle^{1/2}\|_p=\big(\mathrm{Tr}\,\langle\xi,\xi\rangle^{p/2}\big)^{1/p}$.
--   4. **Right $L^p$ module (Definition 2.3, $p<\infty$).** The action is a right module action and $\mathfrak X$ is complete in $\|\cdot\|$: every $\|\cdot\|$-Cauchy sequence converges.
--   5. **Column sum (2.4).** For projections $(q_\alpha)_{\alpha\in I}$ of $\mathcal M$,
--   $$\textstyle\bigoplus_c q_\alpha L^p=\Big\{(\xi_\alpha)_{\alpha\in I}\ \Big|\ \xi_\alpha\in q_\alpha L^p,\ \sum_\alpha \xi_\alpha^*\xi_\alpha \text{ converges}\Big\},\qquad \langle(\xi_\alpha),(\eta_\alpha)\rangle=\sum_\alpha\xi_\alpha^*\eta_\alpha .$$
--   6. **Auxiliary objects.** The support projection $s(A)$ of a Hermitian $A$ (the projection onto its range), the submodule $\sum_\alpha \xi_\alpha\mathcal M$ of finite sums $\sum_{\alpha\in F}\xi_\alpha x_\alpha$, and the closure of a set in $\|\cdot\|$.
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note** The scope is finite-dimensional: Haagerup $L^p$ spaces of a general von Neumann algebra are not available in Mathlib. In this scope $L^{p/2}(\mathcal M)=\mathcal M$ as a set, so the inner-product structure does not depend on $p$; only the norm does. The action is a function `act : 𝔛 → M_n(ℂ) → 𝔛` whose axioms are imposed only for arguments in $\mathcal M$. Square roots and powers use the Hermitian continuous functional calculus `cfc`, so `ipNorm p A = lpNorm p (cfc Real.sqrt A)` $=\|A^{1/2}\|_p$. Positivity is `Matrix.PosSemidef`, a projection of $\mathcal M$ is `q ∈ M ∧ IsStarProjection q`, and $s(A)$ is `cfc` of the indicator of $t\neq0$. Completeness is sequential completeness for the gauge $\xi\mapsto\|\xi\|$, because $\|\cdot\|$ is only a $p/2$-norm for $p<2$. In (2.4), "$\sum\xi_\alpha^*\xi_\alpha\in L^{p/2}$" is unconditional summability of the family (the net of finite sums converges), and $\xi_\alpha\in q_\alpha L^p$ is written $\xi_\alpha\in\mathcal M$, $q_\alpha\xi_\alpha=\xi_\alpha$. The column sum is a *set* of families; that it is a module is milestone `columnSum_isLpModule`.
-- source:
--   Junge & Sherman, Noncommutative Lp modules, arXiv:math/0301044v2, pp. 8–10, Definition 2.1, Proposition 2.2 (the norm ‖ξ‖), Definition 2.3, display (2.4); §3 Case 2, p. 12 (the closed span 𝔛_0)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

namespace NCLpModules.Principal

open scoped Matrix ComplexOrder Topology
open Filter

/-- The tracial `L^p` (quasi)norm `‖a‖_p = (Tr (a* a)^{p/2})^{1/p}` of a matrix, for real `0 < p`.
It is the published Schatten norm `schattenNorm` of `Information100.P50` at the finite exponent
`ENNReal.ofReal p`. -/
noncomputable def lpNorm {n : ℕ} (p : ℝ) (a : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Information100.P50.schattenNorm (ENNReal.ofReal p) a

/-- The module (quasi)norm attached to a positive semidefinite inner-product value `A`:
`‖A^{1/2}‖_p`, with the square root `A^{1/2}` taken by the Hermitian functional calculus. -/
noncomputable def ipNorm {n : ℕ} (p : ℝ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  lpNorm p (cfc Real.sqrt A)

/-- `q` is a projection of `M`: `q ∈ M`, `q* = q`, `q² = q`. -/
def IsProj {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (q : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  q ∈ M ∧ IsStarProjection q

/-- The support projection `s(A)` of a Hermitian matrix `A`: the orthogonal projection onto its
range, i.e. `f(A)` for `f(t) = 0` at `t = 0` and `f(t) = 1` otherwise. -/
noncomputable def supportProj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  cfc (fun t : ℝ => if t = 0 then (0 : ℝ) else 1) A

/-- The axioms of a right `M`-module action `act ξ x = ξx` on a complex vector space `𝔛`
(only elements `x ∈ M` are ever acted with). -/
structure IsRightModuleAction {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (𝔛 : Type*) [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) : Prop where
  add_act : ∀ (ξ η : 𝔛) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ M → act (ξ + η) x = act ξ x + act η x
  act_add : ∀ (ξ : 𝔛) (x y : Matrix (Fin n) (Fin n) ℂ), x ∈ M → y ∈ M →
    act ξ (x + y) = act ξ x + act ξ y
  act_one : ∀ ξ : 𝔛, act ξ 1 = ξ
  act_mul : ∀ (ξ : 𝔛) (x y : Matrix (Fin n) (Fin n) ℂ), x ∈ M → y ∈ M →
    act (act ξ x) y = act ξ (x * y)
  smul_act : ∀ (c : ℂ) (ξ : 𝔛) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ M → act (c • ξ) x = c • act ξ x
  act_smul : ∀ (c : ℂ) (ξ : 𝔛) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ M → act ξ (c • x) = c • act ξ x

/-- Definition 2.1 (finite-dimensional `M`, where `L^{p/2}(M) = M` as a set): an
`L^{p/2}`-valued inner product on the right `M`-module `𝔛`. A sesquilinear map
`𝔛 × 𝔛 → M`, conjugate linear in the first variable, with
(i) `⟨ξ, ηx⟩ = ⟨ξ, η⟩x`, (ii) `⟨ξ, η⟩ = ⟨η, ξ⟩*`, (iii) `⟨ξ, ξ⟩ ≥ 0` and `⟨ξ, ξ⟩ = 0 ⟺ ξ = 0`. -/
structure LpInnerProduct {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    (𝔛 : Type*) [AddCommGroup 𝔛] [Module ℂ 𝔛]
    (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛) where
  ip : 𝔛 → 𝔛 → Matrix (Fin n) (Fin n) ℂ
  ip_mem : ∀ ξ η : 𝔛, ip ξ η ∈ M
  ip_add_left : ∀ ξ ξ' η : 𝔛, ip (ξ + ξ') η = ip ξ η + ip ξ' η
  ip_add_right : ∀ ξ η η' : 𝔛, ip ξ (η + η') = ip ξ η + ip ξ η'
  ip_smul_left : ∀ (c : ℂ) (ξ η : 𝔛), ip (c • ξ) η = star c • ip ξ η
  ip_smul_right : ∀ (c : ℂ) (ξ η : 𝔛), ip ξ (c • η) = c • ip ξ η
  ip_act : ∀ (ξ η : 𝔛) (x : Matrix (Fin n) (Fin n) ℂ), x ∈ M → ip ξ (act η x) = ip ξ η * x
  ip_conj : ∀ ξ η : 𝔛, ip ξ η = (ip η ξ)ᴴ
  ip_pos : ∀ ξ : 𝔛, (ip ξ ξ).PosSemidef
  ip_eq_zero : ∀ ξ : 𝔛, ip ξ ξ = 0 ↔ ξ = 0

/-- The inherited (quasi)norm `‖ξ‖ = ‖⟨ξ, ξ⟩^{1/2}‖_p` (Proposition 2.2). -/
noncomputable def gauge {n : ℕ} {M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)}
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛] {act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛}
    (p : ℝ) (ip : LpInnerProduct M 𝔛 act) (ξ : 𝔛) : ℝ :=
  ipNorm p (ip.ip ξ ξ)

/-- Sequential completeness of `𝔛` in the inherited (quasi)norm: every Cauchy sequence for
`ξ ↦ ‖⟨ξ, ξ⟩^{1/2}‖_p` converges in it. -/
def GaugeComplete {n : ℕ} {M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)}
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛] {act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛}
    (p : ℝ) (ip : LpInnerProduct M 𝔛 act) : Prop :=
  ∀ u : ℕ → 𝔛, (∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ k ≥ N, gauge p ip (u m - u k) < ε) →
    ∃ x : 𝔛, Tendsto (fun k => gauge p ip (u k - x)) atTop (𝓝 0)

/-- Definition 2.3 (`p < ∞`): `𝔛`, with the action `act` and the inner product `ip`, is a right
`L^p M`-module: `act` is a right `M`-module action and `𝔛` is complete in the inherited
(quasi)norm. -/
def IsLpModule {n : ℕ} (p : ℝ) (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛] (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛)
    (ip : LpInnerProduct M 𝔛 act) : Prop :=
  IsRightModuleAction M 𝔛 act ∧ GaugeComplete p ip

/-- The set (2.4), `⊕_c q_α L^p`: families `(ξ_α)_{α ∈ ι}` with `ξ_α ∈ q_α L^p` (that is,
`ξ_α ∈ M` and `q_α ξ_α = ξ_α`) and `Σ_α ξ_α* ξ_α` convergent. -/
def columnSumSet {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) {ι : Type*}
    (q : ι → Matrix (Fin n) (Fin n) ℂ) : Set (ι → Matrix (Fin n) (Fin n) ℂ) :=
  {ξ | (∀ α, ξ α ∈ M ∧ q α * ξ α = ξ α) ∧ Summable (fun α => (ξ α)ᴴ * ξ α)}

/-- The column-sum inner product `⟨(ξ_α), (η_α)⟩ = Σ_α ξ_α* η_α`. -/
noncomputable def colIp {n : ℕ} {ι : Type*} (ξ η : ι → Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ∑' α, (ξ α)ᴴ * η α

/-- The submodule `Σ_α ξ_α M`: finite sums `Σ_{α ∈ F} ξ_α x_α` with `x_α ∈ M`. -/
def spanSet {n : ℕ} (M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ))
    {𝔛 : Type*} [AddCommGroup 𝔛] (act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛)
    {ι : Type*} (ξ : ι → 𝔛) : Set 𝔛 :=
  {η | ∃ (F : Finset ι) (x : ι → Matrix (Fin n) (Fin n) ℂ), (∀ α, x α ∈ M) ∧
    η = ∑ α ∈ F, act (ξ α) (x α)}

/-- The closure of a set `S ⊆ 𝔛` in the inherited (quasi)norm. -/
def gaugeClosure {n : ℕ} {M : StarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)}
    {𝔛 : Type*} [AddCommGroup 𝔛] [Module ℂ 𝔛] {act : 𝔛 → Matrix (Fin n) (Fin n) ℂ → 𝔛}
    (p : ℝ) (ip : LpInnerProduct M 𝔛 act) (S : Set 𝔛) : Set 𝔛 :=
  {η | ∀ ε > 0, ∃ η' ∈ S, gauge p ip (η - η') < ε}

end NCLpModules.Principal


