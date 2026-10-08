-- Prove2me | Definitions.Def_NonlinFPE_Main_Setting
-- name    : NonlinFPE_Main_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:59.031605+00:00
-- url     : https://prove2.me/theorems/70150c5a-c263-4c2b-8dfa-4cfce0b91f05
-- title:
--   §3, pp. 7–11, 18 — (H1)–(H3), (H1)′–(H3)′, (K), the operator A of (3.8)–(3.9), the equation (3.10), H¹, b∞, c∞, a = σσᵀ, the sense (3.39)
-- statement:
--   Throughout, $x \in \mathbb R^d$, indices $i,j \in \{1,\dots,d\}$, $a_{ij} : \mathbb R^d \times \mathbb R \to \mathbb R$ and $b_i : \mathbb R^d \times \mathbb R \to \mathbb R$, and $D_i$, $D^2_{ij} = D_iD_j$ are partial derivatives in $x$. Test functions $\varphi \in C_0^\infty(\Omega)$ are smooth with compact support in $\Omega$.
--
--   1. **(H1)** each $a_{ij}$ is $C^2$ on $\mathbb R^d \times \mathbb R$ and bounded, $\nabla_x a_{ij}$ is bounded, and $a_{ij} = a_{ji}$. **(H2)** for some $\gamma > 0$,
--   $$\sum_{i,j=1}^d \big(a_{ij}(x,u) + \partial_u a_{ij}(x,u)\,u\big)\xi_i\xi_j \ge \gamma|\xi|^2, \qquad \xi, x \in \mathbb R^d,\ u \in \mathbb R .$$
--   **(H3)** each $b_i$ is bounded and $C^1$, and $b_i(x,0) = 0$. These are the nondegenerate hypotheses.
--
--   2. **(H1)′–(H3)′** (degenerate, $x$-independent): $a_{ij}(u)$ is $C^2$, bounded, symmetric; $\sum_{i,j}(a_{ij}(u) + u\,a_{ij}'(u))\xi_i\xi_j \ge 0$; $b_i(u)$ is bounded, $C^1$, with $b_i(0) = 0$. Such coefficients are viewed as $x$-dependent ones constant in $x$.
--
--   3. **The operator** $A$ on $L^1(\mathbb R^d)$, (3.8)–(3.9): $v = Au$ means $v \in L^1$ and
--   $$v = -\sum_{i,j=1}^d D^2_{ij}\big(a_{ij}(x,u)u\big) + \operatorname{div}\big(b(x,u)u\big) \quad\text{in } \mathcal D'(\mathbb R^d),$$
--   i.e. $\int v\varphi = -\sum_{i,j}\int a_{ij}(x,u)u\,D^2_{ij}\varphi - \int \sum_i b_i(x,u)u\,D_i\varphi$ for all $\varphi \in C_0^\infty(\mathbb R^d)$; $D(A)$ is the set of $u \in L^1$ for which such $v$ exists. For $x$-independent coefficients this is the operator $A_1$ of (3.42).
--
--   4. **The equation** $u - \lambda\sum_{i,j}D^2_{ij}(a_{ij}(x,u)u) + \lambda\operatorname{div}(b(x,u)u) = f$ in $\mathcal D'(\Omega)$ for functions $u, f$ ((3.10) for $\Omega = \mathbb R^d$, (3.16) for a ball $\Omega = B_N$), in the same weak form.
--
--   5. $u \in H^1(\mathbb R^d)$ with weak gradient $(g_1, \dots, g_d)$: $u, g_i \in L^2$ and $g_i$ is the weak derivative $D_iu$.
--
--   6. **(K)** with $a^*_{ij}(x,u) = a_{ij}(x,u)u$: $\partial_u a^*_{ij}$ is bounded, $b_i \in C^1_b$, and (3.15): $|\partial_u a^*_{ij}(x,u) - \partial_u a^*_{ij}(x,\bar u)| + |\nabla_x a^*_{ij}(x,u) - \nabla_x a^*_{ij}(x,\bar u)| \le C|u - \bar u|$.
--
--   7. $b_\infty = \sup\{|b_i(x,u)|\}$ and $c_\infty = \sup\{|(a_{ij})_{x_j}(x,u)|\}$ over $(x,u) \in \mathbb R^d \times \mathbb R$ and indices.
--
--   8. $u \in L^1$ is a **probability density** if $u \ge 0$ a.e. and $\int u\,dx = 1$.
--
--   9. For $\sigma : \mathbb R^d \times \mathbb R \to L(\mathbb R^d;\mathbb R^d)$, $a_{ij}(x,r) = (\sigma\sigma^T)_{ij}(x,r) = \sum_k \sigma_{ik}(x,r)\sigma_{jk}(x,r)$.
--
--   10. $u \in C([0,\infty); L^1)$ **solves (3.1) in $\mathcal D'((0,\infty)\times\mathbb R^d)$** in the sense of (3.39): for a jointly measurable version $u(t,x)$,
--   $$\int_0^\infty\!\!\int_{\mathbb R^d}\Big(u\varphi_t + \sum_{i,j=1}^d a_{ij}(x,u)u\,D^2_{ij}\varphi + b(x,u)\cdot\nabla_x\varphi\,u\Big)\,dx\,dt = 0, \qquad \varphi \in C_0^\infty((0,\infty)\times\mathbb R^d).$$
--
--   This file fixes every object of §3 that the mission's statements use, so that all of them refer to one definition of each concept of the paper.
--
--   **Formalization Note** $\mathbb R^d$ is `EthierKurtz.SDEState d`, indices are `Fin d` (0-based), partial derivatives are `HunterPDE.Shared.partialDeriv` and weak derivatives `HunterPDE.Shared.HasWeakDeriv` on all of $\mathbb R^d$. The page's "$C_b(\mathbb R^d\times\mathbb R^d)$" in (H1) is read as $C_b(\mathbb R^d\times\mathbb R)$ and "$C^1(\mathbb R^d)$" in (H3)′ as $C^1(\mathbb R)$ (typos: the functions live on $\mathbb R^d\times\mathbb R$, resp. $\mathbb R$). Continuity in (H1), (K) follows from $C^2$ and is not restated. $A$ is a relation on $L^1$ elements, evaluated on a representative; the integrals do not depend on it. $b_\infty$, $c_\infty$ are `sSup` of sets bounded under (H1), (H3). The version $u(t,x)$ in (3.39) is required to agree a.e. with $u(t)$ for every $t \ge 0$; the integral is iterated, $x$ inside. The factor in $a = \sigma\sigma^T$ deliberately omits the printed 2 of p. 23 (see the goal theorem).
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3, pp. 7–11 and 18, (H1)–(H3), (H1)′–(H3)′, (3.8)–(3.10), (3.15)–(3.16), (K), b∞, c∞, (3.39); §4, p. 23

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory
open scoped NNReal ContDiff

namespace NonlinFPE.Main

open EthierKurtz HunterPDE.Shared

/-- The second partial derivative `D²ᵢⱼ φ = ∂ᵢ ∂ⱼ φ` of `φ : ℝᵈ → ℝ` (indices `Fin d`, 0-based),
built from `HunterPDE.Shared.partialDeriv` (Fréchet derivative along `eᵢ`). -/
noncomputable def pd2 {d : ℕ} (φ : SDEState d → ℝ) (i j : Fin d) (x : SDEState d) : ℝ :=
  partialDeriv (fun y => partialDeriv φ j y) i x

/-- (H1), p. 7: each `a i j : ℝᵈ × ℝ → ℝ` is `C²`, bounded, with bounded `x`-gradient, and `a` is
symmetric. (The page's `C_b(ℝᵈ × ℝᵈ)` is read as `C_b(ℝᵈ × ℝ)`; continuity of `a` and of `∇ₓ a`
follows from `C²`.) -/
def HypH1 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ) : Prop :=
  ∀ i j : Fin d,
    ContDiff ℝ 2 (fun p : SDEState d × ℝ => a i j p.1 p.2) ∧
    (∃ M : ℝ, ∀ x r, |a i j x r| ≤ M) ∧
    (∃ M : ℝ, ∀ x r, ‖fderiv ℝ (fun y => a i j y r) x‖ ≤ M) ∧
    a i j = a j i

/-- (H2), p. 7: `∑ᵢⱼ (aᵢⱼ(x,u) + ∂ᵤaᵢⱼ(x,u) u) ξᵢ ξⱼ ≥ γ |ξ|²` for all `ξ, x ∈ ℝᵈ`, `u ∈ ℝ`, with
`γ > 0`. -/
def HypH2 {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ) (γ : ℝ) : Prop :=
  0 < γ ∧ ∀ (ξ x : SDEState d) (r : ℝ),
    γ * ‖ξ‖ ^ 2 ≤ ∑ i, ∑ j, (a i j x r + deriv (fun s => a i j x s) r * r) * ξ i * ξ j

/-- (H3), p. 7: each `b i : ℝᵈ × ℝ → ℝ` is bounded, `C¹`, and `b i x 0 = 0`. -/
def HypH3 {d : ℕ} (b : Fin d → SDEState d → ℝ → ℝ) : Prop :=
  ∀ i : Fin d,
    ContDiff ℝ 1 (fun p : SDEState d × ℝ => b i p.1 p.2) ∧
    (∃ M : ℝ, ∀ x r, |b i x r| ≤ M) ∧
    ∀ x, b i x 0 = 0

/-- The nondegenerate, `x`-dependent hypotheses (H1)–(H3) of §3, with ellipticity constant `γ`. -/
def HypND {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ) (b : Fin d → SDEState d → ℝ → ℝ)
    (γ : ℝ) : Prop :=
  HypH1 a ∧ HypH2 a γ ∧ HypH3 b

/-- The degenerate, `x`-independent hypotheses (H1)′–(H3)′ of §3, p. 7, for `a' i j : ℝ → ℝ`,
`b' i : ℝ → ℝ`: `a'` is `C²`, bounded, symmetric; `∑ᵢⱼ (a'ᵢⱼ(u) + u a'ᵢⱼ′(u)) ξᵢ ξⱼ ≥ 0`; `b'` is
bounded, `C¹` (the page's `C¹(ℝᵈ)` is read as `C¹(ℝ)`), with `b' i 0 = 0`. -/
def HypDeg {d : ℕ} (a' : Fin d → Fin d → ℝ → ℝ) (b' : Fin d → ℝ → ℝ) : Prop :=
  (∀ i j : Fin d, ContDiff ℝ 2 (a' i j) ∧ (∃ M : ℝ, ∀ r, |a' i j r| ≤ M) ∧ a' i j = a' j i) ∧
  (∀ (ξ : SDEState d) (r : ℝ),
    0 ≤ ∑ i, ∑ j, (a' i j r + r * deriv (a' i j) r) * ξ i * ξ j) ∧
  (∀ i : Fin d, ContDiff ℝ 1 (b' i) ∧ (∃ M : ℝ, ∀ r, |b' i r| ≤ M) ∧ b' i 0 = 0)

/-- An `x`-independent diffusion coefficient viewed as an `x`-dependent one. -/
def liftA {d : ℕ} (a' : Fin d → Fin d → ℝ → ℝ) : Fin d → Fin d → SDEState d → ℝ → ℝ :=
  fun i j _ r => a' i j r

/-- An `x`-independent drift coefficient viewed as an `x`-dependent one. -/
def liftB {d : ℕ} (b' : Fin d → ℝ → ℝ) : Fin d → SDEState d → ℝ → ℝ :=
  fun i _ r => b' i r

/-- The operator `A` of (3.8)–(3.9) on `L¹(ℝᵈ)`, as a graph: `opA a b u v` means
`v = Au = -∑ᵢⱼ D²ᵢⱼ(aᵢⱼ(x,u)u) + div(b(x,u)u)` in `𝒟′(ℝᵈ)` with `v ∈ L¹`, i.e. for every test
function `φ ∈ C₀^∞(ℝᵈ)`, `∫ v φ = -∑ᵢⱼ ∫ aᵢⱼ(x,u)u ∂ᵢⱼφ - ∫ ∑ᵢ bᵢ(x,u)u ∂ᵢφ`.
So `D(A) = {u | ∃ v, opA a b u v}`. The integrals do not depend on the representative of `u`. -/
def opA {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ) (b : Fin d → SDEState d → ℝ → ℝ)
    (u v : SDEState d →₁[volume] ℝ) : Prop :=
  ∀ φ : SDEState d → ℝ, IsTestFunction Set.univ φ →
    ∫ x, v x * φ x =
      -(∑ i, ∑ j, ∫ x, a i j x (u x) * u x * pd2 φ i j x) -
        ∫ x, ∑ i, b i x (u x) * u x * partialDeriv φ i x

/-- The resolvent equation `u - λ ∑ᵢⱼ D²ᵢⱼ(aᵢⱼ(x,u)u) + λ div(b(x,u)u) = f` in `𝒟′(Ω)` for functions
`u, f : ℝᵈ → ℝ` ((3.10) for `Ω = ℝᵈ`, (3.16) for `Ω = B_N`): for every `φ ∈ C₀^∞(Ω)`,
`∫ u φ - λ ∑ᵢⱼ ∫ aᵢⱼ(x,u)u ∂ᵢⱼφ - λ ∫ ∑ᵢ bᵢ(x,u)u ∂ᵢφ = ∫ f φ`. -/
def ResolventEqOn {d : ℕ} (Ω : Set (SDEState d)) (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (lam : ℝ) (u f : SDEState d → ℝ) : Prop :=
  ∀ φ : SDEState d → ℝ, IsTestFunction Ω φ →
    ∫ x, u x * φ x - lam * (∑ i, ∑ j, ∫ x, a i j x (u x) * u x * pd2 φ i j x) -
        lam * ∫ x, ∑ i, b i x (u x) * u x * partialDeriv φ i x =
      ∫ x, f x * φ x

/-- `u ∈ H¹(ℝᵈ)` with weak gradient `g = (g₀, …, g_{d-1})`: `u ∈ L²`, and each `gᵢ ∈ L²` is the
weak partial derivative `∂ᵢ u` on `ℝᵈ` (`HunterPDE.Shared.HasWeakDeriv` with multi-index `eᵢ`). -/
def IsH1 {d : ℕ} (u : SDEState d → ℝ) (g : Fin d → SDEState d → ℝ) : Prop :=
  MemLp u 2 volume ∧
    ∀ i : Fin d, MemLp (g i) 2 volume ∧
      HasWeakDeriv Set.univ (Pi.single i 1 : Fin d → ℕ) u (g i)

/-- The additional hypotheses (K) and (3.15) of p. 10, with `a*ᵢⱼ(x,u) = aᵢⱼ(x,u)u`:
`∂ᵤ a*ᵢⱼ` is bounded (its continuity follows from (H1)), `bᵢ ∈ C¹_b` (bounded derivative; `C¹` and
boundedness of `bᵢ` come from (H3)), and for some `C`,
`|∂ᵤa*ᵢⱼ(x,u) - ∂ᵤa*ᵢⱼ(x,ū)| + |∇ₓa*ᵢⱼ(x,u) - ∇ₓa*ᵢⱼ(x,ū)| ≤ C|u - ū|`. -/
def HypK {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ) (b : Fin d → SDEState d → ℝ → ℝ) :
    Prop :=
  (∀ i j : Fin d, ∃ M : ℝ, ∀ x r, |deriv (fun s => a i j x s * s) r| ≤ M) ∧
  (∀ i : Fin d, ∃ M : ℝ, ∀ p : SDEState d × ℝ,
    ‖fderiv ℝ (fun q : SDEState d × ℝ => b i q.1 q.2) p‖ ≤ M) ∧
  ∃ C : ℝ, ∀ (i j : Fin d) (x : SDEState d) (r r' : ℝ),
    |deriv (fun s => a i j x s * s) r - deriv (fun s => a i j x s * s) r'| +
        ‖fderiv ℝ (fun y => a i j y r * r) x - fderiv ℝ (fun y => a i j y r' * r') x‖ ≤
      C * |r - r'|

/-- `b∞ = sup {|bᵢ(x,u)| : (x,u) ∈ ℝᵈ × ℝ, i = 1, …, d}` (p. 11); the set is bounded under (H3). -/
noncomputable def bSup {d : ℕ} (b : Fin d → SDEState d → ℝ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (i : Fin d) (x : SDEState d) (r : ℝ), s = |b i x r|}

/-- `c∞ = sup {|(aᵢⱼ)_{xⱼ}(x,u)| : (x,u) ∈ ℝᵈ × ℝ, i, j = 1, …, d}` (p. 11); bounded under (H1). -/
noncomputable def cSup {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ) : ℝ :=
  sSup {s : ℝ | ∃ (i j : Fin d) (x : SDEState d) (r : ℝ),
    s = |partialDeriv (fun y => a i j y r) j x|}

/-- `u ∈ L¹(ℝᵈ)` is a probability density: `u ≥ 0` a.e. and `∫ u = 1`. -/
def IsProbDensity {d : ℕ} (u : SDEState d →₁[volume] ℝ) : Prop :=
  0 ≤ᵐ[volume] (u : SDEState d → ℝ) ∧ ∫ x, u x = 1

/-- The diffusion coefficient `aᵢⱼ(x,r) = (σσᵀ)ᵢⱼ(x,r) = ∑ₖ σᵢₖ(x,r) σⱼₖ(x,r)` attached to the noise
coefficient `σ(x,r) ∈ L(ℝᵈ;ℝᵈ)` (entry `σ x r i k`) of the SDE (4.1) with noise `√2 σ dW`.
(The page prints `aᵢⱼ := 2(σσᵀ)ᵢⱼ`; with noise `√2 σ` the marginals solve (3.1) for `a = σσᵀ`.) -/
def aOf {d : ℕ} (σ : SDEState d → ℝ → Fin d → Fin d → ℝ) : Fin d → Fin d → SDEState d → ℝ → ℝ :=
  fun i j x r => ∑ k, σ x r i k * σ x r j k

/-- `u : [0, ∞) → L¹` solves (3.1) in `𝒟′((0,∞) × ℝᵈ)`, in the sense of (3.39): for some jointly
measurable `ũ : ℝ × ℝᵈ → ℝ` with `ũ(t, ·) = u(t)` a.e. for every `t ≥ 0`, and every
`φ ∈ C₀^∞((0,∞) × ℝᵈ)` (smooth, compact support inside `{t > 0}`),
`∫_{t>0} ∫_{ℝᵈ} (ũ φ_t + ∑ᵢⱼ aᵢⱼ(x,ũ) ũ D²ᵢⱼφ + ∑ᵢ bᵢ(x,ũ) ∂ᵢφ ũ) dx dt = 0`
(iterated integral, `x` inside, derivatives of `φ(t, ·)` in `x`). -/
def IsDistribSolution {d : ℕ} (a : Fin d → Fin d → SDEState d → ℝ → ℝ)
    (b : Fin d → SDEState d → ℝ → ℝ) (u : ℝ≥0 → SDEState d →₁[volume] ℝ) : Prop :=
  ∃ ut : ℝ → SDEState d → ℝ, Measurable (Function.uncurry ut) ∧
    (∀ t : ℝ≥0, ut t =ᵐ[volume] (u t : SDEState d → ℝ)) ∧
    ∀ φ : ℝ × SDEState d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ {p | 0 < p.1} →
        ∫ t in Set.Ioi (0 : ℝ), ∫ x,
          (ut t x * deriv (fun s => φ (s, x)) t +
            ∑ i, ∑ j, a i j x (ut t x) * ut t x * pd2 (fun y => φ (t, y)) i j x +
            ∑ i, b i x (ut t x) * partialDeriv (fun y => φ (t, y)) i x * ut t x) = 0

end NonlinFPE.Main


