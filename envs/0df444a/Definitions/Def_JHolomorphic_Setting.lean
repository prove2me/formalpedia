-- Prove2me | Definitions.Def_JHolomorphic_Setting
-- name    : JHolomorphic_Setting
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-10-20T20:31:13.721209+00:00
-- url     : https://prove2.me/theorems/159a6079-38d8-4512-bf78-9951e03d3196
-- title:
--   Almost complex structures, pseudoholomorphic maps and weak solutions on planar domains
-- statement:
--   Basic objects for pseudoholomorphic maps from planar domains into a finite-dimensional real vector space (C. Wendl, *Lectures on Symplectic Field Theory*, Lecture 2, § 2.4, and Lecture 9).
--
--   1. **Almost complex structures on an open set.** For an open $O\subseteq E$, a map $J:E\to\operatorname{End}_{\mathbb{R}}(E)$ is a smooth almost complex structure on $O$ if it is $C^\infty$ on $O$ and $J(x)^2=-\mathrm{Id}$ for every $x\in O$. Values of $J$ outside $O$ play no role.
--   2. **The nonlinear Cauchy–Riemann operator.** For $u:\mathbb{C}\to E$ and $z=s+it$, $\bar\partial_Ju(z)=\partial_su(z)+J(u(z))\,\partial_tu(z)$.
--   3. **$J$-holomorphic maps.** $u$ is $J$-holomorphic on $U\subseteq\mathbb{C}$ if it is differentiable at every $z\in U$ and $\bar\partial_Ju(z)=0$ there.
--   4. **Weak partial derivatives.** $u_s,u_t$ are weak partial derivatives of $u$ on $U$ if $\int(\partial_s\varphi)\,u=-\int\varphi\,u_s$ and $\int(\partial_t\varphi)\,u=-\int\varphi\,u_t$ for every real $C^\infty$ function $\varphi$ with compact support in $U$.
--   5. **$W^{1,p}_{\mathrm{loc}}$ solutions.** $u$ is a weak solution of $\bar\partial_Ju=0$ on $U$ with values in $O$ if $u$ is continuous on $U$, $u(U)\subseteq O$, $u$ has weak partial derivatives $u_s,u_t$ on $U$, the maps $u,u_s,u_t$ lie in $L^p(K)$ for every compact $K\subseteq U$, and $u_s+J(u)\,u_t=0$ almost everywhere on $U$.
--   6. **$C^\infty_{\mathrm{loc}}$ convergence.** $f_\nu\to g$ in $C^\infty_{\mathrm{loc}}$ on $O$ if for every compact $K\subseteq O$ and every $m\ge0$ the $m$-th derivatives $D^mf_\nu$ converge to $D^mg$ uniformly on $K$.
--
--   **Formalization Note** $E$ is a real normed space with `[FiniteDimensional ℝ E]`; no inner product is assumed (product norms are allowed). $J$ has type `E → E →L[ℝ] E`. $\partial_su$ and $\partial_tu$ are `fderiv ℝ u z 1` and `fderiv ℝ u z Complex.I`. Smoothness is `ContDiff ℝ ∞` / `ContDiffOn ℝ ∞` ($C^\infty$, not analytic). $L^p$ membership is `MemLp _ (ENNReal.ofReal p) (volume.restrict K)` and integrals are Bochner integrals for Lebesgue measure on $\mathbb{C}$. Derivatives of order $m$ are `iteratedFDeriv ℝ m`. The module imports the `DbarRegularity` setting, whose `sobolevNorm k p U φ` $=\sum_{j\le k}\|D^j\varphi\|_{L^p(U)}$ appears in the statements.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 2, Section 2.4 (nonlinear Cauchy–Riemann equation, p. 35), and Lecture 9, Proposition 9.1 (p. 151)

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Topology.UniformSpace.UniformConvergence

/-!
# Pseudoholomorphic maps from planar domains

C. Wendl, *Lectures on Symplectic Field Theory*, arXiv:1612.01009, Lecture 2 (§ 2.4–2.5) and
Lecture 9, Proposition 9.1.

Conventions. The target is a finite-dimensional real normed space `E`; an almost complex
structure is only required on an open subset `O ⊆ E`. A point of the domain is `z = s + i t ∈ ℂ`,
`∂ₛu = Du(z) 1` and `∂ₜu = Du(z) i`.

* `IsAlmostComplexOn J O`: `O` is open, `J : E → (E →L[ℝ] E)` is `C^∞` on `O` and
  `J(x)² = -1` for `x ∈ O` (Wendl, Lecture 2).
* `dbarJ J u z = ∂ₛu + J(u) ∂ₜu`, the nonlinear Cauchy–Riemann operator `∂̄_J` (Wendl § 2.4.2).
* `IsJHolomorphicOn J U u`: `u` is differentiable at every `z ∈ U` and `∂̄_J u(z) = 0`.
* `HasWeakPartialsOn U u uₛ uₜ`: `uₛ`, `uₜ` are the weak partial derivatives of `u` on `U`,
  tested against real `C^∞` functions with compact support in `U`.
* `IsWeakJHolomorphicOn p J O U u`: `u` is continuous on `U` with values in `O`, `u` and its
  weak partials lie in `L^p(K)` for every compact `K ⊆ U`, and `uₛ + J(u) uₜ = 0` almost
  everywhere on `U`. For `p > 2` this is a `W^{1,p}_loc` solution of `∂̄_J u = 0` (Wendl, Theorem 2.22 (1) and Remark 2.25).
* `TendstoCInftyLocOn f g O`: `f ν → g` in `C^∞_loc` on `O`, i.e. every derivative `Dᵐ f ν`
  converges to `Dᵐ g` uniformly on every compact subset of `O`.

The `W^{k,p}(U)` norm `DbarRegularity.sobolevNorm` of the `DbarRegularity` mission is reused.
-/

namespace JHolomorphic

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `J` is a smooth almost complex structure on the open set `O ⊆ E`: `J` is `C^∞` on `O` and
`J(x) ∘ J(x) = -1` for every `x ∈ O`. -/
def IsAlmostComplexOn (J : E → E →L[ℝ] E) (O : Set E) : Prop :=
  IsOpen O ∧ ContDiffOn ℝ ∞ J O ∧ ∀ x ∈ O, (J x).comp (J x) = -ContinuousLinearMap.id ℝ E

/-- The nonlinear Cauchy–Riemann operator `∂̄_J u = ∂ₛu + J(u) ∂ₜu` at `z = s + i t`. -/
def dbarJ (J : E → E →L[ℝ] E) (u : ℂ → E) (z : ℂ) : E :=
  fderiv ℝ u z 1 + J (u z) (fderiv ℝ u z Complex.I)

/-- `u` is `J`-holomorphic on `U`: it is differentiable at every `z ∈ U` and
`∂ₛu + J(u) ∂ₜu = 0` there. -/
def IsJHolomorphicOn (J : E → E →L[ℝ] E) (U : Set ℂ) (u : ℂ → E) : Prop :=
  ∀ z ∈ U, DifferentiableAt ℝ u z ∧ dbarJ J u z = 0

/-- `uₛ` and `uₜ` are weak partial derivatives of `u` on `U`: for every real `C^∞` function `φ`
with compact support in `U`, `∫ (∂ₛφ) u = -∫ φ uₛ` and `∫ (∂ₜφ) u = -∫ φ uₜ`. -/
def HasWeakPartialsOn (U : Set ℂ) (u us ut : ℂ → E) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
    (∫ z, fderiv ℝ φ z 1 • u z = -∫ z, φ z • us z) ∧
      (∫ z, fderiv ℝ φ z Complex.I • u z = -∫ z, φ z • ut z)

/-- `u` is a `W^{1,p}_loc` solution of `∂̄_J u = 0` on `U` with values in `O`: `u` is continuous
on `U` with `u(U) ⊆ O`, `u` has weak partial derivatives `uₛ`, `uₜ` on `U`, the three maps lie in
`L^p(K)` for every compact `K ⊆ U`, and `uₛ + J(u) uₜ = 0` almost everywhere on `U`. -/
def IsWeakJHolomorphicOn (p : ℝ) (J : E → E →L[ℝ] E) (O : Set E) (U : Set ℂ) (u : ℂ → E) :
    Prop :=
  ContinuousOn u U ∧ Set.MapsTo u U O ∧
    ∃ us ut : ℂ → E, HasWeakPartialsOn U u us ut ∧
      (∀ K ⊆ U, IsCompact K →
        MemLp u (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp us (ENNReal.ofReal p) (volume.restrict K) ∧
        MemLp ut (ENNReal.ofReal p) (volume.restrict K)) ∧
      ∀ᵐ z ∂(volume.restrict U), us z + J (u z) (ut z) = 0

/-- `f ν → g` in `C^∞_loc` on `O`: for every compact `K ⊆ O` and every `m`, the `m`-th
derivatives `Dᵐ (f ν)` converge to `Dᵐ g` uniformly on `K`. -/
def TendstoCInftyLocOn {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : ℕ → X → Y) (g : X → Y) (O : Set X) : Prop :=
  ∀ K ⊆ O, IsCompact K → ∀ m : ℕ,
    TendstoUniformlyOn (fun ν => iteratedFDeriv ℝ m (f ν)) (iteratedFDeriv ℝ m g) atTop K

end

end JHolomorphic


