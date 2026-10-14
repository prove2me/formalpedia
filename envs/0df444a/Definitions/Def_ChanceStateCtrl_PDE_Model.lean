-- Prove2me | Definitions.Def_ChanceStateCtrl_PDE_Model
-- name    : ChanceStateCtrl_PDE_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:47.621436+00:00
-- url     : https://prove2.me/theorems/27ca6357-ed21-4c47-ac92-c78ca812f9f4
-- title:
--   §1.2, §2.2–2.4, pp. 3–4, 9, 12, 14 — class-S domain, weak Dirichlet solution, S, P, g of (24), u_x, M*(ū, v), the set-valued integrand of (40)
-- statement:
--   The model of the paper's PDE application.
--
--   1. **Class S** (p. 3): $D\subseteq\mathbb R^d$ is of class S if there are $\gamma\in(0,1)$ and $r_0>0$ with $\operatorname{meas}(B_r(x)\setminus D)\ge\gamma\operatorname{meas}(B_r(x))$ for all $x\in\partial D$ and all $0<r<r_0$.
--   2. **$L^2(D)$** with the Lebesgue measure.
--   3. **Weak Dirichlet solution**: $y\in H^1_0(D)\cap C(\bar D)$ solves $-\Delta y=F$ in $D$, $y=0$ on $\partial D$, if $y$ is continuous on $\bar D$, vanishes on $\partial D$, lies in $L^2(D)$ with weak first derivatives $\partial_iy\in L^2(D)$, and
--   $$\int_D\sum_{i=1}^d\partial_iy\,\partial_i\phi\,dx=\int_DF\phi\,dx\qquad\forall\phi\in C_c^\infty(D).$$
--   4. **Operators** (5), for the solution operator $A^{-1}:L^2(D)\to C(\bar D)$ and $f_0,\varphi_i\in L^2(D)$ of (3):
--   $$S(u,z)=A^{-1}\Big(u+f_0+\sum_{i=1}^mz_i\varphi_i\Big),\qquad P(u,z)=A^{-1}u+\sum_{i=1}^mz_iA^{-1}\varphi_i,$$
--   and the constraint function of (24), $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$.
--   5. **$u_x$** (Lemma 2.14): for $x\in\bar D$, the element of $L^2(D)$ with $(u_x,h)_{L^2(D)}=(A^{-1}h)(x)$ for all $h$.
--   6. **$M^*(\bar u,v)$** (Lemma 2.14), with $\bar y=S(\bar u,0)$:
--   $$M^*(\bar u,v)=\{x\in\bar D\mid[P(0,\Sigma^{1/2}v)](x)>0,\ \bar y(x)+\rho(\bar u,v)[P(0,\Sigma^{1/2}v)](x)=\alpha\}.$$
--   7. **The integrand and the integral of (40)/(43)**: $K(\bar u,v)=\operatorname{clco}\{[P(0,\Sigma^{1/2}v)](x)^{-1}\,u_x\mid x\in M^*(\bar u,v)\}$ (closed convex hull in $L^2(D)$), and
--   $$I(\bar u)=\int_{\{v\in\mathbb S^{m-1}\mid\rho(\bar u,v)<\infty\}}\chi(\rho(\bar u,v))\cdot K(\bar u,v)\,d\mu_\zeta(v),$$
--   the Aumann integral over the restriction of $\mu_\zeta$.
--   8. **Theorem 2.15's equality conditions**: $M^*(\bar u,v)$ is a singleton for $\mu_\zeta$-a.e. $v$ with $\rho(\bar u,v)<\infty$, or the set $M=\{z\in\mathbb R^m\mid g(\bar u,z)\le0\}$ of (11) is bounded.
--
--   These are the explicit problem data in which Theorems 2.15 and 2.16 are stated.
--
--   **Formalization Note** An $H^1(D)$ function that is continuous on $\bar D$ and vanishes on $\partial D$ lies in $H^1_0(D)$ ($D$ bounded), so item 3 is the paper's class $H^1_0(D)\cap C(\bar D)$; weak derivatives are the published `HunterPDE.Shared.HasWeakDeriv`. The normed space $C(\bar D)$ needs `CompactSpace (closure D)`, which follows from boundedness. The maximum in $g$ is a supremum over $\bar D$ (equal to the maximum for nonempty $D$ by compactness; the page shows it equals the supremum over $D$). $u_x$ is the Riesz representative of $h\mapsto (A^{-1}h)(x)$, continuous because $A^{-1}$ maps into $C(\bar D)$. In $M^*$, $\rho(\bar u,v)$ is used as a real number and the set is only used where $\rho(\bar u,v)<\infty$. The closed convex hull is the norm closure of the convex hull, which agrees with the weak closure (Mazur). $I(\bar u)$ is the integral without the leading minus sign of (40); the theorems write $-I(\bar u)$. For empty $D$ the supremum in $g$ is the junk value $0$, so the theorems using $g$ assume $D$ nonempty.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 3–4 (§1.2, class S, (2), (3), Assumption 1.1, (5)), p. 9 ((24)), p. 12 (Lemma 2.14: u_x, M*(ū, v)), p. 14 (Theorem 2.15, (40))

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Definitions.Def_ChanceStateCtrl_PDE_Setting

open MeasureTheory Filter Topology
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

section Domain

variable {d : ℕ}

/-- The domain `D ⊆ ℝ^d` is of class S (p. 3): there are `γ ∈ (0, 1)` and `r₀ > 0` with
`meas(B_r(x) \ D) ≥ γ meas(B_r(x))` for all `x ∈ ∂D` and all `0 < r < r₀`. -/
def IsClassS (D : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ γ ∈ Set.Ioo (0 : ℝ) 1, ∃ r₀ > (0 : ℝ), ∀ x ∈ frontier D, ∀ r : ℝ, 0 < r → r < r₀ →
    ENNReal.ofReal γ * volume (Metric.ball x r) ≤ volume (Metric.ball x r \ D)

/-- `L²(D)`, the Lebesgue space on `D` with the Lebesgue measure. -/
abbrev L2 (D : Set (EuclideanSpace ℝ (Fin d))) : Type :=
  MeasureTheory.Lp ℝ 2 (volume.restrict D)

/-- `y ∈ H¹₀(D) ∩ C(D̄)` is a weak solution of `-Δy = F` in `D`, `y = 0` on `∂D`: `y` is continuous
on `D̄`, vanishes on `∂D`, lies in `L²(D)` with weak first derivatives `G i = ∂_i y ∈ L²(D)`, and
`∫_D ∑_i ∂_i y ∂_i φ = ∫_D F φ` for every test function `φ ∈ C_c^∞(D)`. -/
def IsDirichletSol (D : Set (EuclideanSpace ℝ (Fin d))) (F y : EuclideanSpace ℝ (Fin d) → ℝ) :
    Prop :=
  ContinuousOn y (closure D) ∧ (∀ x ∈ frontier D, y x = 0) ∧ MemLp y 2 (volume.restrict D) ∧
    ∃ G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ i, MemLp (G i) 2 (volume.restrict D) ∧
        HunterPDE.Shared.HasWeakDeriv D (Pi.single i 1) y (G i)) ∧
      ∀ φ, HunterPDE.Shared.IsTestFunction D φ →
        ∫ x in D, ∑ i, G i x * HunterPDE.Shared.partialDeriv φ i x = ∫ x in D, F x * φ x

end Domain

section Operators

variable {d m : ℕ} {D : Set (EuclideanSpace ℝ (Fin d))} [CompactSpace (closure D)]

/-- The control-to-state operator (5): `S(u, z) = A⁻¹(u + f(·, z))` with
`f(·, z) = f₀ + ∑ᵢ zᵢ φᵢ` (3). -/
noncomputable def stateS (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D)
    (u : L2 D) (z : EuclideanSpace ℝ (Fin m)) : C(closure D, ℝ) :=
  Ainv (u + f₀ + ∑ i, z i • φ i)

/-- The linear part of (5): `P(u, z) = A⁻¹u + ∑ᵢ zᵢ A⁻¹φᵢ`. -/
noncomputable def stateP (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (φ : Fin m → L2 D)
    (u : L2 D) (z : EuclideanSpace ℝ (Fin m)) : C(closure D, ℝ) :=
  Ainv u + ∑ i, z i • Ainv (φ i)

/-- The constraint function of (24): `g(u, z) = max_{x ∈ D̄} [S(u, z)](x) - α`. -/
noncomputable def gPDE (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D)
    (α : ℝ) (u : L2 D) (z : EuclideanSpace ℝ (Fin m)) : ℝ :=
  (⨆ x : closure D, stateS Ainv f₀ φ u z x) - α

/-- `u_x ∈ L²(D)` (Lemma 2.14): the Riesz representative of `h ↦ [P(h, 0)](x) = (A⁻¹h)(x)`. -/
noncomputable def ux (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (x : closure D) : L2 D :=
  (InnerProductSpace.toDual ℝ (L2 D)).symm ((ContinuousMap.evalCLM ℝ x).comp Ainv)

/-- `M*(ū, v) = {x ∈ D̄ | [P(0, Σ^{1/2}v)](x) > 0, ȳ(x) + ρ(ū, v)[P(0, Σ^{1/2}v)](x) = α}`
(Lemma 2.14), with `ȳ = S(ū, 0)`; used only where `ρ(ū, v) < ∞`. -/
def Mstar (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (Sigma : Matrix (Fin m) (Fin m) ℝ) (ubar : L2 D)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : Set (closure D) :=
  {x | 0 < stateP Ainv φ 0 (sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m))) x ∧
    stateS Ainv f₀ φ ubar 0 x +
      (radius (gPDE Ainv f₀ φ α) Sigma ubar v).toReal *
        stateP Ainv φ 0 (sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m))) x = α}

/-- `clco{ [P(0, Σ^{1/2}v)](x)⁻¹ · u_x | x ∈ M*(ū, v) }`, the closed convex hull in `L²(D)`. -/
noncomputable def Kset (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D)
    (α : ℝ) (Sigma : Matrix (Fin m) (Fin m) ℝ) (ubar : L2 D)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1) : Set (L2 D) :=
  closure (convexHull ℝ
    ((fun x => (stateP Ainv φ 0 (sigmaRoot Sigma (v : EuclideanSpace ℝ (Fin m))) x)⁻¹ • ux Ainv x) ''
      Mstar Ainv f₀ φ α Sigma ubar v))

/-- The Aumann integral of (40)/(43):
`∫_{{v ∈ S^{m-1} | ρ(ū, v) < ∞}} χ(ρ(ū, v)) · clco{ … } dμ_ζ(v)`, over the restriction of `μ_ζ`. -/
noncomputable def integralSet (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D)
    (α : ℝ) (Sigma : Matrix (Fin m) (Fin m) ℝ) (ubar : L2 D) : Set (L2 D) :=
  aumannL2 ((sphereLaw m).restrict {v | radius (gPDE Ainv f₀ φ α) Sigma ubar v < ⊤})
    (fun v => chiDensity m (radius (gPDE Ainv f₀ φ α) Sigma ubar v).toReal •
      Kset Ainv f₀ φ α Sigma ubar v)

/-- Theorem 2.15's conditions for equality in (40): `M*(ū, v)` is a singleton for `μ_ζ`-a.e. `v`
with `ρ(ū, v) < ∞`, or the set `M = {z | g(ū, z) ≤ 0}` of (11) is bounded. -/
def EqCond (Ainv : L2 D →L[ℝ] C(closure D, ℝ)) (f₀ : L2 D) (φ : Fin m → L2 D)
    (α : ℝ) (Sigma : Matrix (Fin m) (Fin m) ℝ) (ubar : L2 D) : Prop :=
  (∀ᵐ v ∂(sphereLaw m), radius (gPDE Ainv f₀ φ α) Sigma ubar v < ⊤ →
      ∃ x, Mstar Ainv f₀ φ α Sigma ubar v = {x}) ∨
    Bornology.IsBounded {z : EuclideanSpace ℝ (Fin m) | gPDE Ainv f₀ φ α ubar z ≤ 0}

end Operators

end ChanceStateCtrl.PDE


