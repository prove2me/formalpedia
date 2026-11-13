-- Prove2me | Definitions.Def_FiniteEnergyPlane_Tube
-- name    : FiniteEnergyPlane_Tube
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-12T18:03:19.847237+00:00
-- url     : https://prove2.me/theorems/330c4a7e-5d82-4733-a0a6-1f81a626fe79
-- title:
--   Standard tube structures near $\mathbb{C}\times\{0\}$
-- statement:
--   Let $\mathrm{cylInf}(s,t) = e^{2\pi(s+it)}$ be the cylindrical coordinate at $z = \infty$ on $\mathbb{C}$, and let $J_{\mathrm{std}} = i \oplus i$ be multiplication by $i$ on both factors of $\mathbb{C} \times \mathbb{C}$, viewed as a real linear map.
--
--   **Cylindrical form.** For a field $\bar J : \mathbb{C} \times \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C} \times \mathbb{C})$, put
--   $$\mathrm{cylJ}(\bar J)(s,t,w) = \Lambda_{s,t}^{-1} \circ \bar J\big(e^{2\pi(s+it)}, w\big) \circ \Lambda_{s,t}, \qquad \Lambda_{s,t}(\sigma, \omega) = \big(2\pi e^{2\pi(s+it)}\sigma,\ \omega\big),$$
--   which is $\bar J$ written in the coordinates $(s+it, w)$ with $z = e^{2\pi(s+it)}$ ($\Lambda_{s,t}$ = `cylScale s t`, $\Lambda_{s,t}^{-1}$ = `cylScaleInv s t`).
--
--   **Exponential decay on a tube.** For $f : \mathbb{R} \times \mathbb{R} \times \mathbb{C} \to F$ and $\rho, b \in \mathbb{R}$, `ExpDecayCInftyTube f ρ b` means: $f$ is $C^\infty$ on $(s_0, \infty) \times \mathbb{R} \times B_\rho(0)$ for some $s_0$, and for every $m \in \mathbb{N}$ there are $C, s_1$ with
--   $$\|D^m f(s,t,w)\| \le C e^{-bs} \qquad (s \ge s_1,\ t \in \mathbb{R},\ |w| < \rho).$$
--
--   **Standard tube structure.** For $\rho, b \in \mathbb{R}$, $\bar J$ as above, $J_\infty : \mathbb{R} \times \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C}\times\mathbb{C})$ and a loop $S_\infty : \mathbb{R} \to \mathbb{R}^{2\times 2}$, the predicate `IsStdTubeStructure ρ b Jbar Jinf Sinf` is the conjunction of:
--   1. $\bar J$ is $C^\infty$ on $\mathbb{C} \times B_\rho(0)$ and $\bar J^2 = -\mathrm{id}$ there;
--   2. $\bar J(z, 0) = J_{\mathrm{std}}$ for every $z \in \mathbb{C}$;
--   3. $J_\infty$ is $C^\infty$ on $\mathbb{R} \times B_\rho(0)$ and $1$-periodic in $t$;
--   4. $(s,t,w) \mapsto \mathrm{cylJ}(\bar J)(s,t,w) - J_\infty(t,w)$ satisfies `ExpDecayCInftyTube` with rate $b$ on $B_\rho(0)$;
--   5. $S_\infty(t)$ is symmetric for every $t$ (`IsSymLoop`);
--   6. for all $t$ and $a \in \mathbb{R}^2 \cong \mathbb{C}$,
--   $$S_\infty(t)\,a = \Big[\big(\partial_w J_\infty(t, 0)\,a\big)(i, 0)\Big]_2,$$
--   the second component of the $w$-derivative of $J_\infty$ at $w = 0$ in direction $a$, applied to $(i, 0)$.
--
--   So $\bar J$ is an almost complex structure near $\mathbb{C} \times \{0\}$ for which $\mathbb{C} \times \{0\}$ is a $\bar J$-complex line, and which is asymptotically cylindrical at $z = \infty$ with $t$-periodic limit $J_\infty$; $S_\infty$ is the zero-order term of the normal linearization of the limit along $w = 0$, with the sign convention of the Cauchy–Riemann operators $\partial_s + J_0 \partial_t + S$ of `CauchyRiemannIndex`.
--
--   **Role.** This is the normal form of an almost complex structure in a tubular neighbourhood of a fast finite-energy plane with a nondegenerate asymptotic orbit, in coordinates where the plane is $\mathbb{C} \times \{0\}$. It is the interface between the construction of such coordinates and the analysis of $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ (families of nearby planes, as in Hryniewicz's Lemmas 6.10 and 6.20). Statements about such families can then be phrased without Reeb dynamics.
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_CylClose
import Mathlib

/-!
# Standard tube structures

Almost complex structures `Jbar` on `ℂ × ℂ`, defined near `ℂ × {0}`, which equal `i ⊕ i` along
`w = 0` and which, in the cylindrical coordinates `z = e^{2π(s + it)}` at `z = ∞`, converge
exponentially in `C^∞` to a `t`-periodic limit `Jinf`. The `w`-derivative of `Jinf` along `w = 0`
gives a symmetric loop `Sinf` of real `2 × 2` matrices.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

noncomputable section

/-- Multiplication by `i` on both factors of `ℂ × ℂ`, as a real linear map. -/
def jStd : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.prodMap (Complex.I • ContinuousLinearMap.id ℝ ℂ)
    (Complex.I • ContinuousLinearMap.id ℝ ℂ)

/-- The derivative `(σ + iτ, ω) ↦ (2π e^{2π(s+it)} (σ + iτ), ω)` of `(ζ, w) ↦ (e^{2πζ}, w)` at
`ζ = s + it`. -/
def cylScale (s t : ℝ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.prodMap ((((2 * π : ℝ) : ℂ) * cylInf s t) • ContinuousLinearMap.id ℝ ℂ)
    (ContinuousLinearMap.id ℝ ℂ)

/-- The inverse of `cylScale s t`. -/
def cylScaleInv (s t : ℝ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  ContinuousLinearMap.prodMap ((((2 * π : ℝ) : ℂ) * cylInf s t)⁻¹ • ContinuousLinearMap.id ℝ ℂ)
    (ContinuousLinearMap.id ℝ ℂ)

/-- A structure `Jbar` on `ℂ × ℂ`, written in the coordinates `(s + it, w)` with
`z = e^{2π(s+it)}`. -/
def cylJ (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (s t : ℝ) (w : ℂ) : ℂ × ℂ →L[ℝ] ℂ × ℂ :=
  (cylScaleInv s t).comp ((Jbar (cylInf s t, w)).comp (cylScale s t))

/-- `f(s, t, w)` decays like `e^{-bs}` in `C^∞` as `s → +∞`, uniformly in `t ∈ ℝ` and
`w ∈ ball 0 ρ`. -/
def ExpDecayCInftyTube {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ × ℝ × ℂ → F) (ρ b : ℝ) : Prop :=
  (∃ s₀ : ℝ, ContDiffOn ℝ ∞ f (Set.Ioi s₀ ×ˢ Set.univ ×ˢ ball (0 : ℂ) ρ)) ∧
    ∀ m : ℕ, ∃ C s₁ : ℝ, ∀ s ≥ s₁, ∀ t : ℝ, ∀ w ∈ ball (0 : ℂ) ρ,
      ‖iteratedFDeriv ℝ m f (s, t, w)‖ ≤ C * Real.exp (-(b * s))

/-- `Jbar` is a smooth almost complex structure on `ℂ × ball 0 ρ`, equal to `i ⊕ i` along
`w = 0`, which in cylindrical coordinates converges exponentially in `C^∞` (uniformly in `w`)
to a `t`-periodic `Jinf`; `Sinf` is the symmetric loop given by the `w`-derivative of `Jinf`
along `w = 0`: `Sinf(t) a = [(∂_w Jinf(t, 0) a)(i, 0)]₂`. -/
def IsStdTubeStructure (ρ b : ℝ) (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ)
    (Jinf : ℝ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (Sinf : ℝ → CauchyRiemannIndex.Mat 1) : Prop :=
  ContDiffOn ℝ ∞ Jbar (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
    (∀ p ∈ Set.univ ×ˢ ball (0 : ℂ) ρ,
      (Jbar p).comp (Jbar p) = -ContinuousLinearMap.id ℝ (ℂ × ℂ)) ∧
    (∀ z : ℂ, Jbar (z, 0) = jStd) ∧
    ContDiffOn ℝ ∞ Jinf (Set.univ ×ˢ ball (0 : ℂ) ρ) ∧
    (∀ (t : ℝ) (w : ℂ), Jinf (t + 1, w) = Jinf (t, w)) ∧
    ExpDecayCInftyTube (fun q : ℝ × ℝ × ℂ => cylJ Jbar q.1 q.2.1 q.2.2 - Jinf (q.2.1, q.2.2)) ρ b ∧
    CauchyRiemannIndex.IsSymLoop Sinf ∧
    ∀ (t : ℝ) (a : CauchyRiemannIndex.Vec 1),
      vecToC (Matrix.toEuclideanLin (Sinf t) a) =
        ((fderiv ℝ (fun w : ℂ => Jinf (t, w)) 0 (vecToC a)) (Complex.I, 0)).2

end

end FiniteEnergyPlane


