-- Prove2me | Definitions.Def_ModularCurve_FullLevelLevelAutAt
-- name    : ModularCurve_FullLevelLevelAutAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/6797c8b2-da5b-59f8-8b2e-c85fde4a967b
-- title:
--   Conjugated matrix and a level-automorphism predicate
-- statement:
--   Two declarations. First, for $m\ge 1$ and $\gamma=\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\mathrm{SL}_2(\mathbb{Z})$, `conjElemN m γ` is the element of $\mathrm{GL}_2(\mathbb{R})$ given by the real matrix $\begin{pmatrix}a&b/m\\mc&d\end{pmatrix}$, that is $\operatorname{diag}(m,1)^{-1}\gamma\operatorname{diag}(m,1)$; its determinant equals $\det\gamma=1$, which is what makes the matrix invertible.
--
--   Second, `IsLevelAutAt` is a predicate pinning down an automorphism of a subfield of a Laurent-series field by its effect on ratios of $q$-expansions. Its data are: a field $L$ of characteristic zero, an integer $n$ and an element $\zeta\in L$, an integer $m\ge 1$, a level $N_0$ with a subgroup $H\le(\mathbb{Z}/N_0)^\times$, a matrix $\gamma\in\mathrm{SL}_2(\mathbb{Z})$, an intermediate field $K$ of $L((q))/L$ and an $L$-algebra automorphism $\tau$ of $K$. The predicate asserts: for every weight $k\in\mathbb{Z}$, all modular forms $f,g$ of weight $k$ for the subgroup [`CohCarrier.GammaH N₀ H`](../def/CohCarrier_Level.html#L133) of $\mathrm{GL}_2(\mathbb{R})$ attached to $(N_0,H)$, all integral power series $p_f,p_g$ with `IsIntegralQExp f pf` and `IsIntegralQExp g pg` and with the rational Laurent series `intSeriesC ℚ pg` nonzero, every $x\in K$ whose underlying Laurent series is the coefficientwise image in $L((q))$ of `intSeriesC ℚ pf / intSeriesC ℚ pg`, and every ring homomorphism $\iota\colon L\to\mathbb{C}$ with $\iota(\zeta)=e^{2\pi i/n}$, one has, in $\mathbb{C}((q))$,
--   $$\iota_*\big(\tau(x)\big)\cdot \big(g\mid_k \mathtt{conjElemN }m\,\gamma\big)^{\wedge} = \big(f\mid_k \mathtt{conjElemN }m\,\gamma\big)^{\wedge},$$
--   where $\iota_*$ is the coefficientwise application of $\iota$ and $(\cdot)^{\wedge}$ denotes the width-one $q$-expansion. Thus $\tau$ sends the modular function $f/g$ to $(f\mid_k\gamma^{\sharp})/(g\mid_k\gamma^{\sharp})$, read through the complex embedding normalised by $\iota(\zeta)=e^{2\pi i/n}$. This is a variant of [`ModularCurve.FullLevel.IsLevelAutBar`](../def/ModularCurve_FullLevelJacobian.html#L166) with an arbitrary constant field $L$ in place of $\overline{\mathbb{Q}}$, the order $n$ of the distinguished root of unity and the conjugating modulus $m$ as parameters, an arbitrary level datum $(N_0,H)$, and the relevant elements of $K$ described directly by their Laurent expansions.
--
--   **Relation to Mathlib.** The weight-$k$ slash action, `qExpansion`, Laurent series as Hahn series, intermediate fields and `Matrix.GeneralLinearGroup.mkOfDetNeZero` are Mathlib's; the conjugated matrix and the level-automorphism predicate are the project's own.
--
--   **Where it is used.** Predicates of this shape specify the automorphisms of the function fields of the modular curves $X(\Gamma(m)\cap\Gamma_0(M'))$ that induce, on the associated Jacobians, the level operators out of which the $\mathrm{GL}_2(\mathbb{Z}/q)$-action on the full-level Jacobian is assembled, together with the diamond operators; that action is what makes the cuspidal-type analysis at level $q$ available in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_FullLevelLevelAutAt.lean

import Definitions.Def_ModularCurve_FullLevelJacobian

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane IntermediateField HahnSeries AlgebraicCurve CongruenceSubgroup

open scoped MatrixGroups ModularForm

namespace ModularCurve.FullLevel

def conjElemN (m : ℕ) [NeZero m] (γ : SL(2, ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((γ 0 0 : ℤ) : ℝ), ((γ 0 1 : ℤ) : ℝ) / m; (m : ℝ) * ((γ 1 0 : ℤ) : ℝ), ((γ 1 1 : ℤ) : ℝ)]
    (by
      have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
      have hdet : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe γ
        rw [Matrix.det_fin_two] at h
        exact_mod_cast h
      rw [Matrix.det_fin_two_of]
      have : ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) / m * ((m : ℝ) * ((γ 1 0 : ℤ) : ℝ)) =
          ((γ 0 0 : ℤ) : ℝ) * ((γ 1 1 : ℤ) : ℝ) - ((γ 0 1 : ℤ) : ℝ) * ((γ 1 0 : ℤ) : ℝ) := by
        field_simp
      rw [this, hdet]
      exact one_ne_zero)

def IsLevelAutAt (L : Type) [Field L] [CharZero L] (n : ℕ) (ζ : L) (m : ℕ) [NeZero m]
    (N₀ : ℕ) (H : Subgroup (ZMod N₀)ˣ) (γ : SL(2, ℤ))
    (K : IntermediateField L (LaurentSeries L)) (τ : ↥K ≃ₐ[L] ↥K) : Prop :=
  ∀ (k : ℤ) (f g : ModularForm (CohCarrier.GammaH N₀ H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg : PowerSeries ℤ) (_hf : IsIntegralQExp f pf) (_hg : IsIntegralQExp g pg)
    (_hg0 : intSeriesC ℚ pg ≠ 0)
    (x : ↥K) (_hx : ((x : ↥K) : LaurentSeries L) = coeffEmb L (intSeriesC ℚ pf / intSeriesC ℚ pg))
    (ι : L →+* ℂ), ι ζ = Complex.exp (2 * Real.pi * Complex.I / n) →
      coeffMap ι ((τ x : ↥K) : LaurentSeries L) *
          HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑g ∣[k] conjElemN m γ)) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 (⇑f ∣[k] conjElemN m γ))

end ModularCurve.FullLevel

end


