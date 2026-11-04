-- Prove2me | Definitions.Def_FiniteEnergyPlane_Fredholm
-- name    : FiniteEnergyPlane_Fredholm
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-03T21:07:56.127461+00:00
-- url     : https://prove2.me/theorems/7f5ea34f-54cf-4f73-bc9f-78e555767d68
-- title:
--   Embedded planes, translations in the symplectization, and the set $\Lambda(K,P)$
-- statement:
--   Embedded planes and translations in the symplectization of a strictly star-shaped level $S=H^{-1}(1)\subset\mathbb{R}^4$, in the setting of `FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Asymptotics`, `FiniteEnergyPlane_Winding` and `FiniteEnergyPlane_Compactness` with $n=1$ (U. Hryniewicz 2012, § 2). The symplectization $\mathbb{R}\times S$ is $\mathbb{R}^4\setminus\{0\}$ with $y=e^{2a}x$, $x\in S$; a plane $\tilde u=(a,u)$ is a map $\mathbb{C}\to\mathbb{R}^4$ whose $S$-component is $\mathrm{proj}\circ\tilde u$.
--
--   1. **Embedded plane.** A map $u:\mathbb{C}\to\mathbb{R}^{2n+2}$ is an embedded plane if it is injective and its derivative $du(z)$ is injective at every $z\in\mathbb{C}$.
--   2. **Translation** (Hryniewicz, Remark 3.10). For $c\in\mathbb{R}$, $c\cdot u$ is the map $z\mapsto e^{2c}u(z)$. It adds $c$ to the $\mathbb{R}$-coordinate $a\circ u$ and leaves the $S$-component unchanged.
--   3. **The set $\Lambda(K,P)$** (Hryniewicz (8)). For a periodic Reeb orbit $P$, a set $K\subset\mathbb{R}^4$ and $\gamma\in\mathbb{R}$: the embedded planes in the set $\Theta(K,P)$ of `FiniteEnergyPlane_Compactness` (fast planes asymptotic to $P$ at $\infty$ with $u(0)\in K$ and $d\lambda$-energy $\gamma$ outside the closed unit disk).
--
--   **Formalization Note** "Embedded" is stated as an injective immersion. Hryniewicz's "embedded" asks for an embedding, i.e. in addition a homeomorphism onto the image. The two agree for the planes of this mission: a finite-energy plane with a nondegenerate puncture at $\infty$ is a proper map (its $\mathbb{R}$-coordinate tends to $+\infty$ at $\infty$), and a proper injective immersion is an embedding. $\Lambda(K,P)$ is `embeddedFastPlaneSet H J P K γ`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 2, formula (8) and Theorem 2.3, and Remark 3.10

import Definitions.Def_FiniteEnergyPlane_Compactness

/-!
# Embedded fast finite-energy planes and translations in the symplectization

U. Hryniewicz, *Fast finite-energy planes in symplectizations and applications*, Trans. AMS 364
(2012), § 2 ((8), (10), Theorem 2.3) and § 6. Everything is in the setting of
`FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Asymptotics`, `FiniteEnergyPlane_Winding` and
`FiniteEnergyPlane_Compactness` for `n = 1`: `S = H⁻¹(1) ⊂ V 1 = ℝ⁴` strictly star-shaped, and the
symplectization `ℝ × S` is `V 1 \ {0}` with `y = e^{2 aCoord y} • proj y`.

Conventions.
* A plane `ũ = (a, u) : ℂ → ℝ × S` is a map `u : ℂ → V 1`; its `S`-component is `proj H ∘ u`.
* The translation `c · ũ = (a + c, u)` of Hryniewicz, Remark 3.10, is `y ↦ e^{2c} • y` in `V 1`.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `u : ℂ → V n` is an embedded plane: `u` is injective and its derivative is injective at every
point. -/
def IsEmbeddedPlane {n : ℕ} (u : ℂ → V n) : Prop :=
  Function.Injective u ∧ ∀ z, Function.Injective (fderiv ℝ u z)

/-- Hryniewicz, Remark 3.10: the translation `c · u` of `u` in the `ℝ`-direction of the
symplectization, `(c · u)(z) = e^{2c} • u(z)`. It adds `c` to `aCoord H ∘ u` and leaves
`proj H ∘ u` unchanged. -/
def shiftA {n : ℕ} (c : ℝ) (u : ℂ → V n) : ℂ → V n := fun z => Real.exp (2 * c) • u z

/-- Hryniewicz (2012), (8): the set `Λ(K, P)` of embedded planes in `Θ(K, P)`. -/
def embeddedFastPlaneSet (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H)
    (K : Set (V 1)) (γ : ℝ) : Set (ℂ → V 1) :=
  {u | u ∈ fastPlaneSet H J P K γ ∧ IsEmbeddedPlane u}

end

end FiniteEnergyPlane


