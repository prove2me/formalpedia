-- Prove2me | Definitions.Def_FiniteEnergyPlane_OpenBook
-- name    : FiniteEnergyPlane_OpenBook
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-04T15:46:54.451194+00:00
-- url     : https://prove2.me/theorems/6274e560-1d42-4308-bea0-1f9ea43fa01a
-- title:
--   Reeb trajectories, families of embedded fast planes along a trajectory, and open books of fast planes
-- statement:
--   Families of embedded fast planes in the symplectization of a strictly star-shaped level $S=H^{-1}(1)\subset\mathbb{R}^4$, in the setting of `FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Asymptotics`, `FiniteEnergyPlane_Winding`, `FiniteEnergyPlane_Compactness` and `FiniteEnergyPlane_Fredholm` with $n=1$ (U. Hryniewicz 2012, § 7). A family of planes is a map $U:\mathbb{R}\times\mathbb{C}\to\mathbb{R}^4$, and its $S$-component is $\mathrm{proj}\circ U$. Let $P=(x,T)$ be a periodic Reeb orbit and $\gamma\in\mathbb{R}$.
--
--   1. **Reeb trajectory.** A map $y:\mathbb{R}\to\mathbb{R}^{2n+2}$ with $y(t)\in S$ and $y'(t)=R(y(t))$ for all $t$.
--   2. **`pageMap H U`** is the map $(t,z)\mapsto\mathrm{proj}(U(t,z))$.
--   3. **`IsReebPositiveAt H U p`.** At $p\in\mathbb{R}\times\mathbb{C}$ there are $c>0$ and $v\in\mathbb{C}$ with $D(\mathrm{pageMap}\,H\,U)(p)(c,v)=R(\mathrm{pageMap}\,H\,U\,(p))$.
--   4. **`IsPageFamilyOn H J P γ y l I U`.** $U$ is of class $C^l$ on $I\times\mathbb{C}$, and $U(t,\cdot)\in\Lambda(\{y(t)\},P)$ for every $t\in I$.
--   5. **`IsPageFoliation H J P γ y l L δ U`.** $U$ is such a family on $I=(-\delta,L+\delta)$; on $I\times\mathbb{C}$ the map $\mathrm{pageMap}\,H\,U$ avoids $x(\mathbb{R})$, has injective derivative, and is Reeb positive; the leaves at $t=0$ and $t=L$ have the same image $\Sigma$; and $\mathrm{pageMap}\,H\,U$ maps $(0,L)\times\mathbb{C}$ bijectively onto $S\setminus(\Sigma\cup x(\mathbb{R}))$.
--   6. **`IsPlaneOpenBook H J P l U`.** $U$ is of class $C^l$ on $\mathbb{R}\times\mathbb{C}$ and $1$-periodic in the first variable; every $U(\theta,\cdot)$ is an embedded fast finite-energy plane asymptotic to $P$ at $\infty$; $\mathrm{pageMap}\,H\,U$ avoids $x(\mathbb{R})$; every $q\in S\setminus x(\mathbb{R})$ is the image of exactly one point of $[0,1)\times\mathbb{C}$; and the derivative of $\mathrm{pageMap}\,H\,U$ is injective and Reeb positive at every point.
--
--   **Formalization Note** The point $(0,q)\in\mathbb{R}\times S$ is $q$ itself in $\mathbb{R}^4\setminus\{0\}$, so Hryniewicz's set $\Lambda_t=\Lambda(\{(0,y(t))\},P)$ of (101) is `embeddedFastPlaneSet H J P {y t} γ`. "Orientation preserving" for $u:S^1\times\mathbb{C}\to M\setminus x(\mathbb{R})$ in Hryniewicz's Theorem 2.5 is stated as Reeb positivity. For a map with injective derivative whose slices are fast planes, the two agree: $S$ is oriented by $\lambda\wedge d\lambda$, and since $\lambda(R)=1$ and $i_Rd\lambda=0$, one has $(\lambda\wedge d\lambda)(\partial_\theta u,\partial_su,\partial_tu)=d\lambda(\partial_su,\partial_tu)/c$ with $d\lambda(\partial_su,\partial_tu)>0$ on a fast plane. The circle $S^1=\mathbb{R}/L\mathbb{Z}$ of Hryniewicz's statement is normalized to period $1$, and a map on the circle is a periodic map on $\mathbb{R}$. A bijective $C^l$ map with injective derivative onto $S\setminus x(\mathbb{R})$ is a $C^l$ diffeomorphism, so "diffeomorphism" is not stated separately. No flow map is used: trajectories are maps $y$ with the stated derivative.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Theorem 2.5, formula (101), and Lemma 7.7

import Definitions.Def_FiniteEnergyPlane_Fredholm

/-!
# Families of embedded fast finite-energy planes and open book decompositions

U. Hryniewicz, *Fast finite-energy planes in symplectizations and applications*, Trans. AMS 364
(2012), § 2 (Theorem 2.5) and § 7. Everything is in the setting of `FiniteEnergyPlane_Setting`,
`FiniteEnergyPlane_Asymptotics`, `FiniteEnergyPlane_Winding`, `FiniteEnergyPlane_Compactness` and
`FiniteEnergyPlane_Fredholm` for `n = 1`: `S = H⁻¹(1) ⊂ V 1 = ℝ⁴` strictly star-shaped, and the
symplectization `ℝ × S` is `V 1 \ {0}` with `y = e^{2 aCoord y} • proj y`.

Conventions.
* A family of planes is a map `U : ℝ × ℂ → V 1`; its `S`-component is `pageMap H U = proj H ∘ U`.
* The point `(0, q) ∈ ℝ × S` is `q` itself, so Hryniewicz's set `Λₜ = Λ({(0, y(t))}, P)` is
  `embeddedFastPlaneSet H J P {y t} γ`.
* "Orientation preserving" for a map into the oriented manifold `S` is expressed against the Reeb
  field, see `IsReebPositiveAt`.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- `y : ℝ → V n` is a trajectory of the Reeb field on `S = H⁻¹(1)`: `y(t) ∈ S` and `y' = R(y)`. -/
def IsReebTrajectory {n : ℕ} (H : V n → ℝ) (y : ℝ → V n) : Prop :=
  (∀ t, y t ∈ energySurface H) ∧ ∀ t, HasDerivAt y (reeb H (y t)) t

/-- The `S`-component `(t, z) ↦ proj H (U (t, z))` of a family `U : ℝ × ℂ → V n` of planes. -/
def pageMap {n : ℕ} (H : V n → ℝ) (U : ℝ × ℂ → V n) (p : ℝ × ℂ) : V n := proj H (U p)

/-- At `p`, the Reeb vector at `pageMap H U p` is the image under the derivative of `pageMap H U`
of a vector whose `ℝ`-component is positive. -/
def IsReebPositiveAt {n : ℕ} (H : V n → ℝ) (U : ℝ × ℂ → V n) (p : ℝ × ℂ) : Prop :=
  ∃ c > 0, ∃ v : ℂ, fderiv ℝ (pageMap H U) p (c, v) = reeb H (pageMap H U p)

/-- Hryniewicz (2012), § 7.1: `U` is a `C^l` family on `I × ℂ` along the trajectory `y`, with
`U(t, ·) ∈ Λₜ = Λ({y t}, P)` for every `t ∈ I`. -/
def IsPageFamilyOn (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (γ : ℝ)
    (y : ℝ → V 1) (l : ℕ) (I : Set ℝ) (U : ℝ × ℂ → V 1) : Prop :=
  ContDiffOn ℝ l U (I ×ˢ Set.univ) ∧
    ∀ t ∈ I, (fun z => U (t, z)) ∈ embeddedFastPlaneSet H J P {y t} γ

/-- Hryniewicz (2012), Lemma 7.7: `U` is a `C^l` family along `y` on `(-δ, L + δ) × ℂ`, whose map
`pageMap H U` avoids `x(ℝ)`, has injective derivative and is positive against the Reeb field. The
leaves at `t = 0` and `t = L` have the same image, and `pageMap H U` maps `(0, L) × ℂ` bijectively
onto the complement in `S` of that leaf and of `x(ℝ)`. -/
def IsPageFoliation (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (γ : ℝ)
    (y : ℝ → V 1) (l : ℕ) (L δ : ℝ) (U : ℝ × ℂ → V 1) : Prop :=
  IsPageFamilyOn H J P γ y l (Set.Ioo (-δ) (L + δ)) U ∧
    (∀ p ∈ Set.Ioo (-δ) (L + δ) ×ˢ (Set.univ : Set ℂ),
      pageMap H U p ∉ Set.range P.x ∧ Function.Injective (fderiv ℝ (pageMap H U) p) ∧
        IsReebPositiveAt H U p) ∧
    Set.range (fun z => pageMap H U (L, z)) = Set.range (fun z => pageMap H U (0, z)) ∧
    Set.BijOn (pageMap H U) (Set.Ioo 0 L ×ˢ Set.univ)
      (energySurface H \ (Set.range (fun z => pageMap H U (0, z)) ∪ Set.range P.x))

/-- Hryniewicz (2012), Theorem 2.5 (1) and (2): `U : ℝ × ℂ → V 1` is `C^l` and `1`-periodic in the
first variable; every `U(θ, ·)` is an embedded fast finite-energy plane asymptotic to `P` at `∞`;
`pageMap H U` avoids `x(ℝ)` and maps `[0, 1) × ℂ` bijectively onto `S \ x(ℝ)`, with injective
derivative, and it is positive against the Reeb field. -/
def IsPlaneOpenBook (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (l : ℕ)
    (U : ℝ × ℂ → V 1) : Prop :=
  ContDiff ℝ l U ∧ (∀ θ z, U (θ + 1, z) = U (θ, z)) ∧
    (∀ θ, IsFastPlane H J (fun z => U (θ, z)) ∧
      IsNondegenerateEnd H (fun z => U (θ, z)) cylInf P 1 ∧ IsEmbeddedPlane (fun z => U (θ, z))) ∧
    (∀ p, pageMap H U p ∉ Set.range P.x) ∧
    (∀ q ∈ energySurface H, q ∉ Set.range P.x →
      ∃! p : ℝ × ℂ, p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ pageMap H U p = q) ∧
    (∀ p, Function.Injective (fderiv ℝ (pageMap H U) p)) ∧
    ∀ p, IsReebPositiveAt H U p

end

end FiniteEnergyPlane


