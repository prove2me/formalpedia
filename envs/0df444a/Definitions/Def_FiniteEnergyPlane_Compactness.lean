-- Prove2me | Definitions.Def_FiniteEnergyPlane_Compactness
-- name    : FiniteEnergyPlane_Compactness
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-03T16:23:06.548562+00:00
-- url     : https://prove2.me/theorems/55929435-f2f7-4729-aef4-e8c9a4372459
-- title:
--   Sets of fast finite-energy planes and sequential compactness in $C^\infty_{loc}$
-- statement:
--   Sets of fast finite-energy planes in the symplectization of a strictly star-shaped level $S=H^{-1}(1)\subset\mathbb{R}^4$, in the setting of `FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Asymptotics` and `FiniteEnergyPlane_Winding` with $n=1$ (U. Hryniewicz 2012, § 2). The symplectization $\mathbb{R}\times S$ is $\mathbb{R}^4\setminus\{0\}$ with $y=e^{2a}x$, $x\in S$.
--
--   1. **Conley–Zehnder lower bound.** For a periodic Reeb orbit $Q$ on $S$ and $m\in\mathbb{Z}$, "$\mu_{CZ}(Q)\ge m$" means: for every periodic orbit $R$ of the `HryniewiczCriterion` setting (for the same function) with the same image as $Q$ and action equal to the period of $Q$, and every linearized flow $Y$ along $R$, Hryniewicz's index `czIndexOfPath (linearizedXiPath … R Y)` is at least $m$.
--   2. **The set $\Theta(K,P)$** (Hryniewicz (7)). For a periodic Reeb orbit $P$, a set $K\subset\mathbb{R}^4$ and $\gamma\in\mathbb{R}$: the fast finite-energy planes $u$ (Hryniewicz 2014, Definition 2.14) whose puncture $\infty$ is nondegenerate with asymptotic limit $P$ (Definition 2.9, sign $+1$), with $u(0)\in K$, and with $d\lambda$-energy $\int_{\{|z|>1\}}u^*d\lambda=\gamma$.
--   3. **The set $\Theta_L(K,P)$** (Hryniewicz (9)): the planes of $\Theta(K,P)$ with $a(u(z))\ge-L$ for all $z$, where $a$ is the $\mathbb{R}$-coordinate of the symplectization.
--   4. **Sequential compactness in $C^\infty_{loc}$.** A set $A$ of maps $\mathbb{C}\to\mathbb{R}^4$ is sequentially compact in $C^\infty_{loc}$ if every sequence in $A$ has a subsequence converging in $C^\infty_{loc}(\mathbb{C})$ (every derivative uniformly on compact sets) to an element of $A$.
--
--   **Formalization Note** The compact set $H\subset\mathbb{R}\times S$ of Hryniewicz is a set $K\subset\mathbb{R}^4$; the theorems ask $K$ compact with $0\notin K$. The cylinder $\mathbb{R}\times x(\mathbb{R})$ over an orbit is the cone $\{y\neq0:\mathrm{proj}(y)\in x(\mathbb{R})\}$. `ReebOrbit.IsCZAtLeast` quantifies over all such $R$ and $Y$; for a strictly star-shaped level an $R$ exists (`periodicOrbit_bridge` of a previous mission). $C^\infty_{loc}$ convergence is `JHolomorphic.TendstoCInftyLocOn` on `Set.univ`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 2, formulas (7)–(10) and Theorem 2.2; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 3.10

import Definitions.Def_FiniteEnergyPlane_Winding

/-!
# Sets of fast finite-energy planes and their compactness

U. Hryniewicz, *Fast finite-energy planes in symplectizations and applications*, Trans. AMS 364
(2012), § 2 ((7)–(10), Theorem 2.2); U. Hryniewicz, J. Symplectic Geom. 12 (2014), Theorem 3.10.
Everything is in the setting of `FiniteEnergyPlane_Setting`, `FiniteEnergyPlane_Asymptotics` and
`FiniteEnergyPlane_Winding` for `n = 1`: `S = H⁻¹(1) ⊂ V 1 = ℝ⁴` strictly star-shaped, and the
symplectization `ℝ × S` is `V 1 \ {0}` with `y = e^{2 aCoord y} • proj y`.

Conventions.
* The Conley–Zehnder index of a periodic Reeb orbit `Q` on `S` is the one of
  `HryniewiczCriterion` (`czIndexOfPath` of `linearizedXiPath`), computed on a periodic orbit of
  `H ∘ ofR4` with the same image and the same action as `Q` (as in `periodicOrbit_bridge`).
* A compact set `K ⊂ V 1 \ {0}` plays the role of the compact set `H ⊂ ℝ × S` of Hryniewicz;
  `ℝ × x(ℝ)` is the cone `{y ≠ 0 | proj H y ∈ x(ℝ)}`.
* `C^∞_loc` convergence of maps `ℂ → V 1` is `JHolomorphic.TendstoCInftyLocOn` on `Set.univ`.
-/

namespace FiniteEnergyPlane

noncomputable section

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- The Conley–Zehnder index of the periodic Reeb orbit `Q` on `S ⊂ ℝ⁴` is at least `m`: for every
periodic orbit `R` of `H ∘ ofR4` in `HryniewiczCriterion` with the same image and the same action as
`Q`, and every linearized flow `Y` along `R`, `m ≤ czIndexOfPath (linearizedXiPath (H ∘ ofR4) R Y)`.
(For a strictly star-shaped level such an `R` exists, see `periodicOrbit_bridge`.) -/
def ReebOrbit.IsCZAtLeast {H : V 1 → ℝ} (Q : ReebOrbit H) (m : ℤ) : Prop :=
  ∀ R : HryniewiczCriterion.PeriodicOrbit (fun x => H (ofR4 x)),
    Set.range Q.x = Set.range (fun τ => ofR4 (R.x τ)) →
    Q.T = ∫ τ in (0 : ℝ)..R.T, liouville (ofR4 (R.x τ)) (deriv (fun s => ofR4 (R.x s)) τ) →
    ∀ Y : ℝ → (HryniewiczCriterion.R4 →L[ℝ] HryniewiczCriterion.R4),
      HryniewiczCriterion.IsLinearizedFlow (fun x => H (ofR4 x)) R.x Y →
      m ≤ HryniewiczCriterion.czIndexOfPath
        (HryniewiczCriterion.linearizedXiPath (fun x => H (ofR4 x)) R Y)

/-- Hryniewicz (2012), (7): the set `Θ(K, P)` of fast finite-energy planes `u` asymptotic to `P` at
`∞` (Definition 2.9, sign `+1`) with `u(0) ∈ K` and `dλ`-energy `γ` outside the closed unit disk. -/
def fastPlaneSet (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (K : Set (V 1))
    (γ : ℝ) : Set (ℂ → V 1) :=
  {u | IsFastPlane H J u ∧ IsNondegenerateEnd H u cylInf P 1 ∧ u 0 ∈ K ∧
    dlambdaEnergy H {z | 1 < ‖z‖} u = ENNReal.ofReal γ}

/-- Hryniewicz (2012), (9): the planes of `Θ(K, P)` whose coordinate `a = aCoord H ∘ u` is at least
`-L` everywhere. -/
def fastPlaneSetL (H : V 1 → ℝ) (J : V 1 → V 1 →L[ℝ] V 1) (P : ReebOrbit H) (K : Set (V 1))
    (γ L : ℝ) : Set (ℂ → V 1) :=
  {u | u ∈ fastPlaneSet H J P K γ ∧ ∀ z, -L ≤ aCoord H (u z)}

/-- `A` is sequentially compact in `C^∞_loc(ℂ, V 1)`: every sequence in `A` has a subsequence that
converges in `C^∞_loc` to an element of `A`. -/
def IsSeqCompactCInftyLoc (A : Set (ℂ → V 1)) : Prop :=
  ∀ u : ℕ → ℂ → V 1, (∀ k, u k ∈ A) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ v ∈ A,
      JHolomorphic.TendstoCInftyLocOn (fun k => u (φ k)) v Set.univ

end

end FiniteEnergyPlane


