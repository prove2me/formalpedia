-- Prove2me | Definitions.Def_AlgebraicCurve_ComplexLineIntegral
-- name    : AlgebraicCurve_ComplexLineIntegral
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/9f4b6b69-0178-5786-9678-f2fba57ec609
-- title:
--   Path integrals of differentials and Abel–Jacobi maps
-- statement:
--   Throughout, $F$ is a field extension of a base field, places being the objects of [`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22) (valuation subrings of $F$ containing the base field, proper and principal), and in the complex part $F$ is an extension of $\mathbb{C}$ whose place set `Place ℂ F` is endowed with a topology and a `ChartedSpace ℂ` structure given as instances; values of $f \in F$ at a place are taken with `Place.evalAt` (which returns $0$ when $f$ is not in the valuation subring). First, `Place.dCoordFn v` is a choice of $\pi \in F$ with $\operatorname{ord}_v(\pi) = 1$ and $d\pi =$ `v.dCoord`, the two defining properties being recorded as `ord_dCoordFn` and `dCoord_eq_D_dCoordFn`. Next, `Place.chartRead v f` is the function $z \mapsto f\bigl(\varphi_v^{-1}(z)\bigr)$, where $\varphi_v =$ `extChartAt 𝓘(ℂ, ℂ) v`, and `Place.readDifferential v ω` is $z \mapsto h(\varphi_v^{-1}(z)) \cdot (\pi_v \circ \varphi_v^{-1})'(z)$ with $h =$ `v.differentialCoeff ω` (the chosen $h$ with $\omega = h \cdot$ `v.dCoord`, or $0$ if there is none) and $\pi_v =$ `v.dCoordFn`; the derivative is the ordinary complex derivative of the chart read of $\pi_v$.
--
--   The predicate `IsPrimitiveAlong ω γ g`, for $\omega \in \Omega[F⁄ℂ]$, a path $\gamma$ from $P$ to $Q$ in `Place ℂ F` and $g : [0,1] \to \mathbb{C}$, asserts that for every parameter $t_0$ there is $\Phi : \mathbb{C} \to \mathbb{C}$ which, near $\varphi_{\gamma(t_0)}(\gamma(t_0))$, has derivative `readDifferential (γ t₀) ω` at each point, and such that $g(t) = \Phi(\varphi_{\gamma(t_0)}(\gamma(t)))$ for all $t$ near $t_0$. Then `pathIntegral ω γ` is $g(1) - g(0)$ for a chosen such $g$ when one exists, and $0$ otherwise. For $b : \mathrm{Fin}\,n \to \Omega[F⁄ℂ]$, `abelJacobiVec b P₀ P` is the vector of path integrals of the $b_i$ along one chosen path from $P_0$ to $P$ (and $0$ if the two places are not joined by a path), and `abelJacobiDiv b P₀` is the additive homomorphism from `Divisor ℂ F` to $\mathbb{C}^n$ sending $D$ to $\sum_v D(v) \cdot$ `abelJacobiVec b P₀ v`, as recorded by `abelJacobiDiv_single` and `abelJacobiDiv_apply`. Finally `pathPeriodLattice b` is the $\mathbb{Z}$-submodule of $\mathbb{C}^n$ spanned by the period vectors $\bigl(\mathrm{pathIntegral}\,(b_i)\,\gamma\bigr)_i$ of all loops $\gamma$ at all places, with `mem_pathPeriodLattice_of_loop` recording that each such vector lies in it. Nothing defined here asserts compatibility of the charts with the field structure, or that the relevant primitives exist; such facts are the content of separate statements.
--
--   **Relation to Mathlib.** Mathlib has no integration of Kähler differentials along paths, no Abel–Jacobi map and no period lattice for this setting; these are the project's own notions, phrased in terms of Mathlib's `KaehlerDifferential`, `Path`, `extChartAt`, `deriv` and `Finsupp.liftAddHom`.
--
--   **Where it is used.** These definitions give the analytic side of the curve theory used in the project: integration of regular differentials along paths on the set of places of a function field over $\mathbb{C}$, the associated Abel–Jacobi map on divisors and the lattice of periods, which underlie the complex-analytic description of Jacobians of modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open scoped Manifold Topology

namespace AlgebraicCurve

namespace Place

section general

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def dCoordFn (v : Place K F) : F :=
  Classical.choose v.exists_ord_eq_one_and_dCoord_eq

theorem ord_dCoordFn (v : Place K F) : v.ord v.dCoordFn = 1 :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).1

theorem dCoord_eq_D_dCoordFn (v : Place K F) :
    v.dCoord = KaehlerDifferential.D K F v.dCoordFn :=
  (Classical.choose_spec v.exists_ord_eq_one_and_dCoord_eq).2

end general

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def chartRead (v : Place ℂ F) (f : F) : ℂ → ℂ :=
  fun z => Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f

theorem chartRead_apply (v : Place ℂ F) (f : F) (z : ℂ) :
    v.chartRead f z = Place.evalAt ((extChartAt 𝓘(ℂ, ℂ) v).symm z) f := rfl

def readDifferential (v : Place ℂ F) (ω : Ω[F⁄ℂ]) : ℂ → ℂ :=
  fun z => v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z

theorem readDifferential_apply (v : Place ℂ F) (ω : Ω[F⁄ℂ]) (z : ℂ) :
    v.readDifferential ω z =
      v.chartRead (v.differentialCoeff ω) z * deriv (v.chartRead v.dCoordFn) z := rfl

end Place

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def IsPrimitiveAlong (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) (g : unitInterval → ℂ) :
    Prop :=
  ∀ t₀ : unitInterval, ∃ Φ : ℂ → ℂ,
    (∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t₀)),
        HasDerivAt Φ ((γ t₀).readDifferential ω z) z) ∧
      ∀ᶠ t in 𝓝 t₀, g t = Φ (extChartAt 𝓘(ℂ, ℂ) (γ t₀) (γ t))

open Classical in

def pathIntegral (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) : ℂ :=
  if h : ∃ g, IsPrimitiveAlong ω γ g then h.choose 1 - h.choose 0 else 0

open Classical in
theorem pathIntegral_def (ω : Ω[F⁄ℂ]) {P Q : Place ℂ F} (γ : Path P Q) :
    pathIntegral ω γ = if h : ∃ g, IsPrimitiveAlong ω γ g then h.choose 1 - h.choose 0 else 0 :=
  rfl

open Classical in

def abelJacobiVec {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) : Fin n → ℂ :=
  if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0

open Classical in
theorem abelJacobiVec_def {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ P : Place ℂ F) :
    abelJacobiVec b P₀ P =
      if h : Nonempty (Path P₀ P) then fun i => pathIntegral (b i) (Classical.choice h) else 0 :=
  rfl

def abelJacobiDiv {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) :
    Divisor ℂ F →+ (Fin n → ℂ) :=
  Finsupp.liftAddHom fun v => zmultiplesHom (Fin n → ℂ) (abelJacobiVec b P₀ v)

@[simp]
theorem abelJacobiDiv_single {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ v : Place ℂ F) (m : ℤ) :
    abelJacobiDiv b P₀ (Finsupp.single v m) = m • abelJacobiVec b P₀ v := by
  simp [abelJacobiDiv]

theorem abelJacobiDiv_apply {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) (P₀ : Place ℂ F) (D : Divisor ℂ F) :
    abelJacobiDiv b P₀ D = D.sum fun v m => m • abelJacobiVec b P₀ v := by
  simp only [abelJacobiDiv, Finsupp.liftAddHom_apply]
  rfl

def pathPeriodLattice {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) : Submodule ℤ (Fin n → ℂ) :=
  Submodule.span ℤ {u | ∃ (P : Place ℂ F) (γ : Path P P), u = fun i => pathIntegral (b i) γ}

theorem mem_pathPeriodLattice_of_loop {n : ℕ} (b : Fin n → Ω[F⁄ℂ]) {P : Place ℂ F}
    (γ : Path P P) : (fun i => pathIntegral (b i) γ) ∈ pathPeriodLattice b :=
  Submodule.subset_span ⟨P, γ, rfl⟩

end AlgebraicCurve


