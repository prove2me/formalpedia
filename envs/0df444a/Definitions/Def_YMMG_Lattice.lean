-- Prove2me | Definitions.Def_YMMG_Lattice
-- name    : YMMG_Lattice
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-25T16:19:44.173692+00:00
-- url     : https://prove2.me/theorems/7689c1d4-eb4e-44d2-88e2-264360c7c09c
-- title:
--   Compact simple gauge groups; Wilson lattice gauge theory and its scaling limits
-- statement:
--   The file defines four things.
--
--   1. **Compact simple gauge group.** This is a compact Hausdorff group $G$ with a continuous injective homomorphism $\rho:G\to U(N)$. $G$ must be connected, and the matrix Lie algebra $\mathfrak g=\{X: e^{tX}\in\rho(G)\ \forall t\in\mathbb R\}$ must be a simple real Lie algebra.
--   2. **Wilson lattice gauge theory.** It lives on the periodic lattice $(\mathbb Z/(2L+2))^4$, with link variables in $G$ and plaquette holonomies $U_p$. The action is $S_\beta=\beta\sum_x\sum_{\mu<\nu}(1-\operatorname{Re}\operatorname{tr}\rho(U_p)/N)$, and expectations are taken with respect to $e^{-S_\beta}$ times product Haar measure.
--   3. **Reflection data.** Time reflection between lattice planes, the positive half lattice, and the reflected configuration $\theta U$.
--   4. **Continuum scaling limit.** Here $a_k\to0$, $a_kL_k\to\infty$ and $\beta_k\to\infty$. The rescaled lattice sums $a_k^{4n}\sum f(a_kx)\langle\prod_j Z_k(P(x_j)-c_k)\rangle$ of the renormalized plaquette density converge to $\mathfrak S_n(f)$ for every compactly supported test function $f$ supported away from coinciding points.
-- source:
--   A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §6.5 (Wilson's lattice approach, reflection positivity); K. G. Wilson, Phys. Rev. D 10 (1974) 2445; K. Osterwalder, E. Seiler, Ann. Phys. 110 (1978) 440

module

public import Mathlib
public import Definitions.Def_YMMG_OSAxioms

/-!
# Compact simple gauge groups and Wilson's lattice gauge theory

* A compact gauge group is given as a compact Hausdorff topological group `G` together with a
  faithful continuous unitary representation `ρ : G → U(N)` (every compact Lie group has one, by
  Peter–Weyl). Its Lie algebra is realised as the matrix Lie algebra
  `𝔤 = {X : exp(tX) ∈ ρ(G) for all t ∈ ℝ}`, and "simple" means: `G` connected and `𝔤` a simple
  real Lie algebra (non-abelian, no ideals other than `0` and `𝔤`).
* Wilson's lattice approximation (Jaffe–Witten §6.5): on the periodic hypercubic lattice
  `(ℤ/(2L+2))⁴` a gauge field assigns `U_{x,μ} ∈ G` to each positively oriented link
  `x → x + e_μ`; the Wilson action is
  `S_β(U) = β ∑_x ∑_{μ<ν} (1 - Re tr ρ(U_{p(x,μ,ν)}) / N)` with plaquette holonomy
  `U_p = U_{x,μ} U_{x+e_μ,ν} U_{x+e_ν,μ}⁻¹ U_{x,ν}⁻¹`, and expectations are taken in the
  probability measure `Z⁻¹ e^{-S_β(U)} ∏_links dHaar(U_ℓ)`.
-/

@[expose] public section

noncomputable section

namespace YangMillsMassGap

open MeasureTheory Filter Topology

section GaugeGroup

variable {G : Type} [Group G] [TopologicalSpace G] {N : ℕ}

/-- The underlying matrix of `ρ g`. -/
def repMatrix (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (g : G) : Matrix (Fin N) (Fin N) ℂ :=
  (ρ g : Matrix (Fin N) (Fin N) ℂ)

/-- The matrix Lie algebra `𝔤 = {X ∈ Mat_N(ℂ) : exp(tX) ∈ ρ(G) for every real t}` of `ρ(G)`. -/
def matrixLieAlgebra (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) : Set (Matrix (Fin N) (Fin N) ℂ) :=
  {X | ∀ t : ℝ, ∃ g : G, repMatrix ρ g = NormedSpace.exp ((t : ℂ) • X)}

/-- A set `𝔤` of matrices (closed under the commutator, as a real Lie algebra) is **simple**:
it is non-abelian and every real subspace `I ⊆ 𝔤` with `[𝔤, I] ⊆ I` is `0` or all of `𝔤`. -/
def IsSimpleMatrixLieAlgebra (𝔤 : Set (Matrix (Fin N) (Fin N) ℂ)) : Prop :=
  (∃ X ∈ 𝔤, ∃ Y ∈ 𝔤, X * Y - Y * X ≠ 0) ∧
  ∀ I : Submodule ℝ (Matrix (Fin N) (Fin N) ℂ), (I : Set _) ⊆ 𝔤 →
    (∀ X ∈ 𝔤, ∀ Y ∈ I, X * Y - Y * X ∈ I) → I = ⊥ ∨ 𝔤 ⊆ I

/-- `ρ : G → U(N)` presents `G` as a **compact simple gauge group**: `ρ` is a continuous
injective homomorphism, `G` is connected, and the Lie algebra of `ρ(G)` is simple.
(Compactness and the Hausdorff property of `G` are imposed as type-class assumptions.) -/
structure IsCompactSimpleGaugeGroup (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) : Prop where
  continuous : Continuous ρ
  injective : Function.Injective ρ
  connected : ConnectedSpace G
  simple : IsSimpleMatrixLieAlgebra (matrixLieAlgebra ρ)

end GaugeGroup

section Lattice

/-- Sites of the periodic lattice `(ℤ/(2L+2)ℤ)⁴`; coordinate `0` is (Euclidean) time. -/
abbrev LatticeSite (L : ℕ) := Fin 4 → ZMod (2 * L + 2)

instance (L : ℕ) : NeZero (2 * L + 2) := ⟨by omega⟩

/-- The unit lattice vector `e_μ`. -/
def unitVec {L : ℕ} (μ : Fin 4) : LatticeSite L := Pi.single μ 1

/-- Positively oriented links `x → x + e_μ`, labelled by `(x, μ)`. -/
abbrev Link (L : ℕ) := LatticeSite L × Fin 4

/-- A lattice gauge field: a group element on every positively oriented link. -/
abbrev GaugeConfig (G : Type) (L : ℕ) := Link L → G

variable {G : Type} [Group G] {N : ℕ} {L : ℕ}

/-- Plaquette holonomy `U_{x,μ} U_{x+e_μ,ν} U_{x+e_ν,μ}⁻¹ U_{x,ν}⁻¹`. -/
def plaquette (U : GaugeConfig G L) (x : LatticeSite L) (μ ν : Fin 4) : G :=
  U (x, μ) * U (x + unitVec μ, ν) * (U (x + unitVec ν, μ))⁻¹ * (U (x, ν))⁻¹

/-- `Re tr ρ(g)`. -/
def reTrace (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (g : G) : ℝ :=
  (Matrix.trace ((ρ g : Matrix (Fin N) (Fin N) ℂ))).re

/-- The plaquette action density at the site `x`: `∑_{μ<ν} (1 - Re tr ρ(U_{p(x,μ,ν)}) / N)`.
(This is the lattice approximant of `(a⁴/const) · tr F_{μν}F_{μν}(x)`.) -/
def plaquetteDensity (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (U : GaugeConfig G L)
    (x : LatticeSite L) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then 1 - reTrace ρ (plaquette U x μ ν) / N else 0

/-- The Wilson action `S_β(U) = β ∑_x ∑_{μ<ν} (1 - Re tr ρ(U_p) / N)`. -/
def wilsonAction (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (β : ℝ) (U : GaugeConfig G L) : ℝ :=
  β * ∑ x : LatticeSite L, plaquetteDensity ρ U x

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G]

/-- Product Haar measure `∏_links dHaar(U_ℓ)` on lattice gauge fields. -/
def haarProduct (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G] (L : ℕ) : Measure (GaugeConfig G L) :=
  Measure.pi (fun _ : Link L => (Measure.haar : Measure G))

/-- The Wilson lattice expectation
`⟨F⟩_{β,L} = ∫ F(U) e^{-S_β(U)} ∏ dHaar(U_ℓ) / ∫ e^{-S_β(U)} ∏ dHaar(U_ℓ)`. -/
def wilsonExpectation (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (L : ℕ) (β : ℝ)
    (F : GaugeConfig G L → ℂ) : ℂ :=
  (∫ U, F U * (Real.exp (-wilsonAction ρ β U) : ℂ) ∂(haarProduct G L)) /
    ((∫ U, Real.exp (-wilsonAction ρ β U) ∂(haarProduct G L) : ℝ) : ℂ)

end Lattice

section Reflection

variable {G : Type} [Group G] {L : ℕ}

/-- Reflection of the lattice in the time-zero plane lying *between* lattice sites:
`(t, x⃗) ↦ (-1 - t, x⃗)`. -/
def reflectSite (x : LatticeSite L) : LatticeSite L := Function.update x 0 (-1 - x 0)

/-- The positive-time half lattice `{x : 0 ≤ x⁰ ≤ L}` (the reflection maps it onto its
complement `{L+1 ≤ x⁰ ≤ 2L+1}`). -/
def positiveHalf (L : ℕ) : Set (LatticeSite L) := {x | (x 0).val ≤ L}

/-- Links with both end points in the positive half lattice. -/
def positiveLinks (L : ℕ) : Set (Link L) :=
  {ℓ | ℓ.1 ∈ positiveHalf L ∧ (ℓ.2 = 0 → (ℓ.1 0).val < L)}

/-- The reflected gauge field `θU`: spatial links are mapped to their mirror images, time-like
links to the mirror link traversed in the opposite direction:
`(θU)_{x,k} = U_{θx,k}` for `k ≠ 0`, `(θU)_{x,0} = (U_{θx - e₀,0})⁻¹`. -/
def reflectConfig (U : GaugeConfig G L) : GaugeConfig G L :=
  fun ℓ => if ℓ.2 = 0 then (U (reflectSite ℓ.1 - unitVec 0, 0))⁻¹ else U (reflectSite ℓ.1, ℓ.2)

/-- `F` depends only on the link variables of the positive half lattice. -/
def DependsOnlyOnPositiveLinks {α : Type} (F : GaugeConfig G L → α) : Prop :=
  ∀ U U' : GaugeConfig G L, (∀ ℓ ∈ positiveLinks L, U ℓ = U' ℓ) → F U = F U'

end Reflection

section ScalingLimit

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G] {N : ℕ}

/-- Integer coordinate of a lattice site, taking the representative in `[-(L+1), L]`. -/
def siteCoord {L : ℕ} (x : LatticeSite L) (μ : Fin 4) : ℤ :=
  if (x μ).val ≤ L then ((x μ).val : ℤ) else ((x μ).val : ℤ) - (2 * L + 2)

/-- The point of `ℝ⁴` represented by a lattice site at lattice spacing `a`. -/
def sitePoint {L : ℕ} (a : ℝ) (x : LatticeSite L) : Spacetime :=
  WithLp.toLp 2 (fun μ => a * (siteCoord x μ : ℝ))

/-- The configuration `(a x₁, …, a xₙ) ∈ (ℝ⁴)ⁿ` of `n` lattice sites. -/
def siteConfig {L n : ℕ} (a : ℝ) (xs : Fin n → LatticeSite L) : Config n :=
  Config.mk (fun j => sitePoint a (xs j))

/-- `𝔖` is a **continuum scaling limit of Wilson's lattice gauge theory** for the gauge group
`(G, ρ)`, obtained from the renormalized plaquette field: there are lattice spacings `a_k → 0`,
lattice sizes `L_k` with physical size `a_k L_k → ∞`, inverse couplings `β_k → ∞`, and
multiplicative/additive renormalization constants `Z_k`, `c_k`, such that for every `n ≥ 1` and
every compactly supported Schwartz `f` whose support avoids coinciding points,
`a_k^{4n} ∑_{x₁,…,xₙ} f(a_k x₁, …, a_k xₙ) ⟨∏ⱼ Z_k (P(xⱼ) - c_k)⟩_{β_k, L_k} → 𝔖ₙ(f)`,
where `P(x)` is the plaquette action density at `x`. -/
def IsWilsonScalingLimit (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (S : DistributionFamily) :
    Prop :=
  ∃ (L : ℕ → ℕ) (a β Z c : ℕ → ℝ),
    (∀ k, 0 < a k) ∧ Tendsto a atTop (𝓝 0) ∧
    Tendsto (fun k => a k * (L k : ℝ)) atTop atTop ∧ Tendsto β atTop atTop ∧
    ∀ n : ℕ, 1 ≤ n → ∀ f : SchwartzMap (Config n) ℂ, HasCompactSupport f →
      Disjoint (tsupport f) (coincidenceSet n) →
      Tendsto (fun k => ((a k ^ (4 * n) : ℝ) : ℂ) *
          ∑ xs : Fin n → LatticeSite (L k), f (siteConfig (a k) xs) *
            wilsonExpectation ρ (L k) (β k)
              (fun U => ∏ j, ((Z k * (plaquetteDensity ρ U (xs j) - c k) : ℝ) : ℂ)))
        atTop (𝓝 (S n f))

end ScalingLimit

end YangMillsMassGap

end


