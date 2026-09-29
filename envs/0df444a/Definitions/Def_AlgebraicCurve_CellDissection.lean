-- Prove2me | Definitions.Def_AlgebraicCurve_CellDissection
-- name    : AlgebraicCurve_CellDissection
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/775680a5-b2c4-5199-adfa-3583d30c7154
-- title:
--   Radial regions, analytic coordinates, cells, and cell dissections
-- statement:
--   The module sets up a combinatorial-analytic notion of dissection for the space of places $\mathrm{Place}\,\mathbb{C}\,F$ of a field $F$ over $\mathbb{C}$, carrying a topology and charts modelled on $\mathbb{C}$.
--
--   A `RadialRegion` consists of a centre $q \in \mathbb{C}$, a continuous, $2\pi$-periodic, everywhere positive radius function $r : \mathbb{R} \to \mathbb{R}$, and a subdivision $0 = \varphi_0 < \varphi_1 < \dots < \varphi_N = 2\pi$ (a strictly monotone $\varphi : \mathrm{Fin}(N+1) \to \mathbb{R}$ with the stated endpoints) such that $r$ is $C^2$ on each closed interval $[\varphi_k,\varphi_{k+1}]$. Its `K` is $\{z : \lVert z-q\rVert \le r(\arg(z-q))\}$ and `Kint` the strict version; `loop` is $\varphi \mapsto q + r(\varphi)e^{i\varphi}$ and `loop'` the expression $(r'(\varphi)+i\,r(\varphi))e^{i\varphi}$; `arcIcc k` is $[\varphi_k,\varphi_{k+1}]$ and `arcSet k` its image under `loop`.
--
--   An `AnalyticCoord F` is an open partial homeomorphism $\zeta$ from the place space to $\mathbb{C}$ such that, at each $P$ in its source, the composite of the inverse extended chart at $P$ with $\zeta$ is analytic at the chart image of $P$ with non-vanishing derivative there; `read A u` reads an element $u \in F$ as the function $z \mapsto \mathrm{evalAt}(\zeta^{-1}(z))\,u$ of the coordinate (place evaluation: the residue-field value pulled back to $\mathbb{C}$, or $0$ when $u$ lies outside the valuation subring). A `Cell F` is such a coordinate together with a radial region whose closed region `K` lies in $\zeta$'s target; its `carrier`, `interior'`, `bdry` and `arc` are the images under $\zeta^{-1}$ of `K`, `Kint`, `loop` and `arcSet`.
--
--   A `CellDissection F` packages finite index types $\iota_C, \iota_E, \iota_V$ with decidable equality, a family `cell` of cells, a map `side` sending each pair (cell, arc index) to an edge with a Boolean orientation, and the requirement (`side_bij`) that this be a bijection from the sigma type of all arcs onto $\iota_E \times \mathrm{Bool}$, so each edge carries exactly two arcs, one of each orientation. Further fields: `ends` assigning to each edge an ordered pair of vertices and `vert` realising vertices as places; `arc_ends`, asserting that the boundary points of an arc at its two break angles are the two vertices of its edge, in the order dictated by the orientation bit; `arc_rev`, asserting that two arcs carrying the same edge with opposite bits are related by a strictly antitone $C^1$ reparametrisation $\psi$ of the arc interval exchanging the endpoint angles and satisfying $\mathrm{bdry}_{C'}(t) = \mathrm{bdry}_C(\psi(t))$; `cover`, that the carriers exhaust the whole place space; `inter`, that two cells whose carriers contain a common point $x$ are joined by a reflexive-transitive chain in which consecutive cells share an edge and $x$ lies on the corresponding arc of the earlier cell; and `conn`, the analogous chain condition for the relation of sharing an edge, for arbitrary pairs of cells. These are fields of a structure, so the incidence and covering statements are carried as data-bearing hypotheses rather than proved.
--
--   Finally, `coeffIn ζ θ w` is the value at $w$ of the coefficient of a differential $\theta \in \Omega[F/\mathbb{C}]$ transported to the coordinate $\zeta$: the `readDifferential` of $\theta$ at the place $\zeta^{-1}(w)$, evaluated at its own chart image, times the derivative at $w$ of the extended chart composed with $\zeta^{-1}$. `Cell.bdryIntegrand C θ s` is $\mathrm{coeffIn}(\zeta,\theta)(\mathrm{loop}\,s)\cdot\mathrm{loop}'(s)$; `arcOf` recovers from a side the unique arc carrying it, using surjectivity of `side`; `edgeInt θ e` is the integral of that integrand over the angle interval of the positively oriented arc of $e$; and `skeleton` is the union of all arcs of all cells.
--
--   **Relation to Mathlib.** Mathlib supplies the charted-space and `OpenPartialHomeomorph` framework used here, but has no notion of a cell dissection or polygonal decomposition of a Riemann surface; the radial regions, cells and dissections, and the reading of elements of $F$ and of differentials in an analytic coordinate, are the project's own, built on its `Place`-based model of a complex algebraic curve.
--
--   **Where it is used.** The dissections defined here support the treatment of line integrals of regular differentials on a complex algebraic curve: the edgewise integrals `edgeInt` are the quantities in terms of which the reciprocity law for path integrals, and the associated counting arguments over the cells, edges and vertices of a dissection, are formulated. These in turn feed the analytic input on curves and their Jacobians used for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_CellDissection.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_ComplexLineIntegral

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Manifold ContDiff Topology Real
open Set Complex

namespace AlgebraicCurve

structure RadialRegion where
  q : ℂ
  r : ℝ → ℝ
  hcont : Continuous r
  hper : Function.Periodic r (2 * π)
  hpos : ∀ φ, 0 < r φ
  N : ℕ
  φs : Fin (N + 1) → ℝ
  hφ0 : φs 0 = 0
  hφN : φs (Fin.last N) = 2 * π
  hmono : StrictMono φs
  hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Icc (φs i.castSucc) (φs i.succ))

namespace RadialRegion

def K (R : RadialRegion) : Set ℂ := {z : ℂ | ‖z - R.q‖ ≤ R.r (arg (z - R.q))}

def Kint (R : RadialRegion) : Set ℂ := {z : ℂ | ‖z - R.q‖ < R.r (arg (z - R.q))}

noncomputable def loop (R : RadialRegion) (φ : ℝ) : ℂ := R.q + R.r φ * exp (φ * I)

noncomputable def loop' (R : RadialRegion) (φ : ℝ) : ℂ :=
  (((deriv R.r φ : ℝ) : ℂ) + R.r φ * I) * exp (φ * I)

def arcIcc (R : RadialRegion) (k : Fin R.N) : Set ℝ := Icc (R.φs k.castSucc) (R.φs k.succ)

def arcSet (R : RadialRegion) (k : Fin R.N) : Set ℂ := R.loop '' R.arcIcc k

end RadialRegion

structure AnalyticCoord (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where
  ζ : OpenPartialHomeomorph (Place ℂ F) ℂ
  analytic : ∀ P ∈ ζ.source,
    AnalyticAt ℂ (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P)
  deriv_ne : ∀ P ∈ ζ.source,
    deriv (ζ ∘ (extChartAt 𝓘(ℂ, ℂ) P).symm) (extChartAt 𝓘(ℂ, ℂ) P P) ≠ 0

namespace AnalyticCoord

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

noncomputable def read (A : AnalyticCoord F) (u : F) : ℂ → ℂ :=
  fun z => Place.evalAt (A.ζ.symm z) u

end AnalyticCoord

structure Cell (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] extends AnalyticCoord F where
  R : RadialRegion
  hKt : R.K ⊆ ζ.target

namespace Cell

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

def carrier (C : Cell F) : Set (Place ℂ F) := C.ζ.symm '' C.R.K

def interior' (C : Cell F) : Set (Place ℂ F) := C.ζ.symm '' C.R.Kint

noncomputable def bdry (C : Cell F) (φ : ℝ) : Place ℂ F := C.ζ.symm (C.R.loop φ)

def arc (C : Cell F) (k : Fin C.R.N) : Set (Place ℂ F) := C.ζ.symm '' C.R.arcSet k

end Cell

structure CellDissection (F : Type*) [Field F] [Algebra ℂ F]
    [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)] where

  ιC : Type
  ιE : Type
  ιV : Type
  [fintypeC : Fintype ιC]
  [fintypeE : Fintype ιE]
  [fintypeV : Fintype ιV]
  [decEqC : DecidableEq ιC]
  [decEqE : DecidableEq ιE]
  [decEqV : DecidableEq ιV]
  cell : ιC → Cell F

  side : (C : ιC) → Fin (cell C).R.N → ιE × Bool

  side_bij : Function.Bijective fun p : (Σ C : ιC, Fin (cell C).R.N) => side p.1 p.2

  ends : ιE → ιV × ιV
  vert : ιV → Place ℂ F

  arc_ends : ∀ (C : ιC) (k : Fin (cell C).R.N),
    (cell C).bdry ((cell C).R.φs k.castSucc) =
        vert (if (side C k).2 then (ends (side C k).1).1 else (ends (side C k).1).2) ∧
      (cell C).bdry ((cell C).R.φs k.succ) =
        vert (if (side C k).2 then (ends (side C k).1).2 else (ends (side C k).1).1)

  arc_rev : ∀ (C : ιC) (k : Fin (cell C).R.N) (C' : ιC) (k' : Fin (cell C').R.N),
    (side C k).1 = (side C' k').1 → (side C k).2 = true → (side C' k').2 = false →
    ∃ ψ : ℝ → ℝ,
      StrictAntiOn ψ ((cell C').R.arcIcc k') ∧ ContDiffOn ℝ 1 ψ ((cell C').R.arcIcc k') ∧
      ψ ((cell C').R.φs k'.castSucc) = (cell C).R.φs k.succ ∧
      ψ ((cell C').R.φs k'.succ) = (cell C).R.φs k.castSucc ∧
      ∀ t ∈ (cell C').R.arcIcc k', (cell C').bdry t = (cell C).bdry (ψ t)

  cover : ⋃ C, (cell C).carrier = univ

  inter : ∀ (C C' : ιC) (x : Place ℂ F), x ∈ (cell C).carrier → x ∈ (cell C').carrier →
    Relation.ReflTransGen
      (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N),
        (side A k).1 = (side B k').1 ∧ x ∈ (cell A).arc k)
      C C'

  conn : ∀ C C' : ιC, Relation.ReflTransGen
    (fun A B : ιC => ∃ (k : Fin (cell A).R.N) (k' : Fin (cell B).R.N), (side A k).1 = (side B k').1)
    C C'

attribute [instance] CellDissection.fintypeC CellDissection.fintypeE CellDissection.fintypeV
  CellDissection.decEqC CellDissection.decEqE CellDissection.decEqV

section Integrals

variable {F : Type*} [Field F] [Algebra ℂ F]
variable [TopologicalSpace (Place ℂ F)] [ChartedSpace ℂ (Place ℂ F)]

noncomputable def coeffIn (ζ : OpenPartialHomeomorph (Place ℂ F) ℂ) (θ : Ω[F⁄ℂ]) (w : ℂ) : ℂ :=
  (ζ.symm w).readDifferential θ (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) (ζ.symm w)) *
    deriv (extChartAt 𝓘(ℂ, ℂ) (ζ.symm w) ∘ ζ.symm) w

noncomputable def Cell.bdryIntegrand (C : Cell F) (θ : Ω[F⁄ℂ]) (s : ℝ) : ℂ :=
  coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s

noncomputable def CellDissection.arcOf (𝒟 : CellDissection F) (q : 𝒟.ιE × Bool) :
    Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N :=
  Function.surjInv 𝒟.side_bij.surjective q

noncomputable def CellDissection.edgeInt (𝒟 : CellDissection F) (θ : Ω[F⁄ℂ]) (e : 𝒟.ιE) : ℂ :=
  ∫ s in ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.castSucc)..
      ((𝒟.cell (𝒟.arcOf (e, true)).1).R.φs (𝒟.arcOf (e, true)).2.succ),
    (𝒟.cell (𝒟.arcOf (e, true)).1).bdryIntegrand θ s

def CellDissection.skeleton (𝒟 : CellDissection F) : Set (Place ℂ F) :=
  ⋃ p : (Σ C : 𝒟.ιC, Fin (𝒟.cell C).R.N), (𝒟.cell p.1).arc p.2

end Integrals

end AlgebraicCurve


