-- Prove2me | Definitions.Def_QVolTransducer_Supplement_metroKernel
-- name    : QVolTransducer_Supplement_metroKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:33:47.880433+00:00
-- url     : https://prove2.me/theorems/11ee9316-9b48-41db-8360-eed822a64081
-- title:
--   Metropolis walks on $\mathbb R^d$, their naive discretization, and the speedy, cube and discretized speedy walks
-- statement:
--   For $\Omega\subseteq\mathbb R^d$ and $g\ge0$ write $N_g=\int_\Omega g$, $\pi_g=g/N_g$, and on the grid $\Omega_\zeta=\zeta\mathbb Z^d\cap\Omega$, $N_{g,\zeta}=\sum_{x\in\Omega_\zeta}g(x)$, $(\pi_{g,\zeta})_x=g(x)/N_{g,\zeta}$.
--
--   1. **Metropolis walk** (Definition 7.6) with proposal densities $(p_x)_{x\in\Omega}$ and target density $f>0$: at $x$ propose $y\sim\pi_{p_x}$ and move with probability $a_{xy}=\min\{1,f(y)/f(x)\}$, else stay; that is
--   $$P(x,B)=\int_{B\cap\Omega}\pi_{p_x}(y)a_{xy}\,dy+\mathbb 1_B(x)\Big(1-\int_\Omega\pi_{p_x}(y)a_{xy}\,dy\Big).$$
--   Its **naive discretization** has $(P_\zeta)_{x,y}=(\pi_{p_x,\zeta})_y\,a_{x,y}$ for $x\ne y\in\Omega_\zeta$.
--   2. **Speedy walk** $P_{\beta,\delta}$ on a convex body $K$ (Definition 5.3): the Metropolis walk with $p_x=\mathbb 1_{x+\delta B_d}$ and $f(x)=e^{-\beta\|x\|^2}$; its stationary distribution $\pi_{\beta,\delta}$ has density proportional to $\ell_\delta(x)f(x)$, $\ell_\delta(x)=\mathrm{Vol}((x+\delta B_d)\cap K)/\mathrm{Vol}(\delta B_d)$.
--   3. **Cube speedy walk** $P^C_{\beta,\delta,\zeta}$ (Definition 8.4) on $M_{K,\zeta}=\{x:x_\zeta\in K\}$, $x_\zeta=\zeta\,\mathrm{round}(x/\zeta)$: propose $y$ uniformly in $(x_\zeta+M_{\delta B_d,\zeta})\cap M_{K,\zeta}$ and accept with $\min\{1,f(y)/f(x)\}$; stationary density $\propto\ell^C_{\delta,\zeta}(x)f(x)$.
--   4. **Discretized speedy walk** $P_{\beta,\delta,\zeta}$ on $K_\zeta$ (Definition 8.13): select $y\in(K\cap(x+\delta B_d))_\zeta$ uniformly and move with probability $\min\{1,f(y)/f(x)\}$.
--
--   These walks are the chain of approximations from the continuous speedy walk to the finite walk that the quantum algorithm implements.
--
--   **Formalization Note** Walks are maps from points to measures (outside $\Omega$ the law is the point mass, never used). The stationary distributions of the speedy and cube walks are defined by their printed densities (the normalization removes the constants $\mathrm{Vol}(\delta B_d)$, $\mathrm{Vol}(M_{\delta B_d,\zeta})$); that of the discretized walk is the published `speedyStat`. $y\in x_\zeta+M_{\delta B_d,\zeta}$ iff $\|y_\zeta-x_\zeta\|\le\delta$. Grid sums are `finsum`s over $\Omega_\zeta$ (finite for bounded $\Omega$); the discretized walk's state space is the published grid $(RB_d)_\zeta$ restricted to $K$, and its diagonal is $1$ minus the off-diagonal row sum.
-- source:
--   Cornelissen, Apers, Gribling, Improved quantum volume estimation with transducers and amortized quantum walks, arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definitions 5.3, 5.4, 7.4, 7.6, 8.4, 8.5, 8.13, pp.38, 43, 45, 48, 51 (PDF pp.40, 45, 47, 50, 53)

import Mathlib
import Definitions.Def_QVolTransducer_gridIdx

namespace QVolTransducer.Supplement

open MeasureTheory
open scoped ENNReal

/-- The normalization `N_g = ∫_Ω g(x) dx` of a nonnegative function on `Ω ⊆ ℝ^d` (Cornelissen,
Apers, Gribling, *Improved quantum volume estimation with transducers and amortized quantum walks*,
arXiv:2609.40217 (version of November 3, 2026, sha256 40d7b52d…), Definition 7.4, p.43). -/
noncomputable def massN {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∫ y in Ω, g y

/-- The grid normalization `N_{g,ζ} = Σ_{x ∈ Ω_ζ} g(x)` over `Ω_ζ = ζℤ^d ∩ Ω` (arXiv:2609.40217,
Definition 7.4, p.43).

**Formalization Note** A grid point `ζ z` is indexed by `z ∈ ℤ^d` (the published
`QVolTransducer.latticePt`); the sum is a `finsum`, which is the sum over `Ω_ζ` whenever `Ω_ζ` is
finite (e.g. `Ω` bounded and `ζ > 0`). -/
noncomputable def gridSum {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (ζ : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) : ℝ :=
  ∑ᶠ z ∈ {z : Fin d → ℤ | latticePt ζ z ∈ Ω}, g (latticePt ζ z)

/-- The discretized distribution `(π_{g,ζ})_x = g(x)/N_{g,ζ}` at the grid point `x = ζ z`
(arXiv:2609.40217, Definition 7.4, p.43). -/
noncomputable def gridDist {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (ζ : ℝ)
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (z : Fin d → ℤ) : ℝ :=
  g (latticePt ζ z) / gridSum Ω ζ g

/-- The Metropolis acceptance probability `a_{xy} := min{1, f(y)/f(x)}` (arXiv:2609.40217,
Definition 7.6, p.45). -/
noncomputable def metroAccept {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  min 1 (f y / f x)

open Classical in
/-- The transition law of the Metropolis walk with proposal densities `(p_x)_{x∈Ω}` and target
density `f` on `Ω ⊆ ℝ^d` (arXiv:2609.40217, Definition 7.6, p.45: at `x ∈ Ω` select a proposal
`y ∼ π_{p_x}` and move to `y` with probability `a_{xy} = min{1, f(y)/f(x)}`, else stay at `x`).
For `x ∈ Ω` it is the measure
`P(x, B) = ∫_{B∩Ω} π_{p_x}(y) a_{xy} dy + 1_B(x) (1 − ∫_Ω π_{p_x}(y) a_{xy} dy)`, with
`π_{p_x}(y) = p_x(y)/N_{p_x}`; `p x y` is `p_x(y)`.

**Formalization Note** States outside `Ω` are never visited from `Ω`; there the law is the point
mass `δ_x` (an arbitrary convention that no statement uses). -/
noncomputable def metroKernel {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  if x ∈ Ω then
    (volume.restrict Ω).withDensity
        (fun y => ENNReal.ofReal (p x y / massN Ω (p x) * metroAccept f x y)) +
      ENNReal.ofReal (1 - ∫ y in Ω, p x y / massN Ω (p x) * metroAccept f x y) • Measure.dirac x
  else Measure.dirac x

/-- The probability distribution `π_g` on `Ω` with density `g/N_g` (arXiv:2609.40217,
Definition 7.4, p.43), as a measure on `ℝ^d` concentrated on `Ω`. -/
noncomputable def metroStat {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (volume.restrict Ω).withDensity (fun x => ENNReal.ofReal (g x / massN Ω g))

/-- The off-diagonal transition probabilities of the naive discretization `(Ω_ζ, P_ζ)`
(arXiv:2609.40217, Definition 7.6, p.45): for grid points `x = ζ z ≠ y = ζ w` of `Ω_ζ`,
`(P_ζ)_{x,y} = (π_{p_x,ζ})_y · a_{x,y}`; the diagonal entry is `1` minus the row sum. -/
noncomputable def metroGrid {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (p : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) → ℝ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (ζ : ℝ) (z w : Fin d → ℤ) : ℝ :=
  gridDist Ω ζ (p (latticePt ζ z)) w * metroAccept f (latticePt ζ z) (latticePt ζ w)

/-- The Gaussian weight `f(x) = exp(−β‖x‖²)` (arXiv:2609.40217, Definition 5.3, p.38). -/
noncomputable def gaussF {d : ℕ} (β : ℝ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  Real.exp (-β * ‖x‖ ^ 2)

open Classical in
/-- The proposal weight of the speedy walk, `p_x(y) = 1_{y ∈ x + δB_d}` (arXiv:2609.40217,
Definition 5.3, p.38: select `y ∈ (x + δB_d) ∩ K` uniformly at random). -/
noncomputable def ballInd {d : ℕ} (δ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if dist x y ≤ δ then 1 else 0

/-- The speedy walk `P_{β,δ}` on `K` (arXiv:2609.40217, Definition 5.3, p.38): at `x ∈ K` select
`y ∈ (x + δB_d) ∩ K` uniformly at random and accept it with probability `min{1, f(y)/f(x)}`,
`f(x) = exp(−β‖x‖²)`, else stay at `x`. It is the Metropolis walk of Definition 7.6 with proposal
`p_x = 1_{x + δB_d}` on `Ω = K`. -/
noncomputable def speedyKernel {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ : ℝ) :
    EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) :=
  metroKernel K (ballInd δ) (gaussF β)

/-- The stationary distribution `π_{β,δ}` of the speedy walk (arXiv:2609.40217, Definition 5.3 and
p.38: "supported on K and has a density proportional to ℓ_δ(x) f(x)", with the local conductance
`ℓ_δ(x) = Vol((x + δB_d) ∩ K)/Vol(δB_d)` of Definition 5.4).

**Formalization Note** Defined by the printed density: `Vol((x + δB_d) ∩ K) = N_{p_x}` is `ℓ_δ(x)`
up to the constant `Vol(δB_d)`, which the normalization removes. -/
noncomputable def speedyStatMeas {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  metroStat K (fun x => gaussF β x * massN K (ballInd δ x))

/-- The rounding `x_ζ = ζ · round(x/ζ)` to the grid `ζℤ^d`, coordinatewise to the nearest integer
(arXiv:2609.40217, Definition 7.4, p.43).

**Formalization Note** Mathlib's `round` sends half-integers up; ties form a null set. -/
noncomputable def roundGrid {d : ℕ} (ζ : ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun i => ζ * (round (x i / ζ) : ℝ))

/-- The cube set `M_{Ω,ζ} = ∪_{x ∈ Ω_ζ} M_{x,ζ} = {x ∈ ℝ^d : x_ζ ∈ Ω}` (arXiv:2609.40217,
Definition 7.4, p.43: `M_{y,ζ} = {x : x_ζ = y_ζ}`). -/
def cubeSet {d : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin d))) (ζ : ℝ) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {x | roundGrid ζ x ∈ Ω}

open Classical in
/-- The proposal weight of the cube speedy walk, `p_x(y) = 1_{y ∈ x_ζ + M_{δB_d,ζ}}`
(arXiv:2609.40217, Definition 8.4, p.48); `y ∈ x_ζ + M_{δB_d,ζ}` iff `‖y_ζ − x_ζ‖ ≤ δ`. -/
noncomputable def cubeInd {d : ℕ} (δ ζ : ℝ) (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖roundGrid ζ y - roundGrid ζ x‖ ≤ δ then 1 else 0

/-- The cube speedy walk `P^C_{β,δ,ζ}` on `M_{K,ζ}` (arXiv:2609.40217, Definition 8.4, p.48): at
`x ∈ M_{K,ζ}` select `y ∈ (x_ζ + M_{δB_d,ζ}) ∩ M_{K,ζ}` uniformly at random and move there with
probability `min{1, f(y)/f(x)}`, else stay. -/
noncomputable def cubeKernel {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ ζ : ℝ) :
    EuclideanSpace ℝ (Fin d) → Measure (EuclideanSpace ℝ (Fin d)) :=
  metroKernel (cubeSet K ζ) (cubeInd δ ζ) (gaussF β)

/-- The stationary distribution `π^C_{β,δ,ζ}` of the cube speedy walk, with density proportional
to `ℓ^C_{δ,ζ}(x) f(x)` on `M_{K,ζ}` (arXiv:2609.40217, p.48, with the cube local conductance
`ℓ^C_{δ,ζ}(x) = Vol((x_ζ + M_{δB_d,ζ}) ∩ M_{K,ζ})/Vol(M_{δB_d,ζ})` of Definition 8.5).

**Formalization Note** Defined by the printed density; the normalization removes the constant
`Vol(M_{δB_d,ζ})`. -/
noncomputable def cubeStat {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ ζ : ℝ) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  metroStat (cubeSet K ζ) (fun x => gaussF β x * massN (cubeSet K ζ) (cubeInd δ ζ x))

/-- The state space `K_ζ` of the discretized speedy walk, as the grid points of `(RB_d)_ζ` (the
published `QVolTransducer.Grid`) lying in `K` (arXiv:2609.40217, Definition 8.13, p.51). -/
abbrev KGrid {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (ζ R : ℝ) : Type :=
  {z : Grid d ζ R // latticePt ζ z.1 ∈ K}

open Classical in
/-- The probability transition matrix `P_{β,δ,ζ}` of the discretized speedy walk on `K_ζ`
(arXiv:2609.40217, Definition 8.13, p.51: at `x ∈ K_ζ` select `y ∈ (K ∩ (x + δB_d))_ζ` uniformly at
random and move there with probability `min{1, f(y)/f(x)}`, else stay at `x`). It is the naive
discretization of the speedy walk (Definition 7.6); the diagonal is `1` minus the off-diagonal row
sum. -/
noncomputable def discSpeedyMatrix {d : ℕ} (K : Set (EuclideanSpace ℝ (Fin d))) (β δ ζ R : ℝ) :
    Matrix (KGrid K ζ R) (KGrid K ζ R) ℝ :=
  fun x y =>
    if x = y then
      1 - ∑ y' ∈ Finset.univ.filter (fun y' => y' ≠ x),
        metroGrid K (ballInd δ) (gaussF β) ζ x.1.1 y'.1.1
    else metroGrid K (ballInd δ) (gaussF β) ζ x.1.1 y.1.1

end QVolTransducer.Supplement


