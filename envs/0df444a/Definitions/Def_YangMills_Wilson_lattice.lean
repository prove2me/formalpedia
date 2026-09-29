-- Prove2me | Definitions.Def_YangMills_Wilson_lattice
-- name    : YangMills_Wilson_lattice
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T12:33:14.408892+00:00
-- url     : https://prove2.me/theorems/e85c310a-beb3-4de2-917f-09c468af0d8b
-- title:
--   Wilson lattice regularisation of $SU(N)$ Yang–Mills theory
-- statement:
--   This file fixes the lattice side of the Yang–Mills problem: Wilson's regularisation of
--   $SU(N)$ gauge theory, and the notion of a continuum (scaling) limit of it.
--
--   **Gauge group and lattice.** The gauge group is $SU(N)$, the special unitary subgroup of
--   $N\times N$ complex matrices. The lattice is the periodic four-dimensional torus
--   $\Lambda_L=(\mathbb Z/(L+1))^4$ of side $L+1$ with unit spacing; a *link* is a pair $(x,\mu)$ of
--   a site and a direction $\mu\in\{0,1,2,3\}$, with direction $0$ the Euclidean time direction. A
--   *gauge configuration* $U$ assigns an element $U_\mu(x)\in SU(N)$ to every link.
--
--   **Plaquettes and the Wilson action.** Writing $\hat\mu$ for the unit step in direction $\mu$, the
--   plaquette variable is
--   $$U_{\mu\nu}(x)=U_\mu(x)\,U_\nu(x+\hat\mu)\,U_\mu(x+\hat\nu)^{-1}\,U_\nu(x)^{-1},$$
--   and, with $\operatorname{retr}(g)=\tfrac1N\operatorname{Re}\operatorname{tr}(g)$, the Wilson
--   energy density at a site is $P_x(U)=\sum_{\mu<\nu}\bigl(1-\operatorname{retr}U_{\mu\nu}(x)\bigr)$.
--   For an inverse coupling $\beta$ the Wilson action is $S_\beta(U)=\beta\sum_{x\in\Lambda_L}P_x(U)$
--   and the Gibbs expectation of an observable $F$ is
--   $$\langle F\rangle_{L,\beta}=\frac{\int F(U)\,e^{-S_\beta(U)}\,d\mu_G^{\otimes}(U)}
--   {\int e^{-S_\beta(U)}\,d\mu_G^{\otimes}(U)},$$
--   the integrals being taken against the product over links of the Haar probability measure $\mu_G$
--   on $SU(N)$.
--
--   **Wilson loops.** For $R,T\ge0$, the $R\times T$ Wilson loop is the normalised real trace of the
--   holonomy around the rectangle based at the origin that runs $R$ steps in the spatial direction
--   $1$, $T$ steps in the time direction $0$, and back.
--
--   **Link reflection.** The Osterwalder–Seiler reflection is taken in the hyperplane half way
--   between the time slices $0$ and $1$: on sites it is $(x^0,\vec x)\mapsto(1-x^0,\vec x)$, on
--   spatial links it transports the link to its mirror image, and on temporal links it takes the
--   inverse of the mirror image, because the reflection reverses the time orientation. An observable
--   is supported in the positive-time half when it depends only on links both of whose endpoints lie
--   in the time slices $1,\dots,\lfloor(L+1)/2\rfloor$.
--
--   **Smeared field and the scaling limit.** At lattice spacing $a>0$ and field normalisation $Z$,
--   the smeared plaquette-density field is the Riemann sum
--   $$\Phi_{a,Z}(f)(U)=Z\,a^4\sum_{x\in\Lambda_L}f(a\,x)\,\bigl(P_x(U)-\langle P_x\rangle_{L,\beta}\bigr),$$
--   where sites are embedded in $\mathbb R^4$ by their representatives, centred at the origin, and
--   the lattice Schwinger functions are the Gibbs expectations of products
--   $\langle\prod_i\Phi_{a,Z}(f_i)\rangle_{L,\beta}$. Finally, a Euclidean theory $Q$ is a
--   **continuum (scaling) limit of $SU(N)$ Wilson lattice gauge theory** when there are spacings
--   $a_k\to0$, sides $L_k+1$ with physical size $a_k(L_k+1)\to\infty$, inverse couplings
--   $\beta_k\to\infty$ and normalisations $Z_k$ such that every lattice Schwinger function converges
--   to the corresponding Schwinger function of $Q$.
--
--   **Formalization Note.** The Haar measure enters as a hypothesis — a Borel probability measure on
--   $SU(N)$, invariant under translations — rather than being constructed; the periodic torus avoids
--   boundary conditions; and the continuum field is built from the gauge-invariant plaquette density,
--   so no gauge fixing is needed.
-- source:
--   K. G. Wilson, Confinement of quarks, Phys. Rev. D 10 (1974) 2445-2459, Section II (eq. 3.4, the plaquette action); K. Osterwalder and E. Seiler, Gauge field theories on a lattice, Ann. Physics 110 (1978) 440-471, Sections 2-3 (link reflection, Theorem 2.1); E. Seiler, Gauge Theories as a Problem of Constructive Quantum Field Theory and Statistical Mechanics, Lecture Notes in Physics 159 (1982), Chapter 2.

import Definitions.Def_YangMills_OS_axioms

/-!
# Wilson's lattice regularisation of `SU(N)` Yang–Mills theory

This file sets up the lattice side of the Yang–Mills existence and mass gap problem:
`SU(N)` gauge configurations on a periodic hypercubic lattice, the Wilson plaquette action,
the corresponding Gibbs expectation, Wilson loops, the smeared plaquette-density field,
Osterwalder–Seiler link reflection, and the notion of a continuum (scaling) limit of the
lattice theory.

Throughout, the lattice is the discrete four-torus of side `L + 1` with unit spacing; a
physical lattice spacing `a > 0` enters only when lattice observables are smeared against
continuum test functions.
-/

namespace YangMills

open MeasureTheory Filter Topology Finset

/-- The gauge group `SU(N)`, as the special unitary subgroup of `N × N` complex matrices. -/
abbrev SU (N : ℕ) : Type := Matrix.specialUnitaryGroup (Fin N) ℂ

/-- Sites of the periodic four-dimensional lattice of side `L + 1`. -/
abbrev Site (L : ℕ) : Type := Fin 4 → ZMod (L + 1)

/-- Oriented links: a site together with a positive lattice direction. -/
abbrev Link (L : ℕ) : Type := Site L × Fin 4

/-- A lattice gauge field: an `SU(N)` element on every link. -/
abbrev Cfg (N L : ℕ) : Type := Link L → SU N

/-- Translate a site by `k` steps in direction `μ`. -/
def shift {L : ℕ} (x : Site L) (μ : Fin 4) (k : ℤ) : Site L :=
  Function.update x μ (x μ + (k : ZMod (L + 1)))

/-- The normalised real trace `Re tr(g) / N` of a gauge group element. -/
noncomputable def reTr {N : ℕ} (g : SU N) : ℝ :=
  ((g : Matrix (Fin N) (Fin N) ℂ).trace).re / (N : ℝ)

/-- The plaquette variable: the holonomy around the unit square at `x` in the `(μ, ν)` plane. -/
def plaquette {N L : ℕ} (U : Cfg N L) (x : Site L) (μ ν : Fin 4) : SU N :=
  U (x, μ) * U (shift x μ 1, ν) * (U (shift x ν 1, μ))⁻¹ * (U (x, ν))⁻¹

/-- The Wilson energy density at a site: `∑_{μ < ν} (1 - Re tr(U_{μν}(x)) / N)`. -/
noncomputable def plaqDensity {N L : ℕ} (U : Cfg N L) (x : Site L) : ℝ :=
  ∑ μ : Fin 4, ∑ ν : Fin 4, if μ < ν then 1 - reTr (plaquette U x μ ν) else 0

/-- The Wilson action at inverse coupling `β`: `β` times the sum of the energy density over
all sites of the torus. -/
noncomputable def wilsonAction {N L : ℕ} (β : ℝ) (U : Cfg N L) : ℝ :=
  β * ∑ x : Site L, plaqDensity U x

/-- The Wilson–Gibbs expectation of an observable `F`, computed with respect to the product of
the Haar probability measure `μG` over the links, weighted by `exp (- wilsonAction β)`. -/
noncomputable def wilsonExp {N : ℕ} (L : ℕ) [MeasurableSpace (SU N)] (μG : Measure (SU N))
    [IsProbabilityMeasure μG] (β : ℝ) (F : Cfg N L → ℝ) : ℝ :=
  (∫ U, F U * Real.exp (-wilsonAction β U) ∂(Measure.pi fun _ : Link L => μG)) /
    (∫ U, Real.exp (-wilsonAction β U) ∂(Measure.pi fun _ : Link L => μG))

/-- The graph distance between two sites of the periodic lattice. -/
def torusDist {L : ℕ} (x y : Site L) : ℕ :=
  ∑ μ : Fin 4, min ((x μ - y μ).val) ((y μ - x μ).val)

/-- The normalised real trace of the holonomy around the `R × T` rectangle based at the origin,
extending `R` steps in the spatial direction `1` and `T` steps in the time direction `0`. -/
noncomputable def wilsonLoop {N L : ℕ} (R T : ℕ) (U : Cfg N L) : ℝ :=
  let o : Site L := fun _ => 0
  let p1 := ((List.range R).map fun i => U (shift o 1 (i : ℤ), 1)).prod
  let p2 := ((List.range T).map fun j => U (shift (shift o 1 (R : ℤ)) 0 (j : ℤ), 0)).prod
  let p3 := ((List.range R).map fun i =>
      (U (shift (shift o 1 ((R : ℤ) - 1 - (i : ℤ))) 0 (T : ℤ), 1))⁻¹).prod
  let p4 := ((List.range T).map fun j => (U (shift o 0 ((T : ℤ) - 1 - (j : ℤ)), 0))⁻¹).prod
  reTr (p1 * p2 * p3 * p4)

/-! ### Osterwalder–Seiler link reflection -/

/-- Link reflection of sites in the hyperplane half way between the time slices `0` and `1`:
`(x⁰, x⃗) ↦ (1 - x⁰, x⃗)`. -/
def siteRefl {L : ℕ} (x : Site L) : Site L := Function.update x 0 (1 - x 0)

/-- The induced reflection on gauge configurations: spatial links are transported to their
mirror image, temporal links to the reverse of their mirror image. -/
def cfgRefl {N L : ℕ} (U : Cfg N L) : Cfg N L := fun l =>
  if l.2 = 0 then (U (shift (siteRefl l.1) 0 (-1), 0))⁻¹ else U (siteRefl l.1, l.2)

/-- A link lies in the positive-time half of the torus of side `L + 1`: both of its endpoints
are in the time slices `1, …, (L + 1) / 2`. -/
def PosLink {L : ℕ} (l : Link L) : Prop :=
  if l.2 = 0 then 1 ≤ (l.1 0).val ∧ (l.1 0).val + 1 ≤ (L + 1) / 2
  else 1 ≤ (l.1 0).val ∧ (l.1 0).val ≤ (L + 1) / 2

/-- An observable is supported in the positive-time half if it depends only on the gauge field
on links lying in that half. -/
def PosObs {N L : ℕ} (F : Cfg N L → ℝ) : Prop :=
  ∀ U V : Cfg N L, (∀ l : Link L, PosLink l → U l = V l) → F U = F V

/-! ### Smeared fields and the continuum limit -/

/-- The embedding of lattice sites into `ℝ⁴` at lattice spacing `1`, centred at the origin. -/
noncomputable def emb (L : ℕ) (x : Site L) : Spacetime :=
  fun μ => ((x μ).val : ℝ) - ((L : ℝ) + 1) / 2

/-- The plaquette-density field at lattice spacing `a` and field normalisation `Z`, smeared
against a test function `f`: the Riemann sum `Z a⁴ ∑_x f(a x) (P_x - ⟨P_x⟩)` of the centred
Wilson energy density. -/
noncomputable def smearedField {N : ℕ} (L : ℕ) [MeasurableSpace (SU N)] (μG : Measure (SU N))
    [IsProbabilityMeasure μG] (β a Z : ℝ) (f : TestFn) (U : Cfg N L) : ℝ :=
  Z * a ^ 4 * ∑ x : Site L,
    f (a • emb L x) * (plaqDensity U x - wilsonExp L μG β fun V => plaqDensity V x)

/-- The `n`-point Schwinger function of the smeared lattice plaquette-density field. -/
noncomputable def latticeSchwinger {N : ℕ} (L : ℕ) [MeasurableSpace (SU N)]
    (μG : Measure (SU N)) [IsProbabilityMeasure μG] (β a Z : ℝ) (n : ℕ)
    (f : Fin n → TestFn) : ℝ :=
  wilsonExp L μG β fun U => ∏ i : Fin n, smearedField L μG β a Z (f i) U

/-- `Q` is a *continuum (scaling) limit of `SU(N)` Wilson lattice gauge theory*: there are
lattice spacings `a k → 0`, lattice sides `L k + 1` whose physical size `a k * (L k + 1)` tends
to infinity, inverse couplings `β k → ∞` (asymptotic freedom) and field normalisations `Z k`
such that all Schwinger functions of the smeared plaquette-density field converge to those
of `Q`. -/
def IsWilsonScalingLimit (N : ℕ) [MeasurableSpace (SU N)] (μG : Measure (SU N))
    [IsProbabilityMeasure μG] (Q : OSTheory) : Prop :=
  ∃ a : ℕ → ℝ, ∃ L : ℕ → ℕ, ∃ β Z : ℕ → ℝ,
    (∀ k, 0 < a k) ∧ Tendsto a atTop (𝓝 0) ∧
    Tendsto (fun k => a k * ((L k : ℝ) + 1)) atTop atTop ∧
    Tendsto β atTop atTop ∧
    ∀ (n : ℕ) (f : Fin n → TestFn),
      Tendsto (fun k => ((latticeSchwinger (N := N) (L k) μG (β k) (a k) (Z k) n f : ℝ) : ℂ))
        atTop (𝓝 (Q.S n f))

end YangMills


