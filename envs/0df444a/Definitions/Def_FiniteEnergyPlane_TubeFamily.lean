-- Prove2me | Definitions.Def_FiniteEnergyPlane_TubeFamily
-- name    : FiniteEnergyPlane_TubeFamily
-- status  : Definition
-- author  : @Mazecto
-- created : 2026-11-12T18:04:20.783523+00:00
-- url     : https://prove2.me/theorems/6ec407a9-0aa2-4803-b922-c16f2baadb2e
-- title:
--   Weighted cylinder coordinates and the $\bar J$-Cauchy–Riemann operator near $\mathbb{C}\times\{0\}$
-- statement:
--   Throughout, $\mathbb{R} \times \mathbb{R}/\mathbb{Z}$ carries the measure `cylMeasure` (Lebesgue measure on $\mathbb{R} \times [0,1)$), $L^4 = $ `LpCyl 1 4`, and $W^{1,4} = $ `W1p 4 1` $\subset L^4 \times L^4 \times L^4$ is the space of triples $(f, \partial_s f, \partial_t f)$ from `CauchyRiemannIndex`. The coordinate $z = e^{2\pi(s+it)}$ identifies the cylinder with $\mathbb{C}^*$, and $s \to -\infty$ corresponds to $z = 0$.
--
--   **Weights and cut-offs.**
--   - `IsSlopeWeight χ a b`: $\chi : \mathbb{R} \to \mathbb{R}$ is $C^\infty$, $\chi' = a$ on $(-\infty, -1]$ and $\chi' = b$ on $[1, \infty)$.
--   - `IsLeftCutoff β`: $\beta$ is $C^\infty$, $\beta = 1$ on $(-\infty, -1]$ and $\beta = 0$ on $[0, \infty)$.
--   - `cToVec` $: \mathbb{C} \to \mathbb{R}^2$ is the inverse of `vecToC`.
--   - `fact_one_le_four_ennreal` is the instance $1 \le 4$ in $[0, \infty]$ needed to form $L^4$.
--
--   **Normal coefficient.** For $\bar J : \mathbb{C} \times \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C} \times \mathbb{C})$, `normalCoeff Jbar (s, t)` is the real $2 \times 2$ matrix of
--   $$a \mapsto \Big[\big(\partial_w \bar J(z, 0)\, a\big)(2\pi i z, 0)\Big]_2, \qquad z = e^{2\pi(s+it)},$$
--   in the basis $1, i$ of $\mathbb{C} \cong \mathbb{R}^2$.
--
--   **Coefficients from the plane.** `IsPlaneCoeff S`, for $S : \mathbb{R} \times \mathbb{R} \to \mathbb{R}^{2\times 2}$, means: there is a $C^\infty$ map $A : \mathbb{C} \to \mathrm{End}_{\mathbb{R}}(\mathbb{C})$ with
--   $$S(s,t)\,a = 4\pi\, \bar z\, A(z)\,a, \qquad z = e^{2\pi(s+it)},$$
--   for all $s, t, a$. Equivalently, $\partial_s + i\partial_t + S = 4\pi \bar z\,(\partial_{\bar z} + A)$ under $z = e^{2\pi(s+it)}$: the cylinder operator is the pull-back of a smooth zeroth-order perturbation of $\partial_{\bar z}$ on all of $\mathbb{C}$, including $z = 0$.
--
--   **The nonlinear operator.** `QDom` $= W^{1,4} \times \mathbb{C} \times W^{1,4}$. For $x = (\zeta_T, c, \zeta_N) \in$ `QDom` and weights $\chi_T, \chi_N, \beta$, let (with representatives of the $L^4$ classes)
--   $$\psi = z + e^{\chi_T(s)} \zeta_T, \qquad v = \beta(s)\,c + e^{\chi_N(s)} \zeta_N,$$
--   with $\partial_s\psi, \partial_t\psi, \partial_s v, \partial_t v$ computed from $z = e^{2\pi(s+it)}$, the weights, and the derivative components of the triples. Put $G = (\psi, v)$ and
--   $$\mathrm{qPoint}(x)(s,t) = \Big(e^{-\chi_T(s)}\big[\partial_s G + \bar J(G)\,\partial_t G\big]_1,\ e^{-\chi_N(s)}\big[\partial_s G + \bar J(G)\,\partial_t G\big]_2\Big).$$
--   `qMap Jbar χT χN β x` $\in L^4 \times L^4$ is the pair of $L^4$ classes of the two components of `qPoint` (`toLpOrZero`: the class when the function lies in $L^4$, and $0$ otherwise).
--
--   **Role.** A zero of `qMap` is a $\bar J$-holomorphic map $G : \mathbb{C}^* \to \mathbb{C} \times \mathbb{C}$ near $z \mapsto (z, 0)$, with the tangential component $\psi - z$ weighted by $e^{\chi_T}$, the normal component $v$ weighted by $e^{\chi_N}$, and its value $c$ at $z = 0$ split off. These are the objects for statements about the space of $\bar J$-holomorphic planes near $\mathbb{C} \times \{0\}$ for a standard tube structure (`FiniteEnergyPlane_Tube`).
-- source:
--   Normal form near a fast plane, toward U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), arXiv:0812.4076, Section 6 (Lemmas 6.10, 6.20); cylinder conventions of C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Ch. 4

import Definitions.Def_FiniteEnergyPlane_Tube

/-!
# The Cauchy–Riemann operator of a standard tube structure on weighted cylinder Sobolev spaces

For a structure `Jbar` on `ℂ × ℂ` (see `FiniteEnergyPlane_Tube`), maps `G = (ψ, v) : ℂ → ℂ × ℂ`
near `z ↦ (z, 0)` are parametrized on the cylinder `ℝ × ℝ/ℤ`, `z = e^{2π(s+it)}`, by
`x = (ζT, c, ζN) ∈ W^{1,4} × ℂ × W^{1,4}`:
* `ψ = z + e^{χT(s)} ζT`;
* `v = β(s) c + e^{χN(s)} ζN`;

where `χT, χN` are smooth weights with constant slopes near `s = ±∞` and `β` is a cut-off equal
to `1` near `s = -∞`. `qMap` sends `x` to the two weighted components of `∂ₛG + Jbar(G) ∂ₜG` in
`L⁴ × L⁴`. Also: the zero-order coefficient `normalCoeff` of the normal linearization of `Jbar`
along `w = 0`, and the condition `IsPlaneCoeff` that a cylinder coefficient comes from a smooth
zero-order term on the plane.
-/

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology CauchyRiemannIndex
open scoped ContDiff ENNReal Real

noncomputable section

instance fact_one_le_four_ennreal : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- `χ` is smooth with slope `a` on `(-∞, -1]` and slope `b` on `[1, ∞)`. -/
def IsSlopeWeight (χ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContDiff ℝ ∞ χ ∧ (∀ s ≤ -1, deriv χ s = a) ∧ ∀ s ≥ 1, deriv χ s = b

/-- `ℂ → ℝ²`, the inverse of `vecToC`. -/
def cToVec (z : ℂ) : Vec 1 :=
  (EuclideanSpace.equiv (Fin 1 ⊕ Fin 1) ℝ).symm (Sum.elim (fun _ => z.re) (fun _ => z.im))

/-- `β` is smooth, `1` on `(-∞, -1]` and `0` on `[0, ∞)`. -/
def IsLeftCutoff (β : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ β ∧ (∀ s ≤ -1, β s = 1) ∧ ∀ s ≥ 0, β s = 0

/-- The real `2 × 2` matrix of the zero-order term of the normal linearization of `Jbar` along
`w = 0` in cylinder coordinates: `a ↦ [(∂_w Jbar(z, 0) a)(2πi z, 0)]₂` at `z = cylInf s t`. -/
def normalCoeff (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (x : ℝ × ℝ) : Mat 1 :=
  Matrix.of fun i j =>
    (Sum.elim (fun _ (y : ℂ) => y.re) (fun _ (y : ℂ) => y.im) : Fin 1 ⊕ Fin 1 → ℂ → ℝ) i
      ((fderiv ℝ (fun w : ℂ => Jbar (cylInf x.1 x.2, w)) 0
          ((Sum.elim (fun _ => (1 : ℂ)) (fun _ => Complex.I) : Fin 1 ⊕ Fin 1 → ℂ) j))
        (((2 * π : ℝ) : ℂ) * Complex.I * cylInf x.1 x.2, 0)).2

/-- The cylinder coefficient `S` is the pull-back of a smooth zero-order term `A` on the plane:
`∂ₛ + J₀ ∂ₜ + S = 4π z̄ (∂_{z̄} + A(z))` under `z = cylInf s t`. -/
def IsPlaneCoeff (S : ℝ × ℝ → Mat 1) : Prop :=
  ∃ A : ℂ → ℂ →L[ℝ] ℂ, ContDiff ℝ ∞ A ∧ ∀ (s t : ℝ) (a : Vec 1),
    vecToC (Matrix.toEuclideanLin (S (s, t)) a) =
      (4 * π : ℝ) * (starRingEnd ℂ) (cylInf s t) * A (cylInf s t) (vecToC a)

/-- The unknowns `(ζT, c, ζN)`. -/
abbrev QDom := ↥(W1p 4 1) × ℂ × ↥(W1p 4 1)

open Classical in
/-- The class in `L⁴` of `f`, or `0` if `f ∉ L⁴`. -/
def toLpOrZero (f : ℝ × ℝ → Vec 1) : LpCyl 1 4 :=
  if h : MemLp f 4 cylMeasure then h.toLp f else 0

/-- `∂ₛG + Jbar(G) ∂ₜG` at `(s, t)`, with the component weights `e^{-χT}`, `e^{-χN}`. -/
def qPoint (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (x : QDom) (q : ℝ × ℝ) :
    ℂ × ℂ :=
  let s := q.1
  let z := cylInf q.1 q.2
  let T : Triple 1 4 := (x.1 : Triple 1 4)
  let N : Triple 1 4 := (x.2.2 : Triple 1 4)
  let c := x.2.1
  let eT : ℂ := (Real.exp (χT s) : ℂ)
  let eN : ℂ := (Real.exp (χN s) : ℂ)
  let ψ := z + eT * vecToC (T.1 q)
  let ψs := ((2 * π : ℝ) : ℂ) * z + eT * (((deriv χT s : ℝ) : ℂ) * vecToC (T.1 q) + vecToC (T.2.1 q))
  let ψt := ((2 * π : ℝ) : ℂ) * Complex.I * z + eT * vecToC (T.2.2 q)
  let v := (β s : ℂ) * c + eN * vecToC (N.1 q)
  let vs := ((deriv β s : ℝ) : ℂ) * c + eN * (((deriv χN s : ℝ) : ℂ) * vecToC (N.1 q) + vecToC (N.2.1 q))
  let vt := eN * vecToC (N.2.2 q)
  let E := (ψs, vs) + Jbar (ψ, v) (ψt, vt)
  ((Real.exp (-χT s) : ℂ) * E.1, (Real.exp (-χN s) : ℂ) * E.2)

/-- The nonlinear Cauchy–Riemann operator of `Jbar` on the unknowns, `QDom → L⁴ × L⁴`. -/
def qMap (Jbar : ℂ × ℂ → ℂ × ℂ →L[ℝ] ℂ × ℂ) (χT χN β : ℝ → ℝ) (x : QDom) :
    LpCyl 1 4 × LpCyl 1 4 :=
  (toLpOrZero fun q => cToVec (qPoint Jbar χT χN β x q).1,
    toLpOrZero fun q => cToVec (qPoint Jbar χT χN β x q).2)

end

end FiniteEnergyPlane


