-- Prove2me | Definitions.Def_APSCounting893_Main_Resultant
-- name    : APSCounting893_Main_Resultant
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:24:22.05327+00:00
-- url     : https://prove2.me/theorems/19c96f71-0c43-4f51-9a4a-d6678038d983
-- title:
--   Homogenization, actual resultant, perturbation limits and trailing coefficients
-- statement:
--   All $N=n+m$ affine coordinates are homogenized with $z_0$ using positive formal degrees $d_i$. The perturbed forms are $\widehat G_i=G_i+\epsilon z_i^{d_i}$. A universal integer resultant is selected from the independently published normalized irreducible resultant specification, then evaluated on these actual forms and
--
--   $$H_{T,w}=Tz_0^2-z_0\ell(y)+\sum_{j=1}^Nw^jz_j^2.$$
--
--   Thus $R=\operatorname{Res}(\widehat G_1,\ldots,\widehat G_N,H_{T,w})$ is defined without any assumed APS factorization. The finite-limit candidate set is constructed by specializing actual nonnegative-valuation $\epsilon$-Puiseux solutions and passing to projective representatives; infinity points are retained.
--
--   For a nonzero polynomial, $\mathrm{TC}_v$ extracts the coefficient of the least nonzero power of $v$, without retaining that power. Auxiliary indices order $\epsilon,w,t,T$, and nested extraction follows that order. The zero-polynomial default is zero, outside every nonzero-polynomial theorem hypothesis. Projective rescaling remains explicit in the factorization milestone.
-- source:
--   Sanyam Agarwal, Archit Hari, Anurag Pandey, Himanshu Shukla, STOC 2027 submission #893 (October 2026), §§4.3–5.2, equations (4.4), (5.2)–(5.5), p. 20, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf

import Definitions.Def_APSCounting893_Main_LineGeometry
import Definitions.Def_ResultantVNP_IsMultivariateResultant

set_option autoImplicit false

namespace APSCounting893.Main

/-- The normalized universal integer polynomial is selected by its independent specification,
not by the APS factorization to be proved. All subsequent evaluations use this one polynomial. -/
noncomputable def universalResultant {n : ℕ} (d : Fin n → ℕ) :
    MvPolynomial (ResultantVNP.CoeffVar d) ℤ :=
  Classical.epsilon (ResultantVNP.IsMultivariateResultant d)

noncomputable def homogeneousResultant {K : Type} [CommRing K] {n : ℕ}
    (d : Fin n → ℕ) (G : Fin n → MvPolynomial (Fin n) K) : K :=
  MvPolynomial.eval₂ (Int.castRingHom K)
    (fun v : ResultantVNP.CoeffVar d => (G v.1).coeff v.2.val) (universalResultant d)

/-- Extract the coefficient of v^k, retaining all other polynomial variables. -/
noncomputable def coefficientIn {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (k : ℕ) (p : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  ∑ e ∈ p.support, if e v = k then MvPolynomial.monomial (e - Finsupp.single v k) (p.coeff e) else 0

open Classical in
noncomputable def trailingCoefficient {K : Type} [CommRing K] {n : ℕ}
    (v : Fin n) (p : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  if h : p.support.Nonempty then
    coefficientIn v ((p.support.image (fun e => e v)).min' (h.image _)) p
  else 0

noncomputable def nestedTrailing {K : Type} [CommRing K] {n : ℕ}
    (order : List (Fin n)) (p : MvPolynomial (Fin n) K) : MvPolynomial (Fin n) K :=
  order.foldl (fun q v => trailingCoefficient v q) p

/-- Auxiliary indices are ε=0, w=1, t=2 and T=3. -/
abbrev Aux := MvPolynomial (Fin 4) ℂ

noncomputable def homogenizeAll {K : Type} [CommRing K] {n : ℕ}
    (degree : ℕ) (p : MvPolynomial (Fin n) K) : MvPolynomial (Fin (n + 1)) K :=
  ∑ e ∈ p.support,
    MvPolynomial.monomial
      (Finsupp.single 0 (degree - e.sum (fun _ k => k)) + e.mapDomain Fin.succ) (p.coeff e)

noncomputable def equationWithAux (F : RawMap) (c alpha : Affine ℂ F.n)
    (i : Fin (F.n + (F.n + 1))) : MvPolynomial (Fin (F.n + (F.n + 1))) Aux :=
  MvPolynomial.map (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X 2))
    (affineLineEquations F c alpha (Fin.cast (Nat.add_comm _ _) i))

noncomputable def homogenizedEquation (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (i : Fin (F.n + (F.n + 1))) :
    MvPolynomial (Fin (F.n + (F.n + 1) + 1)) Aux :=
  homogenizeAll (degrees i) (equationWithAux F c alpha i)

noncomputable def perturbedEquation (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) (i : Fin (F.n + (F.n + 1))) :
    MvPolynomial (Fin (F.n + (F.n + 1) + 1)) Aux :=
  homogenizedEquation F c alpha degrees i +
    MvPolynomial.C (MvPolynomial.X 0) * MvPolynomial.X i.succ ^ degrees i

noncomputable def separatingForm {n : ℕ} (lambda : Affine ℂ n) (y : Affine ℂ n) : ℂ :=
  ∑ i, lambda i * y i

noncomputable def HForm (F : RawMap) (lambda : Affine ℂ (F.n + 1)) :
    MvPolynomial (Fin (F.n + (F.n + 1) + 1)) Aux :=
  MvPolynomial.C (MvPolynomial.X 3) * MvPolynomial.X 0 ^ 2 -
    MvPolynomial.X 0 * (∑ j : Fin (F.n + 1),
      MvPolynomial.C (MvPolynomial.C (lambda j)) * MvPolynomial.X (j.natAdd F.n).succ) +
    ∑ j : Fin (F.n + (F.n + 1)),
      MvPolynomial.C (MvPolynomial.X 1 ^ (j.val + 1)) * MvPolynomial.X j.succ ^ 2

noncomputable def resultantFor (F : RawMap) (c alpha : Affine ℂ F.n)
    (lambda : Affine ℂ (F.n + 1)) (degrees : Fin (F.n + (F.n + 1)) → ℕ) : Aux :=
  homogeneousResultant (Fin.lastCases 2 degrees)
    (Fin.lastCases (HForm F lambda) (perturbedEquation F c alpha degrees))

noncomputable def HomogenizingDegrees (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) : Prop :=
  ∀ i, 0 < degrees i ∧ degrees i ≤ F.d ∧ (equationWithAux F c alpha i).totalDegree ≤ degrees i

noncomputable def resultantCriterion (R : Aux) : Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C (fun i => if i = 3 then Polynomial.X else 0)
    (nestedTrailing [0, 1, 2] R)

open Classical in
/-- A projective point is represented uniquely by scaling its first nonzero coordinate to 1. -/
noncomputable def projectiveRepresentative {K : Type} [Field K] {n : ℕ}
    (z : Fin n → K) : Fin n → K :=
  if h : (Finset.univ.filter (fun i => z i ≠ 0)).Nonempty then
    fun i => z i / z ((Finset.univ.filter (fun j => z j ≠ 0)).min' h)
  else 0

abbrev EpsilonAmbient := HahnSeries ℚ PuiseuxAmbient

/-- Actual specialization of ε-Puiseux solutions over the t-series field. -/
noncomputable def epsilonLimitSet (F : RawMap) (c alpha : Affine ℂ F.n)
    (degrees : Fin (F.n + (F.n + 1)) → ℕ) :
    Set (Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) :=
  {z | ∃ q : Fin (F.n + (F.n + 1) + 1) → EpsilonAmbient,
    (∀ j, (∃ (e : ℕ) (he : 0 < e), q j ∈ HahnSeries.puiseuxRamSubfield PuiseuxAmbient he) ∧
      0 ≤ (q j).orderTop) ∧
    (∃ j, (q j).orderTop = 0) ∧
    (∀ i : Fin (F.n + (F.n + 1)),
      MvPolynomial.eval₂
        (MvPolynomial.eval₂Hom (HahnSeries.C.comp HahnSeries.C)
          (fun v : Fin 4 => if v = 0 then HahnSeries.single (1 : ℚ) 1
            else if v = 2 then HahnSeries.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0))
        q (perturbedEquation F c alpha degrees i) = 0) ∧
    z = projectiveRepresentative (fun j => (q j).coeff 0)}

noncomputable def trailingEpsilonResultant (R : Aux) : MvPolynomial (Fin 2) PuiseuxAmbient :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp HahnSeries.C)
    (fun v : Fin 4 => if v = 1 then MvPolynomial.X 0 else if v = 3 then MvPolynomial.X 1
      else if v = 2 then MvPolynomial.C (HahnSeries.single (1 : ℚ) (1 : ℂ)) else 0)
    (trailingCoefficient 0 R)

noncomputable def HAtPoint (F : RawMap) (lambda : Affine ℂ (F.n + 1))
    (z : Fin (F.n + (F.n + 1) + 1) → PuiseuxAmbient) : MvPolynomial (Fin 2) PuiseuxAmbient :=
  MvPolynomial.X 1 * MvPolynomial.C (z 0 ^ 2) -
    MvPolynomial.C (z 0 * ∑ j : Fin (F.n + 1), HahnSeries.C (lambda j) * z (j.natAdd F.n).succ) +
    ∑ j : Fin (F.n + (F.n + 1)), MvPolynomial.X 0 ^ (j.val + 1) * MvPolynomial.C (z j.succ ^ 2)

end APSCounting893.Main


