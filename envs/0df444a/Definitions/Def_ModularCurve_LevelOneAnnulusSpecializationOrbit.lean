-- Prove2me | Definitions.Def_ModularCurve_LevelOneAnnulusSpecializationOrbit
-- name    : ModularCurve_LevelOneAnnulusSpecializationOrbit
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/95192254-a357-56b6-8737-c3644a57c58f
-- title:
--   Rational-depth annulus specialization datum at level one
-- statement:
--   Working over a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a perfect field $k$ of characteristic $q$ with a ring map $\mathrm{red}\colon A \to k$, modular polynomial data satisfying the Kronecker congruence, integrality hypotheses for the two Hecke embeddings at level $1$, a place specialization $P$ and a prolongation tuple $R$ for it, this module introduces the structure `AnnulusDatumQ W` attached to a finite set $W$ of places of `modularFunctionFieldC k 1`. Its fields are: a family of intermediate fields $K(w)$ of $\overline{\mathbb Q}/\mathbb Q$; for each $w \in W$ a term of `R.NodeCoordinates (K w) w`, i.e. a pair $x_w,y_w$ of node integers over $K(w)$ whose first residue kills $x_w$ and has $\operatorname{ord}_w$ of the residue of $y_w$ equal to $1$ (and symmetrically for the second residue at $\mathrm{arithFrob}\cdot w$); a width function $W \to \mathbb N$; a **rational**-valued depth $\delta$ on the places of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$ (this is the one change from `AnnulusDatum`, whose depth is $\mathbb N$-valued, and `ofAnnulusDatum` is the resulting coercion); a cusp place; two uniformiser families `unifFst`, `unifSnd`; and three families of units $u_0, \lambda, \mu$ of $k$.
--
--   On such a datum the module defines the chain value $\mathrm{chainVal}$ of a twist vector $a$ ($a_Z$ at $d=0$, $a_{Z'}$ for $d \ge$ width, $a_E(w,d)$ in between), the two end slopes, and the predicate `IsNodeAnnulusPlace V`: $P.\mathrm{reduceFst}\,V \in W$, $V$ neither strict of the first nor of the second kind, and $0 < \delta(V) < \mathrm{width}$. Circle degrees are tent-weighted, $\mathrm{circleDeg}(D,w,d) = \sum_V D(V)\max(0, 1 - |\delta(V) - d|)$ over the non-strict $V$ above $w$ in the support of $D$; the end shares are the numerators of $\mathrm{circleDeg}$ at $d = 0$ and $d = \mathrm{width}\,w$ when these are integral and $0$ otherwise, and the end orders add end slope and end share. `IsTwistOf a D` asserts that $\deg P.\mathrm{fstDiv}\,D$ and $\deg P.\mathrm{sndDiv}\,D$ are minus the sums of the respective end orders over $W$, and that for $1 \le d$, $d+1 \le \mathrm{width}\,w$ the circle degree equals minus the discrete second difference of $\mathrm{chainVal}$.
--
--   The angular data are: $\mathrm{angCoord}$, the reduction of $V(y_w)\,q^{-\delta(V)}$ when $\delta(V)$ is integral and that element lies in $A$, else $0$ (with $\mathrm{angUnit}$ its unit version); the depth moment $m_w(D) = \sum_V D(V)\delta(V)$ over the same $V$; and $\mathrm{angFactor}$, the reduction of $\bigl(\prod_V V(y_w)^{-D(V)}\bigr) q^{m_w(D)}$ as a unit of $k$ when $m_w(D)$ is integral and that element lies in $A$ with non-zero reduction, and $1$ otherwise — so a single residue per node replaces the pointwise product of angular units. The cross terms $\mathrm{crossFst}(w',w)$, $\mathrm{crossSnd}(w',w)$ evaluate `unifFst w'` at $w$, resp. `unifSnd w'` at $\mathrm{arithFrob} \cdot w$, as units when non-zero. The node unit $\mathrm{nodeUnitOf}\,a\,D$ sends a node pair $s$ with first coordinate $w \in W$ to the additive image of $(-1)^{\mathrm{annulusDeg}\,D\,w}\,u_0(w)^{o_2}\lambda_w^{o_1}\mu_w^{-o_2}\,\mathrm{angFactor}_w(D)\prod_{w' \neq w}\mathrm{crossFst}(w',w)^{-o_1(w')}\mathrm{crossSnd}(w',w)^{o_2(w')}$, with $o_1,o_2$ the end orders, and to $1$ for pairs whose first coordinate lies outside $W$. Finally `spData a D` is the gluing datum whose two divisors are the push-forwards along $P.\mathrm{reduceFst}$, $P.\mathrm{reduceSnd}$ of the strict parts of $D$, each corrected at the cusp to degree zero, and whose node component is $\mathrm{nodeUnitOf}\,a\,D$; `sp a D` is its class in the glued degree-zero class group $\mathrm{GluedPic0}$ over the node pairs $\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,k\,1)\,W$ when the datum is admissible, and $0$ otherwise.
--
--   **Relation to Mathlib.** The ambient notions of place, divisor, gluing datum and glued degree-zero class group, as well as place specializations, prolongation tuples and node coordinates, are the project's own; Mathlib has no Picard group of a curve with prescribed nodes. Only the standard apparatus of valuation subrings, Laurent series, finitely supported functions and `Additive`/`Units` is taken from Mathlib.
--
--   **Where it is used.** The glued degree-zero class group here models the Picard group of the special fibre of $X_0(q)$ at $q$, two copies of the $j$-line crossing at the supersingular points, and `sp` is the specialization of an inertia-invariant divisor class to it. Unlike the pointwise version, the rational depth accommodates divisors that are only stable, not pointwise fixed, under inertia, the individual angular coordinates of a ramified orbit being replaced by the reduction of their product. These specialization maps feed the analysis of the component group and of the Galois action on the $q$-torsion of $J_0(q)$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneAnnulusSpecializationOrbit.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_LevelOneAnnulusSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve.PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)

structure AnnulusDatumQ (W : Finset (Place k (modularFunctionFieldC k 1))) where
  K : Place k (modularFunctionFieldC k 1) → IntermediateField ℚ (AlgebraicClosure ℚ)
  coord : ∀ w : Place k (modularFunctionFieldC k 1), w ∈ W → R.NodeCoordinates (K w) w
  width : Place k (modularFunctionFieldC k 1) → ℕ

  depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℚ

  cusp : Place k (modularFunctionFieldC k 1)

  unifFst : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)
  unifSnd : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)

  u0 : Place k (modularFunctionFieldC k 1) → kˣ
  lam : Place k (modularFunctionFieldC k 1) → kˣ
  mu : Place k (modularFunctionFieldC k 1) → kˣ

variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k 1))} (dat : R.AnnulusDatumQ W)

namespace AnnulusDatumQ

def ofAnnulusDatum (dat₀ : R.AnnulusDatum W) : R.AnnulusDatumQ W where
  K := dat₀.K
  coord := dat₀.coord
  width := dat₀.width
  depthQ V := dat₀.depth V
  cusp := dat₀.cusp
  unifFst := dat₀.unifFst
  unifSnd := dat₀.unifSnd
  u0 := dat₀.u0
  lam := dat₀.lam
  mu := dat₀.mu

def chainVal (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if dat.width w ≤ d then a.aZ' else a.aE w d

def endSlopeFst (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.chainVal a w 1 - dat.chainVal a w 0

def endSlopeSnd (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.chainVal a w (dat.width w - 1) - dat.chainVal a w (dat.width w)

def IsNodeAnnulusPlace (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  P.reduceFst V ∈ W ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
    0 < dat.depthQ V ∧ dat.depthQ V < dat.width (P.reduceFst V)

open Classical in

def circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) : ℚ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
    (D V : ℚ) * max 0 (1 - |dat.depthQ V - d|)

def endShareFst (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  if (dat.circleDeg D w 0).den = 1 then (dat.circleDeg D w 0).num else 0

def endShareSnd (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  if (dat.circleDeg D w (dat.width w)).den = 1 then (dat.circleDeg D w (dat.width w)).num else 0

def endOrderFst (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.endSlopeFst a w + dat.endShareFst D w

def endOrderSnd (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.endSlopeSnd a w + dat.endShareSnd D w

def IsTwistOf (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w ∧
    Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w ∧
    ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.circleDeg D w d = -((dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1) : ℤ) : ℚ)

open Classical in

def angCoord (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : k :=
  if h : (dat.depthQ V).den = 1 ∧
      V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))) *
        ((q : AlgebraicClosure ℚ) ^ (dat.depthQ V).num)⁻¹ ∈ A
  then red ⟨_, h.2⟩ else 0

open Classical in
def angUnit (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : kˣ :=
  if h : dat.angCoord w hw V ≠ 0 then Units.mk0 _ h else 1

open Classical in

def depthMoment (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℚ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ) * dat.depthQ V

open Classical in

def angFactor (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : kˣ :=
  if h : (dat.depthMoment D w).den = 1 ∧
      ∃ hmem : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
          V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))) ^ (-(D V))) *
        (q : AlgebraicClosure ℚ) ^ (dat.depthMoment D w).num ∈ A, red ⟨_, hmem⟩ ≠ 0
  then Units.mk0 (red ⟨_, h.2.choose⟩) h.2.choose_spec else 1

open Classical in

def crossFst (w' w : Place k (modularFunctionFieldC k 1)) : kˣ :=
  if h : w.evalAt (dat.unifFst w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def crossSnd (w' w : Place k (modularFunctionFieldC k 1)) : kˣ :=
  if h : (arithFrobC q k 1 • w).evalAt (dat.unifSnd w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def nodeUnitOf (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    ↥(nodePairsOfPlaces (arithFrobC q k 1) W) → Additive kˣ := fun s =>
  let w : Place k (modularFunctionFieldC k 1) :=
    (s : Place k (modularFunctionFieldC k 1) × Place k (modularFunctionFieldC k 1)).1
  Additive.ofMul <|
    if hw : w ∈ W then
      (-1 : kˣ) ^ (AnnulusDatum.annulusDeg (P := P) D w) *
      dat.u0 w ^ (dat.endOrderSnd a D w) *
      dat.lam w ^ (dat.endOrderFst a D w) *
      (dat.mu w ^ (dat.endOrderSnd a D w))⁻¹ *
      dat.angFactor w hw D *
      (∏ w' ∈ W.erase w,
        (dat.crossFst w' w ^ (dat.endOrderFst a D w'))⁻¹ * dat.crossSnd w' w ^ (dat.endOrderSnd a D w'))
    else 1

def spData (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    GluingData k (modularFunctionFieldC k 1) (nodePairsOfPlaces (arithFrobC q k 1) W) :=
  (Finsupp.mapDomain P.reduceFst (P.fstDiv D)
      - Divisor.degree (Finsupp.mapDomain P.reduceFst (P.fstDiv D)) • Finsupp.single dat.cusp 1,
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D)
      - Divisor.degree (Finsupp.mapDomain P.reduceSnd (P.sndDiv D)) • Finsupp.single dat.cusp 1,
    dat.nodeUnitOf a D)

open Classical in
def sp (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) :
    GluedPic0 k (modularFunctionFieldC k 1) (nodePairsOfPlaces (arithFrobC q k 1) W) :=
  if h : dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k 1) W) then
    GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k 1) W) ⟨dat.spData a D, h⟩
  else 0

end AnnulusDatumQ

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end


