-- Prove2me | Definitions.Def_ModularCurve_LevelOneAnnulusSpecialization
-- name    : ModularCurve_LevelOneAnnulusSpecialization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/287ae9ad-d661-57f4-b5f9-7292354b766f
-- title:
--   Level-one annulus specialisation of divisor classes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a perfect field $k$ of characteristic $q$ with a ring homomorphism $\mathrm{red}:A\to k$, modular polynomial data with its Kronecker congruence, integrality of the two Hecke branches, a level-one place specialisation $P$ and a prolongation tuple $R$ for it. For a finite set $W$ of places of the level-one geometric modular function field $\mathrm{modularFunctionFieldC}\,k\,1$, an `AnnulusDatum` over $W$ packages: an intermediate field $K(w)\subseteq\overline{\mathbb{Q}}$ and, for $w\in W$, a choice of node coordinates `R.NodeCoordinates (K w) w` (a pair $x,y$ of node integers over $K(w)$ with $x$ killed by the first residue map and a uniformiser for the second, and symmetrically for $y$); a width function on places of the level-one field; a depth function on places of $\mathrm{modularFunctionFieldBar}(1\cdot q)$; a distinguished place `cusp`; two uniformiser assignments `unifFst`, `unifSnd`; and three $k^\times$-valued functions `u0`, `lam`, `mu`. A `TwistVector` consists of integers `aZ`, `aZ'` and a family `aE` indexed by places and naturals; `chainVal` reads it as a function on the chain over $w$, equal to `aZ` at index $0$, to `aZ'` at all indices $\ge$ the width, and to `aE w d` in between, and `endSlopeFst`, `endSlopeSnd` are its two boundary differences (the index `width w - 1` being truncated natural subtraction). `IsNodeAnnulusPlace` says that a place $V$ above lies over a member of $W$, is fixed by the inertia subgroup of $A$ acting through arithmetic Galois, and has depth strictly between $0$ and the width. `annulusDeg` and `circleDeg` sum the coefficients of a divisor $D$ over places lying over $w$ that are neither strictly first nor strictly second type, the latter also restricting to a fixed depth. `IsTwistOf a D` asserts that $\deg P.\mathrm{fstDiv}\,D$ and $\deg P.\mathrm{sndDiv}\,D$ are the negatives of the summed end slopes, and that for $1\le d$, $d+1\le\mathrm{width}\,w$ the circle degree equals minus the second difference of `chainVal`: the twist vector is a discrete potential for the annulus degrees. The angular coordinate `angCoord` is the image under $\mathrm{red}$ of $V(y_w)\cdot q^{-\mathrm{depth}\,V}$ when that element lies in $A$, and $0$ otherwise; `angUnit` turns it into a unit (or $1$); `crossFst w' w` and `crossSnd w' w` are the evaluations of `unifFst w'` at $w$ and of `unifSnd w'` at the Frobenius translate $\mathrm{arithFrobC}\cdot w$, again as units or $1$. The node unit `nodeUnitOf a D` attaches to a node pair with first entry $w\in W$ the product $(-1)^{\mathrm{annulusDeg}}u_0(w)^{n_2}\lambda_w^{n_1}\mu_w^{-n_2}\prod_{V/w}\mathrm{angUnit}(V)^{-D(V)}\prod_{w'\ne w}\mathrm{crossFst}(w',w)^{-n_1(w')}\mathrm{crossSnd}(w',w)^{n_2(w')}$, with $n_1,n_2$ the end slopes, and $1$ otherwise. Finally `spData a D` is the gluing datum whose two divisors are the pushforwards of $P.\mathrm{fstDiv}\,D$ and $P.\mathrm{sndDiv}\,D$ along $P.\mathrm{reduceFst}$, $P.\mathrm{reduceSnd}$, each corrected by subtracting its degree times the cusp, and whose node component is `nodeUnitOf a D`; `sp a D` is the class of this datum in the glued degree-zero Picard group when the datum is admissible, and $0$ otherwise.
--
--   **Relation to Mathlib.** Mathlib has no notion of gluing data or of the glued degree-zero Picard group of two curves identified along pairs of places; `GluingData`, `GluedPic0`, `Place`, `Divisor` and the prolongation and place-specialisation structures are the project's own, Mathlib contributing the ambient machinery (`Finsupp.mapDomain`, `Additive`, `Units`, valuation subrings, `AlgebraicClosure ℚ`).
--
--   **Where it is used.** These data give the explicit candidate value of a specialisation map on inertia-invariant degree-zero classes of the modular curve of level $q$ in terms of the reduction of its two branches glued at the supersingular places, refining the cruder gluing datum of the level-one glue data module by the contributions of places supported on the annuli over the nodes and by the cusp correction that forces degree zero. The twist vector records the discrete potential whose existence reflects the vanishing of the component class, so that a class may be pushed into the glued Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LevelOneAnnulusSpecialization.lean

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_ModularCurve_NodeDepth
import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_ProlongationTuple

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

structure AnnulusDatum (W : Finset (Place k (modularFunctionFieldC k 1))) where
  K : Place k (modularFunctionFieldC k 1) → IntermediateField ℚ (AlgebraicClosure ℚ)
  coord : ∀ w : Place k (modularFunctionFieldC k 1), w ∈ W → R.NodeCoordinates (K w) w
  width : Place k (modularFunctionFieldC k 1) → ℕ
  depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) → ℕ

  cusp : Place k (modularFunctionFieldC k 1)

  unifFst : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)
  unifSnd : Place k (modularFunctionFieldC k 1) → ↥(modularFunctionFieldC k 1)

  u0 : Place k (modularFunctionFieldC k 1) → kˣ
  lam : Place k (modularFunctionFieldC k 1) → kˣ
  mu : Place k (modularFunctionFieldC k 1) → kˣ

structure TwistVector (W : Finset (Place k (modularFunctionFieldC k 1))) where
  aZ : ℤ
  aZ' : ℤ
  aE : Place k (modularFunctionFieldC k 1) → ℕ → ℤ

variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k 1))} (dat : R.AnnulusDatum W)

namespace AnnulusDatum

def chainVal (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if dat.width w ≤ d then a.aZ' else a.aE w d

def endSlopeFst (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.chainVal a w 1 - dat.chainVal a w 0

def endSlopeSnd (a : TwistVector (k := k) W) (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  dat.chainVal a w (dat.width w - 1) - dat.chainVal a w (dat.width w)

def IsNodeAnnulusPlace (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  P.reduceFst V ∈ W ∧
    (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (modularFunctionFieldFull (1 * q)) σ • V = V) ∧
    0 < dat.depth V ∧ dat.depth V < dat.width (P.reduceFst V)

open Classical in
def annulusDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) : ℤ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V

open Classical in
def circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (w : Place k (modularFunctionFieldC k 1)) (d : ℕ) : ℤ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ dat.depth V = d ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V

def IsTwistOf (a : TwistVector (k := k) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endSlopeFst a w ∧
    Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endSlopeSnd a w ∧
    ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.circleDeg D w d = -(dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1))

open Classical in

def angCoord (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : k :=
  if h : V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (1 * q))) *
      ((q : AlgebraicClosure ℚ) ^ dat.depth V)⁻¹ ∈ A
  then red ⟨_, h⟩ else 0

open Classical in
def angUnit (w : Place k (modularFunctionFieldC k 1)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : kˣ :=
  if h : dat.angCoord w hw V ≠ 0 then Units.mk0 _ h else 1

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
      (-1 : kˣ) ^ (annulusDeg (P := P) D w) *
      dat.u0 w ^ (dat.endSlopeSnd a w) *
      dat.lam w ^ (dat.endSlopeFst a w) *
      (dat.mu w ^ (dat.endSlopeSnd a w))⁻¹ *
      (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
        dat.angUnit w hw V ^ (-(D V))) *
      (∏ w' ∈ W.erase w,
        (dat.crossFst w' w ^ (dat.endSlopeFst a w'))⁻¹ * dat.crossSnd w' w ^ (dat.endSlopeSnd a w'))
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

end AnnulusDatum

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end


