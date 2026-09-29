-- Prove2me | Definitions.Def_ModularCurve_AnnulusSpecializationLevel
-- name    : ModularCurve_AnnulusSpecializationLevel
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/5701ff1f-dbf4-5d0a-bc57-a86681f4ef51
-- title:
--   Level-N annulus data, twist vectors and twisted specialization
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb Q}$, $N \ge 1$, $k$ a perfect field of characteristic $q$ with a ring map $red : A \to k$, and $P$ a `PlaceSpecialization` for the data $(q,N,\mathrm{data},h_{Kr},h_\alpha,h_\beta)$ together with a `ProlongationTuple` $R$ for $P$; $W$ is a finite set of places of the geometric level-$N$ function field `modularFunctionFieldC k N`. Two structures are defined, both pure data. An `AnnulusDatumLevel W` consists of: a subfield $K_w \subset \overline{\mathbb Q}$ for each place $w$; for each $w \in W$ a choice of node coordinates `R.NodeCoordinates (K w) w` (a pair $x,y$ of node integers over $K_w$ with $\mathrm{res}_1 x = 0$, $\mathrm{ord}_{\varphi w}(\mathrm{res}_2 x) = 1$, $\mathrm{res}_2 y = 0$, $\mathrm{ord}_w(\mathrm{res}_1 y) = 1$); a width $e_w \in \mathbb N$; a rational depth function $\delta$ on the places of `modularFunctionFieldBar (N*q)` over $\overline{\mathbb Q}$; two functions $\pi_w, \pi'_w$ in the level-$N$ function field; two divisors $R_w, R'_w$ on it; and three units $u_0(w), \lambda_w, \mu_w \in k^\times$. No compatibility between $\pi_w,\pi'_w$ and $R_w,R'_w$ (such as $\operatorname{div} \pi_w = (w) + R_w$) is part of the structure. A `TwistVectorLevel W` consists of two integers $a_Z, a_{Z'}$ and a family $a_{w,d} \in \mathbb Z$ indexed by places and naturals.
--
--   The derived notions all restrict attention to the places $V$ above with $P.\mathrm{reduceFst}\,V = w$ that are neither `IsStrictFst` nor `IsStrictSnd`. For a divisor $D$: `annulusDeg` sums $D V$ over these; `circleDeg D w d` is the tent-weighted sum $\sum_V D V \cdot \max(0, 1 - |\delta(V) - d|)$, a piecewise-linear distribution of $D$ onto the integers $d$ of the chain; `depthMoment` is $\sum_V D V \cdot \delta(V)$. On the twist side, `chainVal a w d` equals $a_Z$ for $d = 0$, $a_{Z'}$ for $d \ge e_w$ and $a_{w,d}$ in between; `endSlopeFst`/`endSlopeSnd` are its one-sided differences at the two ends, and `endOrderFst`/`endOrderSnd` add to these the integer parts `endShareFst`/`endShareSnd` of `circleDeg` at $d = 0$ and $d = e_w$ (taken to be $0$ when the value is not an integer). `IsNodeAnnulusPlace V` says $P.\mathrm{reduceFst}\,V \in W$, $V$ is strict on neither side, and $0 < \delta(V) < e_{P.\mathrm{reduceFst} V}$. `IsTwistOf a D` asserts $\deg P.\mathrm{fstDiv}\,D = -\sum_{w \in W} \mathrm{endOrderFst}$, the same for the second side, and that for $1 \le d \le e_w - 1$ the value `circleDeg D w d` is minus the discrete Laplacian $a_{w,d-1} - 2a_{w,d} + a_{w,d+1}$ of the chain values.
--
--   The unit data at a node is assembled from: `angCoord`/`angUnit`, the reduction under $red$ of $V(y) \cdot q^{-\delta(V)}$ when $\delta(V) \in \mathbb Z$ and this lies in $A$ (otherwise $0$, resp. $1$); `angFactor w hw D`, the reduction of $\bigl(\prod_V V(y)^{-D V}\bigr) q^{\mathrm{depthMoment}}$ when the moment is an integer and the element lies in $A$ with nonzero reduction (otherwise $1$); and the cross factors `crossFst w' w`, `crossSnd w' w`, the values of $\pi_{w'}$ at $w$ and of $\pi'_{w'}$ at $\varphi \cdot w$ ($\varphi =$ `arithFrobC q k N`) as units when nonzero. For $s$ a node pair in `nodePairsOfPlaces (arithFrobC q k N) W` with first coordinate $w \in W$, `nodeUnitOf a D` is
--   $$(-1)^{\mathrm{annulusDeg}\,D\,w}\, u_0(w)^{o_2(w)}\, \lambda_w^{o_1(w)}\, \mu_w^{-o_2(w)}\, \mathrm{angFactor}_w(D) \prod_{w' \in W \setminus \{w\}} \mathrm{crossFst}(w',w)^{-o_1(w')}\,\mathrm{crossSnd}(w',w)^{o_2(w')},$$
--   written additively, where $o_1 = \mathrm{endOrderFst}\,a\,D$ and $o_2 = \mathrm{endOrderSnd}\,a\,D$; it is $1$ otherwise. Finally `spData a D` is the gluing datum whose two divisors are the push-forwards $\mathrm{reduceFst}_*(P.\mathrm{fstDiv}\,D) - \sum_{w \in W} o_1(w)\, R_w$ and $\mathrm{reduceSnd}_*(P.\mathrm{sndDiv}\,D) - \sum_{w \in W} o_2(w)\, R'_w$ and whose node-unit component is `nodeUnitOf a D`, and `sp a D` is its class in `GluedPic0 k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W)` when that datum is admissible (both divisors of degree zero and vanishing at the node places), and $0$ otherwise.
--
--   **Relation to Mathlib.** Mathlib has no notion of gluing data for a curve with nodes or of the resulting glued degree-zero Picard group; `GluingData`, `GluedPic0`, `Place`, `Divisor` and the modular function fields used here are the project's own, while `Finsupp`, `Additive`, `IntermediateField` and `ValuationSubring` are Mathlib's.
--
--   **Where it is used.** These data describe, on the level of divisors, units at the crossings and twists along the chains of exceptional curves, the specialization of degree-zero divisor classes on $X_0(Nq)_{\overline{\mathbb Q}}$ to the Deligne–Rapoport special fibre at $q$ (two copies of $X_0(N)_k$ meeting at the supersingular places, with chains of rational curves in a regular model). They are the level-$N$ counterpart of the level-one annulus data and feed the computation of the component group and of the special fibre of the Néron model of $J_0(Nq)$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_AnnulusSpecializationLevel.lean

import Mathlib
import Definitions.Def_ModularCurve_GlueData
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

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] [PerfectField k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)

structure AnnulusDatumLevel (W : Finset (Place k (modularFunctionFieldC k N))) where
  K : Place k (modularFunctionFieldC k N) → IntermediateField ℚ (AlgebraicClosure ℚ)
  coord : ∀ w : Place k (modularFunctionFieldC k N), w ∈ W → R.NodeCoordinates (K w) w
  width : Place k (modularFunctionFieldC k N) → ℕ

  depthQ : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℚ

  unifFst : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N)
  unifSnd : Place k (modularFunctionFieldC k N) → ↥(modularFunctionFieldC k N)

  corrFst : Place k (modularFunctionFieldC k N) → Divisor k ↥(modularFunctionFieldC k N)
  corrSnd : Place k (modularFunctionFieldC k N) → Divisor k ↥(modularFunctionFieldC k N)

  u0 : Place k (modularFunctionFieldC k N) → kˣ
  lam : Place k (modularFunctionFieldC k N) → kˣ
  mu : Place k (modularFunctionFieldC k N) → kˣ

structure TwistVectorLevel (W : Finset (Place k (modularFunctionFieldC k N))) where
  aZ : ℤ
  aZ' : ℤ
  aE : Place k (modularFunctionFieldC k N) → ℕ → ℤ

variable {R}
variable {W : Finset (Place k (modularFunctionFieldC k N))} (dat : R.AnnulusDatumLevel W)

namespace AnnulusDatumLevel

open Classical in

def annulusDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), D V

def chainVal (a : TwistVectorLevel (k := k) (N := N) W) (w : Place k (modularFunctionFieldC k N)) (d : ℕ) : ℤ :=
  if d = 0 then a.aZ else if dat.width w ≤ d then a.aZ' else a.aE w d

def endSlopeFst (a : TwistVectorLevel (k := k) (N := N) W) (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.chainVal a w 1 - dat.chainVal a w 0

def endSlopeSnd (a : TwistVectorLevel (k := k) (N := N) W) (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.chainVal a w (dat.width w - 1) - dat.chainVal a w (dat.width w)

def IsNodeAnnulusPlace (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  P.reduceFst V ∈ W ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V ∧
    0 < dat.depthQ V ∧ dat.depthQ V < dat.width (P.reduceFst V)

open Classical in

def circleDeg (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) (d : ℕ) : ℚ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
    (D V : ℚ) * max 0 (1 - |dat.depthQ V - d|)

def endShareFst (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  if (dat.circleDeg D w 0).den = 1 then (dat.circleDeg D w 0).num else 0

def endShareSnd (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  if (dat.circleDeg D w (dat.width w)).den = 1 then (dat.circleDeg D w (dat.width w)).num else 0

def endOrderFst (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.endSlopeFst a w + dat.endShareFst D w

def endOrderSnd (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℤ :=
  dat.endSlopeSnd a w + dat.endShareSnd D w

def IsTwistOf (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : Prop :=
  Divisor.degree (P.fstDiv D) = -∑ w ∈ W, dat.endOrderFst a D w ∧
    Divisor.degree (P.sndDiv D) = -∑ w ∈ W, dat.endOrderSnd a D w ∧
    ∀ w ∈ W, ∀ d : ℕ, 1 ≤ d → d + 1 ≤ dat.width w →
      dat.circleDeg D w d = -((dat.chainVal a w (d - 1) - 2 * dat.chainVal a w d + dat.chainVal a w (d + 1) : ℤ) : ℚ)

open Classical in

def angCoord (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : k :=
  if h : (dat.depthQ V).den = 1 ∧
      V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))) *
        ((q : AlgebraicClosure ℚ) ^ (dat.depthQ V).num)⁻¹ ∈ A
  then red ⟨_, h.2⟩ else 0

open Classical in
def angUnit (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : kˣ :=
  if h : dat.angCoord w hw V ≠ 0 then Units.mk0 _ h else 1

open Classical in

def depthMoment (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)))
    (w : Place k (modularFunctionFieldC k N)) : ℚ :=
  ∑ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V), (D V : ℚ) * dat.depthQ V

open Classical in

def angFactor (w : Place k (modularFunctionFieldC k N)) (hw : w ∈ W)
    (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : kˣ :=
  if h : (dat.depthMoment D w).den = 1 ∧
      ∃ hmem : (∏ V ∈ D.support with (P.reduceFst V = w ∧ ¬ P.IsStrictFst V ∧ ¬ P.IsStrictSnd V),
          V.evalAt ((dat.coord w hw).y : ↥(modularFunctionFieldBar (N * q))) ^ (-(D V))) *
        (q : AlgebraicClosure ℚ) ^ (dat.depthMoment D w).num ∈ A, red ⟨_, hmem⟩ ≠ 0
  then Units.mk0 (red ⟨_, h.2.choose⟩) h.2.choose_spec else 1

open Classical in

def crossFst (w' w : Place k (modularFunctionFieldC k N)) : kˣ :=
  if h : w.evalAt (dat.unifFst w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def crossSnd (w' w : Place k (modularFunctionFieldC k N)) : kˣ :=
  if h : (arithFrobC q k N • w).evalAt (dat.unifSnd w') ≠ 0 then Units.mk0 _ h else 1

open Classical in

def nodeUnitOf (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    ↥(nodePairsOfPlaces (arithFrobC q k N) W) → Additive kˣ := fun s =>
  let w : Place k (modularFunctionFieldC k N) :=
    (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1
  Additive.ofMul <|
    if hw : w ∈ W then
      (-1 : kˣ) ^ (annulusDeg (P := P) D w) *
      dat.u0 w ^ (dat.endOrderSnd a D w) *
      dat.lam w ^ (dat.endOrderFst a D w) *
      (dat.mu w ^ (dat.endOrderSnd a D w))⁻¹ *
      dat.angFactor w hw D *
      (∏ w' ∈ W.erase w,
        (dat.crossFst w' w ^ (dat.endOrderFst a D w'))⁻¹ * dat.crossSnd w' w ^ (dat.endOrderSnd a D w'))
    else 1

def spData (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    GluingData k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W) :=
  (Finsupp.mapDomain P.reduceFst (P.fstDiv D) - ∑ w ∈ W, dat.endOrderFst a D w • dat.corrFst w,
    Finsupp.mapDomain P.reduceSnd (P.sndDiv D) - ∑ w ∈ W, dat.endOrderSnd a D w • dat.corrSnd w,
    dat.nodeUnitOf a D)

open Classical in
def sp (a : TwistVectorLevel (k := k) (N := N) W) (D : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    GluedPic0 k (modularFunctionFieldC k N) (nodePairsOfPlaces (arithFrobC q k N) W) :=
  if h : dat.spData a D ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q k N) W) then
    GluedPic0.mk (nodePairsOfPlaces (arithFrobC q k N) W) ⟨dat.spData a D, h⟩
  else 0

end AnnulusDatumLevel

end ProlongationTuple

end ModularCurve.PlaceSpecialization

end


