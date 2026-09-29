-- Prove2me | Definitions.Def_WeierstrassCurve_DrinfeldBasisRelative
-- name    : WeierstrassCurve_DrinfeldBasisRelative
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/17feda56-7d18-5cd5-b56f-bdb81d440033
-- title:
--   Drinfeld bases over a test scheme for a relative group law
-- statement:
--   Fix a commutative ring $R$ and a projective Weierstrass curve $V$ over $R$, with its graded Proj model $E =$ `projModelCR V` and structure morphism $f =$ `projModelStrCR V` to $\operatorname{Spec} R$, and let $G$ be a `RelativeGroupLaw` for $f$: a choice, for every $T \to \operatorname{Spec} R$, of group operations on the set of $T$-points of $f$, with associativity, unit and inverse axioms and naturality of multiplication under base change along $T' \to T$. For a test morphism $t : T \to \operatorname{Spec} R$ and $T$-points $P, Q$ of $f$, `linCombOver` is the point $aP + bQ$, formed from the iterated multiplications $G.\mathrm{nsmul}$ (repeated multiplication by $P$ resp. $Q$ starting from the unit point). Given $q$, `basisTupleOver` is the family of $q^2$ underlying morphisms $T \to E$ indexed by $i \in \mathrm{Fin}(q\cdot q)$ obtained from the coefficient pair $(\lfloor i/q\rfloor, i \bmod q)$, and `basisTupleOver_over` records that each of these lies over $t$. Then `basisDivisorOver` is the product, over these $q^2$ indices, of the kernel ideal sheaves of the graphs $T \to E \times_{\operatorname{Spec} R} T$ of the points, i.e. the ideal sheaf of the effective divisor $\sum_{a,b<q} [aP+bQ]$ on $E \times_{\operatorname{Spec} R} T$. Independently of $P,Q$, `torsionIdealOver` is the kernel ideal sheaf, on $E$, of the first projection of the fibre product of the scheme-level multiplication-by-$q$ morphism `G.schemeNsmul q` with the unit section, pulled back (comap) along $E \times_{\operatorname{Spec} R} T \to E$. Finally `IsDrinfeldBasisOver` is the predicate asserting the equality of these two ideal sheaves on $E \times_{\operatorname{Spec} R} T$.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient machinery (Proj of a graded ring, pullbacks of schemes, `Scheme.IdealSheafData` and the kernel ideal sheaf of a morphism); the relative group law, the graph divisor `prodKerGraph` and the Drinfeld basis predicate are the project's own notions.
--
--   **Where it is used.** These definitions give the Drinfeld $\Gamma(q)$-level-structure condition on pairs of $T$-points of a fixed projective Weierstrass model with a fixed relative group law, in the form of an identity of ideal sheaves on $E \times_R T$ rather than on a base-changed model; they are the relative counterpart of the corresponding predicate over the base itself, and serve the moduli-of-elliptic-curves-with-level-structure side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_WeierstrassCurve_DrinfeldBasisRelative.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_ProjModel
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NeronModelInfra WeierstrassProjModel

namespace WeierstrassProjModel.RelativeGroupLaw

variable {R : Type u} [CommRing R] {V : WeierstrassCurve.Projective R}

def linCombOver (G : RelativeGroupLaw R (projModelStrCR V)) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (P Q : SchemeHomOver t (projModelStrCR V)) (a b : ℕ) : SchemeHomOver t (projModelStrCR V) :=
  G.mul t (G.nsmul t a P) (G.nsmul t b Q)

def basisTupleOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) :
    Fin (q * q) → (T ⟶ projModelCR V) :=
  fun i => (G.linCombOver t P Q (i.val / q) (i.val % q)).1

theorem basisTupleOver_over (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) (i : Fin (q * q)) :
    G.basisTupleOver q t P Q i ≫ projModelStrCR V = t :=
  (G.linCombOver t P Q (i.val / q) (i.val % q)).2

def basisDivisorOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) :
    (pullback (projModelStrCR V) t).IdealSheafData :=
  prodKerGraph (projModelStrCR V) (G.basisTupleOver q t P Q) (G.basisTupleOver_over q t P Q)

def torsionIdealOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : (pullback (projModelStrCR V) t).IdealSheafData :=
  (pullback.fst (G.schemeNsmul q) (G.one (𝟙 (Spec (CommRingCat.of R)))).1).ker.comap
    (pullback.fst (projModelStrCR V) t)

def IsDrinfeldBasisOver (G : RelativeGroupLaw R (projModelStrCR V)) (q : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t (projModelStrCR V)) : Prop :=
  G.basisDivisorOver q t P Q = G.torsionIdealOver q t

end WeierstrassProjModel.RelativeGroupLaw

end


