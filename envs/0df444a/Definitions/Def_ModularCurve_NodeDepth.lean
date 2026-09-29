-- Prove2me | Definitions.Def_ModularCurve_NodeDepth
-- name    : ModularCurve_NodeDepth
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/78d56cd1-49f5-51af-80fa-d5b7ef4f7bfa
-- title:
--   Node depths, crossing coordinates, and the component-group law
-- statement:
--   Throughout, $q$ is a prime, $A$ a valuation subring of $\overline{\mathbb Q}$ with a reduction homomorphism $red : A \to k$ to a field $k$ of characteristic $q$, $N \ge 1$, and $P$ a `PlaceSpecialization` attached to modular polynomial data satisfying a Kronecker congruence together with integrality hypotheses for the two degeneracy maps; $R$ is a `ProlongationTuple` over $P$. First, for a finite index set $\iota$ and $s \in \iota$, `crossingCoord s` is the $\mathbb Z$-linear functional on the character lattice `characterLattice ι` (a submodule of $\iota \to \mathbb Z$) given by $\gamma \mapsto \gamma(s)$. Next, given a weight function $depth$ on the places of $\overline{\mathbb Q}$-rational function field of level $Nq$ and a divisor $D$ there, `depthDiv` is the divisor on the level-$N$ fibre over $k$ obtained by pushing $D$ forward along $P$'s first reduction map `reduceFst`, each multiplicity being multiplied by $depth$ of the place; `depthDual` packages this into the functional $\sum_s (\mathrm{depthDiv}\,D)(s_1)\cdot\,$`crossingCoord s` on the character lattice of the set of node pairs $\{(w, g\cdot w) : w \in W\}$ for a semilinear automorphism $g$ and a finite set $W$ of places. `DepthCompLaw` is then a property of an additive map $comp$ from the inertia invariants of $\mathrm{Pic}^0$ at level $Nq$ to the component group of the width function $w \mapsto e(w)$: for every degree-zero divisor $D$ whose class lies in those invariants and all of whose support places are fixed by the arithmetic Galois action of the inertia subgroup of $A$ over $\mathbb Q$ and are strict for the first or second reduction or reduce to a place of $W$, and for every node pair $s_0$, the value of $comp$ on the class of $D$ is the image under `componentGroupProj` of `depthDual` applied to $D$ plus $\deg(P.\mathrm{sndDiv}\,D)$ times $e(s_{0,1})\cdot$`crossingCoord` at $s_0$. Finally, for a place $w$ of the level-$N$ fibre, `ValueIntegralityLaw` asserts that every $f$ in the node ring $R.\mathrm{nodeIntegers}\,w$ takes values in $A$ at all places $V$ with $\mathrm{reduceFst}\,V = w$; and for node coordinates $c = (x,y)$ at $w$ over an intermediate field $K$ (so that $x$ has zero first residue and is a uniformiser for the second residue at $g\cdot w$, and $y$ symmetrically), `xDepth` and `yDepth` are the $A$-valuations of the values $x(V)$, $y(V)$ in the value group of $A$, and `DepthValueLaw` states that at every inertia-fixed $V$ over $w$ one has $\mathrm{yDepth}(V) = v_A(q)^{depth(V)}$.
--
--   **Relation to Mathlib.** The linear algebra and valuation-theoretic ingredients are Mathlib's (`Module.Dual`, `LinearMap.proj`, `Finsupp` divisors, `ValuationSubring.valuation` and its value group); the node rings, depth weights, character lattice of crossings and the component-group laws are project notions with no Mathlib counterpart.
--
--   **Where it is used.** These notions quantify how a divisor on the level-$Nq$ curve meets the crossings of a semistable model at $q$: the depth of a place measures the $q$-adic position of the point in the annulus $xy =$ (power of $q$) at a node, and `DepthCompLaw` records that specialisation of inertia-invariant degree-zero classes into the component group of the special fibre is computed by the resulting functional on the character lattice. They are the local input for the description of the inertia action on the Jacobian at $q$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_NodeDepth.lean

import Definitions.Def_ModularCurve_NodeLocalizedPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

namespace ModularCurve

section CrossingCoord

variable {ι : Type*} [Fintype ι]

def crossingCoord (s : ι) : Module.Dual ℤ (characterLattice ι) :=
  (LinearMap.proj s).comp (characterLattice ι).subtype

@[simp] theorem crossingCoord_apply (s : ι) (γ : characterLattice ι) :
    crossingCoord s γ = γ.1 s :=
  rfl

end CrossingCoord

namespace PlaceSpecialization

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
  (P : PlaceSpecialization A q N data hKr k red hα hβ)

def depthDiv (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Divisor k (modularFunctionFieldC k N) :=
  D.sum fun V n => Finsupp.single (P.reduceFst V) (n * (depth V : ℤ))

def depthDual (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :
    Module.Dual ℤ (characterLattice ↥(nodePairsOfPlaces g W)) :=
  ∑ s : ↥(nodePairsOfPlaces g W),
    P.depthDiv depth D
        (s : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N)).1 •
      crossingCoord s

def DepthCompLaw (g : SemilinearAut k (modularFunctionFieldC k N))
    (W : Finset (Place k (modularFunctionFieldC k N)))
    (e : Place k (modularFunctionFieldC k N) → ℕ)
    (depth : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)) → ℕ)
    (comp : ↥(inertiaInvariants A (N * q)) →+ componentGroup (widthOfPlaces g W e)) : Prop :=
  ∀ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))))
    (hH : Pic0.mk D ∈ inertiaInvariants A (N * q)),
    (∀ V ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))).support,
      (∀ σ ∈ A.inertiaSubgroupIn ℚ,
          arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) ∧
        (P.IsStrictFst V ∨ P.IsStrictSnd V ∨ P.reduceFst V ∈ W)) →
    ∀ (s₀ : Place k (modularFunctionFieldC k N) × Place k (modularFunctionFieldC k N))
      (hs₀ : s₀ ∈ nodePairsOfPlaces g W),
      comp ⟨Pic0.mk D, hH⟩ =
        componentGroupProj (widthOfPlaces g W e)
          (P.depthDual g W depth (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) +
            Divisor.degree (P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))) •
              ((e s₀.1 : ℤ) • crossingCoord ⟨s₀, hs₀⟩))

namespace ProlongationTuple

variable {P} (R : ProlongationTuple P)

def ValueIntegralityLaw (w : Place k (modularFunctionFieldC k N)) : Prop :=
  ∀ f : ↥(modularFunctionFieldBar (N * q)), f ∈ R.nodeIntegers w →
    ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w → V.evalAt f ∈ A

namespace NodeCoordinates

variable {R} [PerfectField k] {K : IntermediateField ℚ (AlgebraicClosure ℚ)}
  {w : Place k (modularFunctionFieldC k N)} (c : R.NodeCoordinates K w)

def xDepth (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : A.ValueGroup :=
  A.valuation (V.evalAt (c.x : ↥(modularFunctionFieldBar (N * q))))

def yDepth (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) : A.ValueGroup :=
  A.valuation (V.evalAt (c.y : ↥(modularFunctionFieldBar (N * q))))

def DepthValueLaw (depth : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)) → ℕ) : Prop :=
  ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q)), P.reduceFst V = w →
    (∀ σ ∈ A.inertiaSubgroupIn ℚ,
        arithmeticGalois (modularFunctionFieldFull (N * q)) σ • V = V) →
    c.yDepth V = A.valuation ((q : ℕ) : AlgebraicClosure ℚ) ^ depth V

end NodeCoordinates

end ProlongationTuple

end PlaceSpecialization

end ModularCurve

end


