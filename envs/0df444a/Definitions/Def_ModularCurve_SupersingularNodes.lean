-- Prove2me | Definitions.Def_ModularCurve_SupersingularNodes
-- name    : ModularCurve_SupersingularNodes
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/f693d4ab-a398-5844-a653-87b7958374b2
-- title:
--   Frobenius-paired places on the j-line, with widths
-- statement:
--   Throughout, $K$ is a field and $F =$ `modularFunctionFieldC K 1`, the intermediate field of $K((q))$ generated over $K$ by the formal $q$-expansion `jqModC K` of the modular invariant; since that series is transcendental over $K$, this field is $K$-isomorphic to $K(T)$, and for $a \in K$ the place `charLGeomPlaceOfPoint K a` of $F$ over $K$ is the transport along that isomorphism of the place $T = a$ of the rational function field, a place of degree one. Fix a natural number $q$. The map `frobNodePair q` sends $a \in K$ to the ordered pair of places $(P_a, P_{a^q})$, where $P_b$ denotes `charLGeomPlaceOfPoint K b`; it is injective because $b \mapsto P_b$ is, and `frobNodePairEmb q` packages it as an embedding of $K$ into the product of the place set with itself. For a finite subset $S \subseteq K$, `nodePairsOf q S` is the image finset $\{(P_a,P_{a^q}) : a \in S\}$, whose membership criterion and cardinality ($=\#S$) are recorded. The map `jOfNode q S` picks, for an element $s$ of `nodePairsOf q S`, the parameter $a \in S$ with $(P_a,P_{a^q}) = s$; it is a two-sided inverse of `frobNodePair q` on $S$, and `nodeEquiv q S` is the resulting equivalence $S \simeq$ `nodePairsOf q S`, with its coercion lemmas. Finally, given a weight $e \colon K \to \mathbb{N}$, `widthOf q S e` is the function on `nodePairsOf q S` obtained by transporting $e$ along `jOfNode q S`, so that the pair attached to $a$ receives the value $e(a)$. The module defines only this indexing and bookkeeping: nothing is asserted here about any modular curve or its reduction.
--
--   **Relation to Mathlib.** The places used are the project's own [`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22) (a valuation subring of the field, containing the image of the base field, proper, and a principal ideal ring), and `modularFunctionFieldC` is the project's formal $q$-expansion model of the function field; Mathlib has no counterpart. The packaging uses Mathlib's `Finset.map` and `Equiv` machinery.
--
--   **Where it is used.** The intended instantiation takes $K$ of characteristic $q$, $S$ the finite set of supersingular $j$-invariants there, and $e$ the weight $3$ at $j = 0$, $2$ at $j = 1728$ and $1$ elsewhere: the pairs $(P_a, P_{a^q})$ then index the crossing points of the two copies of the $j$-line in the Deligne–Rapoport description of $X_0(q)$ in characteristic $q$, glued by Frobenius, and `widthOf` records the thickness of each crossing. These finite data are the combinatorial input to the semistable specialisation datum for $J_0(q)$ at $q$ used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SupersingularNodes.lean

import Definitions.Def_ModularCurve_SpecializeModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

variable {K : Type*} [Field K]

def frobNodePair (q : ℕ) (a : K) :
    Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  (charLGeomPlaceOfPoint K a, charLGeomPlaceOfPoint K (a ^ q))

@[simp] theorem frobNodePair_fst (q : ℕ) (a : K) :
    (frobNodePair q a).1 = charLGeomPlaceOfPoint K a := rfl

@[simp] theorem frobNodePair_snd (q : ℕ) (a : K) :
    (frobNodePair q a).2 = charLGeomPlaceOfPoint K (a ^ q) := rfl

theorem frobNodePair_injective (q : ℕ) : Function.Injective (frobNodePair (K := K) q) :=
  fun _ _ h => charLGeomPlaceOfPoint_injective K (congrArg Prod.fst h)

def frobNodePairEmb (q : ℕ) :
    K ↪ Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1) :=
  ⟨frobNodePair q, frobNodePair_injective q⟩

@[simp] theorem frobNodePairEmb_apply (q : ℕ) (a : K) :
    frobNodePairEmb q a = frobNodePair q a := rfl

def nodePairsOf (q : ℕ) (S : Finset K) :
    Finset (Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :=
  S.map (frobNodePairEmb q)

theorem mem_nodePairsOf_iff (q : ℕ) (S : Finset K)
    (s : Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1)) :
    s ∈ nodePairsOf q S ↔ ∃ a ∈ S, frobNodePair q a = s := by
  simp only [nodePairsOf, Finset.mem_map, frobNodePairEmb_apply]

theorem frobNodePair_mem_nodePairsOf (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    frobNodePair q a ∈ nodePairsOf q S :=
  Finset.mem_map_of_mem (frobNodePairEmb q) ha

@[simp] theorem card_nodePairsOf (q : ℕ) (S : Finset K) : (nodePairsOf q S).card = S.card :=
  Finset.card_map _

def jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : K :=
  Classical.choose ((mem_nodePairsOf_iff q S s).mp s.2)

theorem jOfNode_mem (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) : jOfNode q S s ∈ S :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).1

@[simp] theorem frobNodePair_jOfNode (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    frobNodePair q (jOfNode q S s) = s :=
  (Classical.choose_spec ((mem_nodePairsOf_iff q S s).mp s.2)).2

@[simp] theorem jOfNode_mk (q : ℕ) {S : Finset K} {a : K} (ha : a ∈ S) :
    jOfNode q S ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = a :=
  frobNodePair_injective q (frobNodePair_jOfNode q S _)

theorem jOfNode_injective (q : ℕ) (S : Finset K) : Function.Injective (jOfNode q S) :=
  fun s t h => Subtype.ext (by rw [← frobNodePair_jOfNode q S s, ← frobNodePair_jOfNode q S t, h])

def nodeEquiv (q : ℕ) (S : Finset K) : ↥S ≃ ↥(nodePairsOf q S) where
  toFun a := ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q a.2⟩
  invFun s := ⟨jOfNode q S s, jOfNode_mem q S s⟩
  left_inv a := Subtype.ext (jOfNode_mk q a.2)
  right_inv s := Subtype.ext (frobNodePair_jOfNode q S s)

@[simp] theorem coe_nodeEquiv_apply (q : ℕ) (S : Finset K) (a : ↥S) :
    ((nodeEquiv q S a : ↥(nodePairsOf q S)) :
      Place K (modularFunctionFieldC K 1) × Place K (modularFunctionFieldC K 1))
      = frobNodePair q (a : K) := rfl

@[simp] theorem coe_nodeEquiv_symm_apply (q : ℕ) (S : Finset K) (s : ↥(nodePairsOf q S)) :
    ((nodeEquiv q S).symm s : K) = jOfNode q S s := rfl

def widthOf (q : ℕ) (S : Finset K) (e : K → ℕ) : ↥(nodePairsOf q S) → ℕ :=
  fun s => e (jOfNode q S s)

theorem widthOf_apply (q : ℕ) (S : Finset K) (e : K → ℕ) (s : ↥(nodePairsOf q S)) :
    widthOf q S e s = e (jOfNode q S s) := rfl

@[simp] theorem widthOf_mk (q : ℕ) {S : Finset K} (e : K → ℕ) {a : K} (ha : a ∈ S) :
    widthOf q S e ⟨frobNodePair q a, frobNodePair_mem_nodePairsOf q ha⟩ = e a := by
  rw [widthOf_apply, jOfNode_mk q ha]

theorem widthOf_nodeEquiv (q : ℕ) (S : Finset K) (e : K → ℕ) (a : ↥S) :
    widthOf q S e (nodeEquiv q S a) = e a :=
  widthOf_mk q e a.2

end ModularCurve

end


