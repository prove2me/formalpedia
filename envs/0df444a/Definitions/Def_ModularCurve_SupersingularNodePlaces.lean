-- Prove2me | Definitions.Def_ModularCurve_SupersingularNodePlaces
-- name    : ModularCurve_SupersingularNodePlaces
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/658f3d73-a9d2-50b9-8edf-18f96560b247
-- title:
--   Node pairs of places; supersingular places of the modular function field
-- statement:
--   Two unrelated groups of definitions. First, for a field extension $F/K$, recall that a place of $F$ over $K$ is a valuation subring $A \subseteq F$ containing the image of $K$, with $A \neq F$ and $A$ a principal ideal ring, and that the group $\mathrm{SemilinearAut}\,K\,F$ of pairs $(\sigma,\tau) \in \mathrm{Aut}(F) \times \mathrm{Aut}(K)$ with $\sigma \circ \iota = \iota \circ \tau$ acts on places by transporting valuation subrings. For $g$ in that group, `smulNodePair` sends a place $w$ to the ordered pair $(w, g \cdot w)$; this is injective (the first coordinate recovers $w$), so it packages as an embedding and, for a finite set $W$ of places, gives the finite set $\mathrm{nodePairsOfPlaces}(g,W) = \{(w, g\cdot w) : w \in W\}$, of the same cardinality as $W$ and in explicit bijection `nodeEquivOfPlaces` with $W$ via the first projection. A member $s$ of this set satisfies $s_1 \in W$ and $s_2 = g \cdot s_1$. A function $e$ on places transports to $\mathrm{widthOfPlaces}(g,W,e)(s) := e(s_1)$ on the pairs.
--
--   Second, for $N \geq 1$, a natural number $q$ and a field $K$, a place $w$ of the level-$N$ modular function field `modularFunctionFieldC K N` is declared supersingular, $\mathrm{IsSupersingularPlace}\,q\,N\,K\,w$, when three conditions hold: $w$ satisfies `Place.IsRational`; $w$ is an affine geometric place, i.e. both generators `jGeomGen K N` and `jNGeomGen K N` lie in the valuation subring of $w$; and the value $w.\mathrm{evalAt}$ of the first generator lies in $\mathrm{ssJSet}\,q\,K$, the set of those $j \in K$ such that every elliptic Weierstrass curve over $K$ with invariant $j$ has no nonzero affine point killed by $q$. The set of such places is `ssPlaces`. Finally, a supersingular place is centred, in the sense of $\mathrm{IsCentreOf}$ (positive order of each generator minus the corresponding coordinate), at the pair of evaluations $(w.\mathrm{evalAt}(j), w.\mathrm{evalAt}(j_N))$.
--
--   **Relation to Mathlib.** Mathlib has no notion of place of a function field over a base field, of semilinear automorphism of such an extension, of modular function field, or of supersingular $j$-invariant; `Place`, `SemilinearAut`, `modularFunctionFieldC` and `ssJSet` are the project's own. The Mathlib ingredients used are `WeierstrassCurve` with its $j$-invariant and affine point group, valuation subrings, and finite sets with their maps.
--
--   **Where it is used.** The pairs $(w, g \cdot w)$ model the crossing points of the two copies of the level-$N$ modular curve in the special fibre at $q$ of $X_0(Nq)$, with $g$ the $q$-Frobenius and $W$ the set of supersingular places; the width function records the thickness data attached to each such node. These combinatorics feed the special-fibre computations used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_SupersingularNodePlaces.lean

import Definitions.Def_ModularCurve_CharLSpecialFibreLevelNDictionary
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_AlgebraicCurve_BaseChangeGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Pairs

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

def smulNodePair (g : SemilinearAut K F) (w : Place K F) : Place K F × Place K F :=
  (w, g • w)

@[simp] theorem smulNodePair_fst (g : SemilinearAut K F) (w : Place K F) :
    (smulNodePair g w).1 = w := rfl

@[simp] theorem smulNodePair_snd (g : SemilinearAut K F) (w : Place K F) :
    (smulNodePair g w).2 = g • w := rfl

theorem smulNodePair_injective (g : SemilinearAut K F) :
    Function.Injective (smulNodePair g) :=
  fun _ _ h => congrArg Prod.fst h

def smulNodePairEmb (g : SemilinearAut K F) : Place K F ↪ Place K F × Place K F :=
  ⟨smulNodePair g, smulNodePair_injective g⟩

@[simp] theorem smulNodePairEmb_apply (g : SemilinearAut K F) (w : Place K F) :
    smulNodePairEmb g w = smulNodePair g w := rfl

def nodePairsOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) :
    Finset (Place K F × Place K F) :=
  W.map (smulNodePairEmb g)

theorem mem_nodePairsOfPlaces_iff (g : SemilinearAut K F) (W : Finset (Place K F))
    (s : Place K F × Place K F) :
    s ∈ nodePairsOfPlaces g W ↔ ∃ w ∈ W, smulNodePair g w = s := by
  simp only [nodePairsOfPlaces, Finset.mem_map, smulNodePairEmb_apply]

theorem smulNodePair_mem_nodePairsOfPlaces (g : SemilinearAut K F)
    {W : Finset (Place K F)} {w : Place K F} (hw : w ∈ W) :
    smulNodePair g w ∈ nodePairsOfPlaces g W :=
  Finset.mem_map_of_mem (smulNodePairEmb g) hw

@[simp] theorem card_nodePairsOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) :
    (nodePairsOfPlaces g W).card = W.card :=
  Finset.card_map _

theorem fst_mem_of_mem_nodePairsOfPlaces {g : SemilinearAut K F} {W : Finset (Place K F)}
    {s : Place K F × Place K F} (hs : s ∈ nodePairsOfPlaces g W) : s.1 ∈ W := by
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff g W s).mp hs
  exact hw

theorem snd_eq_of_mem_nodePairsOfPlaces {g : SemilinearAut K F} {W : Finset (Place K F)}
    {s : Place K F × Place K F} (hs : s ∈ nodePairsOfPlaces g W) : s.2 = g • s.1 := by
  obtain ⟨w, hw, rfl⟩ := (mem_nodePairsOfPlaces_iff g W s).mp hs
  rfl

def nodeEquivOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) :
    ↥W ≃ ↥(nodePairsOfPlaces g W) where
  toFun w := ⟨smulNodePair g w, smulNodePair_mem_nodePairsOfPlaces g w.2⟩
  invFun s := ⟨(s : Place K F × Place K F).1, fst_mem_of_mem_nodePairsOfPlaces s.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv s := Subtype.ext
    (Prod.ext rfl (snd_eq_of_mem_nodePairsOfPlaces s.2).symm)

@[simp] theorem coe_nodeEquivOfPlaces_apply (g : SemilinearAut K F) (W : Finset (Place K F))
    (w : ↥W) :
    ((nodeEquivOfPlaces g W w : ↥(nodePairsOfPlaces g W)) : Place K F × Place K F)
      = smulNodePair g (w : Place K F) := rfl

@[simp] theorem coe_nodeEquivOfPlaces_symm_apply (g : SemilinearAut K F)
    (W : Finset (Place K F)) (s : ↥(nodePairsOfPlaces g W)) :
    (((nodeEquivOfPlaces g W).symm s : ↥W) : Place K F)
      = (s : Place K F × Place K F).1 := rfl

def widthOfPlaces (g : SemilinearAut K F) (W : Finset (Place K F)) (e : Place K F → ℕ) :
    ↥(nodePairsOfPlaces g W) → ℕ :=
  fun s => e (s : Place K F × Place K F).1

theorem widthOfPlaces_apply (g : SemilinearAut K F) (W : Finset (Place K F))
    (e : Place K F → ℕ) (s : ↥(nodePairsOfPlaces g W)) :
    widthOfPlaces g W e s = e (s : Place K F × Place K F).1 := rfl

@[simp] theorem widthOfPlaces_mk (g : SemilinearAut K F) {W : Finset (Place K F)}
    (e : Place K F → ℕ) {w : Place K F} (hw : w ∈ W) :
    widthOfPlaces g W e ⟨smulNodePair g w, smulNodePair_mem_nodePairsOfPlaces g hw⟩ = e w :=
  rfl

theorem widthOfPlaces_nodeEquiv (g : SemilinearAut K F) (W : Finset (Place K F))
    (e : Place K F → ℕ) (w : ↥W) :
    widthOfPlaces g W e (nodeEquivOfPlaces g W w) = e (w : Place K F) := rfl

end Pairs

section Supersingular

variable (q N : ℕ) [NeZero N] (K : Type*) [Field K] [DecidableEq K]

def IsSupersingularPlace (w : Place K (modularFunctionFieldC K N)) : Prop :=
  w.IsRational ∧ IsAffineGeomPlace K N w ∧ w.evalAt (jGeomGen K N) ∈ ssJSet q K

theorem isSupersingularPlace_iff (w : Place K (modularFunctionFieldC K N)) :
    IsSupersingularPlace q N K w ↔
      w.IsRational ∧ IsAffineGeomPlace K N w ∧ w.evalAt (jGeomGen K N) ∈ ssJSet q K :=
  Iff.rfl

def ssPlaces : Set (Place K (modularFunctionFieldC K N)) :=
  {w | IsSupersingularPlace q N K w}

theorem mem_ssPlaces_iff {w : Place K (modularFunctionFieldC K N)} :
    w ∈ ssPlaces q N K ↔ IsSupersingularPlace q N K w :=
  Iff.rfl

variable {q N K}

theorem IsSupersingularPlace.isCentreOf_evalAt {w : Place K (modularFunctionFieldC K N)}
    (h : IsSupersingularPlace q N K w) :
    IsCentreOf K N (w.evalAt (jGeomGen K N), w.evalAt (jNGeomGen K N)) w :=
  exists_isCentreOf_of_isRational h.1 h.2.1

end Supersingular

end ModularCurve

end


