-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Corners__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:39:05.390525+00:00
-- url     : https://prove2.me/theorems/5d12ac45-5bc3-4562-b020-3b4bc57970f2
-- title:
--   Corner monoids at idempotents of a semigroup, restricted homomorphisms, and corners of corners
-- statement:
--   Let $A$ be a semigroup. An element $e\in A$ is idempotent if $e^2=e$. The corner of an idempotent $e$ is
--   $$eAe=\{x\in A:\ ex=x\ \text{and}\ xe=x\},$$
--   which coincides with $\{ere:\ r\in A\}$ and is closed under multiplication.
--
--   1. **Corner monoid.** For an idempotent $e$, the corner $eAe$ with the multiplication of $A$ is a monoid whose identity element is $e$.
--   2. **Finiteness.** If $A$ is finite, then every corner $eAe$ is finite.
--   3. **Restricted homomorphisms.** Let $\theta:A\to M$ be a semigroup homomorphism, $\theta(xy)=\theta(x)\theta(y)$, and let $d\in A$ and $q\in M$ be idempotents with $\theta(d)=q$. Then $\theta$ maps $dAd$ into $qMq$, and the restriction $dAd\to qMq$ is a monoid homomorphism (it sends the identity $d$ to the identity $q$).
--   4. **Corners of corners.** Let $p\in M$ be idempotent and let $q$ be an idempotent element of the corner monoid $pMp$. The corner of $q$ taken inside $pMp$ has the same elements as the corner of $q$ taken in $M$, and the identity map on elements is a multiplicative bijection $q\,(pMp)\,q\cong qMq$.
--
--   Corners are the local monoids of semigroup theory. They make it possible to work inside the finite monoid of boundary diagrams of a two-way automaton while keeping a unit element: an idempotent becomes the identity of its corner, semigroup homomorphisms that match two idempotents restrict to unital homomorphisms between their corners, and nested corners can be flattened.
--
--   **Formalization Note** The corner is Mathlib's `Subsemigroup.corner e` (defined as the range of $r\mapsto ere$), viewed as the type `he.Corner` for `he : IsIdempotentElem e`; membership is characterized by `Subsemigroup.mem_corner_iff`. The monoid structure is the instance `cornerMonoid`, finiteness is `finite_corner`, the restricted homomorphism is `cornerMap θ hd hq hθd` for a non-unital multiplicative map `θ : A →ₙ* M`, and the flattening is the multiplicative equivalence `cornerFlatten hp q hq`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

/-- Mathlib's semigroup corner, equipped with its idempotent as identity. -/
instance cornerMonoid {A : Type*} [Semigroup A] {e : A} (he : IsIdempotentElem e) :
    Monoid he.Corner where
  __ : Semigroup he.Corner := inferInstanceAs (Semigroup (Subsemigroup.corner e))
  one := ⟨e, (Subsemigroup.mem_corner_iff he).mpr ⟨he, he⟩⟩
  one_mul x := Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.property).1
  mul_one x := Subtype.ext ((Subsemigroup.mem_corner_iff he).mp x.property).2

@[instance]
theorem finite_corner {A : Type*} [Semigroup A] [Finite A] {e : A}
    (he : IsIdempotentElem e) : Finite he.Corner :=
  inferInstanceAs (Finite (Subsemigroup.corner e))

/-- A multiplicative map restricts to a unital map between matching idempotent corners. -/
def cornerMap {A M : Type*} [Semigroup A] [Semigroup M] (θ : A →ₙ* M)
    {d : A} {q : M} (hd : IsIdempotentElem d) (hq : IsIdempotentElem q) (hθd : θ d = q) :
    hd.Corner →* hq.Corner where
  toFun x := ⟨θ x.val, (Subsemigroup.mem_corner_iff hq).mpr (by
    obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hd).mp x.property
    exact ⟨by rw [← hθd, ← map_mul, hl], by rw [← hθd, ← map_mul, hr]⟩)⟩
  map_one' := Subtype.ext hθd
  map_mul' x y := Subtype.ext (map_mul θ x.val y.val)

/-- Taking a corner inside an absorbing corner gives the same smaller corner. -/
def cornerFlatten {M : Type*} [Semigroup M] {p : M} (hp : IsIdempotentElem p)
    (q : hp.Corner) (hq : IsIdempotentElem q) :
    hq.Corner ≃* (show IsIdempotentElem q.val from congrArg Subtype.val hq.eq).Corner := by
  let hQ : IsIdempotentElem q.val := congrArg Subtype.val hq.eq
  have hqprop := (Subsemigroup.mem_corner_iff hp).mp q.property
  refine
    { toFun := fun x => ⟨x.val.val, (Subsemigroup.mem_corner_iff hQ).mpr ?_⟩
      invFun := fun y => ⟨⟨y.val, (Subsemigroup.mem_corner_iff hp).mpr ?_⟩,
        (Subsemigroup.mem_corner_iff hq).mpr ?_⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  · obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hq).mp x.property
    exact ⟨congrArg Subtype.val hl, congrArg Subtype.val hr⟩
  · obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp y.property
    constructor
    · calc
        p * y.val = p * (q.val * y.val) := by rw [hl]
        _ = y.val := by rw [← mul_assoc, hqprop.1, hl]
    · calc
        y.val * p = (y.val * q.val) * p := by rw [hr]
        _ = y.val := by rw [mul_assoc, hqprop.2, hr]
  · obtain ⟨hl, hr⟩ := (Subsemigroup.mem_corner_iff hQ).mp y.property
    exact ⟨Subtype.ext hl, Subtype.ext hr⟩

end TwoWayComplementation

end OAI


