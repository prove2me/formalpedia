-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Corners
-- name    : OAI_Combinatorics_TwoWayAutomata_Corners
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:16:08.152218+00:00
-- url     : https://prove2.me/theorems/fbdb5c15-ad70-4d80-b2e0-ce7a20a5b7c5
-- title:
--   Corner monoids at idempotents of a semigroup, restricted homomorphisms and corners of corners
-- statement:
--   Let $A$ and $M$ be semigroups; no identity element is assumed. For an idempotent $e\in A$, $e^2=e$, the corner of $A$ at $e$ is
--   $$eAe=\{exe:\ x\in A\}=\{x\in A:\ ex=x=xe\}.$$
--
--   1. **Corner monoid.** $eAe$ is a monoid under the multiplication of $A$, with identity element $e$. If $A$ is finite, so is $eAe$.
--   2. **Restricted homomorphisms.** Let $\theta:A\to M$ be multiplicative, $\theta(xy)=\theta(x)\theta(y)$, and let $d\in A$ and $q\in M$ be idempotents with $\theta(d)=q$. Then $\theta$ maps $dAd$ into $qMq$, and $x\mapsto\theta(x)$ is a monoid homomorphism $dAd\to qMq$; in particular it sends the identity $d$ of $dAd$ to the identity $q$ of $qMq$.
--   3. **Corners of corners.** Let $p\in M$ be idempotent and let $q$ be an idempotent of the monoid $pMp$. Then the corner of $pMp$ at $q$ and the corner of $M$ at $q$ have the same elements, and the identity map on elements is a monoid isomorphism $q\,(pMp)\,q\cong qMq$.
--
--   The lower-bound argument repeatedly passes from a finite monoid to its corner at a suitable idempotent, where that idempotent becomes the identity element. Restricted homomorphisms carry a map into a relation monoid along to such corners, and item 3 allows passing to a smaller corner inside a corner without changing the ambient monoid.
--
--   **Formalization Note** The corner is Mathlib's `IsIdempotentElem.Corner`, the subsemigroup `Subsemigroup.corner e` of elements of the form $exe$, whose membership criterion for idempotent $e$ is `Subsemigroup.mem_corner_iff`. Item 1 is the instance `cornerMonoid` together with `finite_corner`; item 2 is `cornerMap θ hd hq hθd` for a `MulHom` `θ : A →ₙ* M`; item 3 is the `MulEquiv` `cornerFlatten hp q hq`, where `hq` is idempotence of `q` inside the corner of `p`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Corners.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes

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


