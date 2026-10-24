-- Prove2me | Definitions.Def_PricingWithTips3DM_9b371543de0be5a588dc23d1
-- name    : PricingWithTips3DM_9b371543de0be5a588dc23d1
-- status  : Definition
-- author  : @qmaai2907271020
-- created : 2026-10-22T20:19:59.034412+00:00
-- url     : https://prove2.me/theorems/20c5638c-534b-4292-8c2f-fa2927e75efd
-- title:
--   PricingWithTips 3DM dependency: HardnessReductions.Sets.Matching3D.Encoding
-- statement:
--   A private, kernel-checked dependency module used by the formal NP-hardness proof for three-dimensional matching and Theorems 4.1 and 4.2 of arXiv:2507.10872.
-- source:
--   https://github.com/DominikPeters/HardnessReductionsLean

import Definitions.Def_PricingWithTips3DM_2b9b1ca3b5e0361c4e5bb9c7
import Definitions.Def_PricingWithTips3DM_259835d7bdacc7647a6f2f2b
set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Concrete encoding of 3-dimensional matching instances

A concrete 3DM instance is `(ws, (xs, (ys, ts)))`: three explicit element
lists and a list of triples of element *indices*.

## Decoding discipline

Decoding must be **total**:

* the elements of each coordinate are the *positions* of its list
  (`Fin ws.length` and so on); the entries are ignored labels, exactly as
  vertices are the positions of a graph's vertex list. Elements lying in no
  triple are thereby representable, which the size model demands and the
  problem needs: an unmatchable element is what makes a no-instance;
* a triple is a triple of indices. One with an out-of-range index names no
  triple of the decoded instance and simply contributes nothing — the
  intersection with `univ` drops it, so no well-formedness predicate is
  needed;
* duplicate triples collapse, as they must: the decoded triples are a
  `Finset`, matching Garey–Johnson's `M ⊆ W × X × Y`.

## Index arithmetic

The element types of a gadget are products and sums of index ranges
(`Ext`, `Slot` in `Matching3D/FromSat.lean`), while a concrete instance can
only name elements by positions. The passage is a mixed-radix numbering — an
instance of the block layer of `Cert/Numbering.lean`.
-/

namespace Hardness
namespace Cert

/-- The concrete triple type: a triple of element indices. -/
abbrev TripleTy : Ty := .pair .nat (.pair .nat .nat)

/-- Concrete 3DM instances: `(ws, (xs, (ys, ts)))` — three element lists whose
*positions* are the elements of the three coordinates, and a list of index
triples. -/
abbrev Matching3DTy : Ty :=
  .pair (.list .nat) (.pair (.list .nat) (.pair (.list .nat) (.list TripleTy)))

/-- Decode a concrete 3DM instance. Each coordinate's element set is the
positions of its list; the available triples are the index triples that occur
in the triple list (out-of-range ones name nothing and are dropped). Total. -/
def decodeMatching3D (x : Matching3DTy.denote) : Matching3DInstance where
  W := Fin x.1.length
  X := Fin x.2.1.length
  Y := Fin x.2.2.1.length
  triples := Finset.univ.filter fun t ↦ ((t.1 : ℕ), (t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ x.2.2.2

/-- Membership in the decoded triple set: a triple of positions is available
exactly when its index triple occurs in the concrete triple list. -/
theorem mem_decodeMatching3D_triples (x : Matching3DTy.denote)
    (t : Fin x.1.length × Fin x.2.1.length × Fin x.2.2.1.length) :
    t ∈ (decodeMatching3D x).triples ↔
      ((t.1 : ℕ), (t.2.1 : ℕ), (t.2.2 : ℕ)) ∈ x.2.2.2 :=
  -- term mode: the decoded field's `DecidablePred` instance is not reachable
  -- by `simp`, which skips instance arguments
  Finset.mem_filter_univ t

namespace Concrete

/-- 3-DIMENSIONAL MATCHING on concrete instances. -/
def MATCHING_3D : Problem Matching3DTy.denote :=
  Hardness.MATCHING_3D.comap decodeMatching3D

end Concrete

end Cert
end Hardness


