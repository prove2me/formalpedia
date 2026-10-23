-- Prove2me | Definitions.Def_RSF_geo
-- name    : RSF_geo
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-23T02:19:04.641545+00:00
-- url     : https://prove2.me/theorems/c5920c44-38b1-464b-b241-1242e1cf42ba
-- title:
--   The rigid cohomology worlds: the Poincare duality data and the comparison data
-- statement:
--   The cohomological interface of the Poincare duality statements: the rigid cohomology world - an abstract base field and variety carrying the geometric conditions (non-archimedean, algebraically closed, mixed characteristic (0, p), proper, smooth, pure dimension) as labels, the etale cohomology groups with coefficients in the prime field, the Tate object F_l(-d), and the bundled addition, zero, and scalar multiplication operations; the bundled ZMod-linear maps between bundled spaces; and the comparison world of the primitive comparison theorem - the two cohomology theories of a proper smooth rigid-analytic variety as two abstract families of groups with bundled operations. Constructing the interface data for the actual rigid-analytic geometry is part of the proposed work of the mission.
-- source:
--   L. Mann, A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry, arXiv:2206.02022 (2022), introduction (Theorem 1.1.1, Corollary 1.2.9, and the primitive comparison theorem cited as [34, Theorem 5.1]).

import Mathlib
import Definitions.Def_RSF_cat

/-!
# The geometric layer: the rigid cohomology worlds

The geometric layer of the RSF mission, carrying the propositional content
of the Poincare duality statements of the introduction of Lucas Mann,
"A p-Adic 6-Functor Formalism in Rigid-Analytic Geometry"
(arXiv:2206.02022): the bundled ZMod-linear maps between bundled spaces;
the rigid cohomology world - the abstract base field and variety carrying
the geometric conditions as labels, the etale cohomology groups with
coefficients in F_ell, the Tate object F_ell(-d), and the bundled
operations; and the comparison world of the primitive comparison theorem,
with the two cohomology theories of a proper smooth rigid-analytic variety
as two abstract families of groups.

As in the categorical layer, the rigid-analytic geometry of the thesis
exceeds the objects available in Mathlib; the world carries the operations
as bundled data and the theorem drafts quantify over it. Constructing the
interface data for the actual geometry of the thesis is part of the
proposed work of the mission.
-/

namespace RSF

/-- A bundled ZMod-ell-linear map between two bundled spaces: a function
compatible with the bundled addition, zero, and scalar multiplication. -/
structure ZModLinear (ℓ : ℕ) (V W : Type)
    (addV : V → V → V) (zeroV : V) (smulV : ZMod ℓ → V → V)
    (addW : W → W → W) (zeroW : W) (smulW : ZMod ℓ → W → W) where
  map : V → W
  map_add : ∀ x y : V, map (addV x y) = addW (map x) (map y)
  map_zero : map zeroV = zeroW
  map_smul : ∀ (k : ZMod ℓ) (x : V), map (smulV k x) = smulW k (map x)

/-- The rigid cohomology world: the propositional content of the Poincare
duality statements of the thesis. The abstract base field `K` and variety
`X` carry the geometric conditions as labels - `K` is a non-archimedean
field, algebraically closed, of mixed characteristic `(0, P)`; `X` is
proper and smooth of pure dimension `d` over `K`. The etale cohomology
groups `H i` with coefficients in `F_ell`, the Tate object `Tate = F_ell(-d)`,
and the bundled operations are the data of the duality statement. -/
structure RigidCohWorld where
  ℓ : ℕ
  hℓ : Nat.Prime ℓ
  P : ℕ
  hP : Nat.Prime P
  K : Type
  X : Type
  nonarchField : Prop
  algClosed : Prop
  mixedChar : Prop
  properSmooth : Prop
  pureDim : Prop
  d : ℕ
  H : ℤ → Type
  add : ∀ i : ℤ, H i → H i → H i
  zero : ∀ i : ℤ, H i
  smul : ∀ i : ℤ, ZMod ℓ → H i → H i
  Tate : Type
  tadd : Tate → Tate → Tate
  tzero : Tate
  tsmul : ZMod ℓ → Tate → Tate

/-- The comparison world of the primitive comparison theorem: the two
cohomology theories of a proper smooth rigid-analytic variety - the etale
cohomology of the sheaves `O^+/pi`, and the etale cohomology with
coefficients in `F_P` - as two abstract families of groups with bundled
addition and zero. -/
structure ComparisonWorld where
  P : ℕ
  hP : Nat.Prime P
  X : Type
  properSmooth : Prop
  A : ℤ → Type
  aadd : ∀ i : ℤ, A i → A i → A i
  azero : ∀ i : ℤ, A i
  B : ℤ → Type
  badd : ∀ i : ℤ, B i → B i → B i
  bzero : ∀ i : ℤ, B i

end RSF


