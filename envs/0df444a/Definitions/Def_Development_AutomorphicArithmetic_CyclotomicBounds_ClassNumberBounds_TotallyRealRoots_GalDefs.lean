-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
-- name    : Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:13.857805+00:00
-- url     : https://prove2.me/theorems/c5e4833f-4277-4934-aae5-fb453ca36574
-- title:
--   Gal Defs
-- statement:
--   Definitions and structural lemmas for Gal Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CyclotomicBounds/ClassNumberBounds/TotallyRealRoots/GalDefs.lean

import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_LeNuIffPowMemPrinc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace KStar.TotallyRealRoots
noncomputable def eps (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] :
    Gal(AlgebraicClosure E/E) →* ℤ_[l]ˣ :=
  (cyclotomicCharacter (AlgebraicClosure E) l).comp
    (MulSemiringAction.toRingAut Gal(AlgebraicClosure E/E) (AlgebraicClosure E))
noncomputable def galImage (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] : Subgroup ℤ_[l]ˣ :=
  (eps l E).range
noncomputable def nuGal (l : ℕ) [Fact l.Prime] (E : Type*) [Field E] (tr : ℕ) : ℕ∞ :=
  ⨅ g : Gal(AlgebraicClosure E/E),
    emultiplicity (l : ℤ_[l]) (((eps l E g : ℤ_[l]ˣ) : ℤ_[l]) ^ tr - 1)
noncomputable def adjoinRoots (E : Type*) [Field E] (m : ℕ) :
    IntermediateField E (AlgebraicClosure E) :=
  IntermediateField.adjoin E {ζ : AlgebraicClosure E | ζ ^ m = 1}
noncomputable def fieldSubgroup (N : ℕ) [NeZero N] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {N} ℚ K] (E : IntermediateField ℚ K) : Subgroup (ZMod N)ˣ :=
  E.fixingSubgroup.map (IsCyclotomicExtension.Rat.galEquivZMod N K).toMonoidHom
noncomputable def nuLevel (N : ℕ) (H : Subgroup (ZMod N)ˣ) (tr l : ℕ) : ℕ :=
  if h : l.Prime then (@nu l ⟨h⟩ (@levelGroup l ⟨h⟩ N H) tr).toNat else 0
noncomputable def nuField (E : Type*) [Field E] (tr l : ℕ) : ℕ :=
  if h : l.Prime then (@nuGal l ⟨h⟩ E _ tr).toNat else 0
end KStar.TotallyRealRoots


