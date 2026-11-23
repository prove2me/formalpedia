-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_GaloisLibrary_GaloisCohomologyLength_LevelInertiaLeLevelDec
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:37:01.816069+00:00
-- url     : https://prove2.me/theorems/2a3d612b-3d80-48e4-9426-04526c371c42
-- title:
--   Level Inertia Le Level Dec
-- statement:
--   Definitions and structural lemmas for Level Inertia Le Level Dec, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/GaloisLibrary/GaloisCohomologyLength/LevelInertiaLeLevelDec.lean

import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Development_AutomorphicArithmetic_CyclotomicBounds_ClassNumberBounds_TotallyRealRoots_GalDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology
namespace UpperTheory.V.LDataCardLeFinrank
section
variable (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime]
def decImage (A : ValuationSubring Ω) : Subgroup ℤ_[l]ˣ := (Dec (F := F) A).map (cycZ F Ω l)
def ineImage (A : ValuationSubring Ω) : Subgroup ℤ_[l]ˣ := (Ine (F := F) A).map (cycZ F Ω l)
variable (Ω) in

def qzG (e : ℤ) : Representation ℤ_[l] (G F Ω) (QZ l) := scalRep (QZ l) (cycZ F Ω l ^ (-e))
variable {F l}
end
section
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
  {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousConstSMul R M]
def ShaAbs (ρ : Representation R (G F Ω) M) (S : Set (HeightOneSpectrum (𝓞 F))) : Submodule R (H1 ρ) :=
  (⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∈ S) (A : ValuationSubring Ω) (_ : IsPlaceOver A v),
      LinearMap.ker (resH1 ρ (Dec (F := F) A).subtype continuous_subtype_val)) ⊓
    ⨅ (v : HeightOneSpectrum (𝓞 F)) (_ : v ∉ S) (A : ValuationSubring Ω) (_ : IsPlaceOver A v),
      LinearMap.ker (resH1 ρ (Ine (F := F) A).subtype continuous_subtype_val)
end
def shaInv (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (e : ℤ) : ℕ∞ :=
  Module.length ℤ_[l] (ShaAbs (qzG F (AlgebraicClosure F) l e) (Above F l))
def levelDec (l N : ℕ) : Subgroup (ZMod N)ˣ :=
  (Subgroup.closure {u : (ZMod (ordCompl[l] N))ˣ | (u : ZMod (ordCompl[l] N)) = (l : ZMod (ordCompl[l] N))}).comap
    (ZMod.unitsMap (Nat.ordCompl_dvd N l))
def nuBound (l N e : ℕ) : ℕ :=
  if l ∣ N ∨ l - 1 ∣ e then max (N.factorization l) (if l = 2 then 2 else 1) + e.factorization l else 0
end UpperTheory.V.LDataCardLeFinrank
end


