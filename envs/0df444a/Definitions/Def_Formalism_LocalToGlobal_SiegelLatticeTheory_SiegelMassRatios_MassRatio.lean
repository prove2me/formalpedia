-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_MassRatio
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:08:36.724818+00:00
-- url     : https://prove2.me/theorems/a4458158-e53c-4d1a-9ccc-a699bc0a05fe
-- title:
--   Mass Ratio
-- statement:
--   Definitions and structural lemmas for Mass Ratio, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/SiegelMassRatios/MassRatio.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
noncomputable section
namespace Formalism.L2.SG.MassRatio
section Defs
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
def IsCMPair : Prop :=
  Formalism.HermitianLatticesTheory.IsCMUnram E ∧ Set.range (algebraMap F E) = {a : E | star a = a}
def dF : ℝ := |((discr F : ℤ) : ℝ)|
def fF : ℕ := Module.finrank ℚ F
def vF : ℝ := dF F ^ ((1 : ℝ) / (fF F : ℝ)) / 2
def etaF (v : Ideal (𝓞 F)) : ℝ :=
  by classical exact
    if ∃! P : Ideal (𝓞 E), P.IsMaximal ∧ Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) P = v then -1 else 1
def eulerF (M : ℕ) (v : Ideal (𝓞 F)) : ℝ :=
  (1 - etaF F E v ^ M * ((Ideal.absNorm v : ℕ) : ℝ) ^ (-(M : ℤ)))⁻¹
def lText (M : ℕ) : ℝ :=
  ∏' v : {v : Ideal (𝓞 F) // v.IsMaximal}, eulerF F E M v.1
def rText (M : ℕ) : ℝ :=
  (((Nat.factorial (M - 1) : ℕ) : ℝ) * (vF F / Real.pi) ^ M) ^ fF F * dF F ^ (-(1 : ℝ) / 2) *
    lText F E M
end Defs
def MassRatio : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E →
    ∀ (M : ℕ), 3 ≤ M →
    ∀ (V V' : Type) [AddCommGroup V] [Module E V] [Module (RingOfIntegers E) V]
      [IsScalarTower (RingOfIntegers E) E V] [AddCommGroup V'] [Module E V']
      [Module (RingOfIntegers E) V'] [IsScalarTower (RingOfIntegers E) E V']
      (h : V →ₗ⋆[E] V →ₗ[E] E) (h' : V' →ₗ⋆[E] V' →ₗ[E] E)
      (L : Submodule (RingOfIntegers E) V) (L' : Submodule (RingOfIntegers E) V'),
      h.IsSymm → h'.IsSymm → Formalism.HermitianLatticesTheory.IsOrthoLattice h L M → Formalism.HermitianLatticesTheory.IsOrthoLattice h' L' (M - 1) →
      Formalism.HermitianLatticesTheory.mass h L / Formalism.HermitianLatticesTheory.mass h' L' = rText F E M
def DegEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → fF F = Formalism.HermitianLatticesTheory.fDeg E
def DiscSq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → |((discr E : ℤ) : ℝ)| = dF F ^ 2
def EulerEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∀ M : ℕ, 3 ≤ M → lText F E M = Formalism.HermitianLatticesTheory.lValEta E M
def FormsEq : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    IsCMPair F E → ∀ M : ℕ, 3 ≤ M → rText F E M = Formalism.HermitianLatticesTheory.massRatioRightSide E M
def fixSub (K : Type) [Field K] [StarRing K] : Subfield K where
  carrier := {a | star a = a}
  mul_mem' {a b} ha hb := by
    change star a = a at ha
    change star b = b at hb
    change star (a * b) = a * b
    rw [star_mul', ha, hb]
  one_mem' := star_one K
  add_mem' {a b} ha hb := by
    change star a = a at ha
    change star b = b at hb
    change star (a + b) = a + b
    rw [star_add, ha, hb]
  zero_mem' := star_zero K
  neg_mem' {a} ha := by
    change star a = a at ha
    change star (-a) = -a
    rw [star_neg, ha]
  inv_mem' a ha := by
    change star a = a at ha
    change star a⁻¹ = a⁻¹
    rw [star_inv₀, ha]
def fixFld (K : Type) [Field K] [NumberField K] [StarRing K] : IntermediateField ℚ K :=
  (fixSub K).toIntermediateField (fun q => by
    change star (algebraMap ℚ K q) = algebraMap ℚ K q
    rw [eq_ratCast, star_ratCast])
end Formalism.L2.SG.MassRatio


