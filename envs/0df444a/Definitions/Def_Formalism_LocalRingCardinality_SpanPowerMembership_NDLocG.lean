-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG
-- name    : Formalism_LocalRingCardinality_SpanPowerMembership_NDLocG
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:36.317537+00:00
-- url     : https://prove2.me/theorems/3e6e3565-8f4a-5e1a-a663-722307b9b75f
-- title:
--   NDLoc G
-- statement:
--   Definitions and structural lemmas for NDLoc G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/SpanPowerMembership/NDLocG.lean

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_NDLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions.Examples₂.LB
open NumberField IsDedekindDomain Polynomial IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
variable {l : ℕ} [hl : Fact l.Prime]
section Emb
variable {F : Type} [Field F] [NumberField F]
def Kphi (φ : F →+* PadicAlgCl l) : IntermediateField ℚ_[l] (PadicAlgCl l) :=
  IntermediateField.adjoin ℚ_[l] (Set.range fun i => φ (Module.finBasis ℚ F i))
instance Kphi_fin (φ : F →+* PadicAlgCl l) : FiniteDimensional ℚ_[l] (Kphi φ) :=
  IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
variable (F l) in

def KE : IntermediateField ℚ_[l] (PadicAlgCl l) := ⨆ φ : F →+* PadicAlgCl l, Kphi φ
instance KE_fin : FiniteDimensional ℚ_[l] (KE l F) :=
  IntermediateField.finiteDimensional_iSup_of_finite
end Emb
def powHom {G : Type} [CommGroup G] (ζ : G) (N : ℕ) [NeZero N] (h : ζ ^ N = 1) :
    Multiplicative (ZMod N) →* G where
  toFun a := ζ ^ (Multiplicative.toAdd a).val
  map_one' := by simp
  map_mul' a b := by
    rw [toAdd_mul, ← pow_add, ZMod.val_add]
    conv_rhs => rw [← Nat.div_add_mod ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) N,
      pow_add, pow_mul, h, one_pow, one_mul]
section Mu
variable (LL : FinExt l) {N : ℕ} [NeZero N] {ζ : PadicAlgCl l} (hζ : IsPrimitiveRoot ζ N) (hm : ζ ∈ LL.1)
include hζ in
theorem norm_prim : ‖ζ‖ = 1 := by
  first
  | exact hζ.norm'_eq_one (NeZero.ne N)
  | (have h := congrArg norm hζ.pow_eq_one
     rw [norm_pow, norm_one] at h
     exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (NeZero.ne N)).mp h)
def zO : ↥(OL LL) := ⟨⟨ζ, hm⟩, (mem_OL LL _).mpr (norm_prim hζ).le⟩
theorem zO_pow : zO LL hζ hm ^ N = 1 := by
  first
  | (apply Subtype.ext; apply Subtype.ext; simp [zO, hζ.pow_eq_one])
  | (ext; simp [zO, hζ.pow_eq_one])
def zU : (↥(OL LL))ˣ := Units.ofPowEqOne (zO LL hζ hm) N (zO_pow LL hζ hm) (NeZero.ne N)
theorem zU_pow : zU LL hζ hm ^ N = 1 := by
  first
  | exact Units.ext (by simp [zU, zO_pow LL hζ hm])
  | (ext; simp [zU, zO_pow LL hζ hm])
def muHom : Multiplicative (ZMod N) →* (↥(OL LL))ˣ := powHom (zU LL hζ hm) N (zU_pow LL hζ hm)
end Mu
end Formalism.BasicNotions.Examples₂.LB


