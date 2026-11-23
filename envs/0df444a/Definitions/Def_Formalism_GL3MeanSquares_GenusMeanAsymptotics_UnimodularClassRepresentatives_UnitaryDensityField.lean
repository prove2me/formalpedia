-- Prove2me | Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
-- name    : Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_UnitaryDensityField
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:55:56.038472+00:00
-- url     : https://prove2.me/theorems/6d177a44-5b05-493f-a0f1-5c457b7f1c29
-- title:
--   Unitary Density Field
-- statement:
--   Definitions and structural lemmas for Unitary Density Field, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/UnitaryDensityField.lean

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtPPowLeSpanSup
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardLiftMatrix
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemRangeLinPart
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_idealPowerSpanBounds_conjO_mem_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
namespace Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds
open NormLifting
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
local notation "ι" => algebraMap (𝓞 F) (𝓞 K)
abbrev AQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Type :=
  𝓞 K ⧸ extP K 𝔭 ^ k
def sg (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : AQ K 𝔭 k →+* AQ K 𝔭 k :=
  conjQ (extP K 𝔭 ^ k) (idealPowerSpanBounds.conjO_mem_pow hF 𝔭 k)
def InQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : AQ K 𝔭 k) : Prop :=
  ∃ z ∈ extP K 𝔭, Ideal.Quotient.mk (extP K 𝔭 ^ k) z = a
def cnt (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}
def cntP (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (¬ ∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}
def cntI (hF : IsFixF K F) (𝔭 : Ideal (𝓞 F)) (k M : ℕ) (n : 𝓞 K) : ℕ :=
  Nat.card {x : Fin M → AQ K 𝔭 k // (∀ i, InQ 𝔭 k (x i)) ∧
    ∑ i, sg hF 𝔭 k (x i) * x i = Ideal.Quotient.mk _ n}
end Formalism.HermitianLattices.Ext.L3.unitaryAbsoluteValueBounds


