-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:09.882446+00:00
-- url     : https://prove2.me/theorems/0438b085-3c73-4371-b139-5b6d02049421
-- title:
--   Levelaf
-- statement:
--   Definitions and structural lemmas for Levelaf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Levelaf.lean

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
section Adele
variable {F : Type} [Field F] [NumberField F]
end Adele
section AdeleRes
variable {F : Type} [Field F] [NumberField F]
end AdeleRes
section Tensor
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
variable (E) in

def levelafC (d : 𝓞 F) : E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (1 : E) ⊗ₜ[F] algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) d
def levelafQ {m : ℕ} (b : Fin m → 𝓞 E) (s : 𝒜) : Prop :=
  ∃ r : Fin m → FiniteAdeleRing (𝓞 F) F, (∀ j, r j ∈ intAd F) ∧
    s = ∑ j, algebraMap (𝓞 E) E (b j) ⊗ₜ[F] r j
end Tensor
section Quot
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
end Quot
section Generic
variable {L : Type} [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
end Generic
section Final
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
end Final
end Formalism.UG.P


