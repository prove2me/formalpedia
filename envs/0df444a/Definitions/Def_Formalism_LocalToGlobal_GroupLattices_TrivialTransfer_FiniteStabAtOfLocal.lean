-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
-- name    : Formalism_LocalToGlobal_GroupLattices_TrivialTransfer_FiniteStabAtOfLocal
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T13:05:26.534819+00:00
-- url     : https://prove2.me/theorems/08ee2c5e-553f-4108-a46e-d3eaee54889f
-- title:
--   Finite Stab At Of Local
-- statement:
--   Definitions and structural lemmas for Finite Stab At Of Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GroupLattices/TrivialTransfer/FiniteStabAtOfLocal.lean

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Theorems.Thm_Formalism_UG_P_afsplit_prV_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
namespace Formalism.L2.G.Triv
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
abbrev SV (E : Type) [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) :
    Subring (E ⊗[F] v.adicCompletion F) :=
  tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring
section Trace
end Trace
section Lattice
variable {n : Type} [Fintype n] [DecidableEq n]
def latLoc (F : Type) [Field F] [NumberField F] [Algebra F E] (Λ : Submodule (𝓞 E) (n → E)) :
    Submodule (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) (n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) where
  carrier := {x | ∀ v : HeightOneSpectrum (𝓞 F),
    (fun i => prV (E := E) v (x i)) ∈ latS (F := F) (v.adicCompletion F) (SV E v) Λ}
  add_mem' := by
    intro a b ha hb v
    have : (fun i => prV (E := E) v ((a + b) i)) = (fun i => prV (E := E) v (a i)) + fun i => prV (E := E) v (b i) := by
      ext i; simp
    rw [this]; exact add_mem (ha v) (hb v)
  zero_mem' := by
    intro v
    have : (fun i => prV (E := E) v ((0 : n → E ⊗[F] FiniteAdeleRing (𝓞 F) F) i)) = 0 := by ext i; simp
    rw [this]; exact zero_mem _
  smul_mem' := by
    intro s a ha v
    have : (fun i => prV (E := E) v ((s • a) i)) =
        (⟨prV (E := E) v s, afsplit_prV_int v _ s.2⟩ : SV E v) • fun i => prV (E := E) v (a i) := by
      ext i
      show prV (E := E) v ((s : E ⊗[F] FiniteAdeleRing (𝓞 F) F) * a i) = prV (E := E) v s * prV (E := E) v (a i)
      rw [map_mul]
    rw [this]; exact Submodule.smul_mem _ _ (ha v)
end Lattice
end Formalism.L2.G.Triv
end


