-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Satake
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:41:55.264337+00:00
-- url     : https://prove2.me/theorems/d98f38f3-c708-4fd9-85b9-4d2cb44f7bc7
-- title:
--   Satake
-- statement:
--   Definitions and structural lemmas for Satake, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Satake.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeComb
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeMat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SatakeRes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_HeckeActMem
import Theorems.Thm_Formalism_UG_P_satake_unif_ne_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Main
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
abbrev satakeTset (ϖ : v.adicCompletion F) (j : ℕ) : Set (GL (Fin n) (v.adicCompletion F)) :=
  {g | ∃ a ∈ GLint (Fin n) (Ov F v), ∃ b ∈ GLint (Fin n) (Ov F v),
    (g : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
      (a : Matrix (Fin n) (Fin n) _) * diagJ n ϖ j * (b : Matrix (Fin n) (Fin n) _)}
end Main
section Reps
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)
abbrev SatakeIdx (j : ℕ) : Type :=
  Σ S : {S : Finset (Fin n) // S.card = j}, satakePairs S.1 → satakeRes (Ov F v) ⟨ϖ, hϖ⟩
abbrev satakeB {j : ℕ} (i : SatakeIdx v hϖ (n := n) j) : GL (Fin n) (v.adicCompletion F) :=
  satakeRep (Ov F v) ⟨ϖ, hϖ⟩ (satake_unif_ne_zero v hu) j i
end Reps
section Value
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {n : ℕ}
  {ϖ : v.adicCompletion F} (hϖ : ϖ ∈ Ov F v) (hu : IsUnifV F v ϖ)
end Value
end Formalism.UG.P


