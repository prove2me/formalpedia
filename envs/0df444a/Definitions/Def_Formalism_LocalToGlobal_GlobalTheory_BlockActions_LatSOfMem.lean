-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
-- name    : Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:22.310253+00:00
-- url     : https://prove2.me/theorems/ab52da10-4af2-4411-815e-cdeb7cf3924d
-- title:
--   Lat SOf Mem
-- statement:
--   Definitions and structural lemmas for Lat SOf Mem, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/LatSOfMem.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.GlobalTheoryTheory.Br
open NumberField Formalism.UG IsDedekindDomain
open scoped TensorProduct
def LatLocGlob : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Λ → ∀ x : Fin n → E,
    (fun i => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (x i)) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ →
    x ∈ Λ
def AdLocLat : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)), Module.Finite (𝓞 E) Λ → ∀ x : Fin n → E ⊗[F] FiniteAdeleRing (𝓞 F) F,
    (∀ v : HeightOneSpectrum (𝓞 F), (fun i => prV (E := E) v (x i)) ∈
      latS (F := F) (v.adicCompletion F) (tensInt (F := F) (v.adicCompletion F) (intOE E) (v.adicCompletionIntegers F).toSubring) Λ) →
    x ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
end Formalism.L2.GlobalTheoryTheory.Br


