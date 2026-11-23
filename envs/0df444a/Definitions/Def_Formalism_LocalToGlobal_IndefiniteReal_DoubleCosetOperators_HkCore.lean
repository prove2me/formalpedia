-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_HkCore
-- name    : Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_HkCore
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:17:12.599564+00:00
-- url     : https://prove2.me/theorems/2eff83cd-7135-4a96-8b59-00985288eea2
-- title:
--   Hk Core
-- statement:
--   Definitions and structural lemmas for Hk Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/DoubleCosetOperators/HkCore.lean

import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_DoubleCosetOperators_GoodPartLeTypeSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField TensorProduct
namespace Formalism.IndefR.NX.Core
variable (C : RatCore) {Pl : Type}
def HeckeStab (j : ℕ) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) : Prop :=
  ∀ k P (x : C.WL j), x ∈ (C.A j).WK → hL k P x ∈ (C.A j).WK
def HeckeRatAt (j : ℕ) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) (σ0 : C.L0 →+* ℂ)
    (hC : ℕ → Pl → Module.End ℂ (C.W j σ0)) : Prop :=
  ∀ k P (x : C.WL j), (C.A j).j σ0 (hL k P x) = hC k P ((C.A j).j σ0 x)
def hkK (j : ℕ) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) (hs : HeckeStab C j hL) (k : ℕ) (P : Pl) :
    Module.End C.Ks (FmK C j) :=
  ((hL k P).restrictScalars C.Ks).restrict (p := (C.A j).WK) (q := (C.A j).WK) fun x hx => hs k P x hx
def hkF (i : C.Tw) (j : ℕ) (b : Bool) (hL : ℕ → Pl → Module.End C.L0 (C.WL j)) (hs : HeckeStab C j hL)
    (k : ℕ) (P : Pl) : Module.End (FractionRing (C.O i)) (Fm C i j b) :=
  (Module.End.baseChangeHom C.Ks (KB C i b) (FmK C j) (hkK C j hL hs k P) :
    Module.End (KB C i b) (KB C i b ⊗[C.Ks] FmK C j))
end Formalism.IndefR.NX.Core


