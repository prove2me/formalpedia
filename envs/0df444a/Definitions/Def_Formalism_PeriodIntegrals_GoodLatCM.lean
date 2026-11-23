-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_GoodLatCM
-- name    : Formalism_PeriodIntegrals_GoodLatCM
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:50:46.5988+00:00
-- url     : https://prove2.me/theorems/028f44af-7368-467d-819a-477fcf3556e8
-- title:
--   Good Lat CM
-- statement:
--   Definitions and structural lemmas for Good Lat CM, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/GoodLatCM.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_ThGDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI
namespace GoodLatCM
def stdH (E : Type) [Field E] [StarRing E] (N : ℕ) (x y : Fin N → E) : E := ∑ i, star (x i) * y i
def IsSDLat (E : Type) [Field E] [NumberField E] [StarRing E] (N : ℕ)
    (L : Submodule (𝓞 E) (Fin N → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin N → E)) = ⊤ ∧
    ∀ y, y ∈ L ↔ ∀ x ∈ L, stdH E N x y ∈ (algebraMap (𝓞 E) E).range
section Lat
variable {E : Type} [Field E] [NumberField E]
def gYY (MM : Submodule (𝓞 E) E) {N N' : ℕ} (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) :
    Submodule (𝓞 E) (Matrix (Fin N') (Fin N) E) :=
  Submodule.span (𝓞 E)
    {B | ∃ a ∈ MM, ∃ A ∈ Submodule.span (𝓞 E) {A : Matrix (Fin N') (Fin N) E | ∀ x ∈ L, A.mulVec x ∈ L'}, B = a • A}
def gLa {S : Type} (emb : S → E →+* ℂ) (abelian₂ : AddSubgroup ℂ) (MM : Submodule (𝓞 E) E) {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) : AddSubgroup (S → Fin N' → Fin N → ℂ) :=
  AddSubgroup.closure {z | ∃ w ∈ abelian₂, ∃ A ∈ gYY MM L L', z = w • (fun s i j => emb s (A i j))}
end Lat
end GoodLatCM
open GoodLatCM in

def GoodLatCM : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
  ∀ (K : IntermediateField ℚ E) (d : ℕ), Module.finrank ℚ K = 2 → NumberField.discr K = -(d : ℤ) → d % 4 = 3 →
  ∀ (φ₀ : E →+* ℂ) (S : Type) [Fintype S] (emb : S → E →+* ℂ), Function.Injective emb →
    (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) → Fintype.card S = Module.finrank K E →
  ∀ MM : Submodule (𝓞 E) E, MM.FG → MM ≠ ⊥ →
    (∀ x : E, x ∈ MM ↔ ∀ y ∈ MM, Algebra.trace K E (x * star y) ∈ (algebraMap (𝓞 K) K).range) →
  ∀ (cc : Ideal (𝓞 K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 →
  ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin N → E)) (L₁' L₂' : Submodule (𝓞 E) (Fin N' → E)),
    IsSDLat E N L₁ → IsSDLat E N' L₁' → IsSDLat E N L₂ → IsSDLat E N' L₂' →
    GoodLat (Real.sqrt d / 2) (area (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}))
      (gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₁ L₁') ∧
    ((gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₁ L₁').addSubgroupOf
      (gLa emb (AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}) MM L₂ L₂')).index ≠ 0
end PI


