-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMLatticeAreaFormula_GoodLatCMOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMLatticeAreaFormula_GoodLatCMOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:46.413797+00:00
-- url     : https://prove2.me/theorems/dc984fda-6b3e-4e84-86f1-e81f149241db
-- title:
--   Good Lat CMOf
-- statement:
--   Definitions and structural lemmas for Good Lat CMOf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMLatticeAreaFormula/GoodLatCMOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GoodLatCM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
namespace PI.GoodLatCMWork
open PI.GoodLatCM
def Setup (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    {S : Type} [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ) : Prop :=
  (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) ∧
  Module.finrank ℚ K = 2 ∧ NumberField.discr K = -(d : ℤ) ∧ d % 4 = 3 ∧
  Function.Injective emb ∧ (∀ (s : S) (a : K), emb s (a : E) = φ₀ (a : E)) ∧
  Fintype.card S = Module.finrank K E ∧
  MM.FG ∧ MM ≠ ⊥ ∧
  (∀ x : E, x ∈ MM ↔ ∀ y ∈ MM, Algebra.trace K E (x * star y) ∈ (algebraMap (𝓞 K) K).range) ∧
  cc ≠ ⊥ ∧ δ ≠ 0
def lam {E : Type} [Field E] [NumberField E] (K : IntermediateField ℚ E) (φ₀ : E →+* ℂ) (cc : Ideal (𝓞 K)) (δ : ℂ) :
    AddSubgroup ℂ :=
  AddSubgroup.closure {w | ∃ c ∈ cc, w = δ * φ₀ (((c : K) : E))}
def HfGFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (X Y : Matrix (Fin N') (Fin N) E),
      HfG (area (lam K φ₀ cc δ)) (fun s i j => δ * emb s (X i j)) (fun s i j => δ * emb s (Y i j)) =
        φ₀ ((Algebra.trace K E (∑ i, ∑ j, X i j * star (Y i j)) : K) : E) /
          ((Ideal.absNorm cc : ℂ) * ((Real.sqrt d / 2 : ℝ) : ℂ))
def LaBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (S → Fin N' → Fin N → ℂ)),
        gLa emb (lam K φ₀ cc δ) MM L L' = AddSubgroup.closure (Set.range b)
def LaIntegral : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∀ y ∈ gLa emb (lam K φ₀ cc δ) MM L L',
        ∃ n : ℤ, (HfG (area (lam K φ₀ cc δ)) x y).im = n
def LaSelfDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ v : S → Fin N' → Fin N → ℂ,
        (∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∃ n : ℤ, (HfG (area (lam K φ₀ cc δ)) v x).im = n) →
        v ∈ gLa emb (lam K φ₀ cc δ) MM L L'
def LaSemichar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∀ y ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∀ n : ℤ,
        (HfG (area (lam K φ₀ cc δ)) x y).im = n →
        alG (Real.sqrt d / 2) (area (lam K φ₀ cc δ)) (x + y) =
          alG (Real.sqrt d / 2) (area (lam K φ₀ cc δ)) x * alG (Real.sqrt d / 2) (area (lam K φ₀ cc δ)) y *
            (-1 : ℂ) ^ n
def LaCommens : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L₁ L₂ : Submodule (𝓞 E) (Fin N → E)) (L₁' L₂' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L₁ → IsSDLat E N' L₁' → IsSDLat E N L₂ → IsSDLat E N' L₂' →
      ((gLa emb (lam K φ₀ cc δ) MM L₁ L₁').addSubgroupOf (gLa emb (lam K φ₀ cc δ) MM L₂ L₂')).index ≠ 0
end PI.GoodLatCMWork


