-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMLatticeAreaFormula_AreaFormula
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMLatticeAreaFormula_AreaFormula
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:56:34.945502+00:00
-- url     : https://prove2.me/theorems/27d92102-354d-4d31-8704-f9a35d8aa49e
-- title:
--   Area Formula
-- statement:
--   Definitions and structural lemmas for Area Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CMLatticeAreaFormula/AreaFormula.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_GoodLatCM
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CMLatticeAreaFormula_GoodLatCMOf
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
section Defs
variable {E : Type} [Field E] [NumberField E]
def embM {S : Type} (emb : S → E →+* ℂ) (δ : ℂ) {N N' : ℕ} (X : Matrix (Fin N') (Fin N) E) : S → Fin N' → Fin N → ℂ :=
  fun s i j => δ * emb s (X i j)
noncomputable def hh [StarRing E] (K : IntermediateField ℚ E) {N N' : ℕ} (X Y : Matrix (Fin N') (Fin N) E) : K :=
  Algebra.trace K E (∑ i, ∑ j, X i j * star (Y i j))
def cYY (K : IntermediateField ℚ E) (cc : Ideal (𝓞 K)) (MM : Submodule (𝓞 E) E) {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) : AddSubgroup (Matrix (Fin N') (Fin N) E) :=
  AddSubgroup.closure {Z | ∃ c ∈ cc, ∃ A ∈ gYY MM L L', Z = (((c : K) : E)) • A}
def matO (E : Type) [Field E] [NumberField E] (N N' : ℕ) : AddSubgroup (Matrix (Fin N') (Fin N) E) where
  carrier := {X | ∀ i j, X i j ∈ (algebraMap (𝓞 E) E).range}
  add_mem' := fun {X Y} hX hY i j => by
    rw [Matrix.add_apply]; exact add_mem (hX i j) (hY i j)
  zero_mem' := fun i j => by
    rw [Matrix.zero_apply]; exact zero_mem _
  neg_mem' := fun {X} hX i j => by
    rw [Matrix.neg_apply]; exact neg_mem (hX i j)
end Defs
def NoRealEmb : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ → IsEmpty (K →+* ℝ)
def AreaFormula : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    area (lam K φ₀ cc δ) = ‖δ‖ ^ 2 * (Ideal.absNorm cc : ℝ) * (Real.sqrt d / 2)
def LamInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ z ∈ lam K φ₀ cc δ, ∀ w ∈ lam K φ₀ cc δ, ∃ n : ℤ, (z * (starRingEnd ℂ) w).im / area (lam K φ₀ cc δ) = n
def LamDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ v : ℂ, (∀ w ∈ lam K φ₀ cc δ, ∃ n : ℤ, (v * (starRingEnd ℂ) w).im / area (lam K φ₀ cc δ) = n) → v ∈ lam K φ₀ cc δ
def LamRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ w ∈ lam K φ₀ cc δ, ∃ c ∈ cc, w = δ * φ₀ (((c : 𝓞 K) : K) : E)
def LamMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ t : K, δ * φ₀ (t : E) ∈ lam K φ₀ cc δ → ∃ c ∈ cc, ((c : 𝓞 K) : K) = t
def OKDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ κ : K, (∀ l : 𝓞 K, ∃ n : ℤ, (φ₀ (κ : E) * (starRingEnd ℂ) (φ₀ ((l : K) : E))).im / (Real.sqrt d / 2) = n) →
      κ ∈ (algebraMap (𝓞 K) K).range
def Parity : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ η : 𝓞 K, ∃ a b : ℤ, 2 * (φ₀ ((η : K) : E)).re = a ∧ (φ₀ ((η : K) : E)).im / (Real.sqrt d / 2) = b ∧ Even (a - b)
def LaEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (x : S → Fin N' → Fin N → ℂ),
      x ∈ gLa emb (lam K φ₀ cc δ) MM L L' ↔ ∃ Z ∈ cYY K cc MM L L', x = embM emb δ Z
def ResId : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E], (∀ (φ : E →+* ℂ) (x : E), φ (star x) = (starRingEnd ℂ) (φ x)) →
    ∀ (N : ℕ) (L : Submodule (𝓞 E) (Fin N → E)), IsSDLat E N L →
      ∃ (n : ℕ) (x v : Fin n → Fin N → E), (∀ k, x k ∈ L) ∧ (∀ k, v k ∈ L) ∧ ∀ y : Fin N → E, ∑ k, stdH E N (v k) y • x k = y
def YYInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X ∈ gYY MM L L', ∀ Y ∈ gYY MM L L', hh K X Y ∈ (algebraMap (𝓞 K) K).range
def YYDual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X : Matrix (Fin N') (Fin N) E, (∀ Y ∈ gYY MM L L', hh K X Y ∈ (algebraMap (𝓞 K) K).range) → X ∈ gYY MM L L'
def CInv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X : Matrix (Fin N') (Fin N) E, (∀ Y ∈ gYY MM L L', ∃ c ∈ cc, ((c : 𝓞 K) : K) = hh K X Y) → X ∈ cYY K cc MM L L'
def CCInt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ X ∈ cYY K cc MM L L', ∀ Y ∈ cYY K cc MM L L', ∃ η : 𝓞 K, ((η : K)) * (Ideal.absNorm cc : K) = hh K X Y
def CStd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∃ m : ℕ, 0 < m ∧ (∀ Z ∈ cYY K cc MM L L', (m : E) • Z ∈ matO E N N') ∧ ∀ Z ∈ matO E N N', (m : E) • Z ∈ cYY K cc MM L L'
def StdBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ), ∃ (ι : Type) (_ : Fintype ι) (b : Module.Basis ι ℝ (S → Fin N' → Fin N → ℂ)),
      ∀ x, x ∈ AddSubgroup.closure (Set.range b) ↔ ∃ Z ∈ matO E N N', x = embM emb δ Z
def QSpan : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (K : IntermediateField ℚ E) (d : ℕ) (φ₀ : E →+* ℂ)
    (S : Type) [Fintype S] (emb : S → E →+* ℂ) (MM : Submodule (𝓞 E) E) (cc : Ideal (𝓞 K)) (δ : ℂ),
    Setup E K d φ₀ emb MM cc δ →
    ∀ (N N' : ℕ) (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)),
      IsSDLat E N L → IsSDLat E N' L' →
      ∀ v : S → Fin N' → Fin N → ℂ,
        (∀ x ∈ gLa emb (lam K φ₀ cc δ) MM L L', ∃ n : ℤ, (HfG (area (lam K φ₀ cc δ)) v x).im = n) →
        ∃ X : Matrix (Fin N') (Fin N) E, v = embM emb δ X
end PI.GoodLatCMWork


