-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_LengthEqAddEigen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:15.853782+00:00
-- url     : https://prove2.me/theorems/8e950a6e-c6a2-4ccb-adcf-d35aba461c7a
-- title:
--   Length Eq Add Eigen
-- statement:
--   Definitions and structural lemmas for Length Eq Add Eigen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/LengthEqAddEigen.lean

import Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_PartsConj
import Definitions.Def_Development_AutomorphicArithmetic_CharacterBoxes_ExistsPageN
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.Top
namespace UpperTheory.V
section Parts
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime]
variable (E) in

def cE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv
def cAct (D : LData E Ω l) (e : ℤ) : Module.End ℤ_[l] (H1 (qzTw D e)) := galoisActionOnCohomology D e (cE E)
def ShaPlus (D : LData E Ω l) (e : ℕ) : Submodule ℤ_[l] (H1 (qzTw D (e : ℤ))) :=
  Sha D e ⊓ (cAct D e).eigenspace ((-1) ^ e)
def ShaMinus (D : LData E Ω l) (e : ℕ) : Submodule ℤ_[l] (H1 (qzTw D (e : ℤ))) :=
  Sha D e ⊓ (cAct D e).eigenspace ((-1) ^ (e + 1))
def plusLen (D : LData E Ω l) (e : ℕ) : ℕ∞ := Module.length ℤ_[l] (ShaPlus D e)
def minusLen (D : LData E Ω l) (e : ℕ) : ℕ∞ := Module.length ℤ_[l] (ShaMinus D e)
end Parts
def VVat (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (D : LData E Ω l),
    (∀ e : ℕ, 0 < e → e < t → shaLen D (e : ℤ) ≠ ⊤) ∧ ∑ e ∈ Finset.Ico 1 t, ((shaLen D (e : ℤ)).toNat : ℝ) ≤ B
def BoundedHeightTwoPlaceCondition (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) : Prop := VVat 2 E t B
def VVminusLe (E : Type) [Field E] [NumberField E] [IsCMField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), p ≠ 2 → 0 < e → e < t → minusLen (ld p) e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@minusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ) ≤ B
def VVplusLe (E : Type) [Field E] [NumberField E] [IsCMField E] (t : ℕ) (B : ℝ) : Prop :=
  ∀ (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (ld : ∀ (p : ℕ) [Fact p.Prime], LData E Ω p),
    (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), p ≠ 2 → 0 < e → e < t → plusLen (ld p) e ≠ ⊤) ∧
    ∀ S : Finset Nat.Primes, (∀ l ∈ S, (l : ℕ) ≠ 2) →
      ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@plusLen E Ω _ _ _ _ _ _ l ⟨l.2⟩ (@ld l ⟨l.2⟩) e).toNat : ℝ) ≤ B
end UpperTheory.V
end


