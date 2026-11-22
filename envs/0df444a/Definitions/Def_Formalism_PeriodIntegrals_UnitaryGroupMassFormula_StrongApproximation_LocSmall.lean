-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_LocSmall
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StrongApproximation_LocSmall
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:02:47.135221+00:00
-- url     : https://prove2.me/theorems/f589e8a6-fd1f-4aaa-b867-127d37980cdd
-- title:
--   Loc Small
-- statement:
--   Definitions and structural lemmas for Loc Small, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StrongApproximation/LocSmall.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_StrongApproxE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField ValuativeRel
namespace PI.StrongApproxE
open Formalism.MainNotions.S.Loc
def IntSpan : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ (n : ℕ) (b : Fin n → E), (∀ i, IsIntegral ℤ (b i)) ∧ ∀ e : E, ∃ c : Fin n → F, e = ∑ i, c i • b i
def DedSA : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (T : Finset (HeightOneSpectrum (𝓞 F))) (a c : HeightOneSpectrum (𝓞 F) → F),
    (∀ p ∈ T, c p ≠ 0) →
    ∃ t : F, (∀ p ∈ T, p.valuation F (t - a p) ≤ p.valuation F (c p)) ∧ ∀ p, p ∉ T → p.valuation F t ≤ 1
def LocSmall : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (V : AddSubgroup L.Fp), IsOpen (V : Set L.Fp) →
    ∃ c : F, c ≠ 0 ∧ ∀ z : F, p.valuation F z ≤ p.valuation F c → L.ιF z ∈ V
def LocDense : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (V : AddSubgroup L.Fp), IsOpen (V : Set L.Fp) →
    ∀ α : L.Fp, ∃ a : F, L.ιF a - α ∈ V
def LocInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (z : F) (e : E), p.valuation F z ≤ 1 → IsIntegral ℤ e →
    L.ιF z • L.ιE e ∈ L.O
def LocOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (U : AddSubgroup L.Ep), IsOpen (U : Set L.Ep) →
    ∀ (n : ℕ) (w : Fin n → L.Ep), ∃ V : AddSubgroup L.Fp, IsOpen (V : Set L.Fp) ∧ ∀ α ∈ V, ∀ i, α • w i ∈ U
def LocSpan : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (n : ℕ) (b : Fin n → E),
    (∀ e : E, ∃ c : Fin n → F, e = ∑ i, c i • b i) → ∀ x : L.Ep, ∃ α : Fin n → L.Fp, x = ∑ i, α i • L.ιE (b i)
def LocLin : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (sig : E →ₐ[F] E)
    (p : HeightOneSpectrum (𝓞 F)) (L : LocAt F E sig p) (a : F) (e : E), L.ιE (a • e) = L.ιF a • L.ιE e
end PI.StrongApproxE


