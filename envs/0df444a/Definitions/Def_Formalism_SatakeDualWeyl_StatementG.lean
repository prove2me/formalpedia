-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_StatementG
-- name    : Formalism_SatakeDualWeyl_StatementG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:22:55.009546+00:00
-- url     : https://prove2.me/theorems/8cde1428-8c49-478b-9a2d-ed549778b165
-- title:
--   Statement G
-- statement:
--   Definitions and structural lemmas for Statement G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/StatementG.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_StatementE
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct
namespace Formalism.UG
def IsInertAt (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal
def InertLocal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), σ ≠ AlgHom.id F E → (∀ τ : E →+* ℂ, τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) →
    (∀ e : E, σ e = e → ∃ a : F, algebraMap F E a = e) →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E)), IsInertAt F E v w →
    ∃ (e : E ⊗[F] v.adicCompletion F ≃+* w.adicCompletion E) (σw : w.adicCompletion E →+* w.adicCompletion E)
      (ϖ : w.adicCompletion E),
      (∀ x, e (sigR σ (v.adicCompletion F) x) = σw (e x)) ∧ IsUnramInv ϖ σw (qV F v) ∧
      ∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v) ↔ e x ∈ intL (w.adicCompletion E)
def InertAntidiag : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → Odd q →
    ∃ P : GL (Fin n) L, P ∈ (bc (n := Fin n) (intL L).subtype).range ∧
      cT σ (P : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = antiJ L n
def LocInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (L : Type) [Field L]
    [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (e : E ⊗[F] v.adicCompletion F ≃+* L) (σw : L →+* L) (P : GL (Fin n) L),
    (∀ x, e (sigR σ (v.adicCompletion F) x) = σw (e x)) →
    (∀ x, x ∈ tensInt (F := F) (v.adicCompletion F) (intOE E) (Ov F v) ↔ e x ∈ intL L) →
    P ∈ (bc (n := Fin n) (intL L).subtype).range →
    cT σw (P : Matrix (Fin n) (Fin n) L) * (P : Matrix (Fin n) (Fin n) L) = antiJ L n →
    ∃ f : UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F) ≃* GU σw n,
      (∀ x, ((f x : GU σw n) : GL (Fin n) L) = P⁻¹ * bc (e : E ⊗[F] v.adicCompletion F →+* L) x * P) ∧
      ((levelV σ (1 : Matrix (Fin n) (Fin n) E) v).subgroupOf
          (UPts σ (1 : Matrix (Fin n) (Fin n) E) (v.adicCompletion F))).map f.toMonoidHom = KU σw n
end Formalism.UG


