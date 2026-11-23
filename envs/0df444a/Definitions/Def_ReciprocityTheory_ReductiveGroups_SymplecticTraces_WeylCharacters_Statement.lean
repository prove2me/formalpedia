-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
-- name    : ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Statement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:30:37.895362+00:00
-- url     : https://prove2.me/theorems/8166a09d-76a9-4774-801a-efc56bf446c7
-- title:
--   Statement
-- statement:
--   Definitions and structural lemmas for Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/Statement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_Branch
import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PsiExistsStatement
import Definitions.Def_Formalism_LocalRingCardinality_DataCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
open ReciprocityTheory.ChartRestriction.DS.S7
def kChar {n : ℕ} {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : ℂ :=
  LinearMap.trace ℂ T.V ((T.op k : T.V →L[ℂ] T.V) : T.V →ₗ[ℂ] T.V)
def SqCharStatement : Prop :=
  ∀ (N : ℕ) (lam : Formalism.BasicNotions.DomWeight N) (g : GL (Fin N) ℂ) (t : Fin N → ℂ),
    (g : Matrix (Fin N) (Fin N) ℂ) = Matrix.diagonal t →
    ∃ f : Formalism.BasicNotions.nablaSq ℂ N lam →ₗ[ℂ] Formalism.BasicNotions.nablaSq ℂ N lam,
      (∀ x, (f x : MvPolynomial (Fin N × Fin N) ℂ) = Formalism.BasicNotions.sqAct ℂ N lam g x) ∧
      LinearMap.trace ℂ _ f = gtChar N lam.w t
def UCharStatement : Prop :=
  ∀ (N : ℕ) (Λ : Fin N → ℤ), Antitone Λ →
    ∀ (T : KType (fun _ : Fin N => true) (fun a => (Λ a : ℝ))) (k : KG (fun _ : Fin N => true)) (t : Fin N → ℂ),
      toMK k = Matrix.diagonal t → kChar T k = gtChar N Λ t
def KCharGTStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℤ), (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) →
    ∀ (T : KType ε (fun a => (Λ a : ℝ))) (k : KG ε) (t : Fin n → ℂ), toMK k = Matrix.diagonal t →
      kChar T k = gtChar (cnt ε true) (Λ ∘ blk ε true) (t ∘ blk ε true) *
        gtChar (cnt ε false) (Λ ∘ blk ε false) (t ∘ blk ε false)
def WeylStatement : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℤ), (∀ a b, a < b → ε a = ε b → Λ b ≤ Λ a) →
    ∀ (T : KType ε (fun a => (Λ a : ℝ))) (k : KG ε) (t : Fin n → ℂ), toMK k = Matrix.diagonal t →
      wdenK ε t * kChar T k = numK ε (Λ + rhoK ε) t
end ReciprocityTheory.ChartRestriction.TR.Weyl


