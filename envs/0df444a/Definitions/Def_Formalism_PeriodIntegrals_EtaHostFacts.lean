-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_EtaHostFacts
-- name    : Formalism_PeriodIntegrals_EtaHostFacts
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T18:33:05.882018+00:00
-- url     : https://prove2.me/theorems/1b04055e-c9fd-4331-81f0-42c316cd696d
-- title:
--   Eta Host Facts
-- statement:
--   Definitions and structural lemmas for Eta Host Facts, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/EtaHostFacts.lean

import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_IsUnitaryNormOf
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host
namespace PI.EtaHostFacts
instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _
def Unram : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ P : HeightOneSpectrum (𝓞 H.E), (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card = 1 →
    P.asIdeal.ramificationIdx (𝓞 H.F) = 1
def TotReal : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R), ∀ w : InfinitePlace H.F, w.IsReal
open Classical in

def OnePsi : Prop := Formalism.BasicNotions.FactCardPsi → Formalism.BasicNotions.FactEmb → ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ w : InfinitePlace H.F,
    (Finset.univ.filter (fun i : R.Psi =>
      InfinitePlace.mk (H.emb (i : R.GG)) ∈ aboveInf (L := H.E) H.F w)).card = 1
def Conj : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∃ c : H.E →ₐ[H.F] H.E, (∀ x, c (c x) = x) ∧ (∀ x, c x = x → ∃ a : H.F, algebraMap H.F H.E a = x) ∧
    (∀ (φ : H.E →+* ℂ) (x : H.E), φ (c x) = starRingEnd ℂ (φ x)) ∧ c H.sqrtMinusD = -H.sqrtMinusD
def Roots : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ z : H.E, (∃ n : ℕ, 0 < n ∧ z ^ n = 1) → Algebra.norm H.K z = 1
def SqrtNe : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R), H.sqrtMinusD ≠ 0
def SqrtPos : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → ∀ i : R.Psi,
    ∃ r : ℝ, 0 < r ∧ H.emb (i : R.GG) (s : H.E) = Complex.I * r
def Card4 : Prop := Formalism.BasicNotions.FactCardPsi → ∀ (R : Formalism.BasicNotions.Ranks) (_H : Formalism.BasicNotions.Host R),
  4 ∣ Fintype.card (R.Psi)
def DSplit : Prop := ∀ (R : Formalism.BasicNotions.Ranks) (H : Formalism.BasicNotions.Host R),
  ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD →
    ∀ P : HeightOneSpectrum (𝓞 H.E), ordF P s ≠ 0 → (aboveF (L := H.E) H.F (P.under (𝓞 H.F))).card ≠ 1
def Target : Prop := Unram ∧ TotReal ∧ OnePsi ∧ Conj ∧ Roots ∧ SqrtNe ∧ SqrtPos ∧ Card4 ∧ DSplit
end PI.EtaHostFacts


