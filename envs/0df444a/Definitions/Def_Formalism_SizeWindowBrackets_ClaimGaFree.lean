-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_ClaimGaFree
-- name    : Formalism_SizeWindowBrackets_ClaimGaFree
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:38.535752+00:00
-- url     : https://prove2.me/theorems/0c13b290-696f-409c-9b8a-c81e25c1ca47
-- title:
--   Claim Ga Free
-- statement:
--   Definitions and structural lemmas for Claim Ga Free, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/ClaimGaFree.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.UnitWeightPartition
open Finset
noncomputable section
variable {ι κ : Type*} [DecidableEq ι]
def sgw (J : Finset κ) (gain F E : κ → ι → ℝ) (w : ι) : ℝ :=
  ∑ j ∈ J, (gain j w + F j w - E j w)
def Ga (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain : κ → ι → ℝ) (tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * ((∑ j ∈ J, gain j w) - tau w)
def Fo (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (F : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * F j w
def Ee (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (E : κ → ι → ℝ) : ℝ :=
  2 * ∑ j ∈ J, ∑ w ∈ W, l w * E j w
def Sg (W : Finset ι) (l s tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * (s w - tau w)
def Ta (W : Finset ι) (l tau : ι → ℝ) : ℝ :=
  2 * ∑ w ∈ W, l w * tau w
def IO (W : Finset ι) (l io : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * io w
def be (du : ℝ) (len tau : ι → ℝ) (w : ι) : ℝ :=
  (len w - du * tau w) / du
def BeSum (W : Finset ι) (l : ι → ℝ) (du : ℝ) (len tau : ι → ℝ) : ℝ :=
  ∑ w ∈ W, 2 * l w * be du len tau w
def ClaimSg (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau : ι → ℝ) : Prop :=
  Sg W l (sgw J gain F E) tau = Ga W J l gain tau + Fo W J l F - Ee W J l E
def ClaimGaFree (W Z : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain1 gain2 : κ → ι → ℝ)
    (tau1 tau2 : ι → ℝ) : Prop :=
  (∀ w ∈ W, w ∉ Z → (∀ j ∈ J, gain1 j w = gain2 j w) ∧ tau1 w = tau2 w) →
  (∀ w ∈ W, w ∈ Z → (∀ j ∈ J, gain1 j w = 0 ∧ gain2 j w = 0) ∧ tau1 w = 0 ∧ tau2 w = 0) →
  Ga W J l gain1 tau1 = Ga W J l gain2 tau2
def ClaimUnit (W : Finset ι) (P : Finset ℕ) (pr : ι → ℕ) (l io : ι → ℝ) (iop : ℕ → ℝ) :
    Prop :=
  (∀ w ∈ W, pr w ∈ P) →
  (∀ p ∈ P, ∑ w ∈ W.filter (fun w => pr w = p), l w = Real.log (p : ℝ)) →
  (∀ w ∈ W, io w = iop (pr w)) →
  IO W l io = 2 * ∑ p ∈ P, Real.log (p : ℝ) * iop p
def ClaimDe (f : ℕ) (T dM du : ℝ) : Prop :=
  0 < dM → 2 < T → du = dM * (1 - 1 / (T - 1)) ^ f →
  du = (1 - (1 - du / dM)) * dM ∧ 0 ≤ 1 - du / dM ∧ 1 - du / dM < 1 ∧
    1 - du / dM ≤ 2 * (f : ℝ) / T
def ClaimT (WT : Finset ι) (l len : ι → ℝ) (dM du de lam T : ℝ) : Prop :=
  (∀ w ∈ WT, 0 ≤ l w) → 0 < dM → 0 ≤ de → de ≤ 1 / 2 → du = (1 - de) * dM → 0 ≤ lam →
  (∀ w ∈ WT, len w ≤ dM * lam) → ∑ w ∈ WT, l w = Real.log T →
  ∑ w ∈ WT, 2 * l w * len w / du ≤ 4 * lam * Real.log T
def HypLow (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ 0 < dM ∧ 0 ≤ de ∧ de < 1 ∧ du = (1 - de) * dM ∧ WT ⊆ W ∧
  (∀ w ∈ WT, tau w = 0) ∧ (∀ w ∈ W, 0 ≤ io w) ∧
  (∀ w ∈ W \ WT, len w ≤ dM * (tau w + io w)) ∧
  ∑ w ∈ WT, 2 * l w * len w / du ≤ PT ∧
  ∑ w ∈ W, 2 * l w * (sgw J gain F E w - sg' w) ≤ Rd ∧
  muN = muMu + Sg W l sg' tau - BeSum W l du len tau
def ClaimLow (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ) : Prop :=
  HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  muMu + Ga W J l gain tau + Fo W J l F - Ee W J l E - Rd - PT - IO W l io / (1 - de)
      - de / (1 - de) * Ta W l tau ≤ muN
def HypLow2 (W : Finset ι) (l tau io : ι → ℝ) (f T de b muM muMu IOp PT LT Rd RX : ℝ) :
    Prop :=
  muMu = muM - f * Real.log (T - 1) / (T - 2) ∧ de ≤ 2 * f / T ∧ 2 * f / T ≤ 1 / 2 ∧
  (∀ w ∈ W, 0 ≤ tau w) ∧ Ta W l tau ≤ b ^ 2 ∧
  4 * f / T * b ^ 2 + f * Real.log (T - 1) / (T - 2) ≤ 1 ∧
  IO W l io = 2 * IOp ∧ PT ≤ LT ∧ Rd ≤ RX
def ClaimLow2 (W WT : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau io len sg' : ι → ℝ) (dM du de muMu muN PT Rd : ℝ)
    (f T b muM IOp LT RX : ℝ) : Prop :=
  HypLow W WT J l gain F E tau io len sg' dM du de muMu muN PT Rd →
  HypLow2 W l tau io f T de b muM muMu IOp PT LT Rd RX →
  muM + Ga W J l gain tau + Fo W J l F - Ee W J l E - (4 * IOp + LT + RX + 1) ≤ muN
def HypHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  (∀ w ∈ W, 0 ≤ l w) ∧ (∀ w ∈ W, sg' w ≤ sgw J gain F E w) ∧
  muMaxN ≤ muMaxMu + Sg W l sg' tau ∧ muMaxMu ≤ muMaxM
def ClaimHigh (W : Finset ι) (J : Finset κ) (l : ι → ℝ) (gain F E : κ → ι → ℝ)
    (tau sg' : ι → ℝ) (muMaxM muMaxMu muMaxN : ℝ) : Prop :=
  HypHigh W J l gain F E tau sg' muMaxM muMaxMu muMaxN →
  muMaxN ≤ muMaxM + Ga W J l gain tau + Fo W J l F - Ee W J l E
end
end Formalism.LFunctionChainParameters.UnitWeightPartition


