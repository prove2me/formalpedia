-- Prove2me | Definitions.Def_EFI1PRS_Uniform_Entropy
-- name    : EFI1PRS_Uniform_Entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:18.066817+00:00
-- url     : https://prove2.me/theorems/5bce6ae8-7c40-4845-b78a-5f6020a402c6
-- title:
--   Trace-one conditional min-entropy and purified-distance smoothing
-- statement:
--   For a bipartite operator $\zeta_{AB}$, conditional min-entropy is the extended-real supremum of all real $k$ for which some positive semidefinite trace-one $\sigma_B$ satisfies
--
--   $$\zeta_{AB}\le 2^{-k}I_A\otimes\sigma_B.$$
--
--   Smooth min-entropy takes the supremum over the entire purified-distance ball of subnormalized positive semidefinite states. The published generalized fidelity includes the missing-trace term. Its ball is reused without its separate radius restriction. In particular the zero state can have infinite min-entropy. Conditional von Neumann entropy is the published base-two entropy difference and may be negative. Binary entropy uses $0\log 0=0$, and the AEP penalty is $g(\delta)=-\log_2(1-\sqrt{1-\delta^2})$. The source requires trace-one reference states, so the published subnormalized-reference supremum is not reused without a bridge.
--
--   The conditional min-entropy and smooth min-entropy names are transparent aliases to the exact trace-one published definitions in `QAlgorithms_Papers_Independent_Information100_P67`. They introduce no duplicate supremum. The previously inspected P07 supremum has a different reference-state convention and is not substituted.
-- source:
--   Rishabh Batra, STOC 2027 submission #273 (October 2026), EFI ⇔ 1PRS, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/273.pdf, §2.3, pp.9–10

import Definitions.Def_EFI1PRS_Uniform_Primitives
import Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P07
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P67

/-! Batra, §2.3, pp.9–10. Trace-one conditional min-entropy and the full
purified-distance smoothing ball are reused from the compatible published definition.
Only transparent short-name aliases are introduced; no supremum is redeclared. -/
noncomputable section
namespace EFI1PRS.Uniform
open QAlgorithms
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
attribute [local instance] Classical.propDecidable Classical.decEq

/-- Full extended supremum. In particular, Hmin(0)=+infinity on a nonempty
conditioning register; no real-valued default supremum is used. -/
abbrev conditionalMin {A B : Type*} [Fintype A] [Fintype B]
    (ζ : Matrix (A × B) (A × B) ℂ) : EReal :=
  QAlgorithms.Papers.Independent.Information100.P67.conditionalMinEntropy ζ

abbrev smoothConditionalMin {A B : Type*} [Fintype A] [Fintype B]
    (ζ : Matrix (A × B) (A × B) ℂ) (δ : ℝ) : EReal :=
  QAlgorithms.Papers.Independent.Information100.P67.smoothConditionalMinEntropy ζ δ

def conditionalEntropy {A B : Type*} [Fintype A] [Fintype B]
    (ζ : Matrix (A × B) (A × B) ℂ) : ℝ :=
  QAlgorithms.Papers.Independent.Intakenext100.P07.conditionalVN ζ

def binaryEntropy (e : ℝ) : ℝ :=
  -(e * Real.logb 2 e) - (1-e) * Real.logb 2 (1-e)

def aepPenalty (δ : ℝ) : ℝ := -Real.logb 2 (1 - Real.sqrt (1-δ^2))

end EFI1PRS.Uniform


