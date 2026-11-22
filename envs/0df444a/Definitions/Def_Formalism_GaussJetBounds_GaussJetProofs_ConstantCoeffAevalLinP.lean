-- Prove2me | Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
-- name    : Formalism_GaussJetBounds_GaussJetProofs_ConstantCoeffAevalLinP
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:00:43.311488+00:00
-- url     : https://prove2.me/theorems/96eacda8-0006-4d3c-a91e-d74c1eff1140
-- title:
--   Constant Coeff Aeval Lin P
-- statement:
--   Definitions and structural lemmas for Constant Coeff Aeval Lin P, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/ConstantCoeffAevalLinP.lean

import Definitions.Def_Formalism_GaussJetBounds_StatementJ
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_ThmAOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
namespace Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
section JetPair
variable {K : Type u} [Field K] {ι : Type}
end JetPair
section Chain
variable {K : Type u} [Field K] {ι ι' : Type} [Fintype ι] [Fintype ι']
def linP (A : ι → ι' → K) (j : ι') : MvPolynomial ι K :=
  ∑ i : ι, MvPolynomial.C (A i j) * MvPolynomial.X i
def linP' (A : ι → ι' → K) (i : ι) : MvPolynomial ι' K :=
  ∑ j : ι', MvPolynomial.C (A i j) * MvPolynomial.X j
end Chain
section Frames
def genA {K : Type u} [Field K] {d N0 N1 : ℕ} (TT : Finset (ZMod d))
    (T : ZMod d → Fin N0 → Fin N0 → K) : ZV d N0 N1 → ZV d N0 N1 → K :=
  fun y y' => if y'.1 = y.1 ∧ y'.2.2 = y.2.2 then effMat TT T y.1 y.2.1 y'.2.1 else 0
end Frames
end Formalism.DworkPowerSeriesWeights


