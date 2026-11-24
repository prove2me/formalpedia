-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ThetaOperatorCommutation_RealTh
-- name    : Formalism_LocalToGlobal_ThetaOperatorCommutation_RealTh
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:49.080397+00:00
-- url     : https://prove2.me/theorems/d8349a15-4495-4592-9704-63dd007a6cf5
-- title:
--   Real Th
-- statement:
--   Definitions and structural lemmas for Real Th, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ThetaOperatorCommutation/RealTh.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_JointShape
import Definitions.Def_ReciprocityTheory_ThetaSummability_RealCoinvariants_CoinvSubLeComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action ReciprocityTheory.ThetaSummability.Real
namespace ReciprocityTheory.ChartRestriction.G.ThK.Real
variable {p q r s : ℕ}
def chiTr (c : ℂ) (Z : Mat p q) : ℂ := c * Z.trace
def KCMat (p q : ℕ) : Type := {Z : Mat p q // IsKC Z}
def act1 (p q r s : ℕ) (Z : Mat p q) : Module.End ℂ (Pol p q r s) := fockAct1 p q r s Z
def polChi (p q r s : ℕ) (c : ℂ) : Submodule ℂ (Pol p q r s) :=
  jointEig (fun Z : KCMat p q => fockAct1 p q r s Z.1) (fun Z => chiTr c Z.1)
def jHarm (p q r s : ℕ) : Submodule ℂ (Pol p q r s) := Submodule.span ℂ (Jset p q r s)
abbrev ThC (p q r s : ℕ) (c : ℂ) := Coinv (act1 p q r s) (chiTr c)
def thMkC (p q r s : ℕ) (c : ℂ) : Pol p q r s →ₗ[ℂ] ThC p q r s c :=
  (coinvSub (act1 p q r s) (chiTr c)).mkQ
end ReciprocityTheory.ChartRestriction.G.ThK.Real


