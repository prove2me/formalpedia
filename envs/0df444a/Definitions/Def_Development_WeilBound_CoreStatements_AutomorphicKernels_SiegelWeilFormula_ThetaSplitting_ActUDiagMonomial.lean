-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_SiegelWeilFormula_ThetaSplitting_ActUDiagMonomial
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:00:16.417941+00:00
-- url     : https://prove2.me/theorems/84901b45-1d4d-40d9-86d2-75edb64f31a8
-- title:
--   Act UDiag Monomial
-- statement:
--   Definitions and structural lemmas for Act UDiag Monomial, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/SiegelWeilFormula/ThetaSplitting/ActUDiagMonomial.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_NullSec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix
namespace PositivityTheory.SiegelWeilFormula.KSplit
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
def actU (u : Matrix (Fin m) (Fin m) ℂ) : PX m n →ₐ[ℂ] PX m n :=
  aeval fun k =>
    if k.2.2 then ∑ c, C (star (u k.1 c)) * X (c, k.2.1, true) else ∑ c, C (u k.1 c) * X (c, k.2.1, false)
def lf (b : Bool) (M : Matrix (Fin m) (Fin m) ℂ) (a : Fin m) (i : Fin n) : PX m n := ∑ c, C (M a c) * X (c, i, b)
def am (b : Bool) (u : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ := if b then u.map star else u
def dm (b : Bool) (Y : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ := if b then -Yᵀ else Y
def dY (Y : Matrix (Fin m) (Fin m) ℂ) : Derivation ℂ (PX m n) (PX m n) :=
  MvPolynomial.mkDerivation ℂ fun k => lf k.2.2 (dm k.2.2 Y) k.1 k.2.1
def chg (a : Fin m) (s : Fin m × Fin n × Bool →₀ ℕ) : ℤ :=
  s.sum fun k e => if k.1 = a then (if k.2.2 then -(e : ℤ) else e) else 0
end PositivityTheory.SiegelWeilFormula.KSplit
end


