-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
-- name    : Development_WeilBound_ThetaLifts_EigenvalueEndgame_CuspidalAverages_FirstIdempotentAdjointThird
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:00.587688+00:00
-- url     : https://prove2.me/theorems/035c9a93-c01a-461e-8568-dbdb978d9a9e
-- title:
--   First Idempotent Adjoint Third
-- statement:
--   Definitions and structural lemmas for First Idempotent Adjoint Third, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/EigenvalueEndgame/CuspidalAverages/FirstIdempotentAdjointThird.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace PositivityTheory.ThKEnd.Cusp
open Matrix
variable {R n ι : Type} [CommRing R] [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {c : R →+* R}
  {J x y x' y' : Matrix n n R} {u u' : Matrix n ι R}
def Adj (c : R →+* R) (J x y : Matrix n n R) : Prop := xᵀ * J = J * y.map c
structure Fr (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) : Prop where
  cc : ∀ r, c (c r) = r
  sk : (J.map c)ᵀ = -J
  uu : uᵀ * J * u.map c = 0
  vv : u'ᵀ * J * u'.map c = 0
  uv : uᵀ * J * u'.map c = 1
def row (c : R →+* R) (J : Matrix n n R) (u : Matrix n ι R) : Matrix ι n R := (J * u.map c)ᵀ
namespace Fr
variable (h : Fr c J u u')
include h
end Fr
def e1 (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) : Matrix n n R := u * row c J u'
def e3 (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) : Matrix n n R := -(u' * row c J u)
def lv (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) (g g' : Matrix ι ι R) : Matrix n n R :=
  1 + u * (g - 1) * row c J u' - u' * (g' - 1) * row c J u
def mid (c : R →+* R) (J : Matrix n n R) (u u' : Matrix n ι R) (s : Matrix n n R) : Matrix n n R :=
  e1 c J u u' + (1 - e1 c J u u' - e3 c J u u') * s * (1 - e1 c J u u' - e3 c J u u') + e3 c J u u'
namespace Fr
variable (h : Fr c J u u')
include h
end Fr
end PositivityTheory.ThKEnd.Cusp
end


