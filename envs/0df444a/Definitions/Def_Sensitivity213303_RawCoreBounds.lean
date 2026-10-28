-- Prove2me | Definitions.Def_Sensitivity213303_RawCoreBounds
-- name    : Sensitivity213303_RawCoreBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-25T22:21:20.551318+00:00
-- url     : https://prove2.me/theorems/50973c3a-a76f-4d17-8e6a-538b5e5396d5
-- title:
--   Refined P and D cores with supplied auxiliary upper bounds
-- statement:
--   pCore and dCore evaluate the strict zero-tolerance refinements while taking an auxiliary upper bound as an explicit natural-number argument. For P this argument bounds the simpler upward transfer; for D it bounds the M-plus-P decomposition. Both formulas take the minimum with the applicable strict geometric alternatives. Their monotonicity and sound upper-bound composition theorems allow previously certified raw coordinates to be reused in later finite checks.
-- source:
--   Original Lean formalization for the Prove2Me block-sensitivity-versus-sensitivity campaign, module RawCoreBounds; source SHA256 a99e16f6e0a2bece377c01369b3d4d5873e0dc3265b379477a6488b49f767640.

/- Numeric upper-bound composition using already certified raw A/M/P entries. -/
import Definitions.Def_Sensitivity213303_FullProfileClosure
import Definitions.Def_Sensitivity213303_NumericExpressions
import Definitions.Def_Sensitivity213303_ProfileClosures
import Definitions.Def_Sensitivity213303_Q2FastEvaluator
import Definitions.Def_Sensitivity213303_Q2RawExpressions
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Finset.Union
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
namespace ThreeBoundFullProfile
end ThreeBoundFullProfile


set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace ThreeBoundNumeric
open ThreeBoundFullProfile

def pCore (n : ℕ) (v : Profile n) (caps : Caps)
    (j k l : Entry) (first : ℕ) : ℕ :=
  if j.same k then 0 else
    if j.tolerance=0 ∧ l.tolerance=0 then
      let cross := caps.pcross*(aExpr n j.guard l.t0).eval v
      let m₀ := (minusExpr n l.guard j.t0 k.t0).eval v
      let m₁ := (minusExpr n l.guard k.guard j.guard).eval v
      let z₁ := 2*(bExpr n l.guard j.t0).eval v+cross+
        max ((plusExpr n j.t0 k.t0 l.t0).eval v) m₁
      let target := if j.t0 < k.t0 then cross+maximum [2*m₀,
        m₀+(bExpr n l.guard k.t0).eval v,
        (unionExpr n l.guard j.t0 k.t0 l.t0).eval v+(bExpr n l.guard l.t0).eval v] else 0
      let guard := if k.guard < j.guard then cross+max (2*(bExpr n l.guard k.t0).eval v)
        (2*(bExpr n l.guard l.t0).eval v+m₁) else 0
      min (min first z₁) (max target guard)
    else first


def dCore (n degree : ℕ) (v : Profile n)
    (i j k l : Entry) (first : ℕ) : ℕ :=
  if j.tolerance=0 ∧ l.tolerance=0 then
    let strict := if j.same k then 0 else
      let bb := (bExpr n i.t0 l.t0).eval v
      let aa := (aExpr n l.guard i.guard).eval v
      maximum [(primitiveMExpr n degree i.t0 i.guard 0 j k).eval v,
        if j.t0 < k.t0 then bb+degree*aa+(unionExpr n i.t0 j.t0 k.t0 l.t0).eval v else 0,
        if k.guard < j.guard then 2*bb+(degree-1)*aa+
          (unionExpr n l.guard k.guard j.guard i.guard).eval v else 0]
    min first strict
  else first














end ThreeBoundNumeric


