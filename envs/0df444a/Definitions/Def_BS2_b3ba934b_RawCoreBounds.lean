-- Prove2me | Definitions.Def_BS2_b3ba934b_RawCoreBounds
-- name    : BS2_b3ba934b_RawCoreBounds
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T15:58:49.02929+00:00
-- url     : https://prove2.me/theorems/6c341fb2-0962-4fd5-a41c-9593d6489578
-- title:
--   Sensitivity separation: RawCoreBounds (complete source module)
-- statement:
--   Complete Lean source module `RawCoreBounds` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/RawCoreBounds.lean; original SHA-256 a99e16f6e0a2bece377c01369b3d4d5873e0dc3265b379477a6488b49f767640; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

/- Numeric upper-bound composition using already certified raw A/M/P entries. -/
import Definitions.Def_BS2_b3ba934b_Q2FastEvaluator

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


theorem pCore_mono (n : ℕ) (v : Profile n) (caps : Caps) (j k l : Entry) :
    Monotone (pCore n v caps j k l) := by
  intro a b hab
  unfold pCore
  split_ifs <;> first | exact le_rfl | exact hab |
    exact min_le_min (min_le_min hab le_rfl) le_rfl

theorem dCore_mono (n degree : ℕ) (v : Profile n) (i j k l : Entry) :
    Monotone (dCore n degree v i j k l) := by
  intro a b hab
  unfold dCore
  split_ifs <;> first | exact hab | exact min_le_min hab le_rfl

theorem rawPFast_core (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (j k l : Entry) : rawPFast n degree v caps records j k l=
      pCore n v caps j k l (rawAFast n v caps records k l) := rfl

theorem rawDFast_core (n degree : ℕ) (v : Profile n) (caps : Caps) (records : List (List ℕ))
    (i j k l : Entry) : rawDFast n degree v caps records i j k l=
      dCore n degree v i j k l
        ((rawMExpr n degree i j k).eval v+rawPFast n degree v caps records j k l) := rfl

theorem rawP_bound_from_A (n degree : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (j k l : Entry) (av pv : ℕ)
    (ha : (rawAExpr n caps records k l).eval v≤av)
    (hp : pCore n v caps j k l av≤pv) :
    (rawPExpr n degree caps records j k l).eval v≤pv := by
  rw [← rawPFast_eq,rawPFast_core]
  apply (pCore_mono n v caps j k l _).trans hp
  simpa only [rawAFast_eq] using ha

theorem rawD_bound_from_MP (n degree : ℕ) (v : Profile n) (caps : Caps)
    (records : List (List ℕ)) (i j k l : Entry) (mv pv dv : ℕ)
    (hm : (rawMExpr n degree i j k).eval v≤ mv)
    (hp : (rawPExpr n degree caps records j k l).eval v≤pv)
    (hd : dCore n degree v i j k l (mv+pv)≤dv) :
    (rawDExpr n degree caps records i j k l).eval v≤dv := by
  rw [← rawDFast_eq,rawDFast_core]
  apply (dCore_mono n degree v i j k l _).trans hd
  apply Nat.add_le_add hm
  simpa only [rawPFast_eq] using hp

end ThreeBoundNumeric

#print axioms ThreeBoundNumeric.rawD_bound_from_MP


