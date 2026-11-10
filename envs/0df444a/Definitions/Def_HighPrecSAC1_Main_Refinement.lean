-- Prove2me | Definitions.Def_HighPrecSAC1_Main_Refinement
-- name    : HighPrecSAC1_Main_Refinement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:27:34.277195+00:00
-- url     : https://prove2.me/theorems/cfbd1205-6629-4395-956b-427bd11bc873
-- title:
--   Initialization, invariants and exact simultaneous refinement
-- statement:
--   The state consists of y,r,R,E. Invariants (6.3) use explicit entrywise order. All six operations of (6.4) are defined, as are their iteration, the least round count in (6.5), H, alpha0 and beta0. The initialization uses the prepared b-hat, an arbitrary lower geometric-inverse approximation with the precision supplied by Lemma 3.2, and the exact residual formulas. Sets of entries enumerate the state and every array materialized in a step; no contraction or residual positivity conclusion is built into the initial approximation predicate.
-- source:
--   Cheng, Huang and Wu (2026), arXiv:2610.25623 (preprint; held version, version number not printed in the PDF, sha256 8c9ac662…), Definitions and constructions, §§2, 3, 6, 7, printed p. 29 (PDF 30)

import Definitions.Def_HighPrecSAC1_Main_Preparation

open scoped BigOperators Matrix

namespace HighPrecSAC1.Main

structure RefState (K m : ℕ) where
  y : GVec K m
  r : GVec K m
  R : GMat K m
  E : GMat K m

noncomputable def Invariants {K m : ℕ} (S : LayerSystem K m) (T : RefState K m) : Prop :=
  0 ≤ T.y ∧ T.y ≤ S.exact ∧ T.r = S.global T.y - T.y ∧ 0 ≤ T.r ∧
  EntryLE 0 T.R ∧ T.E = 1 - (1 - S.jac T.y) * T.R ∧ EntryLE 0 T.E

noncomputable def stepS {K m : ℕ} (T : RefState K m) : GVec K m := T.R.mulVec T.r
noncomputable def stepB {K m : ℕ} (S : LayerSystem K m) (T : RefState K m) : GMat K m :=
  T.E + S.dQuad (stepS T) * T.R

/-- All six exact operations in (6.4). -/
noncomputable def refine {K m : ℕ} (S : LayerSystem K m) (T : RefState K m) : RefState K m :=
  ⟨T.y + stepS T, T.E.mulVec T.r + S.quad (stepS T),
    T.R + T.R * stepB S T, (stepB S T)^2⟩

noncomputable def rounds {K m : ℕ} (S : LayerSystem K m) (T : RefState K m) (q : ℕ) : RefState K m :=
  (refine S)^[q] T

noncomputable def H (K : ℕ) : ℝ := (2:ℝ)^(K+1)-1
noncomputable def alpha0 (K : ℕ) : ℝ := 2*(4:ℝ)^K*eta K
noncomputable def beta0 (K : ℕ) : ℝ := (K+1)*eta K*H K

/-- The least round count in (6.5); the set is nonempty for every K,t. -/
noncomputable def roundCount (K t : ℕ) : ℕ :=
  Nat.find (show ∃ j : ℕ, t+4 ≤ (2*K+13)*2^j from
    ⟨t+4, by have h := (Nat.lt_two_pow_self : t+4 < 2^(t+4)); nlinarith⟩)

noncomputable def initialY {K m : ℕ} (b : GVec K m) : GVec K m :=
  fun v => if v.1.val = 0 then b v else (1-(4:ℝ)^v.1.val*eta K)*b v

noncomputable def geometricInverse {K m : ℕ} (S : LayerSystem K m) (y : GVec K m) : GMat K m :=
  ∑ j ∈ Finset.range (K+1), (1-eta K)^j • (S.jac y)^j

noncomputable def initialState {K m : ℕ} (S : LayerSystem K m) (b : GVec K m)
    (R : GMat K m) : RefState K m :=
  let y := initialY b
  ⟨y, S.global y - y, R, 1-(1-S.jac y)*R⟩

/-- The evaluator output is allowed to be any approximation with the stated precision.
    The single constant c is fixed for a whole family. -/
noncomputable def InitialR {K m : ℕ} (S : LayerSystem K m) (b : GVec K m)
    (c : ℕ) (R : GMat K m) : Prop :=
  let G := geometricInverse S (initialY b)
  EntryLE ((1-eta K) • G) R ∧ EntryLE R G ∧
  ∀ v w, HasPrecision (tau K + c*(Nat.log 2 (K+2)+1) + 9) (R v w)

noncomputable def stateEntries {K m : ℕ} (T : RefState K m) : Set ℝ :=
  Set.range T.y ∪ Set.range T.r ∪ Set.range (fun v : Coord K m × Coord K m => T.R v.1 v.2) ∪
    Set.range (fun v : Coord K m × Coord K m => T.E v.1 v.2)

/-- Entries of the arrays materialized by (6.4), including its named intermediates. -/
noncomputable def stepEntries {K m : ℕ} (S : LayerSystem K m) (T : RefState K m) : Set ℝ :=
  stateEntries T ∪ stateEntries (refine S T) ∪ Set.range (stepS T) ∪
  Set.range (S.quad (stepS T)) ∪ Set.range (T.E.mulVec T.r) ∪
  Set.range (fun v : Coord K m × Coord K m => S.dQuad (stepS T) v.1 v.2) ∪
  Set.range (fun v : Coord K m × Coord K m => (S.dQuad (stepS T) * T.R) v.1 v.2) ∪
  Set.range (fun v : Coord K m × Coord K m => stepB S T v.1 v.2) ∪
  Set.range (fun v : Coord K m × Coord K m => (T.R * stepB S T) v.1 v.2)

end HighPrecSAC1.Main


