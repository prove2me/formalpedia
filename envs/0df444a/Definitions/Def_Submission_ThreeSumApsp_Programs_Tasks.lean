-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Programs_Tasks
-- name    : Submission_ThreeSumApsp_Programs_Tasks
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:08:21.907693+00:00
-- url     : https://prove2.me/theorems/9066d41a-1b97-447d-8bea-f3063fc0e45d
-- title:
--   Tasks
-- statement:
--   Definitions and structural lemmas for Tasks, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Programs/Tasks.lean

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
set_option autoImplicit false
section
open ThreeSumApsp
namespace Light
open ThreeSumApsp.Spec
structure TriInst : Type where
  n : ℕ
  U : ℕ
  ab : ℕ
  bc : ℕ
  ac : ℕ
  AB : List ℤ
  BC : List ℤ
  AC : List ℤ
structure TriInst.Pre (x : TriInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenAB : x.AB.length = x.n * x.n
  lenBC : x.BC.length = x.n * x.n
  lenAC : x.AC.length = x.n * x.n
  segAB : Seg μ x.ab x.AB
  segBC : Seg μ x.bc x.BC
  segAC : Seg μ x.ac x.AC
  leAB : AbsLe x.AB x.U
  leBC : AbsLe x.BC x.U
  leAC : AbsLe x.AC x.U
  belowAB : x.ab + x.n * x.n ≤ fr
  belowBC : x.bc + x.n * x.n ≤ fr
  belowAC : x.ac + x.n * x.n ≤ fr
noncomputable def etTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasZeroTriangle ∧ Kept μ μ' fr
noncomputable def ntTask : Task where
  Inst := TriInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.ab, x.bc, x.ac]
  Pre := TriInst.Pre
  Post x μ fr r μ' := r = flag (triOf x.n x.AB x.BC x.AC).HasNegativeTriangle ∧ Kept μ μ' fr
structure VecInst : Type where
  N : ℕ
  U : ℕ
  a : ℕ
  X : List ℤ
structure VecInst.Pre (x : VecInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  U_pos : 1 ≤ x.U
  len : x.X.length = x.N
  seg : Seg μ x.a x.X
  le : AbsLe x.X x.U
  below : x.a + x.N ≤ fr
noncomputable def c3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (Convolution3SUM (vecOf x.N x.X)) ∧ Kept μ μ' fr
noncomputable def s3Task : Task where
  Inst := VecInst
  size x := x.N
  bound x := x.U
  args x := [x.N, x.U, x.a]
  Pre := VecInst.Pre
  Post x μ fr r μ' := r = flag (ThreeSum (vecOf x.N x.X)) ∧ Kept μ μ' fr
structure MatInst : Type where
  n : ℕ
  U : ℕ
  a : ℕ
  b : ℕ
  c : ℕ
  A : List ℤ
  B : List ℤ
structure MatInst.Pre (x : MatInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenA : x.A.length = x.n * x.n
  lenB : x.B.length = x.n * x.n
  segA : Seg μ x.a x.A
  segB : Seg μ x.b x.B
  leA : AbsLe x.A x.U
  leB : AbsLe x.B x.U
  belowA : x.a + x.n * x.n ≤ fr
  belowB : x.b + x.n * x.n ≤ fr
  belowC : x.c + x.n * x.n ≤ fr
  apartA : Apart x.a (x.n * x.n) x.c (x.n * x.n)
  apartB : Apart x.b (x.n * x.n) x.c (x.n * x.n)
def mpTask : Task where
  Inst := MatInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.a, x.b, x.c]
  Pre := MatInst.Pre
  Post x μ fr _ μ' := Seg μ' x.c (minPlusList x.n x.A x.B) ∧ KeptBut μ μ' fr x.c (x.n * x.n)
structure GraphInst : Type where
  n : ℕ
  U : ℕ
  adj : ℕ
  w : ℕ
  out : ℕ
  ADJ : List ℤ
  W : List ℤ
structure GraphInst.Pre (x : GraphInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  n_pos : 1 ≤ x.n
  U_pos : 1 ≤ x.U
  lenADJ : x.ADJ.length = x.n * x.n
  lenW : x.W.length = x.n * x.n
  segADJ : Seg μ x.adj x.ADJ
  segW : Seg μ x.w x.W
  zeroOne : ∀ e ∈ x.ADJ, e = 0 ∨ e = 1
  leW : AbsLe x.W x.U
  belowADJ : x.adj + x.n * x.n ≤ fr
  belowW : x.w + x.n * x.n ≤ fr
  belowOut : x.out + 2 * (x.n * x.n) ≤ fr
  apartADJ : Apart x.adj (x.n * x.n) x.out (2 * (x.n * x.n))
  apartW : Apart x.w (x.n * x.n) x.out (2 * (x.n * x.n))
  noNegativeCycle : NoNegativeCycle (graphOf x.n x.ADJ x.W)
def apTask : Task where
  Inst := GraphInst
  size x := x.n
  bound x := x.U
  args x := [x.n, x.U, x.adj, x.w, x.out]
  Pre := GraphInst.Pre
  Post x μ fr _ μ' :=
    (∃ dist : Fin x.n → Fin x.n → WithTop ℤ, IsDistanceMatrix (graphOf x.n x.ADJ x.W) dist ∧
    ∀ i j : Fin x.n,
      (dist i j = ⊤ → μ' (x.out + 2 * (i.val * x.n + j.val)) = 0) ∧
      ∀ z : ℤ, dist i j = (z : WithTop ℤ) →
        μ' (x.out + 2 * (i.val * x.n + j.val)) = 1 ∧
          μ' (x.out + 2 * (i.val * x.n + j.val) + 1) = z) ∧
    KeptBut μ μ' fr x.out (2 * (x.n * x.n))
structure ThinInst : Type where
  /-- The number of rows of `X` and of columns of `Y`. -/
  N : ℕ
  /-- The number of columns of `X` and of rows of `Y`. -/
  D : ℕ
  /-- The number of wanted positions. -/
  w : ℕ
  /-- The bound on the absolute values of the entries. -/
  U : ℕ
  /-- The address of `X`. -/
  x : ℕ
  /-- The address of `Y`. -/
  y : ℕ
  /-- The address of `WI`. -/
  wi : ℕ
  /-- The address of `WJ`. -/
  wj : ℕ
  /-- The address of the answers. -/
  out : ℕ
  /-- The first matrix, row by row. -/
  X : List ℤ
  /-- The second matrix, row by row. -/
  Y : List ℤ
  /-- The rows of the wanted positions. -/
  WI : List ℕ
  /-- The columns of the wanted positions. -/
  WJ : List ℕ
structure ThinInst.Pre (x : ThinInst) (μ : ℕ → ℤ) (fr : ℕ) : Prop where
  N_pos : 1 ≤ x.N
  D_pos : 1 ≤ x.D
  U_pos : 1 ≤ x.U
  lenX : x.X.length = x.N * x.D
  lenY : x.Y.length = x.D * x.N
  lenWI : x.WI.length = x.w
  lenWJ : x.WJ.length = x.w
  segX : Seg μ x.x x.X
  segY : Seg μ x.y x.Y
  segWI : SegN μ x.wi x.WI
  segWJ : SegN μ x.wj x.WJ
  leX : AbsLe x.X x.U
  leY : AbsLe x.Y x.U
  ltWI : ∀ i ∈ x.WI, i < x.N
  ltWJ : ∀ j ∈ x.WJ, j < x.N
  nodup : (x.WI.zip x.WJ).Nodup
  belowX : x.x + x.N * x.D ≤ fr
  belowY : x.y + x.D * x.N ≤ fr
  belowWI : x.wi + x.w ≤ fr
  belowWJ : x.wj + x.w ≤ fr
  belowOut : x.out + x.w ≤ fr
  apartX : Apart x.out x.w x.x (x.N * x.D)
  apartY : Apart x.out x.w x.y (x.D * x.N)
  apartWI : Apart x.out x.w x.wi x.w
  apartWJ : Apart x.out x.w x.wj x.w
namespace ThinArg
abbrev Rows : ℕ := 0
abbrev Cols : ℕ := 1
abbrev Wanted : ℕ := 2
abbrev Bound : ℕ := 3
abbrev AdrX : ℕ := 4
abbrev AdrY : ℕ := 5
abbrev AdrWI : ℕ := 6
abbrev AdrWJ : ℕ := 7
abbrev AdrOut : ℕ := 8
abbrev Free : ℕ := 9
end ThinArg
def ThinInst.ZeroOne (x : ThinInst) : Prop := (∀ v ∈ x.X, v = 0 ∨ v = 1) ∧ ∀ v ∈ x.Y, v = 0 ∨ v = 1
def thinEntry (N D : ℕ) (X Y : List ℤ) (I J : ℕ) : ℤ :=
  ((List.range D).map fun k => X.getD (I * D + k) 0 * Y.getD (k * N + J) 0).sum
def thinOut (N D : ℕ) (X Y : List ℤ) (WI WJ : List ℕ) : List ℤ :=
  (WI.zip WJ).map fun q => thinEntry N D X Y q.1 q.2
def thinTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w, x.U]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre := ThinInst.Pre
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w
def lopCountTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' := Seg μ' x.out (thinOut x.N x.D x.X x.Y x.WI x.WJ) ∧ KeptBut μ μ' fr x.out x.w
def lopDetectTask : TaskN where
  Inst := ThinInst
  pars x := [x.N, x.D, x.w]
  args x := [x.N, x.D, x.w, x.U, x.x, x.y, x.wi, x.wj, x.out]
  Pre x μ fr := x.Pre μ fr ∧ x.ZeroOne ∧ x.U = 1
  Post x μ fr _ μ' :=
    Seg μ' x.out ((thinOut x.N x.D x.X x.Y x.WI x.WJ).map fun v => if v = 0 then 0 else 1) ∧
      KeptBut μ μ' fr x.out x.w
def ThinSolvedIn (T : ℕ → ℕ → ℕ → ℝ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN thinTask P p Tn need ∧
    ∀ (N D w w' U : ℕ) (u : ℝ), 1 ≤ N → 1 ≤ D → 1 ≤ U → w ≤ w' → (U : ℝ) ≤ u →
      (Tn [N, D, w, U] : ℝ) ≤ T N D w' u
def LopSolvedIn (task : TaskN) (T : ℕ → ℕ → ℕ → ℝ) : Prop :=
  ∃ (P : Program) (p : ℕ) (Tn : List ℕ → ℕ) (need : List ℕ → Need), PolyNeedN need ∧
    SolvesN task P p Tn need ∧
    ∀ (n D w w' : ℕ), 1 ≤ n → 1 ≤ D → w ≤ w' → (Tn [n, D, w] : ℝ) ≤ T n D w'
end Light


