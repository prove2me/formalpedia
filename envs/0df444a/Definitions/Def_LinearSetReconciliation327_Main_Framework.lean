-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_Framework
-- name    : LinearSetReconciliation327_Main_Framework
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:30.191859+00:00
-- url     : https://prove2.me/theorems/2fdf0465-2ebe-482d-b9b2-8844fabf0dc7
-- title:
--   §§3.1, 4.2 — row schemes, exact execution, sketch trees, real decoder
-- statement:
--   A `RowScheme` is a node's rows: universe $N$, $m$ rows, $\ell$ columns, per-row randomness, the linear row code, the prediction from a recovered prefix ($\bot$ is `none`) and the final recovery. A node's own randomness is a permutation of $[N]$ and the row coins. Definition 4.7's execution with exact child answers gives each worker the true row transcript, and derives $U_s$ (workers returning $\bot$), $V_s$ (incorrect predictions), the child's input $C_s(x)+P_s$, its hint $J_s$, the estimate $\hat x$ and $Z=\|x+\hat x\|_0$. `decodeColumn` is Algorithm 1's manager on real feedback. `CRFamily` is a matrix family and decoder with its recovery property as a separate predicate. `Node` is a tree of direct-storage, CR-only, direct and recursive nodes with independent seeds at each node; `sketch` is the stored vector and `decode` the real decoder. `Valid` is Problem 3.1's condition (3). `AllBounds` is the capacity bounds at every node along the exact execution, `BoundsProb` the per-node failure bound over that node's own randomness, and `boundCount` the number $Q$ of bounds.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), §3.1 and Definition 4.7, PDF p.11–12, 17 (printed p.10–11, 16)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

noncomputable section

namespace LinearSetReconciliation327.Main

/-! The general framework of §3.1 and §4.2 (PDF pp.11–12, 16–17), for both the top layer and
HintSketch. Vectors are their supports (`Finset ℕ`), addition is symmetric difference. A row scheme
is the data of one node: a row code, its prediction rule and its final recovery. Nothing here
assumes any performance of those procedures. -/

/-- Rows of a node on universe `[N]`: `m` rows, `ℓ` columns, independent uniform row randomness
`Rand`, the binary linear row code, the prediction made from a recovered prefix (`none` is `⊥`), and
the final row recovery. The second argument of `predict` and `final` after the coins is the row-local
hint (empty at the top layer). -/
structure RowScheme where
  N : ℕ
  m : ℕ
  ℓ : ℕ
  Rand : Type
  [ft : Fintype Rand]
  [ne : Nonempty Rand]
  code : Fin m → Rand → Finset ℕ → Fin ℓ → ZMod 2
  code_linear : ∀ j r C C' s, code j r (symmDiff C C') s = code j r C s + code j r C' s
  predict : Fin m → Rand → Finset ℕ → List (ZMod 2) → Option (ZMod 2)
  final : Fin m → Rand → Finset ℕ → List (ZMod 2) → Finset ℕ

attribute [instance] RowScheme.ft RowScheme.ne

namespace RowScheme

variable (sch : RowScheme)

/-- A node's own randomness: the public uniform permutation of `[N]` and the row coins. -/
abbrev LocalSeed : Type := Equiv.Perm (Fin sch.N) × (Fin sch.m → sch.Rand)

/-- Row-local image in row `j`. -/
def rowOf (lr : sch.LocalSeed) (S : Finset ℕ) (j : Fin sch.m) : Finset ℕ :=
  rowImage sch.N sch.m lr.1 j.val S

/-- The first `a` codeword bits of the row support `S`. -/
def truePrefix (j : Fin sch.m) (r : sch.Rand) (S : Finset ℕ) (a : ℕ) : List (ZMod 2) :=
  ((List.finRange sch.ℓ).take a).map (sch.code j r S)

open Classical in
/-- Support, in `[m]`, of a predicate on rows. -/
def rowsWhere (P : Fin sch.m → Prop) : Finset ℕ := (univ.filter P).image (fun j => j.val)

/-- The true column `C_s(x)`, as a support in `[m]`. -/
def column (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ) : Finset ℕ :=
  sch.rowsWhere fun j => sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1

/-- Definition 4.7: the prediction `q_{j,s}` of worker `j` in the execution with exact child answers,
in which its prefix is the true row transcript. -/
def exactPred (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) (j : Fin sch.m) :
    Option (ZMod 2) :=
  sch.predict j (lr.2 j) (sch.rowOf lr J j)
    (sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) s.val)

/-- `J_s`: the rows returning `⊥` in the exact execution. -/
def exactHint (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) : Finset ℕ :=
  sch.rowsWhere fun j => sch.exactPred lr x J s j = none

/-- `P_s`: the predicted bits in the exact execution, with `⊥` replaced by `0`. -/
def exactP (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) : Finset ℕ :=
  sch.rowsWhere fun j => sch.exactPred lr x J s j = some 1

/-- The child's input `C_s(x) + P_s` in the exact execution. -/
def exactChildInput (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) : Finset ℕ :=
  symmDiff (sch.column lr x s) (sch.exactP lr x J s)

open Classical in
/-- `U_s`: the number of workers returning `⊥` in column `s`, Definition 4.7. -/
def U (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) : ℕ :=
  (univ.filter fun j => sch.exactPred lr x J s j = none).card

open Classical in
/-- `V_s`: the number of incorrect predictions in column `s`, Definition 4.7. -/
def V (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) : ℕ :=
  (univ.filter fun j => ∃ b, sch.exactPred lr x J s j = some b ∧
    b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s).card

/-- The final row estimate on prefixes `pref`, assembled in the original coordinates. -/
def assembled (lr : sch.LocalSeed) (J : Finset ℕ) (pref : Fin sch.m → List (ZMod 2)) : Finset ℕ :=
  assemble sch.N sch.m lr.1 fun p =>
    if h : p < sch.m then sch.final ⟨p, h⟩ (lr.2 ⟨p, h⟩) (sch.rowOf lr J ⟨p, h⟩) (pref ⟨p, h⟩)
    else ∅

/-- The final row estimate `x̂_j` of the exact execution. -/
def exactRowEst (lr : sch.LocalSeed) (x J : Finset ℕ) (j : Fin sch.m) : Finset ℕ :=
  sch.final j (lr.2 j) (sch.rowOf lr J j) (sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ)

/-- `x̂` of the exact execution. -/
def exactEstimate (lr : sch.LocalSeed) (x J : Finset ℕ) : Finset ℕ :=
  sch.assembled lr J fun j => sch.truePrefix j (lr.2 j) (sch.rowOf lr x j) sch.ℓ

/-- `Z = ‖x + x̂‖₀`, Definition 4.7. -/
def Z (lr : sch.LocalSeed) (x J : Finset ℕ) : ℕ := (symmDiff x (sch.exactEstimate lr x J)).card

/-- One column of the real execution (Algorithm 1). From the prefixes the workers predict; `J_s` and
`P_s` go to the child call `childDec s P_s J_s`, which returns its estimate `D̂_s`, and `Ĉ_s = P_s + D̂_s`
is appended to the prefixes. A failed child call fails the node. -/
def decodeColumn (lr : sch.LocalSeed) (J : Finset ℕ)
    (childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ))
    (pref : Fin sch.m → List (ZMod 2)) (s : Fin sch.ℓ) : Option (Fin sch.m → List (ZMod 2)) :=
  let q : Fin sch.m → Option (ZMod 2) := fun j => sch.predict j (lr.2 j) (sch.rowOf lr J j) (pref j)
  let Ps := sch.rowsWhere fun j => q j = some 1
  let Js := sch.rowsWhere fun j => q j = none
  (childDec s Ps Js).map fun Dhat j =>
    pref j ++ [if j.val ∈ symmDiff Ps Dhat then 1 else 0]

/-- All columns of the real execution, in order. -/
def decodeColumns (lr : sch.LocalSeed) (J : Finset ℕ)
    (childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ)) :
    Option (Fin sch.m → List (ZMod 2)) :=
  (List.finRange sch.ℓ).foldlM (sch.decodeColumn lr J childDec) (fun _ => [])

end RowScheme

/-- A sparse-recovery family in the shape of Proposition 2.3: a fixed binary matrix `CR_{N,t}` given
by its number of rows and the rows hit by each coordinate, and a decoder of its syndromes. Its
properties are not part of this structure; `CRFamily.Recovers` states the recovery property. -/
structure CRFamily where
  rows : ℕ → ℕ → ℕ
  col : ℕ → ℕ → ℕ → Finset ℕ
  dec : ℕ → ℕ → Finset ℕ → Option (Finset ℕ)

open Classical in
/-- The syndrome `CR_{N,t} x`, as the support of the XOR of the columns of `x`. -/
def CRFamily.sketch (CR : CRFamily) (N t : ℕ) (x : Finset ℕ) : Finset ℕ :=
  (range (CR.rows N t)).filter fun r => Odd (x.filter fun i => r ∈ CR.col N t i).card

/-- Every `x ∈ S_{N,t}` is recovered from `CR_{N,t} x`. -/
def CRFamily.Recovers (CR : CRFamily) : Prop :=
  ∀ N t : ℕ, t ≤ N → ∀ x : Finset ℕ, x ⊆ range N → x.card ≤ t →
    CR.dec N t (CR.sketch N t x) = some x

/-- A sketch tree: direct storage of `x`; a CR-only leaf `CR_{N,t}`; a direct node storing all columns
and `CR_{N,t} x`; a recursive node sketching each column by a child with capacities `(X s, Y s)` and
storing `CR_{N,t} x`. -/
inductive Node : Type 1 where
  | store (N : ℕ)
  | cr (N t : ℕ)
  | direct (sch : RowScheme) (t : ℕ)
  | recursive (sch : RowScheme) (t : ℕ) (X Y : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node)

namespace Node

/-- The universe of a node. -/
def N : Node → ℕ
  | .store N => N
  | .cr N _ => N
  | .direct sch _ => sch.N
  | .recursive sch _ _ _ _ => sch.N

/-- A public seed of a tree: each node's fresh randomness, independently of all others. -/
def Seed : Node → Type
  | .store _ => Unit
  | .cr _ _ => Unit
  | .direct sch _ => sch.LocalSeed
  | .recursive sch _ _ _ child => sch.LocalSeed × ∀ s, Seed (child s)

/-- Seeds of a tree form a finite type. -/
@[instance_reducible] def seedFintype : (T : Node) → Fintype (Seed T)
  | .store _ => inferInstanceAs (Fintype Unit)
  | .cr _ _ => inferInstanceAs (Fintype Unit)
  | .direct sch _ => inferInstanceAs (Fintype sch.LocalSeed)
  | .recursive sch _ _ _ child =>
      have : ∀ s, Fintype (Seed (child s)) := fun s => seedFintype (child s)
      inferInstanceAs (Fintype (sch.LocalSeed × ∀ s, Seed (child s)))

instance (T : Node) : Fintype (Seed T) := seedFintype T

/-- The stored vector of a tree. -/
def Syn : Node → Type
  | .store _ => Finset ℕ
  | .cr _ _ => Finset ℕ
  | .direct sch _ => (Fin sch.ℓ → Finset ℕ) × Finset ℕ
  | .recursive sch _ _ _ child => (∀ s, Syn (child s)) × Finset ℕ

/-- Addition of stored vectors. -/
def synAdd : (T : Node) → Syn T → Syn T → Syn T
  | .store _, a, b => symmDiff (α := Finset ℕ) a b
  | .cr _ _, a, b => symmDiff (α := Finset ℕ) a b
  | .direct _ _, a, b => (fun s => symmDiff (a.1 s) (b.1 s), symmDiff a.2 b.2)
  | .recursive _ _ _ _ child, a, b =>
      (fun s => synAdd (child s) (a.1 s) (b.1 s), symmDiff a.2 b.2)

/-- The sketch of `x`. The map is binary linear: columns are linear in `x`. -/
def sketch (CR : CRFamily) : (T : Node) → Seed T → Finset ℕ → Syn T
  | .store _, _, x => x
  | .cr N t, _, x => CR.sketch N t x
  | .direct sch t, r, x => (fun s => sch.column r x s, CR.sketch sch.N t x)
  | .recursive sch t _ _ child, r, x =>
      (fun s => sketch CR (child s) (r.2 s) (sch.column r.1 x s), CR.sketch sch.N t x)

/-- Residual correction at a node (Algorithm 1): decode `a + CR x̂` and add the residual to `x̂`. -/
def residual (CR : CRFamily) (N t : ℕ) (a xhat : Finset ℕ) : Option (Finset ℕ) :=
  (CR.dec N t (symmDiff a (CR.sketch N t xhat))).map fun e => symmDiff xhat e

/-- The real decoder of a tree, from the stored vector and the hint (Algorithm 1). -/
def decode (CR : CRFamily) : (T : Node) → Seed T → Syn T → Finset ℕ → Option (Finset ℕ)
  | .store _, _, y, _ => some y
  | .cr N t, _, y, _ => CR.dec N t y
  | .direct sch t, r, y, J =>
      let pref : Fin sch.m → List (ZMod 2) := fun j =>
        (List.finRange sch.ℓ).map fun s => if j.val ∈ y.1 s then 1 else 0
      residual CR sch.N t y.2 (sch.assembled r J pref)
  | .recursive sch t _ _ child, r, y, J =>
      let childDec : Fin sch.ℓ → Finset ℕ → Finset ℕ → Option (Finset ℕ) := fun s Ps Js =>
        decode CR (child s) (r.2 s)
          (synAdd (child s) (y.1 s) (sketch CR (child s) (r.2 s) Ps)) Js
      (sch.decodeColumns r.1 J childDec).bind fun pref =>
        residual CR sch.N t y.2 (sch.assembled r.1 J pref)

/-- Problem 3.1: `x, J ⊆ [N]`, `|J| ≤ X`, `|supp(x) \ J| ≤ Y`. -/
def Valid (N X Y : ℕ) (x J : Finset ℕ) : Prop :=
  x ⊆ range N ∧ J ⊆ range N ∧ J.card ≤ X ∧ (x \ J).card ≤ Y

/-- A tree is well formed for capacities `(X, Y)` of its root: CR capacities do not exceed the
universe, a CR leaf corrects `min(N, X+Y)` errors, each child has universe `m` with its capacities. -/
def WF : Node → ℕ → ℕ → Prop
  | .store _, _, _ => True
  | .cr N t, X, Y => t ≤ N ∧ min N (X + Y) ≤ t
  | .direct sch t, _, _ => t ≤ sch.N
  | .recursive sch t Xs Ys child, _, _ =>
      t ≤ sch.N ∧ ∀ s, (child s).N = sch.m ∧ WF (child s) (Xs s) (Ys s)

/-- The bounds `U_s ≤ X_s`, `V_s ≤ Y_s`, `Z ≤ t` hold at every node of the exact execution below `x, J`:
the child of column `s` receives the exact input `C_s(x) + P_s` and hint `J_s`. -/
def AllBounds : (T : Node) → Seed T → Finset ℕ → Finset ℕ → Prop
  | .store _, _, _, _ => True
  | .cr _ _, _, _, _ => True
  | .direct sch t, r, x, J => sch.Z r x J ≤ t
  | .recursive sch t Xs Ys child, r, x, J =>
      sch.Z r.1 x J ≤ t ∧ ∀ s, sch.U r.1 x J s ≤ Xs s ∧ sch.V r.1 x J s ≤ Ys s ∧
        AllBounds (child s) (r.2 s) (sch.exactChildInput r.1 x J s) (sch.exactHint r.1 x J s)

/-- Each bound at each node fails with probability at most `δ` over that node's own randomness, for
every input and hint valid at that node. -/
def BoundsProb (δ : ℝ) : Node → ℕ → ℕ → Prop
  | .store _, _, _ => True
  | .cr _ _, _, _ => True
  | .direct sch t, X, Y =>
      ∀ x J, Valid sch.N X Y x J → prU (fun lr : sch.LocalSeed => t < sch.Z lr x J) ≤ δ
  | .recursive sch t Xs Ys child, X, Y =>
      (∀ x J, Valid sch.N X Y x J →
        prU (fun lr : sch.LocalSeed => t < sch.Z lr x J) ≤ δ ∧
        ∀ s, prU (fun lr : sch.LocalSeed => Xs s < sch.U lr x J s) ≤ δ ∧
          prU (fun lr : sch.LocalSeed => Ys s < sch.V lr x J s) ≤ δ) ∧
      ∀ s, BoundsProb δ (child s) (Xs s) (Ys s)

/-- `Q`: the total number of the bounds in the tree. -/
def boundCount : Node → ℕ
  | .store _ => 0
  | .cr _ _ => 0
  | .direct _ _ => 1
  | .recursive sch _ _ _ child => 2 * sch.ℓ + 1 + ∑ s, boundCount (child s)

/-- Number of levels of a tree. -/
def depth : Node → ℕ
  | .store _ => 1
  | .cr _ _ => 1
  | .direct _ _ => 1
  | .recursive _ _ _ _ child => 1 + (univ.sup fun s => depth (child s))

/-- Number of recursive nodes. -/
def recursiveCount : Node → ℕ
  | .store _ => 0
  | .cr _ _ => 0
  | .direct _ _ => 0
  | .recursive _ _ _ _ child => 1 + ∑ s, recursiveCount (child s)

/-- Number of all nodes. -/
def nodeCount : Node → ℕ
  | .store _ => 1
  | .cr _ _ => 1
  | .direct _ _ => 1
  | .recursive _ _ _ _ child => 1 + ∑ s, nodeCount (child s)

end Node

end LinearSetReconciliation327.Main


