-- Prove2me | Definitions.Def_StackingStars_Main_Machine
-- name    : StackingStars_Main_Machine
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T23:44:34.266468+00:00
-- url     : https://prove2.me/theorems/c8491a35-76f2-40fe-b4f6-1fac021ad970
-- title:
--   Deterministic real-RAM runs: instance encoding, polynomial time N^k + k, and output decoding
-- statement:
--   The paper names no machine model, and its coordinates are real. An algorithm is a program of the published unit-cost real RAM `MatMulTimeLP.Program`, restricted by the published `FewInnerTSP.Admissible`. It has exact $+,-,\times,\div,\sqrt{\ }$ and comparisons on reals, index cells, rational literals only, no random draws, no floor and no real-to-index conversion, and one step per executed instruction. An admissible program never reads the random tape, so runs use the all-zero tape (`zeroTape`).
--
--   * Input (`polysInput P`): $R[0]=n$, then for each polygon $i=0,\dots,n-1$ in turn its number of vertices $m_i$ followed by the coordinates $x,y$ of its vertices (`vertsReals`). The size is $N=\sum_im_i$ (`totalVerts`).
--   * `groupInput r w P D` is the input of the one-size-group algorithm (Lemma 20): $r$, $w$, $n$, then per star its `vertsReals` followed by $q_P,R_P,L_P$.
--   * `RunsWithin A input T Out`: the run halts within $T$ steps (executed instructions plus the final `halt`, the published `haltTime` convention), and in the halted state the output $\mathrm{out}(j)=R[\text{input length}+j]$ satisfies `Out`.
--   * `polyBound k N` $=N^k+k$.
--   * Decoding: `blockTransl b out i` $=(\mathrm{out}(bi),\mathrm{out}(bi+1))$ is a translation. `blockPose b out i` $=(\mathrm{out}(bi),\dots,\mathrm{out}(bi+3))$ is a pose $(a,b,x,y)$. `outAxisRect out j` $=[\mathrm{out}(j),\mathrm{out}(j+2)]\times[\mathrm{out}(j+1),\mathrm{out}(j+3)]$.
-- source:
--   Abrahamsen, Conradi, Khan, Stade, Wong, Yan, Zhang, Stacking Stars: Minimum-Area Packing with and without Rotation, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2 (Theorem 1: polynomial-time algorithms), p. 3 (Theorem 5: O(N log N)-time, total complexity N)

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_PolygonPack_Pose
import Definitions.Def_StackingStars_Main_Geometry
import Definitions.Def_StackingStars_Main_StarPolygon
import Definitions.Def_StackingStars_Main_ReferenceData

namespace StackingStars.Main

open MatMulTimeLP

/-!
# The machine: instance encoding, running time, output decoding

Abrahamsen et al., *Stacking Stars*, STOC 2027 submission (manuscript sha256 ee9554eb…), p. 2
(PDF 4), Theorem 1: "polynomial-time […] algorithms"; p. 3 (PDF 5), Theorem 5: an
"O(N log N)-time algorithm" on polygons "of total complexity N". The paper names no machine model;
coordinates are real. Programs are those of the published unit-cost real RAM
`MatMulTimeLP.Program` (exact `+ − × ÷ √` and comparisons of reals, index cells, no floor, no
real-to-index conversion, one step per executed instruction), restricted by the published
`FewInnerTSP.Admissible` (rational literals only, no random draws). An admissible program never
reads the random tape, so runs use the all-zero tape.

Input layout (`polysInput`): `R[0] = n`, then for each polygon `i = 0, …, n − 1` in turn its number
of vertices `m_i` followed by the coordinates `x, y` of its vertices in order. The size of the
input is `N = Σ m_i`, the total number of vertices. The output is read from the real cells that
follow the input, `out j = R[input.length + j]`, in the state where the run halts.
-/

/-- The all-zero random tape (never read by an admissible program). -/
def zeroTape : Tape := fun _ => (0, 0)

/-- A vertex list as reals: `m, x₀, y₀, x₁, y₁, …`. -/
def vertsReals (V : List Pt) : List ℝ := (V.length : ℝ) :: V.flatMap fun z => [z.1, z.2]

/-- The encoding of a list of `n` polygons: `n`, then each polygon's `vertsReals` in order. -/
def polysInput {n : ℕ} (P : Fin n → List Pt) : List ℝ :=
  (n : ℝ) :: (List.finRange n).flatMap fun i => vertsReals (P i)

/-- The size `N = Σ_i m_i` of an instance: the total number of vertices. -/
def totalVerts {n : ℕ} (P : Fin n → List Pt) : ℕ := ∑ i, (P i).length

/-- The run of `A` on `input` halts within `T` steps (the executed instructions plus the final
`halt`, the published `haltTime` convention) in a state whose output `out` satisfies `Out`. -/
def RunsWithin (A : Program) (input : List ℝ) (T : ℝ) (Out : (ℕ → ℝ) → Prop) : Prop :=
  ∃ t : ℕ, IsHalted A (stateAt A input zeroTape t) ∧ (t : ℝ) + 1 ≤ T ∧
    Out fun j => (stateAt A input zeroTape t).R (input.length + j)

/-- The polynomial time bound `N^k + k`. -/
def polyBound (k N : ℕ) : ℝ := (N : ℝ) ^ k + k

/-- The input of a one-size-group algorithm (Lemma 20): `r`, `w`, then `n`, then for each star its
`vertsReals` followed by its reference data `q_P, R_P, L_P` (six reals). -/
def groupInput {n : ℕ} (r w : ℝ) (P : Fin n → List Pt) (D : ∀ i, RefData (region (P i))) :
    List ℝ :=
  r :: w :: (n : ℝ) :: (List.finRange n).flatMap fun i =>
    vertsReals (P i) ++ [(D i).q.1, (D i).q.2, (D i).R.1, (D i).R.2, (D i).L.1, (D i).L.2]

/-- Output in blocks of `b` reals per object: the translation of object `i` is the pair
`(out (b i), out (b i + 1))`. -/
def blockTransl (b : ℕ) (out : ℕ → ℝ) (i : ℕ) : Pt := (out (b * i), out (b * i + 1))

/-- Output in blocks of `b` reals per object: the pose `(a, b, x, y)` of object `i` is
`out (b i), …, out (b i + 3)`. -/
def blockPose (b : ℕ) (out : ℕ → ℝ) (i : ℕ) : PolygonPack.Pose :=
  ⟨out (b * i), out (b * i + 1), out (b * i + 2), out (b * i + 3)⟩

/-- The axis-aligned rectangle `[out j, out (j+2)] × [out (j+1), out (j+3)]` written at offset `j`. -/
def outAxisRect (out : ℕ → ℝ) (j : ℕ) : Set Pt :=
  Set.Icc (out j) (out (j + 2)) ×ˢ Set.Icc (out (j + 1)) (out (j + 3))

end StackingStars.Main


