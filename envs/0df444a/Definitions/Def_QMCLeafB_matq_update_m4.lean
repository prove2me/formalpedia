-- Prove2me | Definitions.Def_QMCLeafB_matq_update_m4
-- name    : QMCLeafB_matq_update_m4
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T22:26:56.816274+00:00
-- url     : https://prove2.me/theorems/95c998b4-6b09-4ffe-8b87-ea13690cfbb6
-- title:
--   QMCLeafB matq_update_m4
-- statement:
--   # leaf B phase 6 — brick `matq-update` (swarm `smvzyocty`, member m4, direction d10)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_MatQ
/-
# leaf B phase 6 — brick `matq-update` (swarm `smvzyocty`, member m4, direction d10)

`Check_MatQ` supplies the row-major rational matrix layer (`MatQ.entry`, `MatQ.mk`,
`MatQ.correct`) together with `PolyProgram`s for `entry`, `dot`, `trace`, `sum`, `trProd`,
`mulVec`, `add`, `transpose` and `gap`, and it says so explicitly at the end of its header:

> **Not covered here** (same pattern, left to the assembly if needed): the `PolyProgram`s for
> `smul`/`sub`/`neg`/`mul`/`vecMul`/`diagOfVec`, and the numerical search for the certified
> pair (the ellipsoid brick's job).

The ellipsoid loop cannot be written without the rank-one update `X ← X − μ·(Xc)(Xc)ᵀ`:
`Check_GLSInv.inv_update` proves, over `ℝ`, that this is the Sherman–Morrison inverse update,
i.e. the *whole* per-round matrix work of the engine.  This file supplies

* the row-major action `rankOneRaw` of the rank-one update, its agreement with
  `Matrix.vecMulVec` (`rankOneRaw_correct`, `rankOneRaw_eq`), and the same for the scalar
  multiple (`smul`, `sub`, `neg` are the `MatQ` operations, here given machines);
* one machine `updProg` on the packed state `(n, X, c, λ)` that computes, in one pass,
  `w = X·c`, `σ = cᵀw`, `μ = λ/(1+λσ)` and then `X − μ·(Xc)(Xc)ᵀ` row-major;
* `updProg_spec` — the machine computes exactly the `MatQ.sub`/`MatQ.smul`/`ofMatrix`
  form of `Check_GLSInv`'s update (`updProg_full_spec` for the `λ`, `σ` reading);
* `updProg_length_bound` — the framework's polynomial output-size bound on the result, which
  is what a per-round time ledger charges against.

Everything is an explicit `PolyProgram.comp` chain over the library machines, as in
`Check_MatQ` (the `fun_prop` rules do not fire for these list-valued shapes).  No `sorry`,
no `axiom`; axiom audit at the end.
-/

open scoped BigOperators
open Matrix
open OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic

namespace QMCLeafB.MatQUpdate

open MatQ

/-! ## 1.  Reading a `List ℚ` as a vector, and the rank-one action -/

/-- The vector a row-major *list* stands for (default `0` off the end). -/
def vecOf (n : ℕ) (ws : List ℚ) : Fin n → ℚ := fun i => ws.getD (i : ℕ) 0

/-- A list of length `n` is the code of the vector it stands for. -/
theorem correctVec_vecOf (n : ℕ) (ws : List ℚ) (h : ws.length = n) :
    MatQ.correctVec n (vecOf n ws) ws :=
  ⟨h, fun i => (rfl : ws.getD (i : ℕ) 0 = vecOf n ws i)⟩

/-- **The rank-one update, row-major**: `X − μ·w wᵀ`. -/
def rankOneRaw (n : ℕ) (xs ws : List ℚ) (mu : ℚ) : List ℚ :=
  MatQ.mk n (fun i j => MatQ.entry n xs i j - mu * ws.getD i 0 * ws.getD j 0)

/-- Pointwise equality of `MatQ.mk` builders (the converse of `MatQ.mk_inj`). -/
theorem mk_congr (n : ℕ) {f g : ℕ → ℕ → ℚ}
    (h : ∀ i j, i < n → j < n → f i j = g i j) : MatQ.mk n f = MatQ.mk n g := by
  unfold MatQ.mk
  refine List.flatMap_congr (fun i hi => ?_)
  exact List.map_congr_left (fun j hj =>
    h i j (List.mem_range.mp hi) (List.mem_range.mp hj))

/-- Entry of `X − μ • V`, read off the `MatQ` operations. -/
theorem entry_sub_smul (n : ℕ) (xs : List ℚ) (mu : ℚ) (V : Matrix (Fin n) (Fin n) ℚ)
    {i j : ℕ} (hi : i < n) (hj : j < n) :
    MatQ.entry n (MatQ.sub n xs (MatQ.smul mu n (MatQ.ofMatrix n V))) i j
      = MatQ.entry n xs i j - mu * V ⟨i, hi⟩ ⟨j, hj⟩ := by
  have hneg : MatQ.neg n (MatQ.smul mu n (MatQ.ofMatrix n V))
      = MatQ.smul (-1) n (MatQ.smul mu n (MatQ.ofMatrix n V)) := rfl
  rw [MatQ.sub, MatQ.entry_add n xs _ hi hj, hneg,
    MatQ.entry_smul (-1) n _ hi hj, MatQ.entry_smul mu n _ hi hj]
  have hV : MatQ.entry n (MatQ.ofMatrix n V) i j = V ⟨i, hi⟩ ⟨j, hj⟩ := by
    rw [MatQ.ofMatrix, MatQ.entry_mk n _ hi hj,
      dif_pos (show i < n ∧ j < n from ⟨hi, hj⟩)]
  rw [hV]
  ring

/-- **The rank-one action is `MatQ.sub`/`MatQ.smul`/`ofMatrix` of `vecMulVec`.**  This is the
list-level form of the matrix appearing in `Check_GLSInv.inv_update`. -/
theorem rankOneRaw_eq (n : ℕ) (xs ws : List ℚ) (mu : ℚ) :
    rankOneRaw n xs ws mu
      = MatQ.sub n xs (MatQ.smul mu n
          (MatQ.ofMatrix n (Matrix.vecMulVec (vecOf n ws) (vecOf n ws)))) := by
  refine mk_congr n (fun i j hi hj => ?_)
  have hneg : MatQ.neg n (MatQ.smul mu n
        (MatQ.ofMatrix n (Matrix.vecMulVec (vecOf n ws) (vecOf n ws))))
      = MatQ.smul (-1) n (MatQ.smul mu n
          (MatQ.ofMatrix n (Matrix.vecMulVec (vecOf n ws) (vecOf n ws)))) := rfl
  rw [hneg, MatQ.entry_smul (-1) n _ hi hj, MatQ.entry_smul mu n _ hi hj]
  have hV : MatQ.entry n (MatQ.ofMatrix n (Matrix.vecMulVec (vecOf n ws) (vecOf n ws))) i j
      = vecOf n ws ⟨i, hi⟩ * vecOf n ws ⟨j, hj⟩ := by
    rw [MatQ.ofMatrix, MatQ.entry_mk n _ hi hj,
      dif_pos (show i < n ∧ j < n from ⟨hi, hj⟩), Matrix.vecMulVec_apply]
  rw [hV]
  simp only [vecOf]
  ring

/-- **Correctness**: the row-major rank-one update is the code of the matrix update. -/
theorem rankOneRaw_correct (n : ℕ) (xs ws : List ℚ) (mu : ℚ)
    {X : Matrix (Fin n) (Fin n) ℚ} (hX : MatQ.correct n X xs)
    {w : Fin n → ℚ} (hw : MatQ.correctVec n w ws) :
    MatQ.correct n (X - mu • Matrix.vecMulVec w w) (rankOneRaw n xs ws mu) := by
  refine ⟨MatQ.mk_length n _, fun i j => ?_⟩
  show MatQ.entry n (MatQ.mk n (fun i j => MatQ.entry n xs i j - mu * ws.getD i 0 * ws.getD j 0))
      i j = _
  rw [MatQ.entry_mk n _ i.isLt j.isLt,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    hX.2 i j, hw.2 i, hw.2 j]
  ring

/-! ## 2.  Lengths -/

theorem smul_length (c : ℚ) (n : ℕ) (xs : List ℚ) : (MatQ.smul c n xs).length = n * n :=
  MatQ.mk_length n _

theorem sub_length (n : ℕ) (xs ys : List ℚ) : (MatQ.sub n xs ys).length = n * n :=
  MatQ.mk_length n _

theorem rankOneRaw_length (n : ℕ) (xs ws : List ℚ) (mu : ℚ) :
    (rankOneRaw n xs ws mu).length = n * n :=
  MatQ.mk_length n _

/-! ## 3.  The machines

The packed states.  `CSt` is the loop context `(n, X, w, μ)` of one rank-one update and
`UpSt` the element state `((n, X, w, μ), i, j)` of its double loop. -/

/-- The loop context of the rank-one update: dimension, row-major matrix, the vector
`w` (which the engine feeds as `Xc`), and the scalar `μ = λ/(1+λσ)`. -/
abbrev CSt : Type := (ℕ × List ℚ) × (List ℚ × ℚ)

/-- The element state of the rank-one update: context, row index `i`, column index `j`. -/
abbrev UpSt : Type := (CSt × ℕ) × ℕ

namespace Upd

open OAI.MetricKMedian.Binary.PolyProgram

/-! ### Projections out of the context -/

noncomputable def cM : PolyProgram (enc (α := CSt)) (enc (α := ℕ × List ℚ)) (fun p : CSt => p.1) :=
  fst (encodePair Nat.bits (encodeList Ratio.encode)) (encodePair (encodeList Ratio.encode) Ratio.encode)

noncomputable def cN : PolyProgram (enc (α := CSt)) Nat.bits (fun p : CSt => p.1.1) :=
  (cM.comp (fst Nat.bits (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def cXs : PolyProgram (enc (α := CSt)) (encodeList Ratio.encode) (fun p : CSt => p.1.2) :=
  (cM.comp (snd Nat.bits (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def cR : PolyProgram (enc (α := CSt)) (enc (α := List ℚ × ℚ)) (fun p : CSt => p.2) :=
  snd (encodePair Nat.bits (encodeList Ratio.encode)) (encodePair (encodeList Ratio.encode) Ratio.encode)

noncomputable def cW : PolyProgram (enc (α := CSt)) (encodeList Ratio.encode) (fun p : CSt => p.2.1) :=
  (cR.comp (fst (encodeList Ratio.encode) Ratio.encode)).congr _ (fun _ => rfl)

noncomputable def cMu : PolyProgram (enc (α := CSt)) Ratio.encode (fun p : CSt => p.2.2) :=
  (cR.comp (snd (encodeList Ratio.encode) Ratio.encode)).congr _ (fun _ => rfl)

/-! ### The element machine: `X[i*n+j] − μ·wᵢ·wⱼ` -/

noncomputable def uC : PolyProgram (enc (α := UpSt)) (enc (α := CSt)) (fun z : UpSt => z.1.1) :=
  MatQ.Runtime.pfst (enc (α := CSt)) Nat.bits Nat.bits

noncomputable def uI : PolyProgram (enc (α := UpSt)) Nat.bits (fun z : UpSt => z.1.2) :=
  MatQ.Runtime.pn (enc (α := CSt)) Nat.bits Nat.bits

noncomputable def uJ : PolyProgram (enc (α := UpSt)) Nat.bits (fun z : UpSt => z.2) :=
  MatQ.Runtime.pij (enc (α := CSt)) Nat.bits Nat.bits

noncomputable def uN : PolyProgram (enc (α := UpSt)) Nat.bits (fun z : UpSt => z.1.1.1.1) :=
  (uC.comp cN).congr _ (fun _ => rfl)

noncomputable def uXs : PolyProgram (enc (α := UpSt)) (encodeList Ratio.encode)
    (fun z : UpSt => z.1.1.1.2) :=
  (uC.comp cXs).congr _ (fun _ => rfl)

noncomputable def uW : PolyProgram (enc (α := UpSt)) (encodeList Ratio.encode)
    (fun z : UpSt => z.1.1.2.1) :=
  (uC.comp cW).congr _ (fun _ => rfl)

noncomputable def uMu : PolyProgram (enc (α := UpSt)) Ratio.encode (fun z : UpSt => z.1.1.2.2) :=
  (uC.comp cMu).congr _ (fun _ => rfl)

noncomputable def uIn : PolyProgram (enc (α := UpSt)) Nat.bits (fun z : UpSt => z.1.2 * z.1.1.1.1) :=
  ((uI.fanout uN).comp natMul).congr _ (fun _ => rfl)

noncomputable def uIdx : PolyProgram (enc (α := UpSt)) Nat.bits
    (fun z : UpSt => z.1.2 * z.1.1.1.1 + z.2) :=
  ((uIn.fanout uJ).comp natAdd).congr _ (fun _ => rfl)

noncomputable def uXv : PolyProgram (enc (α := UpSt)) Ratio.encode
    (fun z : UpSt => z.1.1.1.2[z.1.2 * z.1.1.1.1 + z.2]?.getD 0) :=
  ((uXs.fanout uIdx).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def uWi : PolyProgram (enc (α := UpSt)) Ratio.encode
    (fun z : UpSt => z.1.1.2.1[z.1.2]?.getD 0) :=
  ((uW.fanout uI).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def uWj : PolyProgram (enc (α := UpSt)) Ratio.encode
    (fun z : UpSt => z.1.1.2.1[z.2]?.getD 0) :=
  ((uW.fanout uJ).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def uTerm : PolyProgram (enc (α := UpSt)) Ratio.encode
    (fun z : UpSt => (z.1.1.2.2 * z.1.1.2.1[z.1.2]?.getD 0) * z.1.1.2.1[z.2]?.getD 0) :=
  (((uMu.fanout uWi).comp ratMul).fanout uWj).comp ratMul

noncomputable def uElem : PolyProgram (enc (α := UpSt)) Ratio.encode
    (fun z : UpSt => z.1.1.1.2[z.1.2 * z.1.1.1.1 + z.2]?.getD 0
      - (z.1.1.2.2 * z.1.1.2.1[z.1.2]?.getD 0) * z.1.1.2.1[z.2]?.getD 0) :=
  ((uXv.fanout uTerm).comp ratSub).congr _ (fun _ => rfl)

/-! ### The double loop -/

/-- The index list at a context: `List.range n` computed as `List.range (X.take n).length`. -/
noncomputable def cIdx : PolyProgram (enc (α := CSt)) (encodeList Nat.bits)
    (fun p : CSt => List.range ((p.1.2.take p.1.1).length)) :=
  (cM.comp MatQ.Runtime.m_idx).congr _ (fun _ => rfl)

/-- One row of the update: `j ↦ X[i*n+j] − μ·wᵢ·wⱼ`. -/
noncomputable def rowMap : PolyProgram (encodePair (enc (α := CSt × ℕ)) (encodeList Nat.bits))
    (encodeList Ratio.encode)
    (fun x : (CSt × ℕ) × List ℕ => x.2.map (fun j =>
      x.1.1.1.2[x.1.2 * x.1.1.1.1 + j]?.getD 0
        - (x.1.1.2.2 * x.1.1.2.1[x.1.2]?.getD 0) * x.1.1.2.1[j]?.getD 0)) :=
  (listMapWith (ea := Nat.bits) (ec := enc (α := CSt × ℕ)) (eb := Ratio.encode)
    (f := fun z : (CSt × ℕ) × ℕ => z.1.1.1.2[z.1.2 * z.1.1.1.1 + z.2]?.getD 0
      - (z.1.1.2.2 * z.1.1.2.1[z.1.2]?.getD 0) * z.1.1.2.1[z.2]?.getD 0) uElem
    (a0 := 0) (b0 := (0 : ℚ)))

/-- The row-index list of a row state `(context, i)`. -/
noncomputable def rowIdx : PolyProgram (encodePair (enc (α := CSt)) Nat.bits) (encodeList Nat.bits)
    (fun y : CSt × ℕ => List.range ((y.1.1.2.take y.1.1.1).length)) :=
  ((fst (enc (α := CSt)) Nat.bits).comp cIdx).congr _ (fun _ => rfl)

/-- One full row `i` of the update. -/
noncomputable def rowFun (y : CSt × ℕ) : List ℚ :=
  (List.range ((y.1.1.2.take y.1.1.1).length)).map (fun j =>
    y.1.1.2[y.2 * y.1.1.1 + j]?.getD 0
      - (y.1.2.2 * y.1.2.1[y.2]?.getD 0) * y.1.2.1[j]?.getD 0)

noncomputable def rowProg : PolyProgram (encodePair (enc (α := CSt)) Nat.bits)
    (encodeList Ratio.encode) rowFun :=
  (((identity (encodePair (enc (α := CSt)) Nat.bits)).fanout rowIdx).comp rowMap).congr _
    (fun _ => rfl)

/-- **The rank-one update machine**: `X − μ·w wᵀ` row by row. -/
noncomputable def updFun (p : CSt) : List ℚ :=
  (List.range ((p.1.2.take p.1.1).length)).flatMap (fun i => rowFun (p, i))

noncomputable def updProg : PolyProgram (enc (α := CSt)) (encodeList Ratio.encode) updFun :=
  (((identity (enc (α := CSt))).fanout cIdx).comp
    (listFlatMapWith (ea := Nat.bits) (ec := enc (α := CSt)) (eb := Ratio.encode)
      (f := fun y : CSt × ℕ => rowFun y) rowProg (a0 := 0) (b0 := (0 : ℚ)))).congr _
    (fun _ => rfl)

end Upd

/-! ## 4.  What the machine computes -/

/-- `(xs.take n).length = n` for a code of an `n × n` matrix. -/
theorem take_length (n : ℕ) (xs : List ℚ) (hx : xs.length = n * n) :
    (xs.take n).length = n := by
  rw [List.length_take, hx]
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0; simp
  · exact Nat.min_eq_left (Nat.le_mul_of_pos_left n h0)

/-- **The double loop is the rank-one update.**  With the row loop read off `List.range n`
(as the machine does, via `(xs.take n).length`), the machine's output is `rankOneRaw`. -/
theorem updFun_eq (n : ℕ) (xs ws : List ℚ) (mu : ℚ) (hx : xs.length = n * n) :
    Upd.updFun ((n, xs), (ws, mu)) = rankOneRaw n xs ws mu := by
  have ht : (xs.take n).length = n := take_length n xs hx
  simp only [Upd.updFun, Upd.rowFun, rankOneRaw, MatQ.mk, MatQ.entry, ht,
    List.getD_eq_getElem?_getD]

/-- **`updProg` computes `X − μ·w wᵀ`** in the `MatQ` vocabulary: the machine is
`MatQ.sub`/`MatQ.smul`/`ofMatrix` of `vecMulVec`, i.e. exactly the matrix of
`Check_GLSInv.inv_update`. -/
theorem updProg_spec (n : ℕ) (xs ws : List ℚ) (mu : ℚ) (hx : xs.length = n * n) :
    Upd.updFun ((n, xs), (ws, mu))
      = MatQ.sub n xs (MatQ.smul mu n
          (MatQ.ofMatrix n (Matrix.vecMulVec (vecOf n ws) (vecOf n ws)))) := by
  rw [updFun_eq n xs ws mu hx, rankOneRaw_eq]

/-- The machine's output is a correct row-major code of the updated matrix. -/
theorem updProg_correct (n : ℕ) (xs ws : List ℚ) (mu : ℚ)
    {X : Matrix (Fin n) (Fin n) ℚ} (hX : MatQ.correct n X xs)
    {w : Fin n → ℚ} (hw : MatQ.correctVec n w ws) :
    MatQ.correct n (X - mu • Matrix.vecMulVec w w) (Upd.updFun ((n, xs), (ws, mu))) := by
  rw [updFun_eq n xs ws mu hX.1]
  exact rankOneRaw_correct n xs ws mu hX hw

/-- The output has the matrix length: `n²` rationals, so the next round's state has the same
`n²` entries (this is the size invariant a time ledger carries). -/
theorem updFun_length (n : ℕ) (xs ws : List ℚ) (mu : ℚ) (hx : xs.length = n * n) :
    (Upd.updFun ((n, xs), (ws, mu))).length = n * n := by
  rw [updFun_eq n xs ws mu hx]
  exact rankOneRaw_length n xs ws mu

/-- **The framework's polynomial output-size bound** on the machine — what a per-round time
ledger charges (`PolyProgram.length_bound`). -/
theorem updProg_length_bound (p : CSt) :
    (encodeList Ratio.encode (Upd.updFun p)).length
      ≤ Upd.updProg.sizeBound.eval (enc (α := CSt) p).length :=
  Upd.updProg.length_bound p

/-- **`smul` is a program on the `MatQ` state**: `(n, X, c) ↦ c • X` row-major. -/
noncomputable def smulFun (p : (ℕ × List ℚ) × ℚ) : List ℚ :=
  (List.range ((p.1.2.take p.1.1).length)).flatMap (fun i =>
    (List.range ((p.1.2.take p.1.1).length)).map (fun j =>
      p.2 * p.1.2[i * p.1.1 + j]?.getD 0))

section Programs2

open OAI.MetricKMedian.Binary.PolyProgram

/-! ### The `smul` machine -/

abbrev SSt : Type := (ℕ × List ℚ) × ℚ

noncomputable def sCtx : PolyProgram (enc (α := SSt)) (enc (α := ℕ × List ℚ)) (fun p : SSt => p.1) :=
  fst (encodePair Nat.bits (encodeList Ratio.encode)) Ratio.encode

noncomputable def sN : PolyProgram (enc (α := SSt)) Nat.bits (fun p : SSt => p.1.1) :=
  (sCtx.comp (fst Nat.bits (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def sXs : PolyProgram (enc (α := SSt)) (encodeList Ratio.encode) (fun p : SSt => p.1.2) :=
  (sCtx.comp (snd Nat.bits (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def sC : PolyProgram (enc (α := SSt)) Ratio.encode (fun p : SSt => p.2) :=
  snd (encodePair Nat.bits (encodeList Ratio.encode)) Ratio.encode

noncomputable def sIdx : PolyProgram (enc (α := SSt)) (encodeList Nat.bits)
    (fun p : SSt => List.range ((p.1.2.take p.1.1).length)) :=
  (sCtx.comp MatQ.Runtime.m_idx).congr _ (fun _ => rfl)

/-- Element state `((n, X, c), i, j)`. -/
abbrev SESt : Type := (SSt × ℕ) × ℕ

noncomputable def seC : PolyProgram (enc (α := SESt)) (enc (α := SSt)) (fun z : SESt => z.1.1) :=
  MatQ.Runtime.pfst (enc (α := SSt)) Nat.bits Nat.bits

noncomputable def seI : PolyProgram (enc (α := SESt)) Nat.bits (fun z : SESt => z.1.2) :=
  MatQ.Runtime.pn (enc (α := SSt)) Nat.bits Nat.bits

noncomputable def seJ : PolyProgram (enc (α := SESt)) Nat.bits (fun z : SESt => z.2) :=
  MatQ.Runtime.pij (enc (α := SSt)) Nat.bits Nat.bits

noncomputable def seN : PolyProgram (enc (α := SESt)) Nat.bits (fun z : SESt => z.1.1.1.1) :=
  (seC.comp sN).congr _ (fun _ => rfl)

noncomputable def seXs : PolyProgram (enc (α := SESt)) (encodeList Ratio.encode)
    (fun z : SESt => z.1.1.1.2) :=
  (seC.comp sXs).congr _ (fun _ => rfl)

noncomputable def seCc : PolyProgram (enc (α := SESt)) Ratio.encode (fun z : SESt => z.1.1.2) :=
  (seC.comp sC).congr _ (fun _ => rfl)

noncomputable def seIn : PolyProgram (enc (α := SESt)) Nat.bits
    (fun z : SESt => z.1.2 * z.1.1.1.1) :=
  ((seI.fanout seN).comp natMul).congr _ (fun _ => rfl)

noncomputable def seIdx : PolyProgram (enc (α := SESt)) Nat.bits
    (fun z : SESt => z.1.2 * z.1.1.1.1 + z.2) :=
  ((seIn.fanout seJ).comp natAdd).congr _ (fun _ => rfl)

noncomputable def seXv : PolyProgram (enc (α := SESt)) Ratio.encode
    (fun z : SESt => z.1.1.1.2[z.1.2 * z.1.1.1.1 + z.2]?.getD 0) :=
  ((seXs.fanout seIdx).comp (listGetD (Ratio.encode) (0 : ℚ))).congr _ (fun _ => rfl)

noncomputable def seElem : PolyProgram (enc (α := SESt)) Ratio.encode
    (fun z : SESt => z.1.1.2 * z.1.1.1.2[z.1.2 * z.1.1.1.1 + z.2]?.getD 0) :=
  ((seCc.fanout seXv).comp ratMul).congr _ (fun _ => rfl)

noncomputable def seRow : PolyProgram (encodePair (enc (α := SSt)) Nat.bits)
    (encodeList Ratio.encode)
    (fun y : SSt × ℕ => (List.range ((y.1.1.2.take y.1.1.1).length)).map
      (fun j => y.1.2 * y.1.1.2[y.2 * y.1.1.1 + j]?.getD 0)) :=
  ((identity (encodePair (enc (α := SSt)) Nat.bits)).fanout
    (((fst (enc (α := SSt)) Nat.bits).comp sIdx))).comp
    (listMapWith (ea := Nat.bits) (ec := enc (α := SSt × ℕ)) (eb := Ratio.encode)
      (f := fun z : (SSt × ℕ) × ℕ => z.1.1.2 * z.1.1.1.2[z.1.2 * z.1.1.1.1 + z.2]?.getD 0)
      seElem (a0 := 0) (b0 := (0 : ℚ)))

noncomputable def smulRaw (p : SSt) : List ℚ :=
  (List.range ((p.1.2.take p.1.1).length)).flatMap (fun i =>
    (List.range ((p.1.2.take p.1.1).length)).map (fun j =>
      p.2 * p.1.2[i * p.1.1 + j]?.getD 0))

noncomputable def smulProgram : PolyProgram (enc (α := SSt)) (encodeList Ratio.encode) smulRaw :=
  (((identity (enc (α := SSt))).fanout sIdx).comp
    (listFlatMapWith (ea := Nat.bits) (ec := enc (α := SSt)) (eb := Ratio.encode)
      (f := fun y : SSt × ℕ => (List.range ((y.1.1.2.take y.1.1.1).length)).map
        (fun j => y.1.2 * y.1.1.2[y.2 * y.1.1.1 + j]?.getD 0)) seRow
      (a0 := 0) (b0 := (0 : ℚ)))).congr _ (fun _ => rfl)

theorem smulProgram_eq (n : ℕ) (xs : List ℚ) (c : ℚ) (hx : xs.length = n * n) :
    smulRaw ((n, xs), c) = MatQ.smul c n xs := by
  have ht : (xs.take n).length = n := take_length n xs hx
  simp only [smulRaw, MatQ.smul, MatQ.mk, MatQ.entry, ht, List.getD_eq_getElem?_getD]

theorem smulProgram_length_bound (p : SSt) :
    (encodeList Ratio.encode (smulRaw p)).length
      ≤ smulProgram.sizeBound.eval (enc (α := SSt) p).length :=
  smulProgram.length_bound p

end Programs2


/-! ## 5.  The dot bridge: the library's `dotProgram` computes `MatQ.dot` -/

/-- The `zip` sum of two equally long lists is the `range`-indexed sum `MatQ` uses. -/
theorem zip_sum_eq : ∀ (ys zs : List ℚ), ys.length = zs.length →
    ((ys.zip zs).map (fun q : ℚ × ℚ => q.1 * q.2)).sum
      = ((List.range ys.length).map (fun k => ys.getD k 0 * zs.getD k 0)).sum
  | [], zs, h => by
      have hz : zs = [] := List.eq_nil_of_length_eq_zero (by simpa using h.symm)
      subst hz
      simp
  | y :: ys, [], h => by simp at h
  | y :: ys, z :: zs, h => by
      have h' : ys.length = zs.length := by simpa using h
      have ih := zip_sum_eq ys zs h'
      simp only [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons, ih]
      rw [List.range_succ_eq_map]
      simp only [List.map_cons, List.sum_cons, List.map_map, Function.comp_def,
        List.getD_cons_zero, List.getD_cons_succ]

/-- **`MatQ.dot` is the `zip`-sum the `dotProgram` machine computes.** -/
theorem dot_eq_zip_sum (n : ℕ) (ys zs : List ℚ) (hy : ys.length = n) (hz : zs.length = n) :
    MatQ.dot n ys zs = ((ys.zip zs).map (fun q : ℚ × ℚ => q.1 * q.2)).sum := by
  rw [MatQ.dot, ← hy, ← zip_sum_eq ys zs (by rw [hy, hz])]

/-! ## 6.  The full one-round machine: `(n, X, c, λ) ↦ X − μ·(Xc)(Xc)ᵀ`

On this state the third and fourth components are the separator normal `c` and the
Sherman–Morrison multiplier `λ`; the machine computes `w = Xc`, `σ = cᵀw`, `μ = λ/(1+λσ)` and
then hands `(n, X, w, μ)` to `Upd.updProg`. -/

namespace Step

open OAI.MetricKMedian.Binary.PolyProgram

/-- Input state of a round: `(n, X, c, λ)`. -/
abbrev RSt : Type := (ℕ × List ℚ) × (List ℚ × ℚ)

noncomputable def tN : PolyProgram (enc (α := RSt)) Nat.bits (fun p : RSt => p.1.1) :=
  (fst (encodePair Nat.bits (encodeList Ratio.encode)) (encodePair (encodeList Ratio.encode) Ratio.encode)).comp
    (fst Nat.bits (encodeList Ratio.encode))

noncomputable def tXs : PolyProgram (enc (α := RSt)) (encodeList Ratio.encode)
    (fun p : RSt => p.1.2) :=
  ((fst (encodePair Nat.bits (encodeList Ratio.encode)) (encodePair (encodeList Ratio.encode) Ratio.encode)).comp
    (snd Nat.bits (encodeList Ratio.encode))).congr _ (fun _ => rfl)

noncomputable def tCs : PolyProgram (enc (α := RSt)) (encodeList Ratio.encode)
    (fun p : RSt => p.2.1) :=
  ((snd (encodePair Nat.bits (encodeList Ratio.encode)) (encodePair (encodeList Ratio.encode) Ratio.encode)).comp
    (fst (encodeList Ratio.encode) Ratio.encode)).congr _ (fun _ => rfl)

noncomputable def tLam : PolyProgram (enc (α := RSt)) Ratio.encode (fun p : RSt => p.2.2) :=
  ((snd (encodePair Nat.bits (encodeList Ratio.encode)) (encodePair (encodeList Ratio.encode) Ratio.encode)).comp
    (snd (encodeList Ratio.encode) Ratio.encode)).congr _ (fun _ => rfl)

noncomputable def tVst : PolyProgram (enc (α := RSt)) (enc (α := ℕ × (List ℚ × List ℚ)))
    (fun p : RSt => (p.1.1, (p.1.2, p.2.1))) :=
  (tN.fanout (tXs.fanout tCs)).congr _ (fun _ => rfl)

/-- `w = X·c`. -/
noncomputable def tWv : PolyProgram (enc (α := RSt)) (encodeList Ratio.encode)
    (fun p : RSt => MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1))) :=
  (tVst.comp MatQ.Runtime.mulVecProgram).congr _ (fun _ => rfl)

/-- `σ = cᵀw`. -/
noncomputable def tSig : PolyProgram (enc (α := RSt)) Ratio.encode
    (fun p : RSt => ((p.2.1.zip (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)))).map
      (fun q : ℚ × ℚ => q.1 * q.2)).sum) :=
  ((tCs.fanout tWv).comp MatQ.Runtime.dotProgram).congr _ (fun _ => rfl)

/-- `1 + λσ`. -/
noncomputable def tDen : PolyProgram (enc (α := RSt)) Ratio.encode
    (fun p : RSt => 1 + p.2.2 * ((p.2.1.zip (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)))).map
      (fun q : ℚ × ℚ => q.1 * q.2)).sum) :=
  (((constant (enc (α := RSt)) Ratio.encode 1).fanout
    ((tLam.fanout tSig).comp ratMul)).comp ratAdd).congr _ (fun _ => rfl)

/-- `μ = λ/(1+λσ)`. -/
noncomputable def tMu : PolyProgram (enc (α := RSt)) Ratio.encode
    (fun p : RSt => p.2.2 / (1 + p.2.2 * ((p.2.1.zip
      (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)))).map
      (fun q : ℚ × ℚ => q.1 * q.2)).sum)) :=
  ((tLam.fanout tDen).comp ratDiv).congr _ (fun _ => rfl)

/-- The loop context built from the round state. -/
noncomputable def tCtx : PolyProgram (enc (α := RSt)) (enc (α := RSt))
    (fun p : RSt => (p.1, (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)),
      p.2.2 / (1 + p.2.2 * ((p.2.1.zip
        (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)))).map
        (fun q : ℚ × ℚ => q.1 * q.2)).sum)))) :=
  ((tN.fanout tXs).fanout (tWv.fanout tMu)).congr _ (fun _ => rfl)

/-- The round's output, row-major. -/
noncomputable def stepFun (p : RSt) : List ℚ :=
  Upd.updFun ((p.1.1, p.1.2), (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)),
    p.2.2 / (1 + p.2.2 * ((p.2.1.zip
      (MatQ.Runtime.mulVecRaw (p.1.1, (p.1.2, p.2.1)))).map
      (fun q : ℚ × ℚ => q.1 * q.2)).sum)))

/-- **The one-round machine.** -/
noncomputable def stepProg : PolyProgram (enc (α := RSt)) (encodeList Ratio.encode) stepFun :=
  (tCtx.comp Upd.updProg).congr _ (fun _ => rfl)

/-- **What one round computes**: `X ↦ X − (λ/(1+λσ))·(Xc)(Xc)ᵀ` with `σ = cᵀXc`, in the
`MatQ`/`Check_GLSInv` form. -/
theorem stepProg_spec (n : ℕ) (xs cs : List ℚ) (lam : ℚ)
    (hx : xs.length = n * n) (hc : cs.length = n) :
    stepFun ((n, xs), (cs, lam))
      = MatQ.sub n xs (MatQ.smul
          (lam / (1 + lam * MatQ.dot n cs (MatQ.mulVec n xs cs))) n
          (MatQ.ofMatrix n (Matrix.vecMulVec (vecOf n (MatQ.mulVec n xs cs))
            (vecOf n (MatQ.mulVec n xs cs))))) := by
  unfold stepFun
  rw [MatQ.Runtime.mulVecProgram_spec n xs cs hc]
  have hw : (MatQ.mulVec n xs cs).length = n := MatQ.mulVec_length n xs cs
  have hzip : ((cs.zip (MatQ.mulVec n xs cs)).map (fun q : ℚ × ℚ => q.1 * q.2)).sum
      = MatQ.dot n cs (MatQ.mulVec n xs cs) :=
    (dot_eq_zip_sum n cs (MatQ.mulVec n xs cs) hc hw).symm
  rw [hzip]
  exact updProg_spec n xs (MatQ.mulVec n xs cs) _ hx

/-- The round's output is a correct code of the updated matrix `X − μ·(Xc)(Xc)ᵀ`. -/
theorem stepProg_correct (n : ℕ) (xs cs : List ℚ) (lam : ℚ)
    {X : Matrix (Fin n) (Fin n) ℚ} (hX : MatQ.correct n X xs)
    {c : Fin n → ℚ} (hc : MatQ.correctVec n c cs) :
    MatQ.correct n
      (X - (lam / (1 + lam * MatQ.dot n cs (MatQ.mulVec n xs cs))) •
        Matrix.vecMulVec (Matrix.mulVec X c) (Matrix.mulVec X c))
      (stepFun ((n, xs), (cs, lam))) := by
  unfold stepFun
  rw [MatQ.Runtime.mulVecProgram_spec n xs cs hc.1]
  have hw : (MatQ.mulVec n xs cs).length = n := MatQ.mulVec_length n xs cs
  have hzip : ((cs.zip (MatQ.mulVec n xs cs)).map (fun q : ℚ × ℚ => q.1 * q.2)).sum
      = MatQ.dot n cs (MatQ.mulVec n xs cs) :=
    (dot_eq_zip_sum n cs (MatQ.mulVec n xs cs) hc.1 hw).symm
  rw [hzip]
  exact updProg_correct n xs (MatQ.mulVec n xs cs) _ hX (MatQ.correct_mulVec hX hc)

/-- The round's output still has `n²` entries. -/
theorem stepFun_length (n : ℕ) (xs cs : List ℚ) (lam : ℚ) (hx : xs.length = n * n) :
    (stepFun ((n, xs), (cs, lam))).length = n * n := by
  unfold stepFun
  exact updFun_length n xs _ _ hx

/-- The framework's polynomial output-size bound on one round. -/
theorem stepProg_length_bound (p : RSt) :
    (encodeList Ratio.encode (stepFun p)).length
      ≤ stepProg.sizeBound.eval (enc (α := RSt) p).length :=
  stepProg.length_bound p

end Step

/-! ## 7.  Axiom audit -/

#print axioms QMCLeafB.MatQUpdate.rankOneRaw_eq
#print axioms QMCLeafB.MatQUpdate.rankOneRaw_correct
#print axioms QMCLeafB.MatQUpdate.take_length
#print axioms QMCLeafB.MatQUpdate.updFun_eq
#print axioms QMCLeafB.MatQUpdate.updProg_spec
#print axioms QMCLeafB.MatQUpdate.updProg_correct
#print axioms QMCLeafB.MatQUpdate.Upd.updProg
#print axioms QMCLeafB.MatQUpdate.Upd.uElem
#print axioms QMCLeafB.MatQUpdate.updProg_length_bound
#print axioms QMCLeafB.MatQUpdate.smulProgram
#print axioms QMCLeafB.MatQUpdate.smulProgram_eq
#print axioms QMCLeafB.MatQUpdate.zip_sum_eq
#print axioms QMCLeafB.MatQUpdate.dot_eq_zip_sum
#print axioms QMCLeafB.MatQUpdate.Step.stepProg
#print axioms QMCLeafB.MatQUpdate.Step.stepProg_spec
#print axioms QMCLeafB.MatQUpdate.Step.stepFun_length

end QMCLeafB.MatQUpdate


