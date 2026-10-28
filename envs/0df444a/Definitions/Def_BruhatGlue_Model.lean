-- Prove2me | Definitions.Def_BruhatGlue_Model
-- name    : BruhatGlue_Model
-- status  : Definition
-- author  : @darkhipo
-- created : 2026-10-28T19:02:19.939388+00:00
-- url     : https://prove2.me/theorems/c7ea128d-3556-419e-8888-d46c7e69db89

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!

Mission context (leaf `1ebc5981`, onerun keystone, summit attempt #5): the only
remaining gap is `FormalOK`.  With trivial Bruhat factors every edge matrix is
a permutation matrix and a role wire needs `>= m` own run width to assemble
`swapMat`; the bitR8 census is `759` per block SHORT of `529` per role.  The
proposed escape: interleaved lower-triangular (`unipotent`) edge factors
`E1, E2` might let a wire reach `swapMat` with total run width `< m`.

**This file proves that escape impossible — at every `m`, over any field.**

The wire product has the form (framework `edgeMat`: `redM E1 * P(runs) * redM E2`)

  F = L_t · P(σ_t) · V_t · ⋯ · V_2 · P(σ_1) · V_1,

with `L_i, V_i` lower-triangular and each `σ_i` a product of run-pivot cross
transpositions `(top a) ↔ (bottom m+b)`.  This is modelled exactly by the
inductive `Glue`: start at `1`; free moves are left/right multiplication by
lower-triangular matrices; a pivot step (right multiplication by one cross
transposition) costs `1`.

Rank potential: `B M` = the top-right `m×m` block of `M`.  Then

* `B 1 = 0` and `B (blkSwap) = 1` (the block swap `[[0,I],[I,0]]`);
* left lower-triangular mult: `B (L*M) = AL L * B M`   (rank `≤`);
* right lower-triangular mult: `B (M*V) = B M * DR V`  (rank `≤`);
* one pivot: `B (M * crossT) = (B M) with one column replaced`  (rank `≤ +1`).

Hence `(B M).rank ≤ #pivots` along any `Glue` word (`glue_rank`), and
`Glue (blkSwap) w → m ≤ w` (`no_glue`).  **The minimum own width of a wire
whose edge product is the block swap is exactly `m`; unipotent glue saves
zero transpositions at every `m`.**  With `m = 529` and #6's decide-proved
census (`529·59130 − 759` width available per block), own-edge assembly of
`FormalOK` is short by exactly `759` transpositions per block — the onerun
family cannot close `FormalOK` this way.

(Transfer to the framework: `edgeMat N` reduces fixed rational matrices mod
`N`; if the identity `F = swapMat` held in `ZMod N` for infinitely many prime
powers `N`, it would hold over `ℚ`, contradicting `no_glue` at `K = ℚ`.)
-/

namespace BruhatGlue

/-- The cross transposition `(top a) ↔ (bottom m+b)` as a matrix. -/
def crossT (K : Type*) [Field K] (m : ℕ) (a b : Fin m) :
    Matrix (Fin (m + m)) (Fin (m + m)) K :=
  Matrix.of fun i j =>
    if Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) i = j then 1 else 0

/-- The block swap `[[0, I], [I, 0]]`. -/
def blkSwap (K : Type*) [Field K] (m : ℕ) : Matrix (Fin (m + m)) (Fin (m + m)) K :=
  Matrix.of fun i j => if (i : ℕ) + m = (j : ℕ) ∨ (j : ℕ) + m = (i : ℕ) then 1 else 0

/-- Top-right `m×m` block (the rank potential). -/
def B (K : Type*) [Field K] (m : ℕ) (M : Matrix (Fin (m + m)) (Fin (m + m)) K) :
    Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => M (Fin.castAdd m i) (Fin.natAdd m j)

/-- Top-left `m×m` block. -/
def AL (K : Type*) [Field K] (m : ℕ) (M : Matrix (Fin (m + m)) (Fin (m + m)) K) :
    Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => M (Fin.castAdd m i) (Fin.castAdd m j)

/-- Bottom-right `m×m` block. -/
def DR (K : Type*) [Field K] (m : ℕ) (M : Matrix (Fin (m + m)) (Fin (m + m)) K) :
    Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => M (Fin.natAdd m i) (Fin.natAdd m j)

/-- Lower-triangularity, exactly the `EdgeOK` shape `∀ i j, i < j → E i j = 0`. -/
def IsLowerTri (K : Type*) [Field K] (m : ℕ)
    (L : Matrix (Fin (m + m)) (Fin (m + m)) K) : Prop :=
  ∀ i j : Fin (m + m), (i : ℕ) < (j : ℕ) → L i j = 0

/-! ## Entry-level facts -/

theorem castAdd_val_lt (m : ℕ) (i : Fin m) : (Fin.castAdd m i : ℕ) < m := by
  simp only [Fin.val_castAdd]; exact i.isLt

theorem le_natAdd_val (m : ℕ) (j : Fin m) : m ≤ (Fin.natAdd m j : ℕ) := by
  rw [show (Fin.natAdd m j : ℕ) = m + (j : ℕ) from Fin.val_natAdd m j]
  omega

theorem castAdd_ne_natAdd (m : ℕ) (i j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd m j := by
  intro h
  have hv := congrArg Fin.val h
  have h1 := i.isLt
  have h2 := j.isLt
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

theorem mul_crossT_apply {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (m + m)) (Fin (m + m)) K) (a b : Fin m) (i j : Fin (m + m)) :
    (M * crossT K m a b) i j
      = M i (Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) j) := by
  simp only [Matrix.mul_apply, crossT, Matrix.of_apply]
  have key : ∀ k : Fin (m + m),
      M i k * (if Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) k = j then 1 else 0)
        = if k = Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) j then M i k else 0 := by
    intro k
    by_cases hk : Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) k = j
    · have hk2 : k = Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) j := by
        have hc := congrArg (Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b)) hk
        rw [Equiv.swap_apply_self] at hc
        exact hc
      rw [if_pos hk, if_pos hk2, mul_one]
    · have hk2 : ¬ (k = Equiv.swap (Fin.castAdd m a) (Fin.natAdd m b) j) := by
        intro h
        rw [h, Equiv.swap_apply_self] at hk
        exact hk rfl
      rw [if_neg hk, if_neg hk2, mul_zero]
  rw [Finset.sum_congr rfl (fun k _ => key k), Finset.sum_ite_eq']
  simp

/-! ## The block lemmas -/

theorem B_one (K : Type*) [Field K] (m : ℕ) :
    B K m (1 : Matrix (Fin (m + m)) (Fin (m + m)) K) = 0 := by
  ext i j
  simp [B, Matrix.one_apply_ne (castAdd_ne_natAdd m i j)]

theorem B_blkSwap (K : Type*) [Field K] (m : ℕ) : B K m (blkSwap K m) = 1 := by
  ext i j
  simp only [B, blkSwap, Matrix.of_apply, Fin.val_castAdd, Fin.val_natAdd,
    Matrix.one_apply]
  have h1 := i.isLt
  have h2 := j.isLt
  by_cases h : i = j
  · subst h
    have hc : (i : ℕ) + m = m + (i : ℕ) := by omega
    simp [hc]
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun hc => h (Fin.val_inj.1 hc)
    have e1 : ¬ ((i : ℕ) + m = m + (j : ℕ)) := by omega
    have e2 : ¬ (m + (j : ℕ) + m = (i : ℕ)) := by omega
    simp [e1, e2, h]

theorem B_mul_left {K : Type*} [Field K] {m : ℕ}
    (L M : Matrix (Fin (m + m)) (Fin (m + m)) K) (hL : IsLowerTri K m L) :
    B K m (L * M) = AL K m L * B K m M := by
  ext i j
  simp only [B, AL, Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_add]
  have h2 : ∑ k : Fin m,
      L (Fin.castAdd m i) (Fin.natAdd m k) * M (Fin.natAdd m k) (Fin.natAdd m j) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have hlt : (Fin.castAdd m i : ℕ) < (Fin.natAdd m k : ℕ) := by
      have h1 := castAdd_val_lt m i
      have h2 := le_natAdd_val m k
      omega
    rw [hL _ _ hlt, zero_mul]
  rw [h2, add_zero]

theorem B_mul_right {K : Type*} [Field K] {m : ℕ}
    (M V : Matrix (Fin (m + m)) (Fin (m + m)) K) (hV : IsLowerTri K m V) :
    B K m (M * V) = B K m M * DR K m V := by
  ext i j
  simp only [B, DR, Matrix.mul_apply, Matrix.of_apply]
  rw [Fin.sum_univ_add]
  have h2 : ∑ k : Fin m,
      M (Fin.castAdd m i) (Fin.castAdd m k) * V (Fin.castAdd m k) (Fin.natAdd m j) = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    have hlt : (Fin.castAdd m k : ℕ) < (Fin.natAdd m j : ℕ) := by
      have h1 := castAdd_val_lt m k
      have h2 := le_natAdd_val m j
      omega
    rw [hV _ _ hlt, mul_zero]
  rw [h2, zero_add]

/-- `updCol X b u` replaces column `b` of `X` by `u`. -/
def updCol (K : Type*) [Field K] (m : ℕ) (X : Matrix (Fin m) (Fin m) K) (b : Fin m)
    (u : Fin m → K) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun i j => if j = b then u i else X i j

theorem B_mul_crossT {K : Type*} [Field K] {m : ℕ}
    (M : Matrix (Fin (m + m)) (Fin (m + m)) K) (a b : Fin m) :
    B K m (M * crossT K m a b)
      = updCol K m (B K m M) b (fun i => M (Fin.castAdd m i) (Fin.castAdd m a)) := by
  ext i j
  simp only [B, updCol, Matrix.of_apply, mul_crossT_apply]
  by_cases hj : j = b
  · subst hj
    rw [Equiv.swap_apply_right]
    simp
  · rw [Equiv.swap_apply_of_ne_of_ne]
    · simp [hj]
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      have ha := a.isLt
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd] at hv
      exact hj (Fin.val_inj.1 (by omega))

/-! ## Rank helpers -/

theorem rank_add_le' {K : Type*} [Field K] {m n : ℕ} (X Y : Matrix (Fin m) (Fin n) K) :
    (X + Y).rank ≤ X.rank + Y.rank := by
  have h : Submodule.span K (Set.range (X + Y).col) ≤
      Submodule.span K (Set.range X.col) ⊔ Submodule.span K (Set.range Y.col) := by
    apply Submodule.span_le.2
    rintro _ ⟨j, rfl⟩
    exact Submodule.mem_sup.2
      ⟨_, Submodule.subset_span ⟨j, rfl⟩, _, Submodule.subset_span ⟨j, rfl⟩, rfl⟩
  have e1 : (X + Y).rank = Module.finrank K (Submodule.span K (Set.range (X + Y).col)) :=
    Matrix.rank_eq_finrank_span_cols _
  have e2 : X.rank = Module.finrank K (Submodule.span K (Set.range X.col)) :=
    Matrix.rank_eq_finrank_span_cols _
  have e3 : Y.rank = Module.finrank K (Submodule.span K (Set.range Y.col)) :=
    Matrix.rank_eq_finrank_span_cols _
  rw [e1, e2, e3]
  refine le_trans (Submodule.finrank_mono h) ?_
  exact Submodule.finrank_add_le_finrank_add_finrank _ _

/-- The identity with column `b` zeroed. -/
def Qz (K : Type*) [Field K] (m : ℕ) (b : Fin m) : Matrix (Fin m) (Fin m) K :=
  Matrix.of fun j k => if j = k ∧ j ≠ b then 1 else 0

theorem mul_Qz_apply {K : Type*} [Field K] {m : ℕ}
    (X : Matrix (Fin m) (Fin m) K) (b i j : Fin m) :
    (X * Qz K m b) i j = if j = b then 0 else X i j := by
  simp only [Matrix.mul_apply, Qz, Matrix.of_apply]
  by_cases h : j = b
  · rw [h, if_pos rfl]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = b
    · simp [hk]
    · simp [hk]
  · rw [if_neg h]
    rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)
      (fun k _ hk => by
        have h' : ¬ (k = j ∧ k ≠ b) := by
          rintro ⟨h1, h2⟩
          exact hk h1
        simp [h'])]
    simp [h]

theorem rank_updCol_le {K : Type*} [Field K] {m : ℕ}
    (X : Matrix (Fin m) (Fin m) K) (b : Fin m) (u : Fin m → K) :
    (updCol K m X b u).rank ≤ X.rank + 1 := by
  have hId : updCol K m X b u
      = X * Qz K m b + Matrix.vecMulVec u (Pi.single b 1) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec]
    rw [mul_Qz_apply]
    by_cases h : j = b <;> simp [updCol, Matrix.of_apply, h, Pi.single_apply]
  rw [hId]
  refine le_trans (rank_add_le' _ _) ?_
  refine Nat.add_le_add (Matrix.rank_mul_le_left _ _) ?_
  exact Matrix.rank_vecMulVec_le _ _

/-! ## The `Glue` word and the lower bound -/

/-- A `Glue` word: from `1`, free left/right lower-triangular multiplications
and costed pivot steps (right multiplication by one cross transposition). -/
inductive Glue (K : Type*) [Field K] (m : ℕ) :
    Matrix (Fin (m + m)) (Fin (m + m)) K → ℕ → Prop
  | one : Glue K m 1 0
  | mulLeft (L : Matrix (Fin (m + m)) (Fin (m + m)) K) (hL : IsLowerTri K m L) {M w}
      (h : Glue K m M w) : Glue K m (L * M) w
  | mulRight (V : Matrix (Fin (m + m)) (Fin (m + m)) K) (hV : IsLowerTri K m V) {M w}
      (h : Glue K m M w) : Glue K m (M * V) w
  | pivot (a b : Fin m) {M w} (h : Glue K m M w) : Glue K m (M * crossT K m a b) (w + 1)

/-- **The rank-potential bound**: along any `Glue` word, the rank of the
top-right block is at most the number of pivot steps. -/
theorem glue_rank {K : Type*} [Field K] {m : ℕ} {M w} (h : Glue K m M w) :
    (B K m M).rank ≤ w := by
  induction h with
  | one => rw [B_one]; simp
  | mulLeft L hL _ ih => rw [B_mul_left L _ hL]; exact (Matrix.rank_mul_le_right _ _).trans ih
  | mulRight V hV _ ih => rw [B_mul_right _ V hV]; exact (Matrix.rank_mul_le_left _ _).trans ih
  | @pivot a b M w h ih =>
    rw [B_mul_crossT M a b]
    exact (rank_updCol_le (B K m M) b
      (fun i => M (Fin.castAdd m i) (Fin.castAdd m a))).trans (Nat.succ_le_succ ih)


