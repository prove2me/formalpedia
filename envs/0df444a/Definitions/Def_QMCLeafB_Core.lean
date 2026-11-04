-- Prove2me | Definitions.Def_QMCLeafB_Core
-- name    : QMCLeafB_Core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T21:58:41.321972+00:00
-- url     : https://prove2.me/theorems/c73840bc-8402-453e-a425-171e0b472faf
-- title:
--   QMCLeafB analytic core (merged campaign library)
-- statement:
--   The QMC quantum max-cut campaign analytic core.
--
--   This bundle is part of the QMCLeafB library supporting a polynomial-time SDP-value certificate for the quantum max-cut campaign (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QuantumMaxCutFiniteNumericRuntime
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations
import Definitions.Def_QuantumMaxCutEnergyEstimationModel

/-! Full-swarm merge test (m8 probe), with m5's `zpow_neg` qualified as `_root_.zpow_neg`.
Not a deliverable; evidence that the whole set concatenates. -/

/-! #### merged from `Check_LeafB.lean` -/

/-!
# Leaf B reduction: the Max-Cut SDP value sandwich

`ModernConvex.Relaxations.IsMaxcutSDPValue A S` says `S` is the least upper bound of
`X ↦ ¼ ∑ᵢ ∑ⱼ Aᵢⱼ (1 - Xᵢⱼ)` over unit-diagonal positive semidefinite `X`.

This file isolates the *numerical* content of
`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program` from the *runtime* content,
sorry-free:

* `maxcut_objective_eq` : the objective is `(V - tr(A X))/4`, `V = ∑ᵢ ∑ⱼ Aᵢⱼ = 2W`;
* `psd_trace_mul_nonneg` : `0 ≤ tr(M X)` for positive semidefinite `M`, `X`;
* `weak_duality` : `tr(A X) ≤ ∑ᵢ yᵢ` whenever `diagonal y - A ⪰ 0`;
* `sandwich` : a feasible pair `(X, y)` with `diagonal y + A ⪰ 0` and duality gap
  `∑ᵢ yᵢ + tr(A X) ≤ W/2500` gives `L = (V - tr(A X))/4` with `L ≤ S` and
  `S - L ≤ W/10000`.

The only thing not proved here is the *search* for such a pair in polynomial time
(the ellipsoid/interior-point obligation), isolated at the end of the file.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB

variable {n : ℕ}

/-! ### 1. The objective in trace form -/

lemma symm_of_transpose_eq {X : Matrix (Fin n) (Fin n) ℝ} (hX : Xᵀ = X) :
    ∀ i j, X j i = X i j :=
  fun i j => by simpa [Matrix.transpose_apply] using congrFun (congrFun hX i) j

lemma transpose_eq_of_posSemidef {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef) :
    Xᵀ = X := by
  ext i j
  simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using
    congrFun (congrFun hX.1.eq i) j

lemma maxcut_objective_eq (A X : Matrix (Fin n) (Fin n) ℝ) (hX : Xᵀ = X) :
    ModernConvex.Relaxations.maxcutRelaxationObjective A X
      = ((∑ i, ∑ j, A i j) - (A * X).trace) / 4 := by
  have hsym := symm_of_transpose_eq hX
  have htrace : (A * X).trace = ∑ i, ∑ j, A i j * X i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym]
  rw [htrace, ModernConvex.Relaxations.maxcutRelaxationObjective, Finset.mul_sum]
  have hterm : ∀ i, (1 / 4 : ℝ) * ∑ j, A i j * (1 - X i j)
      = (1 / 4 : ℝ) * ((∑ j, A i j) - ∑ j, A i j * X i j) := by
    intro i
    congr 1
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-! ### 2. Traces of products of positive semidefinite matrices -/

lemma trace_mul_vecMulVec_self (M : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) :
    (M * vecMulVec w w).trace = w ⬝ᵥ (M *ᵥ w) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, vecMulVec_apply,
    Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The trace of a product of positive semidefinite matrices is nonnegative. -/
lemma psd_trace_mul_nonneg {M X : Matrix (Fin n) (Fin n) ℝ}
    (hM : M.PosSemidef) (hX : X.PosSemidef) : 0 ≤ (M * X).trace := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  simp only [star_trivial]
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_nonneg fun k _ => ?_
  rw [trace_mul_vecMulVec_self]
  exact hM.dotProduct_mulVec_nonneg (v k)

/-! ### 3. Weak duality -/

lemma trace_diagonal_mul (y : Fin n → ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    (diagonal y * X).trace = ∑ i, y i * X i i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul]

lemma trace_diagonal_mul_of_unitDiag (y : Fin n → ℝ) {X : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ i, X i i = 1) : (diagonal y * X).trace = ∑ i, y i := by
  rw [trace_diagonal_mul]
  exact Finset.sum_congr rfl fun i _ => by rw [h i, mul_one]

/-- **Weak duality.** A feasible dual point bounds `tr (A X)`. -/
theorem weak_duality {A X : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ}
    (hX : X.PosSemidef) (hXdiag : ∀ i, X i i = 1)
    (hy : (diagonal y - A).PosSemidef) :
    (A * X).trace ≤ ∑ i, y i := by
  have h0 : 0 ≤ ((diagonal y - A) * X).trace := psd_trace_mul_nonneg hy hX
  rw [Matrix.sub_mul, Matrix.trace_sub, trace_diagonal_mul_of_unitDiag y hXdiag] at h0
  linarith

/-! ### 4. The sandwich -/

/-- `V = ∑ᵢ ∑ⱼ Aᵢⱼ`, twice the total edge weight of a symmetric weight matrix. -/
noncomputable def V (A : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ i, ∑ j, A i j

/-- The lower value attached to a primal feasible point `X`. -/
noncomputable def lowerValue (A X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (V A - (A * X).trace) / 4

/-- The upper value attached to a dual feasible point `y`. -/
noncomputable def upperValue (A : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ :=
  (V A + ∑ i, y i) / 4

/-- A feasible dual point bounds the SDP value from above. -/
theorem IsMaxcutSDPValue.le_upperValue {A : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S)
    (hy : (diagonal y + A).PosSemidef) : S ≤ upperValue A y := by
  refine hS.2 (Set.forall_mem_image.mpr fun Z hZ => ?_)
  rw [maxcut_objective_eq A Z (transpose_eq_of_posSemidef hZ.1), upperValue, V]
  have hwd : ((-A) * Z).trace ≤ ∑ i, y i := by
    refine weak_duality hZ.1 hZ.2 ?_
    simpa only [Matrix.diagonal_add, sub_neg_eq_add] using hy
  rw [Matrix.neg_mul, Matrix.trace_neg] at hwd
  linarith

/-- A feasible primal point bounds the SDP value from below. -/
theorem le_of_feasible {A X : Matrix (Fin n) (Fin n) ℝ} {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S)
    (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) : lowerValue A X ≤ S := by
  have h := hS.1 ⟨X, ⟨hX, hdiag⟩, rfl⟩
  rwa [maxcut_objective_eq A X (transpose_eq_of_posSemidef hX)] at h

theorem sandwich {A X : Matrix (Fin n) (Fin n) ℝ} {y : Fin n → ℝ} {S : ℝ}
    (hX : X.PosSemidef) (hXdiag : ∀ i, X i i = 1)
    (hy : (diagonal y + A).PosSemidef)
    (hgap : (∑ i, y i) + (A * X).trace ≤ V A / 5000)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue A S) :
    lowerValue A X ≤ S ∧ S - lowerValue A X ≤ V A / 20000 := by
  have hXsym : Xᵀ = X := transpose_eq_of_posSemidef hX
  -- `lowerValue A X` is attained by the feasible point `X`
  have hlow : lowerValue A X = ModernConvex.Relaxations.maxcutRelaxationObjective A X := by
    rw [maxcut_objective_eq A X hXsym, lowerValue, V]
  have hle : lowerValue A X ≤ S := by
    rw [hlow]
    exact hS.1 ⟨X, ⟨hX, hXdiag⟩, rfl⟩
  refine ⟨hle, ?_⟩
  -- `upperValue A y` is an upper bound for the whole feasible image
  have hub : ∀ Z : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD Z →
      ModernConvex.Relaxations.maxcutRelaxationObjective A Z ≤ upperValue A y := by
    intro Z hZ
    rw [maxcut_objective_eq A Z (transpose_eq_of_posSemidef hZ.1), upperValue, V]
    have hwd : ((-A) * Z).trace ≤ ∑ i, y i := by
      refine weak_duality hZ.1 hZ.2 ?_
      simpa only [Matrix.diagonal_add, sub_neg_eq_add] using hy
    rw [Matrix.neg_mul, Matrix.trace_neg] at hwd
    linarith
  have hSle : S ≤ upperValue A y := hS.2 (Set.forall_mem_image.mpr hub)
  have hupper : upperValue A y - lowerValue A X
      = ((∑ i, y i) + (A * X).trace) / 4 := by
    rw [upperValue, lowerValue, V]; ring
  linarith [hSle, hupper, hgap]

end QMCLeafB


/-! ## Part 2: leaf-level assembly -/

namespace QMCLeafB

open QuantumMaxCutEnergy

/-- The weight matrix appearing (verbatim) in the leaf statement. -/
noncomputable def wMatrix (G : Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

@[simp] lemma wMatrix_apply (G : Input) (i j : Fin G.n) :
    wMatrix G i j = (if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) := rfl

lemma wMatrix_apply_of_lt {G : Input} {i j : Fin G.n} (h : i < j) :
    wMatrix G i j = (G.weights ⟨(i, j), h⟩ : ℝ) := by
  rw [wMatrix_apply, dif_pos h]

lemma wMatrix_apply_of_gt {G : Input} {i j : Fin G.n} (h : j < i) :
    wMatrix G i j = (G.weights ⟨(j, i), h⟩ : ℝ) := by
  rw [wMatrix_apply, dif_neg (not_lt.mpr h.le), dif_pos h]

lemma wMatrix_apply_of_eq {G : Input} {i : Fin G.n} : wMatrix G i i = 0 := by
  rw [wMatrix_apply, dif_neg (lt_irrefl i), dif_neg (lt_irrefl i)]

lemma wMatrix_symm (G : Input) : (wMatrix G)ᵀ = wMatrix G := by
  ext i j
  rcases lt_trichotomy i j with h | h | h
  · rw [Matrix.transpose_apply, wMatrix_apply_of_gt h, wMatrix_apply_of_lt h]
  · rw [h]; simp only [Matrix.transpose_apply, wMatrix_apply_of_eq]
  · rw [Matrix.transpose_apply, wMatrix_apply_of_lt h, wMatrix_apply_of_gt h]

lemma wMatrix_nonneg (G : Input) (i j : Fin G.n) : 0 ≤ wMatrix G i j := by
  rw [wMatrix_apply]
  split_ifs <;> positivity

/-- The double sum of the weight matrix is twice the total weight. -/
theorem V_wMatrix (G : Input) : V (wMatrix G) = 2 * ∑ e, (G.weights e : ℝ) := by
  classical
  set U : Fin G.n × Fin G.n → ℝ :=
    fun p => if h : p.1 < p.2 then (G.weights ⟨(p.1, p.2), h⟩ : ℝ) else 0 with hU
  set L : Fin G.n × Fin G.n → ℝ :=
    fun p => if h : p.2 < p.1 then (G.weights ⟨(p.2, p.1), h⟩ : ℝ) else 0 with hL
  have hpt : ∀ i j : Fin G.n, wMatrix G i j = U (i, j) + L (i, j) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · rw [wMatrix_apply_of_lt h, hU, hL]
      simp [dif_pos h, dif_neg (not_lt.mpr h.le)]
    · subst h; rw [wMatrix_apply_of_eq, hU, hL]; simp
    · rw [wMatrix_apply_of_gt h, hU, hL]
      simp [dif_pos h, dif_neg (not_lt.mpr h.le)]
  have hprod : (∑ p : Fin G.n × Fin G.n, wMatrix G p.1 p.2) = ∑ i, ∑ j, wMatrix G i j :=
    Fintype.sum_prod_type (f := fun p : Fin G.n × Fin G.n => wMatrix G p.1 p.2)
  have hupper : ∑ p : Fin G.n × Fin G.n, U p = ∑ e : Edge G.n, (G.weights e : ℝ) := by
    simp only [hU]
    exact (Fintype.sum_of_injective (fun e : Edge G.n => (e.val : Fin G.n × Fin G.n))
      (fun a b hab => Subtype.ext hab) (fun e => (G.weights e : ℝ))
      (fun p => if h : p.1 < p.2 then (G.weights ⟨(p.1, p.2), h⟩ : ℝ) else 0)
      (fun p hp => by
        have hlt : ¬ p.1 < p.2 := fun h => hp ⟨⟨p, h⟩, rfl⟩
        rw [dif_neg hlt])
      (fun e => by rw [dif_pos e.2])).symm
  have hswap : ∑ p : Fin G.n × Fin G.n, L p = ∑ p : Fin G.n × Fin G.n, U p := by
    have : ∀ p : Fin G.n × Fin G.n, L p = U (p.2, p.1) := by
      intro p
      rw [hL, hU]
    rw [Finset.sum_congr rfl (fun p _ => this p)]
    exact Equiv.sum_comp (Equiv.prodComm (Fin G.n) (Fin G.n)) U
  rw [V, ← hprod]
  have h2 : (∑ p : Fin G.n × Fin G.n, wMatrix G p.1 p.2) = (∑ p, U p) + (∑ p, L p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hpt p.1 p.2
  rw [h2, hswap, hupper]
  ring

/-- Off-diagonal entries of a unit-diagonal PSD matrix are at most one. -/
lemma posSemidef_apply_le_one {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) (i j : Fin n) : X i j ≤ 1 := by
  classical
  have hM : (X.submatrix ![i, j] ![i, j]).PosSemidef := hX.submatrix _
  have hv := hM.dotProduct_mulVec_nonneg (fun k : Fin 2 => if k = 0 then (1 : ℝ) else -1)
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Fin.sum_univ_two,
    star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Fin.isValue, Fin.reduceFinMk, zero_add, hdiag] at hv
  norm_num at hv
  have hsym : X j i = X i j := symm_of_transpose_eq (transpose_eq_of_posSemidef hX) i j
  rw [hsym] at hv
  linarith

/-- `lowerValue` is nonnegative for entrywise nonnegative data. -/
lemma lowerValue_nonneg {n : ℕ} {A X : Matrix (Fin n) (Fin n) ℝ}
    (hA : ∀ i j, 0 ≤ A i j) (hX : X.PosSemidef) (hdiag : ∀ i, X i i = 1) :
    0 ≤ lowerValue A X := by
  have hXsym : ∀ i j, X j i = X i j := symm_of_transpose_eq (transpose_eq_of_posSemidef hX)
  have htrace : (A * X).trace = ∑ i, ∑ j, A i j * X i j := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hXsym]
  have hle : (A * X).trace ≤ V A := by
    rw [htrace, V]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have h1 := hA i j
    have h2 := posSemidef_apply_le_one hX hdiag i j
    nlinarith
  rw [lowerValue]
  linarith

/-- **The numerical endgame of Leaf B.** A family of certified primal/dual pairs with
duality gap at most `W/2500` yields the leaf's sandwich with `L = lowerValue`. -/
theorem leafB_sandwich (X : ∀ G : Input, Matrix (Fin G.n) (Fin G.n) ℝ)
    (y : ∀ G : Input, Fin G.n → ℝ)
    (hX : ∀ G, (X G).PosSemidef) (hdiag : ∀ G i, X G i i = 1)
    (hy : ∀ G, (diagonal (y G) + wMatrix G).PosSemidef)
    (hgap : ∀ G, (∑ i, y G i) + (wMatrix G * X G).trace ≤ V (wMatrix G) / 5000)
    (hS : ∀ G : Input, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (wMatrix G) S) :
    ∀ G : Input, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (wMatrix G) S ∧
      lowerValue (wMatrix G) (X G) ≤ S ∧
      S - lowerValue (wMatrix G) (X G) ≤ (∑ e, (G.weights e : ℝ)) / 10000 := by
  intro G
  obtain ⟨S, hS'⟩ := hS G
  obtain ⟨hle, hulp⟩ := sandwich (hX G) (hdiag G) (hy G) (hgap G) hS'
  refine ⟨S, hS', hle, ?_⟩
  rw [V_wMatrix] at hulp
  linarith

end QMCLeafB


/-! #### merged from `Check_Enc.lean` -/

/-!
# Self-delimiting number blocks in the QMC input encoding

`QuantumMaxCutEnergy.encodeNumber` writes `k` as

  `encodeNumber k = (List.replicate bits.length true) ++ [false] ++ bits`,
  `bits = Computability.encodeNat k`,

i.e. the binary expansion of `k` prefixed by a unary copy of its own length.  The binary
expansion `encodeNat` on its own is *not* prefix-free (`[true]` is a prefix of
`[true, true]`), so the unary length is what makes the code readable off a stream.  Any
`PolyProgram` meant to read a weighted graph off `encodeInput` has to parse these blocks,
so this file supplies the decoder and its correctness proof.  It is the string-level layer
underneath `encodeInput`; it says nothing about either leaf's analysis.
-/

namespace QuantumMaxCutEnergy

open Computability

/-- `takeTrues l` is the length of the initial run of `true` in `l`, together with the
remainder of the list. -/
def takeTrues : List Bool → ℕ × List Bool
  | [] => (0, [])
  | true :: l => ((takeTrues l).1 + 1, (takeTrues l).2)
  | false :: l => (0, false :: l)

@[simp] theorem takeTrues_false (l : List Bool) : takeTrues (false :: l) = (0, false :: l) :=
  rfl

theorem takeTrues_true (l : List Bool) :
    takeTrues (true :: l) = ((takeTrues l).1 + 1, (takeTrues l).2) := rfl

theorem takeTrues_replicate_append (m : ℕ) (l : List Bool) :
    takeTrues (List.replicate m true ++ l) = ((takeTrues l).1 + m, (takeTrues l).2) := by
  induction m with
  | zero =>
      rw [List.replicate_zero, List.nil_append]
      simp
  | succ m ih =>
      rw [List.replicate_succ, List.cons_append, takeTrues_true, ih]
      simp only [Nat.add_assoc]

theorem takeTrues_encodeNumber (k : ℕ) (rest : List Bool) :
    takeTrues (encodeNumber k ++ rest) =
      ((Computability.encodeNat k).length, false :: (Computability.encodeNat k ++ rest)) := by
  have h : encodeNumber k ++ rest =
      List.replicate (Computability.encodeNat k).length true ++
        (false :: (Computability.encodeNat k ++ rest)) := by
    unfold encodeNumber
    simp [List.append_assoc]
  rw [h, takeTrues_replicate_append, takeTrues_false]
  simp

/-- Read one `encodeNumber` block off the front of a bit list. -/
def decodeNumber (l : List Bool) : Option (ℕ × List Bool) :=
  match takeTrues l with
  | (m, false :: rest) =>
      if rest.length < m then none
      else some (Computability.decodeNat (rest.take m), rest.drop m)
  | _ => none

theorem take_append_self : ∀ (l₁ l₂ : List Bool), (l₁ ++ l₂).take l₁.length = l₁
  | [], _ => rfl
  | _ :: l₁, l₂ => by
      simp only [List.cons_append, List.length_cons, List.take_succ_cons]
      rw [take_append_self l₁ l₂]

theorem drop_append_self : ∀ (l₁ l₂ : List Bool), (l₁ ++ l₂).drop l₁.length = l₂
  | [], _ => rfl
  | _ :: l₁, l₂ => by
      simp only [List.cons_append, List.length_cons, List.drop_succ_cons]
      rw [drop_append_self l₁ l₂]

/-- The decoder inverts `encodeNumber` on the nose and leaves trailing bits untouched. -/
theorem encodeNumber_decode (k : ℕ) (rest : List Bool) :
    decodeNumber (encodeNumber k ++ rest) = some (k, rest) := by
  unfold decodeNumber
  rw [takeTrues_encodeNumber]
  have hlen : ¬ (Computability.encodeNat k ++ rest).length < (Computability.encodeNat k).length := by
    simp
  dsimp only
  rw [if_neg hlen, take_append_self, drop_append_self, Computability.decode_encodeNat]

/-- The number code is injective: the unary length prefix makes the block unambiguous. -/
theorem encodeNumber_injective : Function.Injective encodeNumber := by
  intro a b hab
  have h1 : decodeNumber (encodeNumber b ++ []) = some (a, []) := by
    rw [← hab]
    exact encodeNumber_decode a []
  have h2 : decodeNumber (encodeNumber b ++ []) = some (b, []) := encodeNumber_decode b []
  rw [h1] at h2
  exact congrArg Prod.fst (Option.some.inj h2)

/-- Prefix-free form: a block never sits properly inside another block. -/
theorem encodeNumber_prefix_free {a b : ℕ} (h : encodeNumber a <+: encodeNumber b) : a = b := by
  obtain ⟨t, ht⟩ := h
  have hd : decodeNumber (encodeNumber a ++ t) = some (a, t) := encodeNumber_decode a t
  rw [ht] at hd
  have hb : decodeNumber (encodeNumber b ++ []) = some (b, []) := encodeNumber_decode b []
  rw [List.append_nil] at hb
  rw [hb] at hd
  exact (congrArg Prod.fst (Option.some.inj hd)).symm

/-- Length of one block: `2 * |encodeNat k| + 1` bits, so a program can advance its read
head by a computable amount. -/
theorem encodeNumber_length (k : ℕ) :
    (encodeNumber k).length = 2 * (Computability.encodeNat k).length + 1 := by
  unfold encodeNumber
  simp [List.length_append, List.length_replicate]
  omega

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy

open Computability

/-- Decode exactly `m` successive `encodeNumber` blocks.  A program always knows how many
weights to read, so the counted form is the one it needs. -/
def decodeNumbers : ℕ → List Bool → Option (List ℕ)
  | 0, _ => some []
  | m + 1, l =>
      match decodeNumber l with
      | none => none
      | some (q, l') => (decodeNumbers m l').map (fun qs => q :: qs)

theorem decodeNumbers_flatMap (m : ℕ) (qs : List ℕ) (rest : List Bool)
    (hlen : qs.length = m) :
    decodeNumbers m (qs.flatMap (fun q => encodeNumber q) ++ rest) = some qs := by
  induction qs generalizing m with
  | nil =>
      subst hlen
      simp [decodeNumbers]
  | cons q qs ih =>
      have hstep : (q :: qs).flatMap (fun r => encodeNumber r) ++ rest =
          encodeNumber q ++ (qs.flatMap (fun r => encodeNumber r) ++ rest) := by simp
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := by
        have : 0 < m := by simp at hlen; omega
        exact ⟨m - 1, by omega⟩
      rw [hstep]
      simp only [decodeNumbers]
      rw [encodeNumber_decode]
      dsimp only
      have hqs : qs.length = m' := by simp at hlen; omega
      rw [ih m' hqs]
      simp

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy

open Computability

/-- Decode a body consisting of `m` `encodeNumber` blocks, where `m` is a fuel bound; the
caller supplies a bound it knows (for a graph body it is the number of weights). -/
def decodeAll : ℕ → List Bool → Option (List ℕ)
  | 0, l => if l = [] then some [] else none
  | m + 1, l =>
      (decodeNumber l).bind (fun p => (decodeAll m p.2).map (fun qs => p.1 :: qs))

theorem decodeAll_succ (m : ℕ) (l : List Bool) :
    decodeAll (m + 1) l =
      (decodeNumber l).bind (fun p => (decodeAll m p.2).map (fun qs => p.1 :: qs)) := rfl

/-- A body that is exactly a concatenation of `encodeNumber` blocks decodes back to the
same list of numbers. -/
theorem decodeAll_flatMap (qs : List ℕ) :
    decodeAll qs.length (qs.flatMap (fun q => encodeNumber q)) = some qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
      have hstep : (q :: qs).flatMap (fun r => encodeNumber r) =
          encodeNumber q ++ qs.flatMap (fun r => encodeNumber r) := by simp
      rw [hstep, List.length_cons, decodeAll_succ, encodeNumber_decode]
      simp only [Option.bind_some]
      rw [ih]
      rfl

/-- The part of `encodeInput` after the order and its separator: the weights, edge by edge
in the order `(0,1),(0,2),…,(0,n-1),(1,2),…`, numerator then denominator. -/
def encodeInputBody (G : Input) : List Bool :=
  (List.finRange G.n).flatMap (fun i =>
    (List.finRange G.n).flatMap (fun j =>
      if hij : i < j then
        let q := G.weights ⟨(i, j), hij⟩
        encodeNumber q.num ++ encodeNumber q.den
      else []))

theorem encodeInput_eq (G : Input) :
    encodeInput G = List.replicate G.n true ++ (false :: encodeInputBody G) := by
  unfold encodeInput encodeInputBody
  simp [List.append_assoc]

/-- The order header is read off unambiguously: `n` is the length of the initial run of
`true`. -/
theorem takeTrues_encodeInput (G : Input) (rest : List Bool) :
    takeTrues (encodeInput G ++ rest) = (G.n, false :: (encodeInputBody G ++ rest)) := by
  have h : encodeInput G ++ rest =
      List.replicate G.n true ++ (false :: (encodeInputBody G ++ rest)) := by
    rw [encodeInput_eq]
    simp [List.append_assoc]
  rw [h, takeTrues_replicate_append, takeTrues_false]
  simp

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy

open Computability

/-- The numbers carried by a graph body, in order: for each edge `i < j` in the enumeration
`(0,1),(0,2),…`, the numerator and then the denominator of its weight. -/
def weightValues (G : Input) : List ℕ :=
  (List.finRange G.n).flatMap (fun i =>
    (List.finRange G.n).flatMap (fun j =>
      if hij : i < j then
        let q := G.weights ⟨(i, j), hij⟩
        [q.num, q.den]
      else []))

/-- The body of `encodeInput` is exactly the concatenation of the blocks of those numbers. -/
theorem encodeInputBody_eq (G : Input) :
    encodeInputBody G = (weightValues G).flatMap (fun q => encodeNumber q) := by
  unfold encodeInputBody weightValues
  simp only [List.flatMap_assoc]
  refine List.flatMap_congr (fun i _ => ?_)
  refine List.flatMap_congr (fun j _ => ?_)
  split_ifs with hij <;> simp

/-- Hence the weight part of an encoded graph decodes back to its number list. -/
theorem encodeInputBody_decode (G : Input) :
    decodeAll (weightValues G).length (encodeInputBody G) = some (weightValues G) := by
  rw [encodeInputBody_eq]
  exact decodeAll_flatMap (weightValues G)

end QuantumMaxCutEnergy

namespace QuantumMaxCutEnergy

open Computability

/-- Bit length of an encoded graph. -/
theorem encodeInput_length (G : Input) :
    (encodeInput G).length = G.n + 1 + (encodeInputBody G).length := by
  rw [encodeInput_eq]
  simp [List.length_append, List.length_replicate]
  omega

/-- The order is bounded by the input length: this is what turns an input-length time bound
into a bound in terms of `n` (Leaf B's `PolyProgram` needs it to talk about `n × n`
matrices at all). -/
theorem n_le_encodeInput_length (G : Input) : G.n ≤ (encodeInput G).length := by
  rw [encodeInput_length]
  omega

/-- Every number block is nonempty, so each weight costs at least one bit and the body is at
least as long as the number of numbers in it. -/
theorem encodeNumber_length_pos (k : ℕ) : 0 < (encodeNumber k).length := by
  rw [encodeNumber_length]
  omega

end QuantumMaxCutEnergy


/-! #### merged from `Check_tm2size.lean` -/

/-!
# Leaf B — `brick-tm2-size`: a runtime/size-analysis toolkit for composition chains

This file supplies the size half of the finite Boolean-machine runtime framework
(`OAI.MetricKMedian.Binary`, from `Definitions.Def_QuantumMaxCutFiniteNumericRuntime`),
namely the lemmas needed to turn an opaque `PolyProgram.sizeBound` into an *explicit
monomial* bound `C * (L+1)^d` on the encoded output length, and to propagate such
bounds through composition chains.

Contents
1. Polynomial evaluation toolkit (monotonicity, coefficient-sum → monomial domination,
   degree bookkeeping for `+`, `*`, `comp`).
2. `sizeBound`-level lemmas: degree bound, monomial evaluation bound, and the
   consequence `length_bound_pow` for the encoded output of *any* `PolyProgram`.
3. Size profiles (`SizeProfile`) and their closure under composition: a two-stage
   monomial chain lemma (degrees multiply), a three-stage corollary, and degree /
   evaluation bookkeeping for `PolyProgram.compTime`.
4. The `k`-fold chain: `chainPoly` with an explicit recursive constant `chainConst`
   and the bound `(chainPoly s k).eval L ≤ chainConst (s.eval 1) s.natDegree k * (L+1)^(d^k)`,
   plus a computable monomial interface (`monoBound`, `chainPair`, `chainPairIter`).
5. Instantiations for the list/`ℚ` programs of the `LeafB_MatQ` dependency graph, plus
   structural size rules for `fanout`/`product`/`exchange`/`duplicate`/`listCons`.
6. Computability checks for the chain data (7. Axiom report).

Everything is over `Polynomial ℕ` evaluated at `ℕ`, so each claim is a kernel-checked
natural-number inequality. Deviation from the brick sketch: the polynomial carrier is
Mathlib's `Polynomial ℕ` rather than a bespoke `List ℚ` polynomial, because
`Polynomial.eval_mono`-style lemmas, `natDegree_add_le`/`natDegree_mul_le`/`natDegree_comp_le`
and `eval_comp` are already proved there; `Polynomial.eval 1` is the coefficient sum.

## Interface for the coordinator

* `length_bound_pow P a` — for **any** `P : PolyProgram ea eb f` and input `a`, the encoded
  output length is `≤ (P.time.eval 1 * P.machine.growth + 1) * ((ea a).length + 1)^(max 1 P.time.natDegree)`.
  This is the pulled-out form of `P.length_bound` with the opaque `sizeBound` replaced by an
  explicit monomial.
* `length_bound_pow_of_le P C d hC hd a` — the same with user-chosen numerals `C`, `d`; the
  side goals `hC : P.time.eval 1 * P.machine.growth + 1 ≤ C` and `hd : max 1 P.time.natDegree ≤ d`
  only mention `P.time` and `P.machine`, so they can be discharged once per program (by
  `decide`/`norm_num` where the time polynomial is given by an explicit expression, or by
  supplying the numerals read off the definition).
* `comp_length_bound_pow hP hQ` — two-stage chain: degrees multiply, constants explicit
  (`(Cp,dp)` then `(Cq,dq)` gives `(Cq*(Cp+1)^dq, dp*dq)`); `comp3_length_bound_pow` is the
  three-stage version. `comp_length_bound_pair` states the same with `monoBound`/`chainPair`.
* `SizeProfile P s` + `SizeProfile.comp` — a `sizeBound`-free way to carry a size polynomial
  through a composition chain (`t.comp s`), with `sizeProfile_monoBound` giving the monomial
  instance `C * (X+1)^d`.
* `chainPoly_eval_le` / `chainPairIter` — a `k`-stage chain of identical bounds costs
  `chainConst C d k * (L+1)^(d^k)`, and `chainPairIter` computes the pair `(C_k, d^k)`.
* `compTime_natDegree_le`, `sizeBound_comp_natDegree_le` — degree bookkeeping for `P.comp Q`.
* `listMap_length_bound`, `listMapWith_length_bound`, `listZip_length_bound` — list-shaped
  bounds (entry count preserved, entry size bounded by `P.sizeBound`), which is the shape
  `matVec`/`matMul` need. `listMapWith_length_bound` is the one matching `PolyProgram.listMapWith`,
  the construction `LeafB_MatQ` needs since `fun_prop` fails on list-mapped functions.
* `fanout_length_bound_pair`, `product_length_bound_pair` — the monomial pair rules of the
  structural constructors: two branches bounded by `(Cp,dp)` and `(Cq,dq)` give a paired output
  bounded by `(2*Cp + Cq + 1, max dp dq)`. Together with `comp_length_bound_pow`/`chainPair`
  this bounds a whole `fanout`/`product`/`listMapWith` dependency graph without ever unfolding
  `sizeBound`. `duplicate_length_bound`, `exchange_length_bound`, `listCons_length_bound` are
  the exact (resp. factor-2) bookkeeping lemmas for the remaining constructors.
* `steps_le_time`, `steps_le_monomial`, `comp_steps_le`, `length_le_input_add_steps` — the
  runtime half: the actual step count of a run is at most the explicit monomial
  `P.time.eval 1 * (L+1)^(P.time.natDegree)`, and for a composition at most
  `P.time.eval L + 2*P.sizeBound.eval L + 2 + Q.time.eval (P.sizeBound.eval L)`.

## Checklist against the brick specification

* (i) `machine.output_length`-level size estimates, `output encoded length ≤ poly(L)`:
  `output_length_le`, `length_bound_pow`, `length_bound_pow_of_le`, `steps_le_monomial`
  (+ per-program anchors `ratAdd_length_bound`, `ratMul_length_bound`,
  `ratFoldAdd_length_bound`, `ratSum_length_bound`, `listMap_length_bound`,
  `listMapWith_length_bound`, `listZip_length_bound`).
* (ii) `sizeBound`-aware composition forms of `PolyProgram.comp` chains:
  `SizeProfile`, `SizeProfile.comp`, `SizeProfile.congr`, `sizeProfile_monoBound`,
  `sizeProfile_comp_monoBound`, `compTime_eval_le`, `compTime_natDegree_le`,
  `sizeBound_comp_natDegree_le`, `comp_length_bound_pow`, `comp_length_bound_pow_sizeBound`,
  `comp3_length_bound_pow`, `comp_length_bound_pow_pair`, `comp_steps_le`,
  `fanout_length_bound_pair`, `product_length_bound_pair`, `pair_arith`.
* (iii) `polyEval_mono` / `polynomial_eval_mono` family:
  `polyEval_mono` (self-contained proof), `eval_le_sum_coeff_mul_pow`,
  `eval_one_eq_sum_coeff`, `eval_le_eval_one_mul_pow`, `sizeBound_eval_mono`,
  `natDegree_add_le'`, `natDegree_mul_le'`, `natDegree_comp_le'`, `natDegree_natCast_le`,
  `natDegree_one_le`.
* extra: the `k`-fold chain (`chainPoly`, `chainConst`, `chainPoly_eval_le`,
  `natDegree_chainPoly_le`, `chainPairIter`, `chainPairIter_fst`, `chainPairIter_snd`).
-/

/-! ## 0. Usage recipe (three lines per chain link)

```lean
-- 1. monomial data for each program in the chain
have h1 := length_bound_pow P a                      -- (Cp, dp)
-- 2. link two programs; the degrees multiply
have h2 := comp_length_bound_pow (f := f) (g := g) hP hQ
-- 3. read off numerals with `length_bound_pow_of_le P C d hC hd` for the final statement
```
-/

namespace OAI
namespace MetricKMedian.Binary
namespace LeafB.Tm2Size

open Polynomial

/-! ## 1. Polynomial evaluation toolkit -/

/-- Evaluation of a `ℕ`-coefficient polynomial is monotone in the argument. -/
theorem polyEval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n x =>
      simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left x (Nat.pow_le_pow_left h n)

/-- The value at `1` of a `ℕ`-polynomial is the sum of its coefficients. -/
theorem eval_one_eq_sum_coeff (p : Polynomial ℕ) :
    p.eval 1 = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i := by
  rw [Polynomial.eval_eq_sum_range]
  simp

/-- A `ℕ`-polynomial is dominated by `(sum of coefficients) * (n+1)^(natDegree p)`. -/
theorem eval_le_sum_coeff_mul_pow (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ p.natDegree := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  have hid : i ≤ p.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  have h1 : n ^ i ≤ (n + 1) ^ i := Nat.pow_le_pow_left (Nat.le_succ n) i
  have h2 : (n + 1) ^ i ≤ (n + 1) ^ p.natDegree := Nat.pow_le_pow_right (Nat.succ_pos n) hid
  exact Nat.mul_le_mul_left (p.coeff i) (h1.trans h2)

/-- `p.eval n ≤ p.eval 1 * (n+1)^(natDegree p)`: every `ℕ`-polynomial is dominated by its
coefficient sum times the corresponding power. This is the lemma that turns an opaque
`PolyProgram.time`/`sizeBound` into an explicit monomial bound. -/
theorem eval_le_eval_one_mul_pow (p : Polynomial ℕ) (n : ℕ) :
    p.eval n ≤ p.eval 1 * (n + 1) ^ p.natDegree := by
  calc p.eval n
      ≤ (∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i) * (n + 1) ^ p.natDegree :=
        eval_le_sum_coeff_mul_pow p n
    _ = p.eval 1 * (n + 1) ^ p.natDegree := by rw [eval_one_eq_sum_coeff]

/-- Monotonicity in the argument, bundled with an evaluation identity for sums. -/
theorem eval_add_le (p q : Polynomial ℕ) (n : ℕ) :
    (p + q).eval n ≤ p.eval n + q.eval n := by
  rw [Polynomial.eval_add]

/-- Evaluation of a product is the product of evaluations. -/
theorem eval_mul_eq (p q : Polynomial ℕ) (n : ℕ) :
    (p * q).eval n = p.eval n * q.eval n := by
  rw [Polynomial.eval_mul]

/-- Evaluation of a composition is the composition of evaluations. -/
theorem eval_comp_eq (p q : Polynomial ℕ) (n : ℕ) :
    (p.comp q).eval n = p.eval (q.eval n) := by
  rw [Polynomial.eval_comp]

/-! ### Degree bookkeeping -/

theorem natDegree_add_le' (p q : Polynomial ℕ) :
    (p + q).natDegree ≤ max p.natDegree q.natDegree := Polynomial.natDegree_add_le p q

theorem natDegree_mul_le' (p q : Polynomial ℕ) :
    (p * q).natDegree ≤ p.natDegree + q.natDegree := Polynomial.natDegree_mul_le

theorem natDegree_comp_le' (p q : Polynomial ℕ) :
    (p.comp q).natDegree ≤ p.natDegree * q.natDegree := Polynomial.natDegree_comp_le

theorem natDegree_natCast_le (c : ℕ) : (c : Polynomial ℕ).natDegree ≤ 0 := by
  rw [Polynomial.natDegree_natCast]

theorem natDegree_one_le : (1 : Polynomial ℕ).natDegree ≤ 0 := by
  rw [Polynomial.natDegree_one]


/-! ## 2. From `sizeBound` to an explicit monomial bound -/

/-- Unfolding of `PolyProgram.sizeBound`. -/
theorem sizeBound_def {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) :
    P.sizeBound = Polynomial.X + P.time * Polynomial.C P.machine.growth := rfl

/-- The degree of the size bound of a program is at most the degree of its time bound
(and at least `1` because of the additive `X`). -/
theorem sizeBound_natDegree_le {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) :
    P.sizeBound.natDegree ≤ max 1 P.time.natDegree := by
  rw [sizeBound_def]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_X]
    exact le_max_left _ _
  · have h := Polynomial.natDegree_mul_le (p := P.time) (q := Polynomial.C P.machine.growth)
    rw [Polynomial.natDegree_C, Nat.add_zero] at h
    exact h.trans (le_max_right _ _)

/-- Explicit evaluation bound for `sizeBound`: at input length `L` it is at most
`(L+1) + (sum of coefficients of the time bound) * (L+1)^(deg time) * growth`. -/
theorem sizeBound_eval_le {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) (L : ℕ) :
    P.sizeBound.eval L ≤ (L + 1) + P.time.eval 1 * (L + 1) ^ P.time.natDegree * P.machine.growth := by
  rw [sizeBound_def]
  simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
  have h := eval_le_eval_one_mul_pow P.time L
  have h2 := Nat.mul_le_mul_right P.machine.growth h
  omega

/-- Pure arithmetic step used to collect `(L+1) + t * (L+1)^d * g` into a single monomial. -/
theorem arith_collect (L t1 d g : ℕ) :
    (L + 1) + t1 * (L + 1) ^ d * g ≤ (t1 * g + 1) * (L + 1) ^ max 1 d := by
  have hN : 0 < L + 1 := Nat.succ_pos L
  have h1 : L + 1 ≤ (L + 1) ^ max 1 d := by
    simpa using Nat.pow_le_pow_right hN (le_max_left 1 d)
  have h2 : (L + 1) ^ d ≤ (L + 1) ^ max 1 d := Nat.pow_le_pow_right hN (le_max_right 1 d)
  have h3 : t1 * (L + 1) ^ d * g ≤ t1 * g * (L + 1) ^ max 1 d := by
    calc t1 * (L + 1) ^ d * g ≤ t1 * (L + 1) ^ max 1 d * g :=
          Nat.mul_le_mul_right g (Nat.mul_le_mul_left t1 h2)
      _ = t1 * g * (L + 1) ^ max 1 d := by ring
  calc (L + 1) + t1 * (L + 1) ^ d * g
      ≤ (L + 1) ^ max 1 d + t1 * g * (L + 1) ^ max 1 d := Nat.add_le_add h1 h3
    _ = (t1 * g + 1) * (L + 1) ^ max 1 d := by ring

/-- **Explicit size bound for an arbitrary `PolyProgram`.** On an input encoded in
`(ea a).length ≤ L` bits, the encoded output has at most
`(P.time.eval 1 * P.machine.growth + 1) * (L+1)^(max 1 P.time.natDegree)` bits. The two
numbers `P.time.eval 1` (coefficient sum) and `P.time.natDegree` are checkable by
`decide`/`norm_num` once the program is explicit. -/
theorem length_bound_pow {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤
      (P.time.eval 1 * P.machine.growth + 1) * ((ea a).length + 1) ^ max 1 P.time.natDegree := by
  refine (P.length_bound a).trans ?_
  exact (sizeBound_eval_le P (ea a).length).trans (arith_collect _ _ _ _)

/-- Monotonicity of `sizeBound` in the input length. -/
theorem sizeBound_eval_mono {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) {L₁ L₂ : ℕ} (h : L₁ ≤ L₂) :
    P.sizeBound.eval L₁ ≤ P.sizeBound.eval L₂ :=
  polyEval_mono P.sizeBound h

/-- `Machine.output_length` restated with an explicit time estimate `T`. -/
theorem output_length_le {M : Machine} {s t : List Bool} {n T : ℕ}
    (h : Turing.TM2OutputsInTime M.tm s (some t) n) (hn : n ≤ T) :
    t.length ≤ s.length + T * M.growth := by
  refine (M.output_length h).trans ?_
  exact Nat.add_le_add_left (Nat.mul_le_mul_right M.growth hn) _



/-! ### Step counts

`length_bound_pow` controls the *size* of what a program writes. The runtime half of the brick
is the same statement for the *number of Turing-machine steps*: the `steps` field of the
`TM2OutputsInTime` witness is bounded by the (monomial form of the) declared time polynomial. -/

/-- The actual number of steps of a `PolyProgram` is at most its declared time. -/
theorem steps_le_time {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) (a : α) : (P.outputs a).steps ≤ P.time.eval (ea a).length :=
  (P.outputs a).steps_le_m

/-- **Explicit step bound for any `PolyProgram`**: `(sum of coefficients of the time
polynomial) * (L+1)^(natDegree of the time polynomial)`. -/
theorem steps_le_monomial {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) (a : α) :
    (P.outputs a).steps ≤ P.time.eval 1 * ((ea a).length + 1) ^ P.time.natDegree :=
  (steps_le_time P a).trans (eval_le_eval_one_mul_pow P.time _)

/-- `Machine.output_length` at the level of a single `PolyProgram` run: the encoded output is
at most the input plus `steps * growth` bits. -/
theorem length_le_input_add_steps {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ (ea a).length + (P.outputs a).steps * P.machine.growth := by
  have ht : Trace P.machine.step (P.outputs a).steps
      (P.machine.initialCfg (ea a)) (P.machine.finalCfg (eb (f a))) :=
    Trace.of_iterate (P.outputs a).evals_in_steps
  simpa using P.machine.trace_volume ht


/-- Identity programs have the unit size profile `1 * (L+1)^1`, the base case of every chain. -/
theorem identity_length_bound {α : Type} (ea : α → List Bool) (a : α) :
    (ea (id a)).length ≤ 1 * ((ea a).length + 1) ^ 1 := by
  simp

/-- Constant programs have the size profile `(eb b).length * (L+1)^0`, the other base case. -/
theorem constant_length_bound {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (b : β)
    (a : α) : (eb b).length ≤ (eb b).length * ((ea a).length + 1) ^ 0 := by
  simp

/-! ## 3. Size profiles and composition chains -/

/-- A `SizeProfile P s` records that `s` dominates the encoded output length of `P`
on every input. `sizeProfile_sizeBound` shows that `P.sizeBound` is always such an `s`;
the point of the structure is that one may replace it by a cleaner monomial. -/
structure SizeProfile {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) (s : Polynomial ℕ) : Prop where
  bound : ∀ a, (eb (f a)).length ≤ s.eval (ea a).length

theorem sizeProfile_sizeBound {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) : SizeProfile P P.sizeBound :=
  ⟨fun a => P.length_bound a⟩

theorem SizeProfile.mono {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {P : PolyProgram ea eb f} {s t : Polynomial ℕ} (h : SizeProfile P s)
    (hst : ∀ n, s.eval n ≤ t.eval n) : SizeProfile P t :=
  ⟨fun a => (h.bound a).trans (hst _)⟩

/-- **Composition of size profiles**: a stage with profile `s` followed by a stage with
profile `t` has profile `t.comp s`. No growth/`sizeBound` bookkeeping is needed. -/
theorem SizeProfile.comp {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} {P : PolyProgram ea eb f}
    {Q : PolyProgram eb ec g} {s t : Polynomial ℕ} (hP : SizeProfile P s)
    (hQ : SizeProfile Q t) : SizeProfile (P.comp Q) (t.comp s) := by
  refine ⟨fun a => ?_⟩
  have h1 : (eb (f a)).length ≤ s.eval (ea a).length := hP.bound a
  have h2 : (ec (g (f a))).length ≤ t.eval ((eb (f a)).length) := hQ.bound (f a)
  calc (ec ((g ∘ f) a)).length = (ec (g (f a))).length := rfl
    _ ≤ t.eval ((eb (f a)).length) := h2
    _ ≤ t.eval (s.eval (ea a).length) := polyEval_mono t h1
    _ = (t.comp s).eval (ea a).length := by rw [Polynomial.eval_comp]

/-- Size profiles transport across `PolyProgram.congr`. -/
theorem SizeProfile.congr {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f f' : α → β} {P : PolyProgram ea eb f} {s : Polynomial ℕ} (h : SizeProfile P s)
    (hff : ∀ a, f a = f' a) : SizeProfile (P.congr f' hff) s := by
  refine ⟨fun a => ?_⟩
  have hb := h.bound a
  simpa only [hff a] using hb

/-- Evaluation form of `PolyProgram.compTime`. -/
theorem compTime_eval_le {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (P : PolyProgram ea eb f)
    (Q : PolyProgram eb ec g) (L : ℕ) :
    (P.compTime Q).eval L
      ≤ P.time.eval L + 2 * P.sizeBound.eval L + 2 + Q.time.eval (P.sizeBound.eval L) := by
  simp only [PolyProgram.compTime, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    Polynomial.eval_ofNat]
  exact le_rfl

/-- **Degree bookkeeping for a two-stage chain.** The time degree of `P.comp Q` is at most
`max 1 (deg P.time)` for the first stage's own work/size, or `deg Q.time * max 1 (deg P.time)`
for the second stage run on outputs of the first. -/
theorem compTime_natDegree_le {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (P : PolyProgram ea eb f)
    (Q : PolyProgram eb ec g) :
    (P.compTime Q).natDegree
      ≤ max (max 1 P.time.natDegree) (Q.time.natDegree * max 1 P.time.natDegree) := by
  have hS : P.sizeBound.natDegree ≤ max 1 P.time.natDegree := sizeBound_natDegree_le P
  have hzero : ((2 : Polynomial ℕ)).natDegree = 0 := Polynomial.natDegree_natCast 2
  have h2 : (2 * P.sizeBound : Polynomial ℕ).natDegree ≤ max 1 P.time.natDegree := by
    refine (Polynomial.natDegree_mul_le (p := (2 : Polynomial ℕ)) (q := P.sizeBound)).trans ?_
    rw [hzero, Nat.zero_add]
    exact hS
  have hcomp : (Q.time.comp P.sizeBound).natDegree
      ≤ Q.time.natDegree * max 1 P.time.natDegree := by
    refine (Polynomial.natDegree_comp_le).trans ?_
    exact Nat.mul_le_mul_left _ hS
  have key : (P.time + 2 * P.sizeBound + 2 + Q.time.comp P.sizeBound).natDegree
      ≤ max (max 1 P.time.natDegree) (Q.time.natDegree * max 1 P.time.natDegree) := by
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
        · exact (le_max_right 1 P.time.natDegree).trans (le_max_left _ _)
        · exact h2.trans (le_max_left _ _)
      · rw [hzero]
        exact Nat.zero_le _
    · exact hcomp.trans (le_max_right _ _)
  rw [PolyProgram.compTime]
  exact key

/-- **Step bound for a composed program**, in the shape of `PolyProgram.compTime`'s evaluation:
the first stage's own time, its size bound (which pays for writing its output twice: once for
the transfer and once for the second stage's input), and the second stage's time at that size. -/
theorem comp_steps_le {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (P : PolyProgram ea eb f)
    (Q : PolyProgram eb ec g) (a : α) :
    ((P.comp Q).outputs a).steps
      ≤ P.time.eval (ea a).length + 2 * P.sizeBound.eval (ea a).length + 2
          + Q.time.eval (P.sizeBound.eval (ea a).length) :=
  (steps_le_time (P.comp Q) a).trans (compTime_eval_le P Q _)

/-- **Two-stage monomial chain lemma.** If stage `P` has output size `≤ Cp * (L+1)^dp`
and stage `Q` has output size `≤ Cq * (M+1)^dq` for inputs of size `M`, then the composite
`P.comp Q` has output size `≤ Cq * (Cp+1)^dq * (L+1)^(dp*dq)`: degrees multiply and the
constants are explicit. -/
theorem comp_length_bound_pow {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} {Cp dp Cq dq : ℕ}
    (hP : ∀ a, (eb (f a)).length ≤ Cp * ((ea a).length + 1) ^ dp)
    (hQ : ∀ b, (ec (g b)).length ≤ Cq * ((eb b).length + 1) ^ dq) :
    ∀ a, (ec (g (f a))).length ≤ Cq * (Cp + 1) ^ dq * ((ea a).length + 1) ^ (dp * dq) := by
  intro a
  have h1 : (eb (f a)).length ≤ Cp * ((ea a).length + 1) ^ dp := hP a
  have h2 : (ec (g (f a))).length ≤ Cq * ((eb (f a)).length + 1) ^ dq := hQ (f a)
  have hN1 : 1 ≤ ((ea a).length + 1) ^ dp := Nat.one_le_pow dp _ (Nat.succ_pos _)
  have hstep : (eb (f a)).length + 1 ≤ (Cp + 1) * ((ea a).length + 1) ^ dp := by
    calc (eb (f a)).length + 1 ≤ Cp * ((ea a).length + 1) ^ dp + 1 := Nat.add_le_add_right h1 1
      _ ≤ Cp * ((ea a).length + 1) ^ dp + ((ea a).length + 1) ^ dp := Nat.add_le_add_left hN1 _
      _ = (Cp + 1) * ((ea a).length + 1) ^ dp := by ring
  calc (ec (g (f a))).length ≤ Cq * ((eb (f a)).length + 1) ^ dq := h2
    _ ≤ Cq * (((Cp + 1) * ((ea a).length + 1) ^ dp) ^ dq) :=
        Nat.mul_le_mul_left Cq (Nat.pow_le_pow_left hstep dq)
    _ = Cq * ((Cp + 1) ^ dq * ((ea a).length + 1) ^ (dp * dq)) := by rw [mul_pow, ← pow_mul]
    _ = Cq * (Cp + 1) ^ dq * ((ea a).length + 1) ^ (dp * dq) := by ring

/-- Two-stage chain lemma, fed directly by `length_bound_pow` for both stages. -/
theorem comp_length_bound_pow_sizeBound {α β γ : Type} {ea : α → List Bool}
    {eb : β → List Bool} {ec : γ → List Bool} {f : α → β} {g : β → γ}
    (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) (a : α) :
    (ec ((g ∘ f) a)).length ≤
      (Q.time.eval 1 * Q.machine.growth + 1) *
        (P.time.eval 1 * P.machine.growth + 1 + 1) ^ max 1 Q.time.natDegree *
        ((ea a).length + 1) ^ (max 1 P.time.natDegree * max 1 Q.time.natDegree) :=
  comp_length_bound_pow (f := f) (g := g) (Cp := P.time.eval 1 * P.machine.growth + 1)
    (dp := max 1 P.time.natDegree) (Cq := Q.time.eval 1 * Q.machine.growth + 1)
    (dq := max 1 Q.time.natDegree) (fun a => length_bound_pow P a)
    (fun b => length_bound_pow Q b) a

/-- **Three-stage monomial chain lemma**: the same statement one level up, showing that the
degrees keep multiplying (`dp*dq*dr`) through a composition chain. -/
theorem comp3_length_bound_pow {α β γ δ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {ed : δ → List Bool} {f : α → β} {g : β → γ} {k : γ → δ}
    {Cp dp Cq dq Cr dr : ℕ}
    (hP : ∀ a, (eb (f a)).length ≤ Cp * ((ea a).length + 1) ^ dp)
    (hQ : ∀ b, (ec (g b)).length ≤ Cq * ((eb b).length + 1) ^ dq)
    (hR : ∀ c, (ed (k c)).length ≤ Cr * ((ec c).length + 1) ^ dr) :
    ∀ a, (ed (k (g (f a)))).length
      ≤ Cr * (Cq * (Cp + 1) ^ dq + 1) ^ dr * ((ea a).length + 1) ^ (dp * dq * dr) := by
  intro a
  have h1 : ∀ a, (ec (g (f a))).length ≤ Cq * (Cp + 1) ^ dq * ((ea a).length + 1) ^ (dp * dq) :=
    comp_length_bound_pow hP hQ
  exact comp_length_bound_pow (f := fun x => g (f x)) (g := k)
    (Cp := Cq * (Cp + 1) ^ dq) (dp := dp * dq) (Cq := Cr) (dq := dr) h1 hR a


/-! ## 4. The `k`-fold chain -/

/-- `k`-fold iterate of a size bound: a chain of `k` stages each bounded by `s` has size
bound `chainPoly s k` (`chainPoly s 0 = 1` is the identity bound, `chainPoly s (k+1)` applies
one more stage to the output of the previous ones). -/
noncomputable def chainPoly (s : Polynomial ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | (k + 1) => s.comp (chainPoly s k)

@[simp] theorem chainPoly_zero (s : Polynomial ℕ) : chainPoly s 0 = 1 := rfl

@[simp] theorem chainPoly_succ (s : Polynomial ℕ) (k : ℕ) :
    chainPoly s (k + 1) = s.comp (chainPoly s k) := rfl

/-- The explicit constant produced by iterating `n ↦ C*(n+1)^d` `k` times. This is a
computable natural number (`#eval chainConst 37 3 5`). -/
def chainConst (C d : ℕ) : ℕ → ℕ
  | 0 => 1
  | (k + 1) => C * (chainConst C d k + 1) ^ d

@[simp] theorem chainConst_zero (C d : ℕ) : chainConst C d 0 = 1 := rfl

@[simp] theorem chainConst_succ (C d k : ℕ) :
    chainConst C d (k + 1) = C * (chainConst C d k + 1) ^ d := rfl

/-- Arithmetic core of one chain step: `C*(K*(L+1)^D + 1)^d ≤ C*((K+1)^d*(L+1)^(D*d))`. -/
theorem chain_step_arith (C d K D L : ℕ) :
    C * (K * (L + 1) ^ D + 1) ^ d ≤ C * ((K + 1) ^ d * (L + 1) ^ (D * d)) := by
  have hN : 1 ≤ (L + 1) ^ D := Nat.one_le_pow D _ (Nat.succ_pos L)
  have hstep : K * (L + 1) ^ D + 1 ≤ (K + 1) * (L + 1) ^ D := by
    calc K * (L + 1) ^ D + 1 ≤ K * (L + 1) ^ D + (L + 1) ^ D := Nat.add_le_add_left hN _
      _ = (K + 1) * (L + 1) ^ D := by ring
  calc C * (K * (L + 1) ^ D + 1) ^ d ≤ C * (((K + 1) * (L + 1) ^ D) ^ d) :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left hstep d)
    _ = C * ((K + 1) ^ d * (L + 1) ^ (D * d)) := by rw [mul_pow, ← pow_mul]

/-- The degree of a `k`-stage chain is `(natDegree s)^k`. -/
theorem natDegree_chainPoly_le (s : Polynomial ℕ) (k : ℕ) :
    (chainPoly s k).natDegree ≤ s.natDegree ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h := Polynomial.natDegree_comp_le (p := s) (q := chainPoly s k)
      calc (chainPoly s (k + 1)).natDegree = (s.comp (chainPoly s k)).natDegree := by
              rw [chainPoly_succ]
        _ ≤ s.natDegree * (chainPoly s k).natDegree := h
        _ ≤ s.natDegree * s.natDegree ^ k := Nat.mul_le_mul_left _ ih
        _ = s.natDegree ^ (k + 1) := by ring

/-- **The `k`-fold chain bound.** If a single stage of the chain has size bound `s`, then a
chain of `k` such stages has size bound `chainConst C d k * (L+1)^(d^k)` where `C = s.eval 1`
(coefficient sum) and `d = s.natDegree`. Both numbers are computed by explicit recursion, so
a concrete chain length gives a concrete polynomial. -/
theorem chainPoly_eval_le (s : Polynomial ℕ) (k L : ℕ) :
    (chainPoly s k).eval L
      ≤ chainConst (s.eval 1) s.natDegree k * (L + 1) ^ (s.natDegree ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc (chainPoly s (k + 1)).eval L = s.eval ((chainPoly s k).eval L) := by
              rw [chainPoly_succ, Polynomial.eval_comp]
        _ ≤ s.eval 1 * ((chainPoly s k).eval L + 1) ^ s.natDegree :=
              eval_le_eval_one_mul_pow s _
        _ ≤ s.eval 1 *
              ((chainConst (s.eval 1) s.natDegree k * (L + 1) ^ (s.natDegree ^ k)) + 1) ^
                s.natDegree := by
              refine Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _)
              exact Nat.add_le_add_right ih 1
        _ ≤ s.eval 1 *
              ((chainConst (s.eval 1) s.natDegree k + 1) ^ s.natDegree *
                (L + 1) ^ (s.natDegree ^ k * s.natDegree)) :=
              chain_step_arith _ _ _ _ _
        _ = chainConst (s.eval 1) s.natDegree (k + 1) * (L + 1) ^ (s.natDegree ^ (k + 1)) := by
              rw [chainConst_succ, pow_succ]
              ring

/-! ### A computable monomial interface

For a program `P` we package the two numbers of `length_bound_pow` into the pair
`monoBound P = (C, d)`, read as the bound `C * (L+1)^d`. Composition of chains is then the
computable binary operation `chainPair`, and a `k`-stage chain is `chainPairIter`. -/

/-- The monomial data of `length_bound_pow`: output length `≤ C * (L+1)^d`. -/
def monoBound {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    (P : PolyProgram ea eb f) : ℕ × ℕ :=
  (P.time.eval 1 * P.machine.growth + 1, max 1 P.time.natDegree)

/-- `length_bound_pow` in pair form. -/
theorem length_bound_monoBound {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ (monoBound P).1 * ((ea a).length + 1) ^ (monoBound P).2 :=
  length_bound_pow P a

/-- Composition of monomial size data: `(Cp,dp)` then `(Cq,dq)` gives
`(Cq*(Cp+1)^dq, dp*dq)`. -/
def chainPair (p q : ℕ × ℕ) : ℕ × ℕ := (q.1 * (p.1 + 1) ^ q.2, p.2 * q.2)

@[simp] theorem chainPair_fst (p q : ℕ × ℕ) :
    (chainPair p q).1 = q.1 * (p.1 + 1) ^ q.2 := rfl

@[simp] theorem chainPair_snd (p q : ℕ × ℕ) : (chainPair p q).2 = p.2 * q.2 := rfl

/-- `k`-stage chain of identical monomial data, as a computable pair. -/
def chainPairIter (p : ℕ × ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | (k + 1) => chainPair (chainPairIter p k) p

@[simp] theorem chainPairIter_zero (p : ℕ × ℕ) : chainPairIter p 0 = (1, 1) := rfl

@[simp] theorem chainPairIter_succ (p : ℕ × ℕ) (k : ℕ) :
    chainPairIter p (k + 1) = chainPair (chainPairIter p k) p := rfl

/-- The first component of `chainPairIter` is exactly `chainConst`. -/
theorem chainPairIter_fst (p : ℕ × ℕ) (k : ℕ) :
    (chainPairIter p k).1 = chainConst p.1 p.2 k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [chainPairIter_succ, chainPair_fst, chainConst_succ, ih]

/-- The second component of `chainPairIter` is `d^k`. -/
theorem chainPairIter_snd (p : ℕ × ℕ) (k : ℕ) : (chainPairIter p k).2 = p.2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [chainPairIter_succ, chainPair_snd, ih, pow_succ]

/-- **`k`-fold chain bound in computable pair form.** -/
theorem chainPoly_eval_le_pair (s : Polynomial ℕ) (k L : ℕ) :
    (chainPoly s k).eval L
      ≤ (chainPairIter (s.eval 1, s.natDegree) k).1 *
          (L + 1) ^ (chainPairIter (s.eval 1, s.natDegree) k).2 := by
  rw [chainPairIter_fst, chainPairIter_snd]
  exact chainPoly_eval_le s k L

/-- **Two-program chain in pair form**: composing two programs multiplies the degrees and
updates the constants by `chainPair`, with no reference to `sizeBound` or `growth`. -/
theorem comp_length_bound_pair {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (P : PolyProgram ea eb f)
    (Q : PolyProgram eb ec g) (a : α) :
    (ec (g (f a))).length
      ≤ (chainPair (monoBound P) (monoBound Q)).1 *
          ((ea a).length + 1) ^ (chainPair (monoBound P) (monoBound Q)).2 :=
  comp_length_bound_pow (f := f) (g := g) (fun a => length_bound_monoBound P a)
    (fun b => length_bound_monoBound Q b) a

/-- Iterating `chainPair` over a list of stage data accumulates a monomial bound for the whole
chain: `chainPairIter p k` is the `k`-fold iterate of the single-stage data `p`. -/
theorem chainPairIter_mono {p q : ℕ × ℕ} (h1 : p.1 ≤ q.1) (h2 : p.2 ≤ q.2) (k : ℕ) :
    (chainPairIter p k).1 ≤ (chainPairIter q k).1 ∧ (chainPairIter p k).2 ≤ (chainPairIter q k).2 := by
  induction k with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ k ih =>
      refine ⟨?_, ?_⟩
      · show (chainPair (chainPairIter p k) p).1 ≤ (chainPair (chainPairIter q k) q).1
        rw [chainPair_fst, chainPair_fst]
        have hbase : (chainPairIter p k).1 + 1 ≤ (chainPairIter q k).1 + 1 :=
          Nat.add_le_add_right ih.1 1
        have hpow : ((chainPairIter p k).1 + 1) ^ p.2 ≤ ((chainPairIter q k).1 + 1) ^ q.2 :=
          (Nat.pow_le_pow_left hbase p.2).trans
            (Nat.pow_le_pow_right (Nat.succ_pos _) h2)
        exact Nat.mul_le_mul h1 hpow
      · show (chainPair (chainPairIter p k) p).2 ≤ (chainPair (chainPairIter q k) q).2
        rw [chainPair_snd, chainPair_snd]
        exact Nat.mul_le_mul ih.2 h2


/-- **Clean-numeral form.** Once the two numbers `monoBound P = (C₀, d₀)` are dominated by
user-chosen numerals `C`, `d` (discharged once, e.g. by `decide`/`norm_num` on an explicit
program), every input length `L` gives `(eb (f a)).length ≤ C * (L+1)^d`. -/
theorem length_bound_pow_of_le {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) (C d : ℕ)
    (hC : P.time.eval 1 * P.machine.growth + 1 ≤ C)
    (hd : max 1 P.time.natDegree ≤ d) (a : α) :
    (eb (f a)).length ≤ C * ((ea a).length + 1) ^ d := by
  refine (length_bound_pow P a).trans ?_
  exact Nat.mul_le_mul hC (Nat.pow_le_pow_right (Nat.succ_pos _) hd)

/-- A `SizeProfile` in explicit monomial form `C * (X+1)^d`. -/
theorem sizeProfile_monoBound {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) :
    SizeProfile P (Polynomial.C (monoBound P).1 * (Polynomial.X + 1) ^ (monoBound P).2) := by
  refine ⟨fun a => ?_⟩
  have h := length_bound_monoBound P a
  simpa only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one, Polynomial.eval_pow] using h

/-- Composition of two monomial size profiles: the composite profile is the composition of the
two explicit monomial polynomials, still in `C * (X+1)^d` shape after evaluation. -/
theorem sizeProfile_comp_monoBound {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (P : PolyProgram ea eb f)
    (Q : PolyProgram eb ec g) :
    SizeProfile (P.comp Q)
      ((Polynomial.C (monoBound Q).1 * (Polynomial.X + 1) ^ (monoBound Q).2).comp
        (Polynomial.C (monoBound P).1 * (Polynomial.X + 1) ^ (monoBound P).2)) :=
  SizeProfile.comp (sizeProfile_monoBound P) (sizeProfile_monoBound Q)

/-- The size-bound degree of a composite is bounded by the time degree of the composite,
so `compTime_natDegree_le` also controls `sizeBound.natDegree` of a chain. -/
theorem sizeBound_comp_natDegree_le {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {g : β → γ} (P : PolyProgram ea eb f)
    (Q : PolyProgram eb ec g) :
    (P.comp Q).sizeBound.natDegree
      ≤ max 1 (max (max 1 P.time.natDegree) (Q.time.natDegree * max 1 P.time.natDegree)) := by
  refine (sizeBound_natDegree_le (P.comp Q)).trans ?_
  exact max_le_max le_rfl (compTime_natDegree_le P Q)


/-! ## 5. Instantiations for the `LeafB_MatQ` dependency graph

`LeafB_MatQ` computes row-major matrix operations as `listMap`/`listZip`/`ratFoldAdd`
chains. Two shapes of size statement are needed there, and both are supplied here:

* the **list-shaped** statement `listMap_length_bound`: mapping over a list preserves the
  number of entries and only grows the entry encoding, so the encoded output is at most
  `as.length * (2 * P.sizeBound.eval L + 1)` bits;
* the **value-shaped** statement `ratFoldAdd_length_bound` (and friends): a rational output is
  a single encoded value, and `length_bound_pow` bounds its encoded length by an explicit
  polynomial of the input length. The number of *bits* of a rational depends on its numerator
  and denominator, which is exactly what the `Ratio.length_height`/`HasHeight` machinery of the
  substrate tracks; this file only supplies the input-length side of that bookkeeping.
-/

/-- **List-shaped size bound for `PolyProgram.listMap`**: if every element of `as` is encoded
in at most `L` bits, then each of the `as.length` output entries is encoded in at most
`P.sizeBound.eval L` bits, hence the encoded output length is at most
`as.length * (2 * P.sizeBound.eval L + 1)`. -/
theorem listMap_length_bound {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) (as : List α) (L : ℕ)
    (hL : (encodeList ea as).length ≤ L) :
    (encodeList eb (as.map f)).length ≤ as.length * (2 * P.sizeBound.eval L + 1) := by
  refine (EncodedList.length_bound eb (as.map f) (P.sizeBound.eval L) ?_).trans ?_
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    refine (P.length_bound a).trans (polyEval_mono P.sizeBound ?_)
    exact (EncodedList.member_length ea as a ha).trans hL
  · rw [List.length_map]

/-- The same list-shaped bound with the entry size replaced by its explicit monomial form. -/
theorem listMap_length_bound_pow {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    {f : α → β} (P : PolyProgram ea eb f) (as : List α) (L : ℕ)
    (hL : (encodeList ea as).length ≤ L) :
    (encodeList eb (as.map f)).length ≤
      as.length * (2 * ((P.time.eval 1 * P.machine.growth + 1) * (L + 1) ^ max 1 P.time.natDegree) + 1) := by
  refine (listMap_length_bound P as L hL).trans ?_
  have h := polyEval_mono P.sizeBound hL
  have h' : P.sizeBound.eval L ≤
      (P.time.eval 1 * P.machine.growth + 1) * (L + 1) ^ max 1 P.time.natDegree :=
    (sizeBound_eval_le P L).trans (arith_collect _ _ _ _)
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h') 1)


/-- **List-shaped size bound for `PolyProgram.listMapWith`** — the workhorse of `LeafB_MatQ`:
mapping a *parameterised* function `a ↦ f (c,a)` over a list keeps the number of entries and
bounds each entry by `P.sizeBound.eval L`, where `L` bounds the whole input `(c, as)`. So the
encoded output length is at most `as.length * (2 * P.sizeBound.eval L + 1)`. -/
theorem listMapWith_length_bound {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : γ × α → β} (P : PolyProgram (encodePair ec ea) eb f)
    (c : γ) (as : List α) (L : ℕ) (hL : (encodePair ec (encodeList ea) (c, as)).length ≤ L) :
    (encodeList eb (as.map (fun a => f (c, a)))).length ≤ as.length * (2 * P.sizeBound.eval L + 1) := by
  refine (EncodedList.length_bound eb (as.map (fun a => f (c, a))) (P.sizeBound.eval L) ?_).trans ?_
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    refine (P.length_bound (c, a)).trans (polyEval_mono P.sizeBound ?_)
    have hmem : (ea a).length ≤ (encodeList ea as).length := EncodedList.member_length ea as a ha
    have h1 : (ec c).length ≤ (encodePair ec (encodeList ea) (c, as)).length := by
      simp only [encodePair_length]; omega
    have h2 : (ea a).length ≤ (encodePair ec (encodeList ea) (c, as)).length := by
      simp only [encodePair_length]; omega
    have hL' : 2 * (ec c).length + 1 + (encodeList ea as).length ≤ L := by
      simpa only [encodePair_length] using hL
    simp only [encodePair_length]
    omega
  · rw [List.length_map]

/-- Monomial form of `listMapWith_length_bound`. -/
theorem listMapWith_length_bound_pow {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : γ × α → β} (P : PolyProgram (encodePair ec ea) eb f)
    (c : γ) (as : List α) (L : ℕ) (hL : (encodePair ec (encodeList ea) (c, as)).length ≤ L) :
    (encodeList eb (as.map (fun a => f (c, a)))).length
      ≤ as.length * (2 * ((P.time.eval 1 * P.machine.growth + 1) * (L + 1) ^ max 1 P.time.natDegree) + 1) := by
  refine (listMapWith_length_bound P c as L hL).trans ?_
  have h' : P.sizeBound.eval L ≤
      (P.time.eval 1 * P.machine.growth + 1) * (L + 1) ^ max 1 P.time.natDegree :=
    (sizeBound_eval_le P L).trans (arith_collect _ _ _ _)
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 h') 1)

/-- Encoded length of a `ℚ`-valued fold: `ratFoldAdd` on a list together with an accumulator. -/
theorem ratFoldAdd_length_bound (x : List ℚ × ℚ) :
    (Ratio.encode (x.1.foldl (· + ·) x.2)).length
      ≤ (PolyProgram.ratFoldAdd.time.eval 1 * PolyProgram.ratFoldAdd.machine.growth + 1) *
          ((encodePair (encodeList Ratio.encode) Ratio.encode x).length + 1) ^
            max 1 PolyProgram.ratFoldAdd.time.natDegree :=
  length_bound_pow PolyProgram.ratFoldAdd x

/-- Encoded length of `ratSum`. -/
theorem ratSum_length_bound (as : List ℚ) :
    (Ratio.encode as.sum).length
      ≤ (PolyProgram.ratSum.time.eval 1 * PolyProgram.ratSum.machine.growth + 1) *
          ((encodeList Ratio.encode as).length + 1) ^ max 1 PolyProgram.ratSum.time.natDegree :=
  length_bound_pow PolyProgram.ratSum as

/-- Encoded length of `ratAdd`. -/
theorem ratAdd_length_bound (x : ℚ × ℚ) :
    (Ratio.encode (x.1 + x.2)).length
      ≤ (PolyProgram.ratAdd.time.eval 1 * PolyProgram.ratAdd.machine.growth + 1) *
          ((encodePair Ratio.encode Ratio.encode x).length + 1) ^
            max 1 PolyProgram.ratAdd.time.natDegree :=
  length_bound_pow PolyProgram.ratAdd x

/-- Encoded length of `ratMul`. -/
theorem ratMul_length_bound (x : ℚ × ℚ) :
    (Ratio.encode (x.1 * x.2)).length
      ≤ (PolyProgram.ratMul.time.eval 1 * PolyProgram.ratMul.machine.growth + 1) *
          ((encodePair Ratio.encode Ratio.encode x).length + 1) ^
            max 1 PolyProgram.ratMul.time.natDegree :=
  length_bound_pow PolyProgram.ratMul x

/-- Size bound for `PolyProgram.listZip`: the coarsest list-shaped statement, namely that the
encoded output of the zipped list is bounded by `listZip`'s own `sizeBound` evaluated at an
input length bound `L` (monotone in `L`, so any input bound may be used). -/
theorem listZip_length_bound {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (a0 : α) (b0 : β) (as : List α) (bs : List β) (L : ℕ)
    (hL : (encodePair (encodeList ea) (encodeList eb) (as, bs)).length ≤ L) :
    (encodeList (encodePair ea eb) (as.zip bs)).length
      ≤ (PolyProgram.listZip ea eb a0 b0).sizeBound.eval L := by
  have h := (PolyProgram.listZip ea eb a0 b0).length_bound (as, bs)
  refine h.trans (polyEval_mono _ ?_)
  simpa only [encodePair, List.length_append] using hL

/-- Monomial form of `listZip`'s size bound. -/
theorem listZip_length_bound_pow {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (a0 : α) (b0 : β) (as : List α) (bs : List β) (L : ℕ)
    (hL : (encodePair (encodeList ea) (encodeList eb) (as, bs)).length ≤ L) :
    (encodeList (encodePair ea eb) (as.zip bs)).length
      ≤ ((PolyProgram.listZip ea eb a0 b0).time.eval 1 *
            (PolyProgram.listZip ea eb a0 b0).machine.growth + 1) *
          (L + 1) ^ max 1 (PolyProgram.listZip ea eb a0 b0).time.natDegree := by
  refine (listZip_length_bound a0 b0 as bs L hL).trans ?_
  exact (sizeBound_eval_le _ L).trans (arith_collect _ _ _ _)

/-! ## 5b. Structural size rules: `fanout`, `product`, `exchange`, `listCons`

`LeafB_MatQ` builds its row-major operations from `PolyProgram.fanout`, `product`, `exchange`,
`duplicate`, `listCons` and `listMapWith`. For those the output encoding is literally
`encodePair`/`encodeList`, so the size bound can be read off `encodePair_length` and
`EncodedList.cons_length` — no `sizeBound` and no `growth` involved. The monomial rules below
combine with `comp_length_bound_pow`/`chainPair` to bound a whole dependency graph. -/

theorem duplicate_length_bound {α : Type} (ea : α → List Bool) (a : α) :
    (encodePair ea ea (a, a)).length = 3 * (ea a).length + 1 := by
  rw [encodePair_length]
  ring

/-- Swapping the two components of a pair encoding costs at most a factor two (the encoding is
`quote first ++ second`, so the two sides are not symmetric). -/
theorem exchange_length_bound {α β : Type} (ea : α → List Bool) (eb : β → List Bool)
    (x : α × β) : (encodePair eb ea (x.2, x.1)).length ≤ 2 * (encodePair ea eb x).length := by
  rw [encodePair_length, encodePair_length]
  dsimp only
  omega

theorem listCons_length_bound {α : Type} (ea : α → List Bool) (a : α) (bs : List α) :
    (encodeList ea (a :: bs)).length = 2 * (ea a).length + 1 + (encodeList ea bs).length :=
  EncodedList.cons_length ea a bs

/-- Arithmetic core of the `fanout`/`product` monomial rule. -/
theorem pair_arith (Cp Cq M : ℕ) (hM : 1 ≤ M) :
    2 * (Cp * M) + 1 + Cq * M ≤ (2 * Cp + Cq + 1) * M := by
  have h : (2 * Cp + Cq + 1) * M = 2 * Cp * M + Cq * M + M := by ring
  have h' : 2 * Cp * M = 2 * (Cp * M) := by ring
  rw [h, h']
  omega

/-- **Monomial rule for `PolyProgram.fanout`** (and hence for `product`, which is
`thread`/`second` around it): if the two branches have monomial bounds `(Cp,dp)` and `(Cq,dq)`
on the same input, the paired output has bound `(2*Cp + Cq + 1, max dp dq)` — the sum of two
monomials plus the `quote` separator. -/
theorem fanout_length_bound_pair {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {f : α → β} {h : α → γ} {Cp dp Cq dq : ℕ}
    (hP : ∀ a, (eb (f a)).length ≤ Cp * ((ea a).length + 1) ^ dp)
    (hQ : ∀ a, (ec (h a)).length ≤ Cq * ((ea a).length + 1) ^ dq) (a : α) :
    (encodePair eb ec (f a, h a)).length ≤ (2 * Cp + Cq + 1) * ((ea a).length + 1) ^ max dp dq := by
  rw [encodePair_length]
  have h1 := hP a
  have h2 := hQ a
  have hM : 1 ≤ ((ea a).length + 1) ^ max dp dq := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have hdp : ((ea a).length + 1) ^ dp ≤ ((ea a).length + 1) ^ max dp dq :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_left _ _)
  have hdq : ((ea a).length + 1) ^ dq ≤ ((ea a).length + 1) ^ max dp dq :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (le_max_right _ _)
  have e1 : 2 * (Cp * ((ea a).length + 1) ^ dp) ≤ 2 * (Cp * ((ea a).length + 1) ^ max dp dq) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left Cp hdp)
  have e2 : Cq * ((ea a).length + 1) ^ dq ≤ Cq * ((ea a).length + 1) ^ max dp dq :=
    Nat.mul_le_mul_left Cq hdq
  have stepA : 2 * (eb (f a)).length + 1 + (ec (h a)).length
      ≤ 2 * (Cp * ((ea a).length + 1) ^ dp) + 1 + Cq * ((ea a).length + 1) ^ dq :=
    Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 h1) le_rfl) h2
  have stepB : 2 * (Cp * ((ea a).length + 1) ^ dp) + 1 + Cq * ((ea a).length + 1) ^ dq
      ≤ 2 * (Cp * ((ea a).length + 1) ^ max dp dq) + 1
        + Cq * ((ea a).length + 1) ^ max dp dq :=
    Nat.add_le_add (Nat.add_le_add e1 le_rfl) e2
  have stepC : 2 * (Cp * ((ea a).length + 1) ^ max dp dq) + 1
        + Cq * ((ea a).length + 1) ^ max dp dq
      ≤ (2 * Cp + Cq + 1) * ((ea a).length + 1) ^ max dp dq :=
    pair_arith Cp Cq _ hM
  exact stepA.trans (stepB.trans stepC)

/-- **Monomial rule for `PolyProgram.product`**: the two components are computed on the two
halves of the input pair, so the output bound is `(2*Cp + Cq + 1, max dp dq)` evaluated on the
two halves separately. -/
theorem product_length_bound_pair {α β γ δ : Type} {ea : α → List Bool} {eb : β → List Bool}
    {ec : γ → List Bool} {ed : δ → List Bool} {f : α → β} {g : γ → δ} {Cp dp Cq dq : ℕ}
    (hP : ∀ a, (eb (f a)).length ≤ Cp * ((ea a).length + 1) ^ dp)
    (hQ : ∀ c, (ed (g c)).length ≤ Cq * ((ec c).length + 1) ^ dq) (x : α × γ) :
    (encodePair eb ed (f x.1, g x.2)).length
      ≤ 2 * (Cp * ((ea x.1).length + 1) ^ dp) + 1 + Cq * ((ec x.2).length + 1) ^ dq := by
  rw [encodePair_length]
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 2 (hP x.1)) le_rfl) (hQ x.2)

/-! ## 6. Computability checks for the chain data -/

example : (chainPairIter (2, 2) 4).2 = 16 := by decide

example : (chainPairIter (2, 2) 4).1 = 2 * (2 * (2 * (2 * (1 + 1) ^ 2 + 1) ^ 2 + 1) ^ 2 + 1) ^ 2 := by
  decide

example : (chainPairIter (2, 1) 4).1 = chainConst 2 1 4 := chainPairIter_fst _ _

example : chainConst 2 1 4 = 46 := by decide

example : chainConst 3 2 3 = 774192 := by decide

-- the chain pair is computable, so concrete constants can be produced by evaluation:

/-! ## 7. Axiom report

The three headline statements, with their axiom footprints (expected: `propext`,
`Classical.choice`, `Quot.sound` only — the framework's `noncomputable` definitions use choice).
-/

#print axioms length_bound_pow
#print axioms sizeBound_eval_le
#print axioms comp_length_bound_pow
#print axioms comp3_length_bound_pow
#print axioms comp_length_bound_pow_sizeBound
#print axioms compTime_natDegree_le
#print axioms chainPoly_eval_le
#print axioms chainPairIter_fst
#print axioms listMap_length_bound
#print axioms length_bound_pow_of_le
#print axioms sizeProfile_comp_monoBound
#print axioms sizeBound_comp_natDegree_le
#print axioms listZip_length_bound
#print axioms listMapWith_length_bound
#print axioms fanout_length_bound_pair
#print axioms product_length_bound_pair
#print axioms duplicate_length_bound
#print axioms steps_le_monomial
#print axioms comp_steps_le
#print axioms ratFoldAdd_length_bound

end LeafB.Tm2Size
end MetricKMedian.Binary
end OAI


/-! #### merged from `LeafB_DyadicSqrt.lean` -/
/-
Copyright: no copyright.

# `DQ` : certified dyadic square roots, inverse square roots and log-scale normalisers

Leaf B (`91ee3bff`, the 0.53 Quantum Max-Cut certified SDP lower-value program) needs, inside a
polynomial-time rational-arithmetic substrate, **exact rational enclosures** of `√x` and `1/√x`
together with an honest accounting of the number of bits required.  This file provides them.

Everything here is *machine-free*: plain computable functions on `ℚ` (`Rat.floor` and `Nat.sqrt` are
both computable), with correctness theorems relating them to `Real.sqrt`.  Every enclosure is a
closed rational statement, so the coordinator can recompile and kernel-check it; the `example`s of
section 7 are decided by the kernel straight from the definitions.  Only `Mathlib` is imported and
no axiom beyond `propext, Classical.choice, Quot.sound` is used (section 9).

## The API

For `x : ℚ`, `k : ℕ`:

* `DQ.sqrtLe x k = ⌊√x·2^k⌋/2^k` and `DQ.sqrtGe x k = (⌊√x·2^k⌋+1)/2^k` (aliases `sqrt_le`,
  `sqrt_ge`).  For `x ≥ 0`:
  * `sqrtLe_le_sqrt : (sqrtLe x k : ℝ) ≤ Real.sqrt x`  (`sqrtLe_sq_le` : `(sqrtLe x k)^2 ≤ x`),
  * `sqrt_lt_sqrtGe : Real.sqrt x < (sqrtGe x k : ℝ)`  (`sq_lt_sqrtGe_sq` : `x < (sqrtGe x k)^2`),
  * `sqrtGe_sub_sqrtLe : sqrtGe x k - sqrtLe x k = 1/2^k` — the enclosure width is *exactly*
    `2^{-k}`, so `k` is literally the number of certified bits,
  * `sqrtLe_dyadic` : the value is an integer over `2^k`,
  * nestedness in `k` (`sqrtLe_mono_k`, `sqrtGe_antitone_k`) and monotonicity in `x`
    (`sqrtLe_mono`, `sqrtGe_mono`),
  * arbitrary tightness: `exists_sqrt_width_le`.
* `DQ.invSqrtLe x k = 1/sqrtGe x k` and `DQ.invSqrtGe x k = 1/sqrtLe x k` (aliases `invSqrt_le`,
  `invSqrt_ge`) bracket `1/√x`:
  * `invSqrtLe_le` : `invSqrtLe x k ≤ 1/√x` for `x > 0` (**no** side condition),
  * `le_invSqrtGe`, `invSqrt_bracket` : `1/√x ≤ invSqrtGe x k` under the **scale side condition**
    `1 ≤ x·4^k` (equivalently `1 ≤ √x·2^k`).  It is genuinely needed: `sqrtLe (1/4) 0 = 0` (§7).
    For `x ≥ 1` it holds at every `k` (`one_le_mul_four_pow`).
  * `invSqrt_width : invSqrtGe - invSqrtLe = 2^{-k}/(sqrtLe·sqrtGe)` (relative accuracy of the
    reciprocal bracket = relative accuracy of the square-root bracket),
    `invSqrt_width_le_of_one_le : ≤ 2^{-k}` for `x ≥ 1`, `invSqrt_width_le : ≤ 2^k` in general,
    `invSqrtGe_le_one` for `x ≥ 1`, antitonicity `invSqrtLe_antitone`.
* `DQ.log2cell x : ℤ = ⌊log₂ (max x 1)⌋`, certified by
  `log2cell_spec : 2^(log2cell x) ≤ max x 1 ∧ max x 1 < 2^(log2cell x + 1)`.
  Also `log2cell_mono`, `log2cell_mul_le` (`log2cell (x·y) ≤ log2cell x + log2cell y + 1`) and
  `log2cell_pow_le` (`log2cell (x^d) ≤ d·(log2cell x + 1)`) — the multiplies-and-powers accounting a
  loop over `d` dimensions needs — and `log2cell_inv` : `log2cell (1/x)` normalises `min x 1`
  (`2^(-(l+1)) < min x 1 ≤ 2^(-l)` for `x > 0`).  Together with `sqrt_bracket_scale` this is the
  log-scale accounting the ellipsoid engine needs: the *squared* bracket of `√x` straddles the cell
  `[2^l, 2^(l+1))` of `x`.
* Product rule (the composition an ellipsoid update performs, `√(xy) = √x·√y`):
  `sqrtLe_mul_le_sqrtGe_mul`, `sqrtLe_mul_le_prod_sqrtGe`.
* Brief-shaped combined forms: `sqrt_bracket_width` (`sqrtLe x k ≤ √x ≤ sqrtLe x k + 2^{-k}`) and
  `invSqrt_bracket_width` (`invSqrtLe x k ≤ 1/√x ≤ invSqrtLe x k + 2^k`).
* Newton/AM–GM refinement over `ℝ` for an iteration engine starting from an over-estimate `s ≥ √x`:
  `sqrt_le_newton_step`, `newton_step_le_self`, and the exact quadratic-convergence identity
  `newton_step_sub_eq : (s + x/s)/2 - √x = (s - √x)^2/(2s)`
  (with `newton_step_error_le : ≤ (s-√x)^2/(2√x)`) — one correct bit per step.

## Conventions

* `Real.sqrt x` always means `Real.sqrt (x : ℝ)`; each statement carries the hypothesis `0 ≤ x`
  (resp. `0 < x`) that makes `√x` the intended target.
* `sqrtLe`/`sqrtGe` are junk (both `0`) at `x < 0`; no theorem asserts anything about that case.
* No custom notation, no macros, no `set_option`: plain `import Mathlib` plus `namespace DQ`.
-/


namespace DQ

/-! ### 1.  The floor–square-root core

`Nat.sqrt ⌊y⌋` is exactly `⌊√y⌋` for `y ≥ 0`, since `r² ≤ y ↔ r² ≤ ⌊y⌋` for natural `r`.  This is
the only place where the number theory happens; everything else is `2`-adic bookkeeping. -/

/-- Casting `⌊y⌋` to `ℚ` through `toNat` for `y ≥ 0`. -/
theorem floor_toNat_cast {y : ℚ} (hy : 0 ≤ y) :
    ((y.floor.toNat : ℕ) : ℚ) = (y.floor : ℚ) := by
  have h0 : (0 : ℤ) ≤ y.floor := Int.floor_nonneg.mpr hy
  have h1 : ((y.floor.toNat : ℕ) : ℚ) = ((y.floor.toNat : ℤ) : ℚ) := by push_cast; ring
  rw [h1, Int.toNat_of_nonneg h0]

/-- For `y : ℚ` with `y ≥ 0`, the natural `⌊√y⌋` satisfies `⌊√y⌋² ≤ y`. -/
theorem floorSqrt_sq_le (y : ℚ) (hy : 0 ≤ y) : ((Nat.sqrt y.floor.toNat : ℚ)) ^ 2 ≤ y := by
  have hnat : ((Nat.sqrt y.floor.toNat : ℕ) : ℚ) ^ 2 ≤ ((y.floor.toNat : ℕ) : ℚ) := by
    have h := Nat.sqrt_le' y.floor.toNat
    have h' : ((Nat.sqrt y.floor.toNat : ℕ) : ℚ) ^ 2
        = (((Nat.sqrt y.floor.toNat : ℕ) ^ 2 : ℕ) : ℚ) := by push_cast; ring
    rw [h']
    exact_mod_cast h
  calc ((Nat.sqrt y.floor.toNat : ℚ)) ^ 2 ≤ ((y.floor.toNat : ℕ) : ℚ) := hnat
    _ = (y.floor : ℚ) := floor_toNat_cast hy
    _ ≤ y := Int.floor_le y

/-- For `y : ℚ` with `y ≥ 0`, `y < (⌊√y⌋ + 1)²`. -/
theorem floorSqrt_lt_succ_sq (y : ℚ) (hy : 0 ≤ y) :
    y < ((Nat.sqrt y.floor.toNat : ℚ) + 1) ^ 2 := by
  have hnat : ((y.floor.toNat : ℕ) : ℚ) + 1 ≤ ((Nat.sqrt y.floor.toNat : ℚ) + 1) ^ 2 := by
    have h : y.floor.toNat + 1 ≤ (Nat.sqrt y.floor.toNat + 1) ^ 2 :=
      Nat.succ_le_of_lt (Nat.lt_succ_sqrt' y.floor.toNat)
    have h1 : (((y.floor.toNat : ℕ) : ℚ) + 1) = ((y.floor.toNat + 1 : ℕ) : ℚ) := by push_cast; ring
    have h2 : ((Nat.sqrt y.floor.toNat : ℚ) + 1) ^ 2
        = (((Nat.sqrt y.floor.toNat + 1) ^ 2 : ℕ) : ℚ) := by push_cast; ring
    rw [h1, h2]
    exact_mod_cast h
  calc y < (y.floor : ℚ) + 1 := by
        have h := Rat.lt_floor_add_one y
        have h' : ((y.floor + 1 : ℤ) : ℚ) = (y.floor : ℚ) + 1 := by push_cast; ring
        rw [h'] at h
        exact h
    _ = ((y.floor.toNat : ℕ) : ℚ) + 1 := by rw [floor_toNat_cast hy]
    _ ≤ ((Nat.sqrt y.floor.toNat : ℚ) + 1) ^ 2 := hnat
/-! ### 2.  The dyadic brackets `sqrtLe` / `sqrtGe`

`sqrtLe x k = ⌊√x·2^k⌋ / 2^k` is the lower dyadic bracket; `sqrtGe x k = (⌊√x·2^k⌋+1)/2^k` is the
successor, so `sqrtGe x k - sqrtLe x k = 1/2^k` exactly.  The computation of `⌊√x·2^k⌋` is
`Nat.sqrt ⌊x·4^k⌋`: multiplying under the square root by `4^k = (2^k)²`. -/

/-- `⌊√x · 2^k⌋`, computed as `Nat.sqrt ⌊x · 4^k⌋`. -/
def sqrtFloorScaled (x : ℚ) (k : ℕ) : ℕ := Nat.sqrt (x * 4 ^ k).floor.toNat

/-- The certified lower dyadic bracket of `√x` at precision `k`: `⌊√x·2^k⌋ / 2^k`. -/
def sqrtLe (x : ℚ) (k : ℕ) : ℚ := (sqrtFloorScaled x k : ℚ) / 2 ^ k

/-- The certified upper dyadic bracket of `√x` at precision `k`: `(⌊√x·2^k⌋+1) / 2^k`. -/
def sqrtGe (x : ℚ) (k : ℕ) : ℚ := ((sqrtFloorScaled x k : ℚ) + 1) / 2 ^ k

theorem two_pow_sq (k : ℕ) : ((2 : ℚ) ^ k) ^ 2 = 4 ^ k := by
  rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]

theorem two_pow_pos (k : ℕ) : (0 : ℚ) < 2 ^ k := by positivity

theorem one_le_two_pow (k : ℕ) : (1 : ℚ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)

theorem one_le_four_pow (k : ℕ) : (1 : ℚ) ≤ 4 ^ k := one_le_pow₀ (by norm_num)

theorem four_pow_pos (k : ℕ) : (0 : ℚ) < 4 ^ k := by positivity

/-- `⌊√x·2^k⌋² ≤ x`, i.e. `sqrtLe x k` underestimates `√x`. -/
theorem sqrtLe_sq_le (x : ℚ) (k : ℕ) (hx : 0 ≤ x) : (sqrtLe x k) ^ 2 ≤ x := by
  have h4 : (0 : ℚ) < 4 ^ k := four_pow_pos k
  have h := floorSqrt_sq_le (x * 4 ^ k) (mul_nonneg hx h4.le)
  have hw : (sqrtLe x k) ^ 2 = ((Nat.sqrt (x * 4 ^ k).floor.toNat : ℚ)) ^ 2 / 4 ^ k := by
    simp only [sqrtLe, sqrtFloorScaled]
    rw [div_pow, two_pow_sq]
  rw [hw, div_le_iff₀ h4]
  linarith [h]

/-- `x < (⌊√x·2^k⌋+1)²`, i.e. `sqrtGe x k` overestimates `√x`. -/
theorem sq_lt_sqrtGe_sq (x : ℚ) (k : ℕ) (hx : 0 ≤ x) : x < (sqrtGe x k) ^ 2 := by
  have h4 : (0 : ℚ) < 4 ^ k := four_pow_pos k
  have h := floorSqrt_lt_succ_sq (x * 4 ^ k) (mul_nonneg hx h4.le)
  have hw : (sqrtGe x k) ^ 2
      = ((Nat.sqrt (x * 4 ^ k).floor.toNat : ℚ) + 1) ^ 2 / 4 ^ k := by
    simp only [sqrtGe, sqrtFloorScaled]
    rw [div_pow, two_pow_sq]
  rw [hw, lt_div_iff₀ h4]
  linarith [h]

/-- **The lower bracket is a lower bound**: `sqrtLe x k ≤ √x`. -/
theorem sqrtLe_le_sqrt (x : ℚ) (k : ℕ) (hx : 0 ≤ x) :
    (sqrtLe x k : ℝ) ≤ Real.sqrt (x : ℝ) := by
  apply Real.le_sqrt_of_sq_le
  have h := sqrtLe_sq_le x k hx
  have h' : ((sqrtLe x k : ℚ) : ℝ) ^ 2 = (((sqrtLe x k) ^ 2 : ℚ) : ℝ) := by push_cast; ring
  rw [h']
  exact_mod_cast h

/-- **The upper bracket is an upper bound**: `√x < sqrtGe x k`. -/
theorem sqrt_lt_sqrtGe (x : ℚ) (k : ℕ) (hx : 0 ≤ x) :
    Real.sqrt (x : ℝ) < (sqrtGe x k : ℝ) := by
  rw [Real.sqrt_lt (by exact_mod_cast hx) (by
    have := sqrtLe_sq_le x k hx
    have h4 : (0 : ℚ) < 4 ^ k := four_pow_pos k
    have hle : (0 : ℚ) ≤ sqrtGe x k := by
      simp only [sqrtGe]
      positivity
    exact_mod_cast hle)]
  have h := sq_lt_sqrtGe_sq x k hx
  have h' : ((sqrtGe x k : ℚ) : ℝ) ^ 2 = (((sqrtGe x k) ^ 2 : ℚ) : ℝ) := by push_cast; ring
  rw [h']
  exact_mod_cast h

/-- **The enclosure**: `sqrtLe x k ≤ √x ≤ sqrtGe x k`. -/
theorem sqrtLe_le_sqrt_le_sqrtGe (x : ℚ) (k : ℕ) (hx : 0 ≤ x) :
    (sqrtLe x k : ℝ) ≤ Real.sqrt (x : ℝ) ∧ Real.sqrt (x : ℝ) ≤ (sqrtGe x k : ℝ) :=
  ⟨sqrtLe_le_sqrt x k hx, le_of_lt (sqrt_lt_sqrtGe x k hx)⟩

/-- The upper bracket is the lower bracket plus one dyadic unit. -/
theorem sqrtGe_eq_sqrtLe_add (x : ℚ) (k : ℕ) : sqrtGe x k = sqrtLe x k + 1 / 2 ^ k := by
  simp only [sqrtGe, sqrtLe]
  rw [add_div]

/-- **The enclosure width is exactly `2^{-k}`.** -/
theorem sqrtGe_sub_sqrtLe (x : ℚ) (k : ℕ) : sqrtGe x k - sqrtLe x k = 1 / 2 ^ k := by
  rw [sqrtGe_eq_sqrtLe_add]; ring

theorem sqrtLe_nonneg (x : ℚ) (k : ℕ) : 0 ≤ sqrtLe x k := by
  simp only [sqrtLe]; positivity

theorem sqrtLe_le_sqrtGe (x : ℚ) (k : ℕ) : sqrtLe x k ≤ sqrtGe x k := by
  rw [sqrtGe_eq_sqrtLe_add]
  have := two_pow_pos k
  have : (0 : ℚ) < 1 / 2 ^ k := by positivity
  linarith

theorem sqrtGe_pos (x : ℚ) (k : ℕ) : 0 < sqrtGe x k := by
  simp only [sqrtGe]; positivity

/-- `sqrtLe x k` is dyadic: an integer over `2^k`. -/
theorem sqrtLe_dyadic (x : ℚ) (k : ℕ) : ∃ N : ℤ, sqrtLe x k = (N : ℚ) / 2 ^ k :=
  ⟨(sqrtFloorScaled x k : ℤ), by simp only [sqrtLe]; push_cast; ring⟩

/-- The bracket numerator is recovered exactly by scaling: `sqrtLe x k * 2^k = ⌊√x·2^k⌋`. -/
theorem sqrtLe_mul_two_pow (x : ℚ) (k : ℕ) :
    sqrtLe x k * 2 ^ k = (sqrtFloorScaled x k : ℚ) := by
  simp only [sqrtLe]
  field_simp

theorem sqrtGe_eq_sqrtLe_add_one_scaled (x : ℚ) (k : ℕ) :
    sqrtGe x k * 2 ^ k = (sqrtFloorScaled x k : ℚ) + 1 := by
  simp only [sqrtGe]
  field_simp
/-! ### 3.  Monotonicity, refinement in `k`, and composition

The ellipsoid engine composes brackets multiplicatively (`√(xy) = √x·√y`) and needs the bracket to
improve as `k` grows: the intervals are nested and their width is exactly `2^{-k}`.  The two integer
facts driving the nesting are `N_{k+1} ∈ {2N_k, 2N_k+1}` for `N_k = ⌊√x·2^k⌋`, proved as
`sqrtFloorScaled_succ_ge` / `sqrtFloorScaled_succ_le`. -/

theorem sqrtFloorScaled_mono {x y : ℚ} (_hx : 0 ≤ x) (hxy : x ≤ y) (k : ℕ) :
    sqrtFloorScaled x k ≤ sqrtFloorScaled y k := by
  have h4 : (0 : ℚ) ≤ 4 ^ k := (four_pow_pos k).le
  have h1 : (x * 4 ^ k).floor ≤ (y * 4 ^ k).floor :=
    Int.floor_mono (mul_le_mul_of_nonneg_right hxy (four_pow_pos k).le)
  have h2 : (x * 4 ^ k).floor.toNat ≤ (y * 4 ^ k).floor.toNat := Int.toNat_le_toNat h1
  simpa only [sqrtFloorScaled] using Nat.sqrt_le_sqrt h2

theorem sqrtLe_mono {x y : ℚ} (hx : 0 ≤ x) (hxy : x ≤ y) (k : ℕ) :
    sqrtLe x k ≤ sqrtLe y k := by
  have h := sqrtFloorScaled_mono hx hxy k
  have hc : (sqrtFloorScaled x k : ℚ) ≤ (sqrtFloorScaled y k : ℚ) := by exact_mod_cast h
  simp only [sqrtLe, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

theorem sqrtGe_mono {x y : ℚ} (hx : 0 ≤ x) (hxy : x ≤ y) (k : ℕ) :
    sqrtGe x k ≤ sqrtGe y k := by
  have h := sqrtFloorScaled_mono hx hxy k
  have hc : ((sqrtFloorScaled x k : ℚ) + 1) ≤ ((sqrtFloorScaled y k : ℚ) + 1) := by
    have : (sqrtFloorScaled x k : ℚ) ≤ (sqrtFloorScaled y k : ℚ) := by exact_mod_cast h
    linarith
  simp only [sqrtGe, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right hc (by positivity)

/-- Refining the precision doubles the scaled integer part (up to rounding): `⌊√x·2^{k+1}⌋` is at
least `2⌊√x·2^k⌋`. -/
theorem sqrtFloorScaled_succ_ge (x : ℚ) (k : ℕ) (hx : 0 ≤ x) :
    2 * sqrtFloorScaled x k ≤ sqrtFloorScaled x (k + 1) := by
  have h4 : (0 : ℚ) < 4 ^ k := four_pow_pos k
  have h4' : (0 : ℚ) < 4 ^ (k + 1) := four_pow_pos (k + 1)
  have hkey : (4 * (x * 4 ^ k).floor : ℤ) ≤ (x * 4 ^ (k + 1)).floor := by
    show (4 * (x * 4 ^ k).floor : ℤ) ≤ ⌊x * 4 ^ (k + 1)⌋
    apply Int.le_floor.mpr
    have hcast : ((4 * (x * 4 ^ k).floor : ℤ) : ℚ) = 4 * ((x * 4 ^ k).floor : ℚ) := by
      push_cast; ring
    rw [hcast]
    have hfl : ((x * 4 ^ k).floor : ℚ) ≤ x * 4 ^ k := Rat.floor_le _
    have hrw : (4 : ℚ) * (x * 4 ^ k) = x * 4 ^ (k + 1) := by ring
    calc (4 : ℚ) * ((x * 4 ^ k).floor : ℚ) ≤ 4 * (x * 4 ^ k) := by linarith [hfl]
      _ = x * 4 ^ (k + 1) := hrw
  have hkeyN : 4 * (x * 4 ^ k).floor.toNat ≤ (x * 4 ^ (k + 1)).floor.toNat := by
    have h0 : (0 : ℤ) ≤ (x * 4 ^ k).floor := Int.floor_nonneg.mpr (mul_nonneg hx h4.le)
    have h0' : (0 : ℤ) ≤ (x * 4 ^ (k + 1)).floor :=
      Int.floor_nonneg.mpr (mul_nonneg hx h4'.le)
    have h2 : ((4 * (x * 4 ^ k).floor.toNat : ℕ) : ℤ)
        ≤ ((x * 4 ^ (k + 1)).floor.toNat : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_ofNat, Int.toNat_of_nonneg h0, Int.toNat_of_nonneg h0']
      exact hkey
    exact_mod_cast h2
  rw [sqrtFloorScaled, sqrtFloorScaled, Nat.le_sqrt']
  calc (2 * Nat.sqrt (x * 4 ^ k).floor.toNat) ^ 2
      = 4 * (Nat.sqrt (x * 4 ^ k).floor.toNat) ^ 2 := by ring
    _ ≤ 4 * (x * 4 ^ k).floor.toNat := by
        have := Nat.sqrt_le' (x * 4 ^ k).floor.toNat
        linarith
    _ ≤ (x * 4 ^ (k + 1)).floor.toNat := hkeyN

/-- Refining the precision cannot gain more than one unit: `⌊√x·2^{k+1}⌋ ≤ 2⌊√x·2^k⌋ + 1`. -/
theorem sqrtFloorScaled_succ_le (x : ℚ) (k : ℕ) (hx : 0 ≤ x) :
    sqrtFloorScaled x (k + 1) ≤ 2 * sqrtFloorScaled x k + 1 := by
  have h4 : (0 : ℚ) < 4 ^ k := four_pow_pos k
  have hx4 : (0 : ℚ) ≤ x * 4 ^ k := mul_nonneg hx h4.le
  have hlt : x * 4 ^ k < ((sqrtFloorScaled x k : ℚ) + 1) ^ 2 := floorSqrt_lt_succ_sq _ hx4
  have hmain : x * 4 ^ (k + 1) < ((2 * (sqrtFloorScaled x k : ℚ)) + 2) ^ 2 := by
    have h1 : (4 : ℚ) * (x * 4 ^ k) < 4 * (((sqrtFloorScaled x k : ℚ)) + 1) ^ 2 := by
      linarith [hlt]
    have e1 : (4 : ℚ) * (x * 4 ^ k) = x * 4 ^ (k + 1) := by ring
    have e2 : (4 : ℚ) * (((sqrtFloorScaled x k : ℚ)) + 1) ^ 2
        = ((2 * (sqrtFloorScaled x k : ℚ)) + 2) ^ 2 := by ring
    linarith [h1, e1, e2]
  have hz2 : (x * 4 ^ (k + 1)).floor.toNat < (2 * sqrtFloorScaled x k + 2) ^ 2 := by
    have hz : (x * 4 ^ (k + 1)).floor
        < (((2 * sqrtFloorScaled x k + 2) ^ 2 : ℕ) : ℤ) := by
      show ⌊x * 4 ^ (k + 1)⌋ < (((2 * sqrtFloorScaled x k + 2) ^ 2 : ℕ) : ℤ)
      apply Int.floor_lt.mpr
      push_cast
      exact hmain
    have h0 : (0 : ℤ) ≤ (x * 4 ^ (k + 1)).floor :=
      Int.floor_nonneg.mpr (mul_nonneg hx (four_pow_pos (k + 1)).le)
    simpa using (Int.toNat_lt (n := (2 * sqrtFloorScaled x k + 2) ^ 2) h0).mpr hz
  have hN : sqrtFloorScaled x (k + 1) < 2 * sqrtFloorScaled x k + 2 := by
    have h3 : Nat.sqrt (x * 4 ^ (k + 1)).floor.toNat < 2 * sqrtFloorScaled x k + 2 := by
      rw [Nat.sqrt_lt']
      exact hz2
    simpa only [sqrtFloorScaled] using h3
  omega

theorem sqrtLe_mono_k (x : ℚ) (k : ℕ) (hx : 0 ≤ x) : sqrtLe x k ≤ sqrtLe x (k + 1) := by
  have h := sqrtFloorScaled_succ_ge x k hx
  have hcast : (2 * sqrtFloorScaled x k : ℚ) ≤ (sqrtFloorScaled x (k + 1) : ℚ) := by
    exact_mod_cast h
  have hp : (0 : ℚ) < 2 ^ k := two_pow_pos k
  have hp' : ((2 : ℚ) ^ k) ≠ 0 := ne_of_gt hp
  have h2 : (2 : ℚ) ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  simp only [sqrtLe]
  rw [div_le_iff₀ hp]
  have hw : (sqrtFloorScaled x (k + 1) : ℚ) / 2 ^ (k + 1) * 2 ^ k
      = (sqrtFloorScaled x (k + 1) : ℚ) / 2 := by
    rw [h2]; field_simp
  rw [hw]
  linarith

/-- **Nestedness**: the upper brackets decrease with the precision `k`. -/
theorem sqrtGe_antitone_k (x : ℚ) (k : ℕ) (hx : 0 ≤ x) : sqrtGe x (k + 1) ≤ sqrtGe x k := by
  have h := sqrtFloorScaled_succ_le x k hx
  have hcast : (sqrtFloorScaled x (k + 1) : ℚ) ≤ (2 * sqrtFloorScaled x k : ℚ) + 1 := by
    exact_mod_cast h
  have hp : (0 : ℚ) < 2 ^ (k + 1) := two_pow_pos (k + 1)
  have hp' : ((2 : ℚ) ^ k) ≠ 0 := ne_of_gt (two_pow_pos k)
  simp only [sqrtGe]
  rw [div_le_iff₀ hp]
  have hw : ((sqrtFloorScaled x k : ℚ) + 1) / 2 ^ k * 2 ^ (k + 1)
      = 2 * ((sqrtFloorScaled x k : ℚ) + 1) := by
    have h2 : (2 : ℚ) ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
    rw [h2]; field_simp
  rw [hw]
  linarith

/-- The bracket can be made arbitrarily tight; one bit per unit of accuracy. -/
theorem exists_sqrt_width_le (x : ℚ) {e : ℚ} (he : 0 < e) :
    ∃ k : ℕ, sqrtGe x k - sqrtLe x k ≤ e := by
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / e) (show (1 : ℚ) < 2 by norm_num)
  refine ⟨k, ?_⟩
  rw [sqrtGe_sub_sqrtLe]
  rw [div_le_iff₀ (two_pow_pos k)]
  have he1 : (0 : ℚ) < 1 / e := by positivity
  have hmul : (1 / e) * e = 1 := by field_simp
  nlinarith [hk, he, hmul]

/-- Product rule: a product of lower brackets lies below `√(xy)`, hence below the upper bracket. -/
theorem sqrtLe_mul_le_sqrtGe_mul {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    sqrtLe x k * sqrtLe y k ≤ sqrtGe (x * y) k := by
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have h1l : (sqrtLe x k : ℝ) ≤ Real.sqrt (x : ℝ) := sqrtLe_le_sqrt x k hx
  have h2l : (sqrtLe y k : ℝ) ≤ Real.sqrt (y : ℝ) := sqrtLe_le_sqrt y k hy
  have h1n : (0 : ℝ) ≤ (sqrtLe x k : ℝ) := by exact_mod_cast sqrtLe_nonneg x k
  have h2n : (0 : ℝ) ≤ (sqrtLe y k : ℝ) := by exact_mod_cast sqrtLe_nonneg y k
  have hxy' : ((x * y : ℚ) : ℝ) = (x : ℝ) * (y : ℝ) := by push_cast; ring
  have hgap : Real.sqrt (x : ℝ) * Real.sqrt (y : ℝ) = Real.sqrt ((x * y : ℚ) : ℝ) := by
    rw [hxy', Real.sqrt_mul (by exact_mod_cast hx)]
  have hlt : Real.sqrt ((x * y : ℚ) : ℝ) < (sqrtGe (x * y) k : ℝ) := sqrt_lt_sqrtGe (x * y) k hxy
  have hreal : (sqrtLe x k : ℝ) * sqrtLe y k ≤ (sqrtGe (x * y) k : ℝ) := by
    calc (sqrtLe x k : ℝ) * sqrtLe y k ≤ Real.sqrt (x : ℝ) * Real.sqrt (y : ℝ) :=
          mul_le_mul h1l h2l h2n (by positivity)
      _ = Real.sqrt ((x * y : ℚ) : ℝ) := hgap
      _ ≤ (sqrtGe (x * y) k : ℝ) := le_of_lt hlt
  exact_mod_cast hreal

/-- Product rule, other direction: `√(xy)` lies below a product of upper brackets. -/
theorem sqrtLe_mul_le_prod_sqrtGe {x y : ℚ} (hx : 0 ≤ x) (hy : 0 ≤ y) (k : ℕ) :
    sqrtLe (x * y) k ≤ sqrtGe x k * sqrtGe y k := by
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have h1l : (sqrtLe (x * y) k : ℝ) ≤ Real.sqrt ((x * y : ℚ) : ℝ) := sqrtLe_le_sqrt (x * y) k hxy
  have hxy' : ((x * y : ℚ) : ℝ) = (x : ℝ) * (y : ℝ) := by push_cast; ring
  have hgap : Real.sqrt ((x * y : ℚ) : ℝ) = Real.sqrt (x : ℝ) * Real.sqrt (y : ℝ) := by
    rw [hxy', Real.sqrt_mul (by exact_mod_cast hx)]
  have hx2 : Real.sqrt (x : ℝ) ≤ (sqrtGe x k : ℝ) := le_of_lt (sqrt_lt_sqrtGe x k hx)
  have hy2 : Real.sqrt (y : ℝ) ≤ (sqrtGe y k : ℝ) := le_of_lt (sqrt_lt_sqrtGe y k hy)
  have hy0 : (0 : ℝ) ≤ Real.sqrt (y : ℝ) := by positivity
  have hgx : (0 : ℝ) ≤ (sqrtGe x k : ℝ) := by
    have := sqrtGe_pos x k; exact_mod_cast this.le
  have hreal : (sqrtLe (x * y) k : ℝ) ≤ (sqrtGe x k : ℝ) * sqrtGe y k := by
    calc (sqrtLe (x * y) k : ℝ) ≤ Real.sqrt ((x * y : ℚ) : ℝ) := h1l
      _ = Real.sqrt (x : ℝ) * Real.sqrt (y : ℝ) := hgap
      _ ≤ (sqrtGe x k : ℝ) * sqrtGe y k := mul_le_mul hx2 hy2 hy0 hgx
  exact_mod_cast hreal
/-! ### 4.  Reciprocal brackets for `1/√x`

`invSqrtLe x k = 1/sqrtGe x k` and `invSqrtGe x k = 1/sqrtLe x k` bracket `1/√x` for `x > 0`: the
reciprocal of the smaller number is the larger one.

**Scale side condition.**  `sqrtLe x k = ⌊√x·2^k⌋/2^k` can vanish (e.g. `x = 1/4`, `k = 0`), and
then `invSqrtGe` is `1/0 = 0` in `ℚ` and is *not* an upper bound.  Every statement about
`invSqrtGe` therefore carries the honest side condition `1 ≤ x·4^k` (equivalently `1 ≤ √x·2^k`,
i.e. "the absolute precision `2^{-k}` is finer than `√x`"); for `x ≥ 1` it holds at every `k`.  The
lower bracket `invSqrtLe` needs no such condition, since `sqrtGe` is always positive.

The width identity `invSqrtGe - invSqrtLe = 2^{-k}/(sqrtLe·sqrtGe)` shows that the relative accuracy
of the reciprocal bracket is that of the square-root bracket, and for `x ≥ 1` the absolute width is
again `≤ 2^{-k}`. -/

/-- The integrated part of `⌊√x·2^k⌋` is at least `1` once `x·4^k ≥ 1`. -/
theorem one_le_sqrtFloorScaled {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) :
    (1 : ℚ) ≤ (sqrtFloorScaled x k : ℚ) := by
  have hpos : (0 : ℚ) < x * 4 ^ k := lt_of_lt_of_le one_pos h
  have hfl : (1 : ℤ) ≤ (x * 4 ^ k).floor := by
    show (1 : ℤ) ≤ ⌊x * 4 ^ k⌋
    exact Int.le_floor.mpr (by exact_mod_cast h)
  have h0 : (0 : ℤ) ≤ (x * 4 ^ k).floor := Int.floor_nonneg.mpr hpos.le
  have hN1 : (1 : ℕ) ≤ (x * 4 ^ k).floor.toNat := by
    rw [Int.le_toNat h0]; exact_mod_cast hfl
  have hN : (1 : ℕ) ≤ sqrtFloorScaled x k := by
    rw [sqrtFloorScaled, Nat.le_sqrt']; simpa using hN1
  exact_mod_cast hN

/-- The integrated part of `⌊√x·2^k⌋` is at least `2^k` once `x ≥ 1`. -/
theorem two_pow_le_sqrtFloorScaled {x : ℚ} (hx : 1 ≤ x) (k : ℕ) :
    2 ^ k ≤ sqrtFloorScaled x k := by
  have hx0 : (0 : ℚ) < x := lt_of_lt_of_le one_pos hx
  have hfl : ((4 ^ k : ℕ) : ℤ) ≤ (x * 4 ^ k).floor := by
    show ((4 ^ k : ℕ) : ℤ) ≤ ⌊x * 4 ^ k⌋
    apply Int.le_floor.mpr
    push_cast
    calc (4 : ℚ) ^ k = 1 * 4 ^ k := by ring
      _ ≤ x * 4 ^ k := mul_le_mul_of_nonneg_right hx (four_pow_pos k).le
  have h0 : (0 : ℤ) ≤ (x * 4 ^ k).floor :=
    Int.floor_nonneg.mpr (mul_pos hx0 (four_pow_pos k)).le
  have hM : 4 ^ k ≤ (x * 4 ^ k).floor.toNat := by
    rw [Int.le_toNat h0]; exact_mod_cast hfl
  rw [sqrtFloorScaled, Nat.le_sqrt']
  calc (2 ^ k) ^ 2 = 4 ^ k := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, Nat.mul_comm]
    _ ≤ _ := hM

/-- `sqrtLe x k > 0` as soon as the scaled argument clears `1`. -/
theorem sqrtLe_pos_of_one_le_mul {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) : 0 < sqrtLe x k := by
  have hN := one_le_sqrtFloorScaled h
  have hp : (0 : ℚ) < (2 ^ k)⁻¹ := inv_pos.mpr (two_pow_pos k)
  simp only [sqrtLe, div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right hN hp.le, hp]

/-- For `x ≥ 1` the scale condition `1 ≤ x·4^k` holds at every precision `k`. -/
theorem one_le_mul_four_pow {x : ℚ} (hx : 1 ≤ x) (k : ℕ) : 1 ≤ x * 4 ^ k := by
  have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one hx
  calc (1 : ℚ) = 1 * 1 := by ring
    _ ≤ x * 4 ^ k := mul_le_mul hx (one_le_four_pow k) zero_le_one hx0

/-- For `x ≥ 1` the lower bracket is strictly positive. -/
theorem sqrtLe_pos {x : ℚ} (hx : 1 ≤ x) (k : ℕ) : 0 < sqrtLe x k :=
  sqrtLe_pos_of_one_le_mul (one_le_mul_four_pow hx k)

/-- The lower bracket clears `2^{-k}` as soon as the scaled argument does. -/
theorem inv_two_pow_le_sqrtLe {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) :
    1 / 2 ^ k ≤ sqrtLe x k := by
  have hN := one_le_sqrtFloorScaled h
  have hp : (0 : ℚ) < (2 ^ k)⁻¹ := inv_pos.mpr (two_pow_pos k)
  simp only [sqrtLe, div_eq_mul_inv]
  nlinarith [mul_le_mul_of_nonneg_right hN hp.le, hp]

/-- For `x ≥ 1` the lower bracket is `≥ 1` (no loss at all). -/
theorem one_le_sqrtLe {x : ℚ} (hx : 1 ≤ x) (k : ℕ) : 1 ≤ sqrtLe x k := by
  have hN := two_pow_le_sqrtFloorScaled hx k
  have hNq : (2 : ℚ) ^ k ≤ (sqrtFloorScaled x k : ℚ) := by exact_mod_cast hN
  have hp : (0 : ℚ) < 2 ^ k := two_pow_pos k
  simp only [sqrtLe]
  rw [le_div_iff₀ hp]
  calc (1 : ℚ) * 2 ^ k = 2 ^ k := by ring
    _ ≤ _ := hNq

/-- The lower certified reciprocal bracket of `1/√x`: `1/sqrtGe x k`. -/
def invSqrtLe (x : ℚ) (k : ℕ) : ℚ := 1 / sqrtGe x k

/-- The upper certified reciprocal bracket of `1/√x`: `1/sqrtLe x k`.  Meaningful only under the
side condition `1 ≤ x·4^k` (see the section header). -/
def invSqrtGe (x : ℚ) (k : ℕ) : ℚ := 1 / sqrtLe x k

theorem invSqrtLe_nonneg (x : ℚ) (k : ℕ) : 0 ≤ invSqrtLe x k :=
  div_nonneg zero_le_one (sqrtGe_pos x k).le

theorem invSqrtLe_pos (x : ℚ) (k : ℕ) : 0 < invSqrtLe x k :=
  one_div_pos.mpr (sqrtGe_pos x k)

theorem invSqrtGe_pos {x : ℚ} (hx : 1 ≤ x) (k : ℕ) : 0 < invSqrtGe x k :=
  one_div_pos.mpr (sqrtLe_pos hx k)

theorem invSqrtLe_le_invSqrtGe {x : ℚ} (hx : 1 ≤ x) (k : ℕ) :
    invSqrtLe x k ≤ invSqrtGe x k := by
  have h1 := sqrtLe_le_sqrtGe x k
  have h2 := sqrtLe_pos hx k
  simp only [invSqrtLe, invSqrtGe]
  exact one_div_le_one_div_of_le h2 h1

/-- **`invSqrtLe` really is a lower bound for `1/√x`** (no side condition: `sqrtGe` is positive). -/
theorem invSqrtLe_le {x : ℚ} (hx : 0 < x) (k : ℕ) :
    (invSqrtLe x k : ℝ) ≤ 1 / Real.sqrt (x : ℝ) := by
  have hspos : (0 : ℝ) < Real.sqrt (x : ℝ) := by
    rw [Real.sqrt_pos]; exact_mod_cast hx
  have hge : Real.sqrt (x : ℝ) ≤ (sqrtGe x k : ℝ) := le_of_lt (sqrt_lt_sqrtGe x k hx.le)
  have hcast : ((invSqrtLe x k : ℚ) : ℝ) = 1 / (sqrtGe x k : ℝ) := by
    simp only [invSqrtLe]; push_cast; ring
  rw [hcast]
  exact one_div_le_one_div_of_le hspos hge

/-- **`invSqrtGe` is an upper bound for `1/√x`** under the scale side condition `1 ≤ x·4^k`. -/
theorem le_invSqrtGe {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) :
    1 / Real.sqrt (x : ℝ) ≤ (invSqrtGe x k : ℝ) := by
  have hx : (0 : ℚ) < x := by
    by_contra hx'
    have hx'' : x ≤ 0 := not_lt.mp hx'
    have h4 : (0 : ℚ) < 4 ^ k := four_pow_pos k
    nlinarith [h, h4, hx'']
  have hle : (0 : ℝ) < (sqrtLe x k : ℝ) := by
    have := sqrtLe_pos_of_one_le_mul h; exact_mod_cast this
  have hle2 : (sqrtLe x k : ℝ) ≤ Real.sqrt (x : ℝ) := sqrtLe_le_sqrt x k hx.le
  have hcast : ((invSqrtGe x k : ℚ) : ℝ) = 1 / (sqrtLe x k : ℝ) := by
    simp only [invSqrtGe]; push_cast; ring
  rw [hcast]
  exact one_div_le_one_div_of_le hle hle2

/-- **The enclosure of `1/√x`**: `invSqrtLe x k ≤ 1/√x ≤ invSqrtGe x k`. -/
theorem invSqrt_bracket {x : ℚ} {k : ℕ} (hx : 0 < x) (h : 1 ≤ x * 4 ^ k) :
    (invSqrtLe x k : ℝ) ≤ 1 / Real.sqrt (x : ℝ) ∧
      1 / Real.sqrt (x : ℝ) ≤ (invSqrtGe x k : ℝ) :=
  ⟨invSqrtLe_le hx k, le_invSqrtGe h⟩

/-- **Width of the reciprocal bracket, exactly**: `2^{-k}/(sqrtLe·sqrtGe)`. -/
theorem invSqrt_width {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) :
    invSqrtGe x k - invSqrtLe x k = (1 / 2 ^ k) / (sqrtLe x k * sqrtGe x k) := by
  have hs : sqrtLe x k ≠ 0 := ne_of_gt (sqrtLe_pos_of_one_le_mul h)
  have hg : sqrtGe x k ≠ 0 := ne_of_gt (sqrtGe_pos x k)
  have key : sqrtGe x k - sqrtLe x k = 1 / 2 ^ k := sqrtGe_sub_sqrtLe x k
  have e : (1 : ℚ) * sqrtGe x k - sqrtLe x k * 1 = 1 / 2 ^ k := by
    rw [← key]; ring
  simp only [invSqrtGe, invSqrtLe]
  rw [div_sub_div _ _ hs hg, e]

/-- Absolute width bound for the reciprocal bracket: it never exceeds `2^k`. -/
theorem invSqrt_width_le {x : ℚ} {k : ℕ} (h : 1 ≤ x * 4 ^ k) :
    invSqrtGe x k - invSqrtLe x k ≤ 2 ^ k := by
  have hs : (0 : ℚ) < sqrtLe x k := sqrtLe_pos_of_one_le_mul h
  have hN : (1 : ℚ) ≤ (sqrtFloorScaled x k : ℚ) := one_le_sqrtFloorScaled h
  have hp : (0 : ℚ) < 2 ^ k := two_pow_pos k
  have hle : (0 : ℚ) ≤ 1 / sqrtGe x k := (one_div_pos.mpr (sqrtGe_pos x k)).le
  have hkey : (1 : ℚ) / sqrtLe x k = 2 ^ k / (sqrtFloorScaled x k : ℚ) := by
    simp only [sqrtLe]
    rw [one_div_div]
  have hfin : (2 : ℚ) ^ k / (sqrtFloorScaled x k : ℚ) ≤ 2 ^ k := by
    calc (2 : ℚ) ^ k / (sqrtFloorScaled x k : ℚ) ≤ 2 ^ k / 1 :=
          div_le_div_of_nonneg_left hp.le one_pos hN
      _ = 2 ^ k := by ring
  simp only [invSqrtGe, invSqrtLe]
  calc (1 : ℚ) / sqrtLe x k - 1 / sqrtGe x k ≤ 1 / sqrtLe x k := by linarith
    _ = 2 ^ k / (sqrtFloorScaled x k : ℚ) := hkey
    _ ≤ 2 ^ k := hfin

/-- For `x ≥ 1` the reciprocal bracket is as accurate as the square-root bracket: width `≤ 2^{-k}`. -/
theorem invSqrt_width_le_of_one_le {x : ℚ} (hx : 1 ≤ x) (k : ℕ) :
    invSqrtGe x k - invSqrtLe x k ≤ 1 / 2 ^ k := by
  have h1 : (1 : ℚ) ≤ sqrtLe x k := one_le_sqrtLe hx k
  have hg : sqrtLe x k ≤ sqrtGe x k := sqrtLe_le_sqrtGe x k
  have hnum : (0 : ℚ) ≤ 1 / 2 ^ k := by positivity
  have hden : (1 : ℚ) ≤ sqrtLe x k * sqrtGe x k := by
    have h0 : (0 : ℚ) ≤ sqrtLe x k := (sqrtLe_pos hx k).le
    have hge1 : (1 : ℚ) ≤ sqrtGe x k := le_trans h1 hg
    calc (1 : ℚ) = 1 * 1 := by ring
      _ ≤ sqrtLe x k * sqrtGe x k := mul_le_mul h1 hge1 zero_le_one h0
  rw [invSqrt_width (one_le_mul_four_pow hx k)]
  calc (1 / 2 ^ k) / (sqrtLe x k * sqrtGe x k) ≤ (1 / 2 ^ k) / 1 :=
        div_le_div_of_nonneg_left hnum one_pos hden
    _ = 1 / 2 ^ k := by ring

/-- For `x ≥ 1` the upper reciprocal bracket is `≤ 1`. -/
theorem invSqrtGe_le_one {x : ℚ} (hx : 1 ≤ x) (k : ℕ) : invSqrtGe x k ≤ 1 := by
  have hs : (0 : ℚ) < sqrtLe x k := sqrtLe_pos hx k
  have h1 : (1 : ℚ) ≤ sqrtLe x k := one_le_sqrtLe hx k
  simp only [invSqrtGe]
  calc 1 / sqrtLe x k ≤ 1 / 1 := one_div_le_one_div_of_le one_pos h1
    _ = 1 := by ring

/-- Antitonicity: if `x ≤ y` then the upper bracket of `y` is below the lower bracket of `x`. -/
theorem invSqrtLe_antitone {x y : ℚ} {k : ℕ} (hx : 0 < x) (hxy : x ≤ y) (hy : 1 ≤ x * 4 ^ k) :
    invSqrtLe y k ≤ invSqrtGe x k := by
  have h1 : (invSqrtLe y k : ℝ) ≤ 1 / Real.sqrt (y : ℝ) :=
    invSqrtLe_le (lt_of_lt_of_le hx hxy) k
  have h2 : 1 / Real.sqrt (y : ℝ) ≤ 1 / Real.sqrt (x : ℝ) := by
    have hxr : (0 : ℝ) < Real.sqrt (x : ℝ) := by rw [Real.sqrt_pos]; exact_mod_cast hx
    apply one_div_le_one_div_of_le hxr
    apply Real.sqrt_le_sqrt
    exact_mod_cast hxy
  have h3 : 1 / Real.sqrt (x : ℝ) ≤ (invSqrtGe x k : ℝ) := le_invSqrtGe hy
  exact_mod_cast (le_trans h1 (le_trans h2 h3))

/-! ### 5.  Log-scale normalisers

The ellipsoid engine tracks radii and determinant ratios in a *logarithmic* scale: instead of
bounding a number it records the exponent `l` of the dyadic cell `[2^l, 2^{l+1})` containing it.
`log2cell x = ⌊log₂ (max x 1)⌋` is the normaliser for a number of size `≥ 0`; `log2cell (1/x)`
triggers the same normaliser for reciprocals, giving the cell of `min x 1` (both directions are
proved).  These are the "log scale" bookkeeping lemmas requested by the ellipsoid brick. -/

/-- `⌊log₂ (max x 1)⌋`, the exponent of the dyadic cell containing `max x 1`. -/
def log2cell (x : ℚ) : ℤ := if x ≤ 1 then 0 else (Nat.log2 x.floor.toNat : ℤ)

theorem log2cell_nonneg (x : ℚ) : 0 ≤ log2cell x := by
  simp only [log2cell]
  split
  · exact le_refl 0
  · exact Int.natCast_nonneg _

theorem log2cell_of_le_one {x : ℚ} (hx : x ≤ 1) : log2cell x = 0 := by
  simp only [log2cell, if_pos hx]

theorem log2cell_of_one_lt {x : ℚ} (hx : 1 < x) : log2cell x = (Nat.log2 x.floor.toNat : ℤ) := by
  simp only [log2cell, if_neg (not_le.mpr hx)]

/-- **Lower half of the scale certificate**: `2^(log2cell x) ≤ max x 1`. -/
theorem two_pow_log2cell_le (x : ℚ) : (2 : ℚ) ^ (log2cell x) ≤ max x 1 := by
  by_cases h : x ≤ 1
  · rw [log2cell_of_le_one h, zpow_zero]
    exact le_max_right _ _
  · have h1 : 1 < x := not_le.mp h
    have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one h1.le
    have hfl1 : (1 : ℤ) ≤ x.floor := by
      show (1 : ℤ) ≤ ⌊x⌋
      exact Int.le_floor.mpr (by exact_mod_cast h1.le)
    have h0 : (0 : ℤ) ≤ x.floor := Int.floor_nonneg.mpr hx0
    have hn : x.floor.toNat ≠ 0 := by
      intro hc
      have hc' : ((x.floor.toNat : ℕ) : ℤ) = 0 := by exact_mod_cast hc
      rw [Int.toNat_of_nonneg h0] at hc'
      omega
    have hle : 2 ^ Nat.log2 x.floor.toNat ≤ x.floor.toNat :=
      (Nat.le_log2 hn).mp (le_refl _)
    have hleq : (2 : ℚ) ^ Nat.log2 x.floor.toNat ≤ (x.floor : ℚ) := by
      calc (2 : ℚ) ^ Nat.log2 x.floor.toNat
          = ((2 ^ Nat.log2 x.floor.toNat : ℕ) : ℚ) := by push_cast; ring
        _ ≤ ((x.floor.toNat : ℕ) : ℚ) := by exact_mod_cast hle
        _ = (x.floor : ℚ) := floor_toNat_cast hx0
    rw [log2cell_of_one_lt h1, zpow_natCast, max_eq_left h1.le]
    exact le_trans hleq (Rat.floor_le x)

/-- **Upper half of the scale certificate**: `max x 1 < 2^(log2cell x + 1)`. -/
theorem max_lt_two_pow_log2cell_succ (x : ℚ) : max x 1 < (2 : ℚ) ^ (log2cell x + 1) := by
  by_cases h : x ≤ 1
  · rw [log2cell_of_le_one h, max_eq_right h]
    norm_num
  · have h1 : 1 < x := not_le.mp h
    have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one h1.le
    have hfl1 : (1 : ℤ) ≤ x.floor := by
      show (1 : ℤ) ≤ ⌊x⌋
      exact Int.le_floor.mpr (by exact_mod_cast h1.le)
    have h0 : (0 : ℤ) ≤ x.floor := Int.floor_nonneg.mpr hx0
    have hn : x.floor.toNat ≠ 0 := by
      intro hc
      have hc' : ((x.floor.toNat : ℕ) : ℤ) = 0 := by exact_mod_cast hc
      rw [Int.toNat_of_nonneg h0] at hc'
      omega
    have hlt : x.floor.toNat < 2 ^ (Nat.log2 x.floor.toNat + 1) := by
      have hiff : (Nat.log2 x.floor.toNat + 1 ≤ Nat.log2 x.floor.toNat) ↔
          (2 ^ (Nat.log2 x.floor.toNat + 1) ≤ x.floor.toNat) := Nat.le_log2 hn
      rw [← not_le]
      intro hc
      exact absurd (hiff.mpr hc) (by omega)
    have hcastn : ((x.floor.toNat : ℕ) : ℚ) = (x.floor : ℚ) := floor_toNat_cast hx0
    have hltq : x < (2 : ℚ) ^ (Nat.log2 x.floor.toNat + 1) := by
      have hstep : ((x.floor.toNat : ℕ) : ℚ) + 1
          ≤ (2 : ℚ) ^ (Nat.log2 x.floor.toNat + 1) := by
        have hsucc : (((x.floor.toNat + 1 : ℕ)) : ℚ)
            ≤ (((2 ^ (Nat.log2 x.floor.toNat + 1) : ℕ)) : ℚ) := by
          exact_mod_cast Nat.succ_le_of_lt hlt
        have hcast : (((2 ^ (Nat.log2 x.floor.toNat + 1) : ℕ) : ℚ))
            = (2 : ℚ) ^ (Nat.log2 x.floor.toNat + 1) := by push_cast; ring
        rw [hcast] at hsucc
        calc ((x.floor.toNat : ℕ) : ℚ) + 1 = (((x.floor.toNat + 1 : ℕ)) : ℚ) := by
              push_cast; ring
          _ ≤ (2 : ℚ) ^ (Nat.log2 x.floor.toNat + 1) := hsucc
      calc x < (x.floor : ℚ) + 1 := by
            have := Rat.lt_floor_add_one x
            rwa [show ((x.floor + 1 : ℤ) : ℚ) = (x.floor : ℚ) + 1 from by push_cast; ring] at this
        _ = ((x.floor.toNat : ℕ) : ℚ) + 1 := by rw [hcastn]
        _ ≤ (2 : ℚ) ^ (Nat.log2 x.floor.toNat + 1) := hstep
    have hz : ((Nat.log2 x.floor.toNat : ℕ) : ℤ) + 1
        = ((Nat.log2 x.floor.toNat + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [log2cell_of_one_lt h1, hz, zpow_natCast, max_eq_left h1.le]
    exact hltq

/-- **The scale certificate**: `2^l ≤ max x 1 < 2^{l+1}` for `l = log2cell x`. -/
theorem log2cell_spec (x : ℚ) :
    (2 : ℚ) ^ (log2cell x) ≤ max x 1 ∧ max x 1 < (2 : ℚ) ^ (log2cell x + 1) :=
  ⟨two_pow_log2cell_le x, max_lt_two_pow_log2cell_succ x⟩

/-- Monotonicity of `Nat.log2`. -/
theorem nat_log2_le_log2 {n m : ℕ} (hn : n ≠ 0) (h : n ≤ m) : n.log2 ≤ m.log2 := by
  have hm : m ≠ 0 := by omega
  rw [Nat.le_log2 hm]
  exact le_trans ((Nat.le_log2 hn).mp (le_refl _)) h

/-- Monotonicity of the scale normaliser. -/
theorem log2cell_mono {x y : ℚ} (hx : 1 < x) (hxy : x ≤ y) : log2cell x ≤ log2cell y := by
  have hy : 1 < y := lt_of_lt_of_le hx hxy
  have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one hx.le
  have h0 : (0 : ℤ) ≤ x.floor := Int.floor_nonneg.mpr hx0
  have hn : x.floor.toNat ≠ 0 := by
    intro hc
    have hc' : ((x.floor.toNat : ℕ) : ℤ) = 0 := by exact_mod_cast hc
    rw [Int.toNat_of_nonneg h0] at hc'
    have hfl1 : (1 : ℤ) ≤ x.floor := by
      show (1 : ℤ) ≤ ⌊x⌋
      exact Int.le_floor.mpr (by exact_mod_cast hx.le)
    omega
  have hle : x.floor.toNat ≤ y.floor.toNat := Int.toNat_le_toNat (Int.floor_mono hxy)
  rw [log2cell_of_one_lt hx, log2cell_of_one_lt hy]
  have := nat_log2_le_log2 hn hle
  exact_mod_cast this

/-- **Log-scale accounting for the square root**: the *squared* bracket of `√x` straddles the scale
cell of `x`.  This is the form in which the ellipsoid engine compares radii with determinants: the
squared radius of the bracket is pinned between `2^l` and `2^{l+1}`. -/
theorem sqrt_bracket_scale {x : ℚ} (hx : 1 ≤ x) (k : ℕ) :
    (2 : ℚ) ^ (log2cell x) ≤ (sqrtGe x k) ^ 2 ∧ (sqrtLe x k) ^ 2 < (2 : ℚ) ^ (log2cell x + 1) := by
  have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one hx
  constructor
  · calc (2 : ℚ) ^ (log2cell x) ≤ max x 1 := two_pow_log2cell_le x
      _ = x := max_eq_left hx
      _ ≤ (sqrtGe x k) ^ 2 := (sq_lt_sqrtGe_sq x k hx0).le
  · calc (sqrtLe x k) ^ 2 ≤ x := sqrtLe_sq_le x k hx0
      _ = max x 1 := (max_eq_left hx).symm
      _ < (2 : ℚ) ^ (log2cell x + 1) := max_lt_two_pow_log2cell_succ x

/-- The bracket of `√x` also fits in the cell of `x` without squaring. -/
theorem sqrtLe_le_two_pow_log2cell_succ {x : ℚ} (hx : 1 ≤ x) (k : ℕ) :
    sqrtLe x k < (2 : ℚ) ^ (log2cell x + 1) := by
  have hx0 : (0 : ℚ) ≤ x := le_trans zero_le_one hx
  have h1 : sqrtLe x k ≤ x := by
    have h := sqrtLe_le_sqrt x k hx0
    have h2 : Real.sqrt (x : ℝ) ≤ (x : ℝ) := by
      have : (1:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ (x:ℝ) by linarith), Real.sqrt_nonneg (x:ℝ)]
    exact_mod_cast le_trans h h2
  calc sqrtLe x k ≤ x := h1
    _ = max x 1 := (max_eq_left hx).symm
    _ < (2 : ℚ) ^ (log2cell x + 1) := max_lt_two_pow_log2cell_succ x

/-- **Products stay on the log scale**: the cell of `x·y` is at most the sum of the cells plus one. -/
theorem log2cell_mul_le {x y : ℚ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    log2cell (x * y) ≤ log2cell x + log2cell y + 1 := by
  have hx0 : (0 : ℚ) < x := lt_of_lt_of_le one_pos hx
  have hy0 : (0 : ℚ) < y := lt_of_lt_of_le one_pos hy
  have hxy1 : (1 : ℚ) ≤ x * y := by
    calc (1 : ℚ) = 1 * 1 := by ring
      _ ≤ x * y := mul_le_mul hx hy zero_le_one hx0.le
  have hltx : x < (2 : ℚ) ^ (log2cell x + 1) := by
    have := max_lt_two_pow_log2cell_succ x
    rwa [max_eq_left hx] at this
  have hlty : y < (2 : ℚ) ^ (log2cell y + 1) := by
    have := max_lt_two_pow_log2cell_succ y
    rwa [max_eq_left hy] at this
  have hP : (0 : ℚ) < (2 : ℚ) ^ (log2cell x + 1) := zpow_pos (by norm_num) _
  have hlt : x * y < (2 : ℚ) ^ (log2cell x + log2cell y + 2) := by
    have s1 : x * y < (2 : ℚ) ^ (log2cell x + 1) * y := mul_lt_mul_of_pos_right hltx hy0
    have s2 : (2 : ℚ) ^ (log2cell x + 1) * y
        < (2 : ℚ) ^ (log2cell x + 1) * (2 : ℚ) ^ (log2cell y + 1) :=
      mul_lt_mul_of_pos_left hlty hP
    have e1 : (2 : ℚ) ^ (log2cell x + 1) * (2 : ℚ) ^ (log2cell y + 1)
        = (2 : ℚ) ^ ((log2cell x + 1) + (log2cell y + 1)) :=
      (zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0) _ _).symm
    have e2 : (2 : ℚ) ^ ((log2cell x + 1) + (log2cell y + 1))
        = (2 : ℚ) ^ (log2cell x + log2cell y + 2) := by
      congr 1
      ring
    linarith [s1, s2, e1, e2]
  by_contra hc
  have hc' : log2cell x + log2cell y + 2 ≤ log2cell (x * y) := by omega
  have hmono : (2 : ℚ) ^ (log2cell x + log2cell y + 2) ≤ (2 : ℚ) ^ (log2cell (x * y)) :=
    zpow_le_zpow_right₀ (by norm_num) hc'
  have hle := two_pow_log2cell_le (x * y)
  rw [max_eq_left hxy1] at hle
  linarith

/-- **Powers stay on the log scale**: `d` factors cost at most `d·(cell+1)`. -/
theorem log2cell_pow_le {x : ℚ} (hx : 1 ≤ x) (d : ℕ) :
    log2cell (x ^ d) ≤ (d : ℤ) * (log2cell x + 1) := by
  induction d with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul]
      exact le_of_eq (log2cell_of_le_one (le_refl 1))
  | succ n ih =>
      have hp : (1 : ℚ) ≤ x ^ n := one_le_pow₀ hx
      have hmul : log2cell (x ^ (n + 1)) ≤ log2cell (x ^ n) + log2cell x + 1 := by
        rw [pow_succ]
        exact log2cell_mul_le hp hx
      have hcast : ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      calc log2cell (x ^ (n + 1)) ≤ log2cell (x ^ n) + log2cell x + 1 := hmul
        _ ≤ (n : ℤ) * (log2cell x + 1) + log2cell x + 1 := by linarith
        _ = ((n + 1 : ℕ) : ℤ) * (log2cell x + 1) := by rw [← hcast]; ring

/-- **Reciprocal scale certificate**: `log2cell (1/x)` gives the dyadic cell of `min x 1`. -/
theorem log2cell_inv {x : ℚ} (hx : 0 < x) :
    (2 : ℚ) ^ (-(log2cell (1 / x) + 1)) < min x 1 ∧
      min x 1 ≤ (2 : ℚ) ^ (-(log2cell (1 / x))) := by
  obtain ⟨h1, h2⟩ := log2cell_spec (1 / x)
  have hm : max (1 / x) 1 = 1 / min x 1 := by
    by_cases h : x ≤ 1
    · have h1x : (1 : ℚ) ≤ 1 / x := by
        rw [le_div_iff₀ hx]; simpa using h
      rw [max_eq_left h1x, min_eq_left h]
    · have h1' : 1 < x := not_le.mp h
      have h1x : 1 / x < 1 := (div_lt_one hx).mpr h1'
      rw [max_eq_right h1x.le, min_eq_right h1'.le]
      norm_num
  rw [hm] at h1 h2
  have hminpos : (0 : ℚ) < min x 1 := lt_min hx one_pos
  have hminpos' : (0 : ℚ) < 1 / min x 1 := by positivity
  have hzpos : (0 : ℚ) < (2 : ℚ) ^ (log2cell (1 / x)) := zpow_pos (by norm_num) _
  have hzpos2 : (0 : ℚ) < (2 : ℚ) ^ (log2cell (1 / x) + 1) := zpow_pos (by norm_num) _
  constructor
  · have hzw : (2 : ℚ) ^ (-(log2cell (1 / x) + 1))
        = 1 / (2 : ℚ) ^ (log2cell (1 / x) + 1) := by
      rw [_root_.zpow_neg, inv_eq_one_div]
    rw [hzw]
    have h3 := one_div_lt_one_div_of_lt hminpos' h2
    rwa [one_div_div, div_one] at h3
  · have hzw : (2 : ℚ) ^ (-(log2cell (1 / x))) = 1 / (2 : ℚ) ^ (log2cell (1 / x)) := by
      rw [_root_.zpow_neg, inv_eq_one_div]
    rw [hzw]
    have h3 := one_div_le_one_div_of_le hzpos h1
    rwa [one_div_div, div_one] at h3

/-! ### 6.  The Newton / AM–GM refinement step (over `ℝ`)

An iteration engine that starts from an *upper* bracket `s ≥ √x` can sharpen it with one Newton step
`s ↦ (s + x/s)/2`.  The exact identity shows the error is *squared and divided by `2s`*: one correct
bit is bought per step (the classical "doubling of digits"), which is exactly the accounting the
certified solver needs when it trades iterations for precision `k`. -/

/-- AM–GM: a Newton step taken from an over-estimate is still an over-estimate. -/
theorem sqrt_le_newton_step {x s : ℝ} (hx : 0 < x) (hs : Real.sqrt x ≤ s) :
    Real.sqrt x ≤ (s + x / s) / 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le (Real.sqrt_pos.mpr hx) hs
  rw [le_div_iff₀ two_pos]
  have h1 : x / s * s = x := div_mul_cancel₀ x (ne_of_gt hs0)
  have h2 : Real.sqrt x * Real.sqrt x = x := by
    simpa [sq] using Real.sq_sqrt hx.le
  nlinarith [sq_nonneg (s - Real.sqrt x), h1, h2]

/-- A Newton step taken from an over-estimate does not increase it. -/
theorem newton_step_le_self {x s : ℝ} (hx : 0 < x) (hs : Real.sqrt x ≤ s) :
    (s + x / s) / 2 ≤ s := by
  have hs0 : 0 < s := lt_of_lt_of_le (Real.sqrt_pos.mpr hx) hs
  have h2 : Real.sqrt x * Real.sqrt x = x := by
    simpa [sq] using Real.sq_sqrt hx.le
  have hr : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hxs : x / s ≤ s := by
    rw [div_le_iff₀ hs0]
    nlinarith [h2, hs, hr]
  linarith

/-- **Quadratic convergence, exact form**: the new error is `(old error)²/(2s)`. -/
theorem newton_step_sub_eq {x s : ℝ} (hx : 0 < x) (hs : Real.sqrt x ≤ s) :
    (s + x / s) / 2 - Real.sqrt x = (s - Real.sqrt x) ^ 2 / (2 * s) := by
  have hs0 : 0 < s := lt_of_lt_of_le (Real.sqrt_pos.mpr hx) hs
  have h1 : x / s * s = x := div_mul_cancel₀ x (ne_of_gt hs0)
  have h2 : Real.sqrt x * Real.sqrt x = x := by
    simpa [sq] using Real.sq_sqrt hx.le
  field_simp
  nlinarith [h1, h2]

/-- The error after one Newton step is at most `(old error)²/(2√x)`. -/
theorem newton_step_error_le {x s : ℝ} (hx : 0 < x) (hs : Real.sqrt x ≤ s) :
    (s + x / s) / 2 - Real.sqrt x ≤ (s - Real.sqrt x) ^ 2 / (2 * Real.sqrt x) := by
  have hspos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hs0 : 0 < s := lt_of_lt_of_le hspos hs
  rw [newton_step_sub_eq hx hs]
  have hnum : (0 : ℝ) ≤ (s - Real.sqrt x) ^ 2 := sq_nonneg _
  have hden : 2 * Real.sqrt x ≤ 2 * s := by linarith
  have hdenpos : (0 : ℝ) < 2 * Real.sqrt x := by linarith
  exact div_le_div_of_nonneg_left hnum hdenpos hden

/-! ### 7.  Kernel-checked computations

The brackets are honest computations: these `example`s are decided by the kernel from the
definitions (`norm_num` closes `Nat.sqrt` and `Nat.log2` on numerals; `Rat.floor` of a natural is
`Rat.floor_intCast`).  They are the sanity evidence that `sqrtLe`/`sqrtGe`/`log2cell` really run. -/

theorem floor_natCast (n : ℕ) : ((n : ℚ).floor) = (n : ℤ) := by
  show ⌊((n : ℕ) : ℚ)⌋ = (n : ℤ)
  rw [Int.floor_eq_iff]
  constructor <;> push_cast <;> norm_num

/-- `⌊√2·2^4⌋ = 22`, i.e. `√2 ≈ 1.375` from below at four bits. -/
example : sqrtFloorScaled 2 4 = 22 := by
  have h : (2 * 4 ^ 4 : ℚ) = ((512 : ℕ) : ℚ) := by norm_num
  simp only [sqrtFloorScaled, h, floor_natCast, Int.toNat_natCast]
  norm_num

example : sqrtLe 2 4 = 11 / 8 := by
  have h : sqrtFloorScaled 2 4 = 22 := by
    have h' : (2 * 4 ^ 4 : ℚ) = ((512 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [sqrtLe, h]
  norm_num

example : sqrtGe 2 4 = 23 / 16 := by
  have h : sqrtFloorScaled 2 4 = 22 := by
    have h' : (2 * 4 ^ 4 : ℚ) = ((512 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [sqrtGe, h]
  norm_num

/-- The bracket really brackets `√2`: `(11/8)² ≤ 2 < (23/16)²`. -/
example : (11 / 8 : ℚ) ^ 2 ≤ 2 ∧ (2 : ℚ) < (23 / 16) ^ 2 := by
  constructor <;> norm_num

/-- Exact at a perfect square: `√4 = 2`. -/
example : sqrtLe 4 5 = 2 := by
  have h : sqrtFloorScaled 4 5 = 64 := by
    have h' : (4 * 4 ^ 5 : ℚ) = ((4096 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [sqrtLe, h]
  norm_num

/-- One bit: `⌊√2⌋ = 1`, and the upper bracket is `2`. -/
example : sqrtLe 2 0 = 1 := by
  have h : sqrtFloorScaled 2 0 = 1 := by
    have h' : (2 * 4 ^ 0 : ℚ) = ((2 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [sqrtLe, h]
  norm_num

example : sqrtGe 2 0 = 2 := by
  have h : sqrtFloorScaled 2 0 = 1 := by
    have h' : (2 * 4 ^ 0 : ℚ) = ((2 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [sqrtGe, h]
  norm_num

/-- The reciprocal bracket at `x = 4`: `32/65 ≤ 1/2 ≤ 1/2`, the upper end exact. -/
example : invSqrtGe 4 5 = 1 / 2 := by
  have h : sqrtFloorScaled 4 5 = 64 := by
    have h' : (4 * 4 ^ 5 : ℚ) = ((4096 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [invSqrtGe, sqrtLe, h]
  norm_num

example : invSqrtLe 4 5 = 32 / 65 := by
  have h : sqrtFloorScaled 4 5 = 64 := by
    have h' : (4 * 4 ^ 5 : ℚ) = ((4096 : ℕ) : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', floor_natCast, Int.toNat_natCast]
    norm_num
  simp only [invSqrtLe, sqrtGe, h]
  norm_num

/-- The scale normaliser on the dyadic cell boundaries. -/
example : log2cell 1024 = 10 := by
  rw [log2cell_of_one_lt (by norm_num : (1 : ℚ) < 1024)]
  have h : ((1024 : ℚ).floor) = 1024 := by
    have h' : ((512 : ℕ) : ℚ) = (512 : ℚ) := by norm_num
    exact floor_natCast 1024
  rw [h]
  decide

example : log2cell 1023 = 9 := by
  rw [log2cell_of_one_lt (by norm_num : (1 : ℚ) < 1023)]
  have h : ((1023 : ℚ).floor) = 1023 := floor_natCast 1023
  rw [h]
  decide

example : log2cell 3 = 1 := by
  rw [log2cell_of_one_lt (by norm_num : (1 : ℚ) < 3)]
  have h : ((3 : ℚ).floor) = 3 := floor_natCast 3
  rw [h]
  decide

example : log2cell 1 = 0 := log2cell_of_le_one (le_refl 1)

example : log2cell (1 / 2) = 0 := log2cell_of_le_one (by norm_num)

/-- The trap that motivates the `1 ≤ x·4^k` side condition: at `x = 1/4`, `k = 0` the lower bracket
is `0` and `1/sqrtLe` collapses to `0`. -/
example : sqrtLe (1 / 4) 0 = 0 := by
  have hfl : ((1 / 4 : ℚ).floor) = 0 := by
    show ⌊(1 / 4 : ℚ)⌋ = 0
    rw [Int.floor_eq_iff]
    constructor <;> norm_num
  have h : sqrtFloorScaled (1 / 4) 0 = 0 := by
    have h' : ((1 / 4) * 4 ^ 0 : ℚ) = (1 / 4 : ℚ) := by norm_num
    simp only [sqrtFloorScaled, h', hfl]
    norm_num
  simp only [sqrtLe, h]
  norm_num

/-- **Brief-shaped statement**: `sqrtLe x k ≤ √x ≤ sqrtLe x k + 2^{-k}`. -/
theorem sqrt_bracket_width (x : ℚ) (k : ℕ) (hx : 0 ≤ x) :
    (sqrtLe x k : ℝ) ≤ Real.sqrt (x : ℝ) ∧
      Real.sqrt (x : ℝ) ≤ (sqrtLe x k : ℝ) + 1 / 2 ^ k := by
  refine ⟨sqrtLe_le_sqrt x k hx, ?_⟩
  have h1 : Real.sqrt (x : ℝ) < (sqrtGe x k : ℝ) := sqrt_lt_sqrtGe x k hx
  have h2 : ((sqrtGe x k : ℚ) : ℝ) = (sqrtLe x k : ℝ) + 1 / 2 ^ k := by
    rw [sqrtGe_eq_sqrtLe_add]; push_cast; ring
  rw [h2] at h1
  exact h1.le

/-- **Brief-shaped statement**: `invSqrtLe x k ≤ 1/√x ≤ invSqrtLe x k + 2^k` (crude width). -/
theorem invSqrt_bracket_width (x : ℚ) (k : ℕ) (hx : 0 < x) (h : 1 ≤ x * 4 ^ k) :
    (invSqrtLe x k : ℝ) ≤ 1 / Real.sqrt (x : ℝ) ∧
      1 / Real.sqrt (x : ℝ) ≤ (invSqrtLe x k : ℝ) + 2 ^ k := by
  refine ⟨invSqrtLe_le hx k, ?_⟩
  have h1 : 1 / Real.sqrt (x : ℝ) ≤ (invSqrtGe x k : ℝ) := le_invSqrtGe h
  have h2 : (invSqrtGe x k : ℝ) ≤ (invSqrtLe x k : ℝ) + (2 : ℝ) ^ k := by
    have hq : invSqrtGe x k ≤ invSqrtLe x k + (2 : ℚ) ^ k := by
      have := invSqrt_width_le h
      linarith
    have hcast : ((invSqrtLe x k + (2 : ℚ) ^ k : ℚ) : ℝ)
        = (invSqrtLe x k : ℝ) + (2 : ℝ) ^ k := by push_cast; ring
    calc (invSqrtGe x k : ℝ) ≤ ((invSqrtLe x k + (2 : ℚ) ^ k : ℚ) : ℝ) := by exact_mod_cast hq
      _ = (invSqrtLe x k : ℝ) + (2 : ℝ) ^ k := hcast
  exact le_trans h1 h2

/-! ### 8.  Name aliases matching the leaf-B brief

The brief calls the two brackets `DQ.sqrt_le` / `DQ.sqrt_ge` and the reciprocal pair
`DQ.invSqrt_le` / `DQ.invSqrt_ge`; these are the same functions under `camelCase` names above. -/

/-- Alias of `DQ.sqrtLe` (brief spelling). -/
abbrev sqrt_le (x : ℚ) (k : ℕ) : ℚ := sqrtLe x k

/-- Alias of `DQ.sqrtGe` (brief spelling). -/
abbrev sqrt_ge (x : ℚ) (k : ℕ) : ℚ := sqrtGe x k

/-- Alias of `DQ.invSqrtLe` (brief spelling). -/
abbrev invSqrt_le (x : ℚ) (k : ℕ) : ℚ := invSqrtLe x k

/-- Alias of `DQ.invSqrtGe` (brief spelling). -/
abbrev invSqrt_ge (x : ℚ) (k : ℕ) : ℚ := invSqrtGe x k

/-! ### 9.  Axiom evidence

Expected output: `[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide`. -/

#print axioms DQ.sqrtLe_le_sqrt
#print axioms DQ.sqrt_lt_sqrtGe
#print axioms DQ.sqrtGe_sub_sqrtLe
#print axioms DQ.sqrtLe_mul_le_sqrtGe_mul
#print axioms DQ.sqrtLe_mul_le_prod_sqrtGe
#print axioms DQ.invSqrt_bracket
#print axioms DQ.invSqrt_width
#print axioms DQ.log2cell_spec
#print axioms DQ.log2cell_inv
#print axioms DQ.newton_step_sub_eq
#print axioms DQ.sqrt_bracket_scale
#print axioms DQ.le_invSqrtGe
#print axioms DQ.sqrt_bracket_width
#print axioms DQ.invSqrt_bracket_width
#print axioms DQ.log2cell_mul_le
#print axioms DQ.log2cell_pow_le
#print axioms DQ.one_le_sqrtLe
#print axioms DQ.invSqrt_width_le_of_one_le

end DQ


/-! #### merged from `LeafB_ErrProp.lean` -/
/-
# Leaf B — `brick-errprop`: error propagation and perturbation bounds

Supporting brick for the certified SDP lower-value program of the 0.53 Quantum Max-Cut leaf
(`91ee3bff`). It supplies the *numerical robustness* layer that the exact-arithmetic bricks need
in order to turn a certificate computed from finitely-precise (dyadic) data into a statement about
the exact real/rational object.

Compile (in the Prove2me workspace): `lake env lean Solutions/Check_errprop.lean`.
Imports: `Mathlib` only. No `sorry`, no new axioms.

## What is proved

**1. Scalar error-budget algebra** (any `[Field R] [LinearOrder R] [IsStrictOrderedRing R]`,
hence both `ℚ` and `ℝ`):
* `abs_sub_le_add_of_abs_sub_le` — budgets compose: `|x-y| ≤ ε`, `|y-z| ≤ δ` ⟹ `|x-z| ≤ ε+δ`.
* `abs_mul_sub_mul_le` — product rule `|xy - x'y'| ≤ εx|y| + |x'|εy`.
* `pos_of_abs_sub_le_lt` — a margin survives: `|x-y| ≤ ε < x` ⟹ `0 < y`.
* `abs_sum_sub_sum_le` — budgets add over finsets.
* `abs_sub_le_natCast_mul_of_steps` — a chain of `m` steps each losing `≤ ε` loses `≤ m·ε`
  (the shape of every iterative numerical subroutine).

**2. The `ℓ¹`–`ℓ²` inequality** (`l1_sq_le_card_mul_l2sq`): `(∑ᵢ|zᵢ|)² ≤ n · ∑ᵢ zᵢ²`.
This is the Cauchy–Schwarz step that converts an entrywise sup-norm bound into an operator bound.

**3. Quadratic forms** of `Matrix (Fin n) (Fin n) R`: `quadForm A z = zᵀ (A z)`, with the double-sum
expansion, and linearity in `A` (`quadForm_add/_sub/_neg/_smul/_zero`), `quadForm_transpose`,
`quadForm_one`.

**4. Entrywise perturbation bounds — the main output**:
* `abs_quadForm_le_of_entry_le` : `(∀ i j, |Δᵢⱼ| ≤ ε) ⟹ |zᵀΔz| ≤ ε (∑ᵢ|zᵢ|)²`.
* `abs_quadForm_le_of_entry_le_card` : `… ⟹ |zᵀΔz| ≤ ε · n · ∑ᵢ zᵢ²`.
  (This is exactly the estimate `brick-certpsd` needs for its residual term `R`.)
* `quadForm_add_perturb_ge` : a margin degrades by the perturbation,
  `zᵀ(A+Δ)z ≥ (δ − ε·n)‖z‖²` when `zᵀAz ≥ δ‖z‖²`.

**5. Positive semidefiniteness** (generic in `R` with `[StarRing R] [TrivialStar R]`, so it applies
to `ℚ` — the exact-certificate notion — and to `ℝ`):
* `posSemidef_of_margin` : symmetric + `zᵀAz ≥ δ‖z‖²` with `δ ≥ 0` ⟹ `A.PosSemidef`.
* `posSemidef_add_of_margin` : `A + Δ` is PSD when `Δ` is symmetric, entrywise `≤ ε`, `ε·n ≤ δ`.
* `posSemidef_of_entry_near` : the pipeline shape — a computed matrix `M'` entrywise within `ε`
  of an exact matrix `M` with margin `δ` is PSD.
* `isSymm_diagonal`.

**6. The duality-gap budget**:
* `abs_sum_mul_sub_le` — a linear functional is Lipschitz in its argument (sup-norm budget).
* `abs_trace_mul_le` — the trace pairing: `|tr(ΔX)| ≤ ε · ∑ᵢⱼ|Xᵢⱼ|` for entrywise `|Δᵢⱼ| ≤ ε`.
* `gap_budget` — the assembled statement: if the dual vector `y` and the constraint matrix `A` are
  known only within budgets `εy`, `εA`, then the computed duality gap `∑ᵢ yᵢ + tr(A X)` differs from
  the exact gap by at most `εA · ∑ᵢⱼ|Xᵢⱼ| + n · εy`.

**7. Size bounds for PSD matrices** (all over `ℝ`, from the Gram factorisation
`Matrix.posSemidef_iff_eq_sum_vecMulVec` and Cauchy–Schwarz over the Gram rank):
* `sq_entry_le_diag_mul` : `X.PosSemidef → Xᵢⱼ ^ 2 ≤ Xᵢᵢ * Xⱼⱼ` (the `2 × 2` minor bound);
* `two_mul_abs_entry_le_diag_add` : `2 |Xᵢⱼ| ≤ Xᵢᵢ + Xⱼⱼ` (AM–GM);
* `sum_abs_entry_le_card_mul_trace` : `X.PosSemidef → ∑ᵢⱼ |Xᵢⱼ| ≤ n · tr X`;
* `abs_trace_mul_le_of_posSemidef` : `|tr(Δ X)| ≤ ε · n · tr X` for entrywise `|Δᵢⱼ| ≤ ε`, `ε ≥ 0`;
* `gap_budget_psd` : the gap budget in terms of the primal trace,
  `|Δgap| ≤ εA · n · tr X + n · εy`.

Two kernel-checked concrete instances at the end (`ℚ` and `ℝ`) exercise the main lemmas with
numerals, and `#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]`.

## Notes for the assembly
* Everything is stated for `n : ℕ` with indices `Fin n`, matching Mathlib's `Matrix` API, so it
  composes directly with `Matrix.PosSemidef` and with any Gram/LDL certificate produced over `ℚ`.
* `commRing_nf`/`ring`/`nlinarith` do the work; there is no custom syntax, no macro, no notation.
* The `ℚ` form of `posSemidef_*` gives `q(z) ≥ 0` for **rational** `z` only. Bridging that to `ℝ`
  (density of `ℚ` in `ℝ` + continuity of the quadratic form) is *not* done here.
-/


namespace LeafB.ErrProp

open Matrix

section Scalar

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

theorem abs_sub_le_add_of_abs_sub_le {x y z ε δ : R}
    (h1 : |x - y| ≤ ε) (h2 : |y - z| ≤ δ) : |x - z| ≤ ε + δ := by
  have h : x - z = (x - y) + (y - z) := by ring
  rw [h]
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem abs_mul_sub_mul_le {x x' y y' εx εy : R}
    (hx : |x - x'| ≤ εx) (hy : |y - y'| ≤ εy) :
    |x * y - x' * y'| ≤ εx * |y| + |x'| * εy := by
  have h : x * y - x' * y' = (x - x') * y + x' * (y - y') := by ring
  rw [h]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg y)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hy (abs_nonneg x')

theorem pos_of_abs_sub_le_lt {x y ε : R} (h : |x - y| ≤ ε) (hlt : ε < x) : 0 < y := by
  have h2 : x - y ≤ ε := (abs_sub_le_iff.1 h).1
  linarith

theorem abs_sum_sub_sum_le {ι : Type*} (s : Finset ι) (f g ε : ι → R)
    (h : ∀ i ∈ s, |f i - g i| ≤ ε i) :
    |∑ i ∈ s, f i - ∑ i ∈ s, g i| ≤ ∑ i ∈ s, ε i := by
  rw [← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum h)

theorem l1_sq_le_card_mul_l2sq {ι : Type*} [Fintype ι] (z : ι → R) :
    (∑ i, |z i|) ^ 2 ≤ (Fintype.card ι : R) * ∑ i, z i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι))
    (f := fun i => |z i|) (g := fun _ => (1 : R))
  simpa [sq_abs, Finset.card_univ, Finset.sum_const, nsmul_eq_mul, mul_comm] using h

end Scalar

section QuadForm

variable {R : Type*} [Field R]

/-- The quadratic form `z ↦ zᵀ A z` of a square matrix, as a plain function. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) : R := z ⬝ᵥ A.mulVec z

theorem quadForm_eq_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm A z = ∑ i, ∑ j, A i j * z i * z j := by
  simp only [quadForm, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem quadForm_zero {n : ℕ} (z : Fin n → R) : quadForm (0 : Matrix (Fin n) (Fin n) R) z = 0 := by
  simp [quadForm_eq_sum]

theorem quadForm_add {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (A + B) z = quadForm A z + quadForm B z := by
  simp only [quadForm_eq_sum]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.add_apply]
  ring

theorem quadForm_neg {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (-A) z = -quadForm A z := by
  simp only [quadForm_eq_sum]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.neg_apply]
  ring

theorem quadForm_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (A - B) z = quadForm A z - quadForm B z := by
  rw [sub_eq_add_neg, quadForm_add, quadForm_neg, sub_eq_add_neg]

theorem quadForm_smul {n : ℕ} (c : R) (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm (c • A) z = c * quadForm A z := by
  simp only [quadForm_eq_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

theorem quadForm_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (z : Fin n → R) :
    quadForm Aᵀ z = quadForm A z := by
  simp only [quadForm_eq_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.transpose_apply]
  ring

end QuadForm

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section Perturbation

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- Entrywise perturbation bound for a quadratic form, in `ℓ¹` form. -/
theorem abs_quadForm_le_of_entry_le {n : ℕ} {Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    |quadForm Δ z| ≤ ε * (∑ i, |z i|) ^ 2 := by
  rw [quadForm_eq_sum]
  have step1 : |∑ i, ∑ j, Δ i j * z i * z j| ≤ ∑ i, ∑ j, |Δ i j| * |z i| * |z j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [abs_mul, abs_mul])
  refine step1.trans ?_
  have step2 : ∑ i, ∑ j, |Δ i j| * |z i| * |z j| ≤ ∑ i, ∑ j, ε * |z i| * |z j| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)) (abs_nonneg _)
  refine step2.trans ?_
  rw [← Finset.sum_mul_sum (f := fun i => ε * |z i|) (g := fun j => |z j|), ← Finset.mul_sum]
  exact le_of_eq (by ring)

/-- Entrywise perturbation bound for a quadratic form: `|zᵀΔz| ≤ ε·n·∑zᵢ²`. -/
theorem abs_quadForm_le_of_entry_le_card {n : ℕ} {Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    |quadForm Δ z| ≤ ε * (n : R) * ∑ i, z i ^ 2 := by
  refine (abs_quadForm_le_of_entry_le hΔ z).trans ?_
  have hle : (∑ i, |z i|) ^ 2 ≤ (n : R) * ∑ i, z i ^ 2 := by
    simpa using l1_sq_le_card_mul_l2sq (R := R) z
  calc ε * (∑ i, |z i|) ^ 2 ≤ ε * ((n : R) * ∑ i, z i ^ 2) :=
        mul_le_mul_of_nonneg_left hle hε
    _ = ε * (n : R) * ∑ i, z i ^ 2 := by ring

/-- A margin survives an entrywise perturbation: the perturbed quadratic form still dominates
`(δ - ε·n)‖z‖²`. -/
theorem quadForm_add_perturb_ge {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) R} {δ ε : R}
    (hε : 0 ≤ ε) (hA : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm A z)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    (δ - ε * (n : R)) * ∑ i, z i ^ 2 ≤ quadForm (A + Δ) z := by
  have hb := abs_quadForm_le_of_entry_le_card hε hΔ z
  have h1 : -quadForm Δ z ≤ ε * (n : R) * ∑ i, z i ^ 2 := by linarith [(abs_le.1 hb).1]
  rw [quadForm_add]
  nlinarith [hA z]

/-- Pointwise form: entrywise perturbation costs at most `ε·n·∑zᵢ²` on the negative side. -/
theorem quadForm_add_entry_le_ge {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) R} {ε : R}
    (hε : 0 ≤ ε) (hA : ∀ z : Fin n → R, 0 ≤ quadForm A z)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → R) :
    -(ε * (n : R) * ∑ i, z i ^ 2) ≤ quadForm (A + Δ) z := by
  have h := quadForm_add_perturb_ge (A := A) (Δ := Δ) (δ := 0) hε (by simpa using hA) hΔ z
  simpa using h

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- `quadForm` of the identity is the squared norm. -/
theorem quadForm_one {n : ℕ} (z : Fin n → R) :
    quadForm (1 : Matrix (Fin n) (Fin n) R) z = ∑ i, z i ^ 2 := by
  simp only [quadForm, Matrix.one_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

end Perturbation

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section PSD

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R]

/-- A symmetric matrix whose quadratic form dominates `δ‖z‖²` with `δ ≥ 0` is positive
semidefinite. Works over `ℚ` (the exact-certificate notion) and over `ℝ`. -/
theorem posSemidef_of_margin {n : ℕ} {A : Matrix (Fin n) (Fin n) R} {δ : R}
    (hAsymm : A.IsSymm) (hA : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm A z)
    (hδ : 0 ≤ δ) : A.PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun z => ?_⟩
  · exact Matrix.isHermitian_iff_isSymm.2 hAsymm
  · have hz' : star z = z := by funext i; exact star_trivial (z i)
    rw [hz']
    change 0 ≤ quadForm A z
    have hz : (0 : R) ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [hA z, mul_nonneg hδ hz]

/-- **Entrywise robustness of a PSD margin.** If `zᵀAz ≥ δ‖z‖²` and every entry of the symmetric
perturbation `Δ` is at most `ε` in absolute value, and `ε·n ≤ δ`, then `A + Δ` is positive
semidefinite. -/
theorem posSemidef_add_of_margin {n : ℕ} {A Δ : Matrix (Fin n) (Fin n) R} {δ ε : R}
    (hAsymm : A.IsSymm) (hA : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm A z)
    (hΔsymm : Δ.IsSymm) (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε)
    (hlt : ε * (n : R) ≤ δ) : (A + Δ).PosSemidef :=
  posSemidef_of_margin (IsSymm.add hAsymm hΔsymm)
    (fun z => quadForm_add_perturb_ge (A := A) (Δ := Δ) (δ := δ) hε hA hΔ z)
    (by linarith)

/-- **Pipeline shape.** If the exact matrix `M` has a positive margin and the computed matrix `M'`
is entrywise within `ε` of it, then `M'` is positive semidefinite. This is the form in which the
perturbation bound is consumed by a certified-solver assembly (`M = diag y + A`). -/
theorem posSemidef_of_entry_near {n : ℕ} {M M' : Matrix (Fin n) (Fin n) R} {δ ε : R}
    (hMsymm : M.IsSymm) (hM : ∀ z : Fin n → R, δ * ∑ i, z i ^ 2 ≤ quadForm M z)
    (hM'symm : M'.IsSymm) (hε : 0 ≤ ε) (hΔ : ∀ i j, |M i j - M' i j| ≤ ε)
    (hlt : ε * (n : R) ≤ δ) : M'.PosSemidef := by
  have hsub : M + (M' - M) = M' := by abel
  rw [← hsub]
  exact posSemidef_add_of_margin (Δ := M' - M) hMsymm hM (IsSymm.sub hM'symm hMsymm) hε
    (fun i j => by simpa [abs_sub_comm] using hΔ i j) hlt

omit [LinearOrder R] [IsStrictOrderedRing R] [StarRing R] [TrivialStar R] in
/-- The diagonal matrix is symmetric. -/
theorem isSymm_diagonal {n : ℕ} (y : Fin n → R) : (Matrix.diagonal y).IsSymm := by
  simp [Matrix.IsSymm, Matrix.diagonal_transpose]

end PSD

section Lipschitz

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- A linear functional is Lipschitz in its argument w.r.t. the sup-norm budget. -/
theorem abs_sum_mul_sub_le {ι : Type*} [Fintype ι] (y b b' : ι → R) {m : R}
    (h : ∀ i, |b i - b' i| ≤ m) :
    |∑ i, y i * b i - ∑ i, y i * b' i| ≤ (∑ i, |y i|) * m := by
  have hre : ∑ i, y i * b i - ∑ i, y i * b' i = ∑ i, y i * (b i - b' i) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hre]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |y i * (b i - b' i)| ≤ ∑ i, |y i| * m := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (h i) (abs_nonneg _)
    _ = (∑ i, |y i|) * m := (Finset.sum_mul _ _ _).symm

/-- **The trace pairing is Lipschitz in the entrywise sup-norm**: an entrywise perturbation of
`Δ` by at most `ε` changes `tr(ΔX)` by at most `ε · ∑ᵢⱼ |Xᵢⱼ|`. -/
theorem abs_trace_mul_le {n : ℕ} {Δ X : Matrix (Fin n) (Fin n) R} {ε : R}
    (hΔ : ∀ i j, |Δ i j| ≤ ε) :
    |Matrix.trace (Δ * X)| ≤ ε * ∑ i, ∑ j, |X i j| := by
  have htr : Matrix.trace (Δ * X) = ∑ i, ∑ j, Δ i j * X j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [htr]
  have step1 : |∑ i, ∑ j, Δ i j * X j i| ≤ ∑ i, ∑ j, |Δ i j| * |X j i| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
      rw [abs_mul])
  have step2 : ∑ i, ∑ j, |Δ i j| * |X j i| ≤ ∑ i, ∑ j, ε * |X j i| := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_right (hΔ i j) (abs_nonneg _)
  refine (step1.trans step2).trans ?_
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum]

/-- Telescoping error budgets: `m` steps each losing at most `ε` lose at most `m·ε` in total. -/
theorem abs_sub_le_natCast_mul_of_steps {x : ℕ → R} {ε : R} {m : ℕ}
    (h : ∀ k, k < m → |x (k + 1) - x k| ≤ ε) : |x m - x 0| ≤ (m : R) * ε := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : |x m - x 0| ≤ (m : R) * ε := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    have h2 : |x (m + 1) - x m| ≤ ε := h m (Nat.lt_succ_self m)
    calc |x (m + 1) - x 0| ≤ (m : R) * ε + ε := by
          have := abs_sub_le_add_of_abs_sub_le (x := x (m + 1)) (y := x m) (z := x 0)
            (δ := (m : R) * ε) h2 h1
          linarith
      _ = ((m + 1 : ℕ) : R) * ε := by push_cast; ring

end Lipschitz

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section PSDBounds

/-- The `2 × 2` minor bound for a positive semidefinite matrix: `Xᵢⱼ² ≤ Xᵢᵢ·Xⱼⱼ`.

Proved from the Gram factorisation `X = ∑ₖ vₖ vₖᵀ`
(`Matrix.posSemidef_iff_eq_sum_vecMulVec`) and Cauchy–Schwarz over `k`. -/
theorem sq_entry_le_diag_mul {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (i j : Fin n) : X i j ^ 2 ≤ X i i * X j j := by
  obtain ⟨m, v, rfl⟩ := Matrix.posSemidef_iff_eq_sum_vecMulVec.mp hX
  have hentry : ∀ a b : Fin n, (∑ k, vecMulVec (v k) (star (v k))) a b = ∑ k, v k a * v k b := by
    intro a b
    simp [Matrix.sum_apply, Matrix.vecMulVec_apply, star_trivial]
  rw [hentry i j, hentry i i, hentry j j]
  have h := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset (Fin m)))
    (f := fun k => v k i) (g := fun k => v k j)
  simpa [sq] using h

/-- For a positive semidefinite matrix, `2|Xᵢⱼ| ≤ Xᵢᵢ + Xⱼⱼ` (AM–GM on the `2 × 2` minor). -/
theorem two_mul_abs_entry_le_diag_add {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) (i j : Fin n) : 2 * |X i j| ≤ X i i + X j j := by
  have hsq : X i j ^ 2 ≤ X i i * X j j := sq_entry_le_diag_mul hX i j
  have hi : 0 ≤ X i i := hX.diag_nonneg
  have hj : 0 ≤ X j j := hX.diag_nonneg
  have h2 : (2 * |X i j|) ^ 2 ≤ (X i i + X j j) ^ 2 := by
    have habs : |X i j| ^ 2 = X i j ^ 2 := sq_abs _
    nlinarith [sq_nonneg (X i i - X j j)]
  have h4 : abs (2 * abs (X i j)) ≤ abs (X i i + X j j) := sq_le_sq.mp h2
  rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * abs (X i j) by positivity),
    abs_of_nonneg (show (0 : ℝ) ≤ X i i + X j j by linarith)] at h4
  exact h4

/-- **Entrywise `ℓ¹` size of a PSD matrix**: `∑ᵢⱼ |Xᵢⱼ| ≤ n · tr X`. -/
theorem sum_abs_entry_le_card_mul_trace {n : ℕ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.PosSemidef) : ∑ i, ∑ j, |X i j| ≤ (n : ℝ) * Matrix.trace X := by
  have hb : ∀ i j : Fin n, |X i j| ≤ (X i i + X j j) / 2 := by
    intro i j
    have h := two_mul_abs_entry_le_diag_add hX i j
    linarith
  have hstep : ∀ i : Fin n, ∑ j : Fin n, ((X i i + X j j) / 2)
      = (n : ℝ) * X i i / 2 + Matrix.trace X / 2 := by
    intro i
    rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Fintype.card_fin, add_div]
    rw [show Matrix.trace X = ∑ x : Fin n, X x x from rfl]
  have hstep2 : ∑ i : Fin n, ((n : ℝ) * X i i / 2 + Matrix.trace X / 2)
      = (n : ℝ) * Matrix.trace X := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ i : Fin n, (n : ℝ) * X i i / 2 = (n : ℝ) * Matrix.trace X / 2 := by
      rw [← Finset.sum_div]
      congr 1
      exact (Finset.mul_sum (s := Finset.univ) (f := fun i => X i i) (a := (n : ℝ))).symm
    have h2 : ∑ _i : Fin n, (Matrix.trace X / 2) = (n : ℝ) * (Matrix.trace X / 2) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [h1, h2]
    ring
  have hsplit : ∑ i, ∑ j, ((X i i + X j j) / 2) = (n : ℝ) * Matrix.trace X := by
    simp only [hstep]
    exact hstep2
  refine (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j).trans ?_
  rw [hsplit]

/-- **Sharp trace-pairing budget**: for a PSD primal matrix `X`, an entrywise perturbation of the
constraint matrix by `ε ≥ 0` moves `tr(A X)` by at most `ε · n · tr X`. -/
theorem abs_trace_mul_le_of_posSemidef {n : ℕ} {Δ X : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hX : X.PosSemidef) (hε : 0 ≤ ε) (hΔ : ∀ i j, |Δ i j| ≤ ε) :
    |Matrix.trace (Δ * X)| ≤ ε * ((n : ℝ) * Matrix.trace X) := by
  have h1 := abs_trace_mul_le (Δ := Δ) (X := X) (ε := ε) hΔ
  have h2 := sum_abs_entry_le_card_mul_trace hX
  have h3 : ε * (∑ i, ∑ j, |X i j|) ≤ ε * ((n : ℝ) * Matrix.trace X) :=
    mul_le_mul_of_nonneg_left h2 hε
  linarith

/-- The gap budget in the PSD case: `εA · n · tr X + n · εy` controls the computed duality gap. -/
theorem gap_budget_psd {n : ℕ} {A A' X : Matrix (Fin n) (Fin n) ℝ} {y y' : Fin n → ℝ}
    {εA εy : ℝ} (hX : X.PosSemidef) (hεA : 0 ≤ εA)
    (hA : ∀ i j, |A i j - A' i j| ≤ εA) (hy : ∀ i, |y i - y' i| ≤ εy) :
    |(∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))|
      ≤ εA * ((n : ℝ) * Matrix.trace X) + (n : ℝ) * εy := by
  have h1 : |Matrix.trace ((A - A') * X)| ≤ εA * ((n : ℝ) * Matrix.trace X) :=
    abs_trace_mul_le_of_posSemidef hX hεA hA
  have key : (∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))
      = (∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    ring
  rw [key]
  have h2 : |∑ i, y i - ∑ i, y' i| ≤ (n : ℝ) * εy := by
    have h := abs_sum_mul_sub_le (fun _ : Fin n => (1 : ℝ)) y y' hy
    simpa using h
  calc |(∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X)|
      ≤ |∑ i, y i - ∑ i, y' i| + |Matrix.trace ((A - A') * X)| := abs_add_le _ _
    _ ≤ (n : ℝ) * εy + εA * ((n : ℝ) * Matrix.trace X) := add_le_add h2 h1
    _ = εA * ((n : ℝ) * Matrix.trace X) + (n : ℝ) * εy := by ring

end PSDBounds

end LeafB.ErrProp

namespace LeafB.ErrProp

open Matrix

section GapBudget

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]

/-- **Duality-gap budget.** The SDP gap of a certified pair is `∑ yᵢ + tr(A X)` (with `X` the
primal matrix). If the data `(A, y)` is only known to within an entrywise budget `εA` and a
linear budget `εy`, then the computed gap differs from the exact gap by at most
`εA · ∑ᵢⱼ |Xᵢⱼ| + n · εy`. -/
theorem gap_budget {n : ℕ} {A A' X : Matrix (Fin n) (Fin n) R} {y y' : Fin n → R}
    {εA εy : R} (hA : ∀ i j, |A i j - A' i j| ≤ εA) (hy : ∀ i, |y i - y' i| ≤ εy) :
    |(∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))|
      ≤ εA * (∑ i, ∑ j, |X i j|) + (n : R) * εy := by
  have key : (∑ i, y i + Matrix.trace (A * X)) - (∑ i, y' i + Matrix.trace (A' * X))
      = (∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X) := by
    rw [Matrix.sub_mul, Matrix.trace_sub]
    ring
  rw [key]
  have h2 : |∑ i, y i - ∑ i, y' i| ≤ (n : R) * εy := by
    have h := abs_sum_mul_sub_le (fun _ : Fin n => (1 : R)) y y' hy
    simpa using h
  have h1 : |Matrix.trace ((A - A') * X)| ≤ εA * ∑ i, ∑ j, |X i j| := abs_trace_mul_le hA
  calc |(∑ i, y i - ∑ i, y' i) + Matrix.trace ((A - A') * X)|
      ≤ |∑ i, y i - ∑ i, y' i| + |Matrix.trace ((A - A') * X)| := abs_add_le _ _
    _ ≤ (n : R) * εy + εA * (∑ i, ∑ j, |X i j|) := add_le_add h2 h1
    _ = εA * (∑ i, ∑ j, |X i j|) + (n : R) * εy := by ring

end GapBudget

section Instances

/-- The ℚ-instance: the exact-arithmetic pipeline gets the entrywise quadratic-form bound. -/
theorem abs_quadForm_le_rat (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℚ) (ε : ℚ) (hε : 0 ≤ ε)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → ℚ) :
    |quadForm Δ z| ≤ ε * (n : ℚ) * ∑ i, z i ^ 2 :=
  abs_quadForm_le_of_entry_le_card hε hΔ z

/-- The ℝ-instance, same statement. -/
theorem abs_quadForm_le_real (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hΔ : ∀ i j, |Δ i j| ≤ ε) (z : Fin n → ℝ) :
    |quadForm Δ z| ≤ ε * (n : ℝ) * ∑ i, z i ^ 2 :=
  abs_quadForm_le_of_entry_le_card hε hΔ z

/-- Concrete ℚ check, kernel-checked: a `2 × 2` matrix all of whose entries are `1/10` has
quadratic form bounded by `(1/10)·2·∑ zᵢ²`. -/
example : |quadForm (fun _ _ : Fin 2 => (1 / 10 : ℚ)) (fun _ => 1)|
    ≤ (1 / 10 : ℚ) * (2 : ℚ) * ∑ _ : Fin 2, (1 : ℚ) ^ 2 :=
  abs_quadForm_le_rat 2 _ (1 / 10) (by norm_num) (fun _ _ => by norm_num) _

/-- Concrete ℝ check: `5 • 1 + Δ` is positive semidefinite for every symmetric `Δ` with entries
at most `1/10` in absolute value (margin `5 - 2·(1/10) = 24/5 > 0`). -/
example (Δ : Matrix (Fin 2) (Fin 2) ℝ) (hΔsymm : Δ.IsSymm)
    (hΔ : ∀ i j, |Δ i j| ≤ 1 / 10) :
    ((5 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) + Δ).PosSemidef := by
  have hmargin : ∀ z : Fin 2 → ℝ,
      (5 : ℝ) * ∑ i, z i ^ 2 ≤ quadForm ((5 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) z := by
    intro z
    rw [quadForm_smul, quadForm_one]
  refine posSemidef_add_of_margin (δ := 5) (ε := 1 / 10) ?_ hmargin hΔsymm (by norm_num) hΔ ?_
  · simp [Matrix.IsSymm]
  · norm_num

/-- Concrete ℚ check: `4 • 1 + Δ` is positive semidefinite over `ℚ` for every rational symmetric
`Δ` with entries at most `1/1000` (margin `4 - 3/1000 > 0`). This is the exact-arithmetic form:
the conclusion is `q(z) ≥ 0` for all *rational* `z`. -/
example (Δ : Matrix (Fin 3) (Fin 3) ℚ) (hΔsymm : Δ.IsSymm)
    (hΔ : ∀ i j, |Δ i j| ≤ 1 / 1000) :
    ((4 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ) + Δ).PosSemidef := by
  have hmargin : ∀ z : Fin 3 → ℚ,
      (4 : ℚ) * ∑ i, z i ^ 2 ≤ quadForm ((4 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ)) z := by
    intro z
    rw [quadForm_smul, quadForm_one]
  refine posSemidef_add_of_margin (δ := 4) (ε := 1 / 1000) ?_ hmargin hΔsymm (by norm_num) hΔ ?_
  · simp [Matrix.IsSymm]
  · norm_num

end Instances

end LeafB.ErrProp

#print axioms LeafB.ErrProp.abs_quadForm_le_of_entry_le
#print axioms LeafB.ErrProp.abs_quadForm_le_of_entry_le_card
#print axioms LeafB.ErrProp.quadForm_add_perturb_ge
#print axioms LeafB.ErrProp.posSemidef_add_of_margin
#print axioms LeafB.ErrProp.abs_trace_mul_le
#print axioms LeafB.ErrProp.abs_sum_mul_sub_le
#print axioms LeafB.ErrProp.gap_budget
#print axioms LeafB.ErrProp.abs_sub_le_natCast_mul_of_steps
#print axioms LeafB.ErrProp.posSemidef_of_margin
#print axioms LeafB.ErrProp.posSemidef_of_entry_near
#print axioms LeafB.ErrProp.l1_sq_le_card_mul_l2sq
#print axioms LeafB.ErrProp.sq_entry_le_diag_mul
#print axioms LeafB.ErrProp.sum_abs_entry_le_card_mul_trace
#print axioms LeafB.ErrProp.abs_trace_mul_le_of_posSemidef
#print axioms LeafB.ErrProp.gap_budget_psd


/-! #### merged from `LeafB_SDPExistence.lean` -/

/-!
# Leaf B, brick `sdp-existence`: the max-cut SDP value exists and is attained

`Solutions/Check_LeafB.lean` reduces the numerical content of
`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program` to a hypothesis

```
hS : ∀ G : Input, ∃ S : ℝ, IsMaxcutSDPValue (wMatrix G) S
```

which it does not prove.  `ModernConvex.Relaxations.IsMaxcutSDPValue A v` is
`IsLUB (maxcutRelaxationObjective A '' {X | IsUnitDiagPSD X}) v`, a *least upper bound*
statement about an uncountable set of matrices, so its existence is not formal.

This file proves it for an **arbitrary** real matrix `A` (`exists_isMaxcutSDPValue`), by an
attainment argument, so no hypothesis on `A` (symmetry, entrywise nonnegativity, …) is needed:

* `IsUnitDiagPSD` is nonempty: the identity matrix is feasible (`isUnitDiagPSD_one`).
* Every feasible `X` satisfies `|X i j| ≤ 1` (`abs_apply_le_one`): the `2 × 2` principal minor
  `X.submatrix ![i,j] ![i,j]` is positive semidefinite with unit diagonal, and the quadratic
  forms at `(1,1)` and `(1,-1)` give `X i j ≥ -1` and `X i j ≤ 1`.
  Hence the feasible set sits in the compact box `[-1,1]^{n × n}` (`feasible_subset_box`).
* The feasible set is closed (`isClosed_feasible`): positive semidefiniteness is the
  intersection of the closed conditions `X = Xᵀ` and `0 ≤ xᵀXx` for all vectors `x`
  (`isClosed_setOf_posSemidef`), together with the closed diagonal conditions.
* So the feasible set is compact, the (continuous) objective attains its maximum, and the image
  is a nonempty compact subset of `ℝ` whose supremum is a member: it is the least upper bound.

Recorded consequences: uniqueness of the value, the value as an upper bound of every feasible
point, monotonicity in `A`, and nonnegativity of the value for entrywise nonnegative `A`
(needed because the leaf's lower value `L` is `ℚ≥0`-valued).  The same existence argument is
given for the three *other* optimisation values of `Def_ModernConvex_Relaxations_SignRelaxations`
(`IsMaxcutValue`, `IsSignQPValue`, `IsSignSDPValue`), so that every `IsLUB`-shaped value in that
file is known to exist.

Finally the value is packaged as a function `sdpValue A` (with `IsMaxcutSDPValue A (sdpValue A)`,
so the leaf no longer has to existentially quantify `S`), together with the stability estimate
`|sdpValue A - sdpValue B| ≤ ½ ∑ᵢ ∑ⱼ |Aᵢⱼ - Bᵢⱼ|`, and for the weighted-graph instance the
sandwich `W/2 ≤ sdpValue (weightMatrix G) ≤ W` with `W = ∑ₑ wₑ` the total edge weight.

## Index of the main statements

| statement | what it says |
|---|---|
| `exists_isMaxcutSDPValue` | `∃ v, IsMaxcutSDPValue A v` for **any** `A : Matrix (Fin n) (Fin n) ℝ` |
| `isMaxcutSDPValue_unique` | the value is unique |
| `exists_optimal`, `exists_maximizer` | the value is attained; the maximiser dominates every feasible point |
| `forall_exists_isMaxcutSDPValue` | the family form `∀ t, ∃ S, IsMaxcutSDPValue (A t) S` |
| `isMaxcutSDPValue_sdpValue`, `eq_sdpValue` | the value as the function `sdpValue` |
| `le_value_of_feasible`, `value_nonneg`, `value_mono` | lower bound, nonnegativity, monotonicity |
| `abs_sdpValue_sub_le`, `abs_sdpValue_sub_le'` | stability / Lipschitz bound in the weight matrix |
| `exists_isMaxcutValue`, `exists_isSignQPValue`, `exists_isSignSDPValue` | the other `IsLUB` values exist |
| `forall_input_exists` | **the leaf's `hS`, discharged** |
| `forall_input_exists_nonneg`, `forall_input_value_sandwich` | existence + `0 ≤ S` + `W/2 ≤ S ≤ W` |

The file compiles with `lake env lean` inside `/workspace/nucleus/work/home/prove2me_workspace`;
`#print axioms` on every statement above reports exactly
`[propext, Classical.choice, Quot.sound]`.

No `sorry`, no new axioms; the imports are `Mathlib` and the platform definitions
`Def_ModernConvex_Relaxations_SignRelaxations` and `Def_QuantumMaxCutEnergyEstimationModel`
(both inside the allowed surface).
-/

open scoped BigOperators
open Matrix

namespace QMCLeafBExistence

variable {n : ℕ}

/-! ## 1. The feasible set is nonempty -/

/-- The identity matrix is feasible for the max-cut SDP: positive semidefinite with unit
diagonal. -/
theorem isUnitDiagPSD_one : ModernConvex.Relaxations.IsUnitDiagPSD (1 : Matrix (Fin n) (Fin n) ℝ) :=
  ⟨Matrix.PosSemidef.one, fun i => by simp⟩

/-- The feasible set of the max-cut SDP is nonempty (it contains the identity). -/
theorem feasible_nonempty :
    ({X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X} : Set _).Nonempty :=
  ⟨1, isUnitDiagPSD_one⟩

/-! ## 2. Every feasible matrix has entries in `[-1, 1]` -/

theorem apply_le_one {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) (i j : Fin n) : X i j ≤ 1 := by
  classical
  have hM : (X.submatrix ![i, j] ![i, j]).PosSemidef := hX.submatrix _
  have hv := hM.dotProduct_mulVec_nonneg (fun k : Fin 2 => if k = 0 then (1 : ℝ) else -1)
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Fin.sum_univ_two,
    star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, hdiag] at hv
  norm_num at hv
  have hsym : X j i = X i j := by
    simpa using (Matrix.IsHermitian.apply hX.1 i j)
  rw [hsym] at hv
  linarith

theorem neg_one_le_apply {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (hdiag : ∀ i, X i i = 1) (i j : Fin n) : -1 ≤ X i j := by
  classical
  have hM : (X.submatrix ![i, j] ![i, j]).PosSemidef := hX.submatrix _
  have hv := hM.dotProduct_mulVec_nonneg (fun k : Fin 2 => (1 : ℝ))
  simp only [dotProduct, Matrix.mulVec, Matrix.submatrix_apply, Fin.sum_univ_two,
    star_trivial, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, hdiag] at hv
  norm_num at hv
  have hsym : X j i = X i j := by
    simpa using (Matrix.IsHermitian.apply hX.1 i j)
  rw [hsym] at hv
  linarith

theorem abs_apply_le_one {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) (i j : Fin n) : |X i j| ≤ 1 := by
  rw [abs_le]
  exact ⟨neg_one_le_apply hX.1 hX.2 i j, apply_le_one hX.1 hX.2 i j⟩

/-- The feasible set sits inside the box `[-1, 1]^{n × n}`. -/
theorem feasible_subset_box :
    ({X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X} : Set _) ⊆
      (Set.Icc (-1 : ℝ) 1).matrix := by
  intro X hX i j
  exact Set.mem_Icc.mpr (abs_le.mp (abs_apply_le_one hX i j))

/-! ## 3. The objective is bounded above on the feasible set -/

/-- A uniform upper bound for the max-cut relaxation objective over the feasible set. -/
noncomputable def objectiveBound (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 4) * ∑ i, ∑ j, (2 * |A i j|)

theorem objective_le_bound {A : Matrix (Fin n) (Fin n) ℝ} {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    ModernConvex.Relaxations.maxcutRelaxationObjective A X ≤ objectiveBound A := by
  have hterm : ∀ i j : Fin n, A i j * (1 - X i j) ≤ 2 * |A i j| := by
    intro i j
    have h1 : |1 - X i j| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [apply_le_one hX.1 hX.2 i j],
        by linarith [neg_one_le_apply hX.1 hX.2 i j]⟩
    calc A i j * (1 - X i j) ≤ |A i j * (1 - X i j)| := le_abs_self _
      _ = |A i j| * |1 - X i j| := abs_mul _ _
      _ ≤ |A i j| * 2 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = 2 * |A i j| := by ring
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective objectiveBound
  have hsum : ∑ i, ∑ j, A i j * (1 - X i j) ≤ ∑ i, ∑ j, 2 * |A i j| :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  linarith

theorem bddAbove_image (A : Matrix (Fin n) (Fin n) ℝ) :
    BddAbove (ModernConvex.Relaxations.maxcutRelaxationObjective A ''
      {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X}) :=
  ⟨objectiveBound A, by rintro _ ⟨X, hX, rfl⟩; exact objective_le_bound hX⟩

/-! ## 4. The SDP value exists -/

/-- **The max-cut SDP has a value.** For an arbitrary real matrix `A` there is `v` with
`IsMaxcutSDPValue A v`, i.e. `v` is the least upper bound of the relaxation objective over the
unit-diagonal positive semidefinite matrices.  This discharges the hypothesis `hS` of
`QMCLeafB.leafB_sandwich`. -/
theorem exists_isMaxcutSDPValue (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue A v :=
  ⟨_, isLUB_csSup (feasible_nonempty.image _) (bddAbove_image A)⟩

/-- The SDP value is unique. -/
theorem isMaxcutSDPValue_unique {A : Matrix (Fin n) (Fin n) ℝ} {v w : ℝ}
    (hv : ModernConvex.Relaxations.IsMaxcutSDPValue A v)
    (hw : ModernConvex.Relaxations.IsMaxcutSDPValue A w) : v = w :=
  hv.unique hw

/-- The same existence statement for a family of matrices indexed by a type, in the shape in
which `Check_LeafB.lean` uses it. -/
theorem forall_exists_isMaxcutSDPValue {ι : Type*} (A : ι → Matrix (Fin n) (Fin n) ℝ) :
    ∀ t : ι, ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (A t) S :=
  fun t => exists_isMaxcutSDPValue (A t)

/-! ## 5. Closedness, compactness, and attainment -/

theorem isClosed_setOf_posSemidef :
    IsClosed {M : Matrix (Fin n) (Fin n) ℝ | M.PosSemidef} := by
  have hset : {M : Matrix (Fin n) (Fin n) ℝ | M.PosSemidef}
      = {M | M.IsHermitian} ∩ ⋂ (x : Fin n → ℝ), {M | 0 ≤ x ⬝ᵥ (M *ᵥ x)} := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter,
      Matrix.posSemidef_iff_dotProduct_mulVec, star_trivial]
  rw [hset]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · have hherm : {M : Matrix (Fin n) (Fin n) ℝ | M.IsHermitian} = {M | Mᵀ = M} := by
      ext M
      simp [Matrix.IsHermitian]
    rw [hherm]
    exact isClosed_eq continuous_id.matrix_transpose continuous_id
  · exact isClosed_le continuous_const
      (continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const))

theorem isClosed_feasible :
    IsClosed {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X} := by
  have hset : {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X}
      = {M | M.PosSemidef} ∩ ⋂ i, {X | X i i = 1} := by
    ext X
    simp [ModernConvex.Relaxations.IsUnitDiagPSD]
  rw [hset]
  refine IsClosed.inter isClosed_setOf_posSemidef (isClosed_iInter fun i => ?_)
  have hcont : Continuous fun X : Matrix (Fin n) (Fin n) ℝ => X i i := continuous_apply_apply i i
  exact isClosed_eq hcont continuous_const

theorem isCompact_feasible :
    IsCompact {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X} :=
  isCompact_Icc.matrix.of_isClosed_subset isClosed_feasible feasible_subset_box

theorem continuous_maxcutRelaxationObjective (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun X : Matrix (Fin n) (Fin n) ℝ =>
      ModernConvex.Relaxations.maxcutRelaxationObjective A X := by
  have h : Continuous fun X : Matrix (Fin n) (Fin n) ℝ => ∑ i, ∑ j, A i j * (1 - X i j) := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact continuous_const.mul (continuous_const.sub (continuous_apply_apply i j))
  exact continuous_const.mul h

theorem isCompact_image (A : Matrix (Fin n) (Fin n) ℝ) :
    IsCompact (ModernConvex.Relaxations.maxcutRelaxationObjective A ''
      {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X}) :=
  isCompact_feasible.image (continuous_maxcutRelaxationObjective A)

/-- **The SDP value is attained.** There is a feasible matrix on which the relaxation objective
equals the optimal value. -/
theorem exists_optimal (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD X ∧
      ModernConvex.Relaxations.IsMaxcutSDPValue A
        (ModernConvex.Relaxations.maxcutRelaxationObjective A X) := by
  set K := ModernConvex.Relaxations.maxcutRelaxationObjective A ''
    {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X} with hKdef
  have hK : IsCompact K := isCompact_image A
  have hne : K.Nonempty := feasible_nonempty.image _
  have hmem : sSup K ∈ K := hK.isClosed.csSup_mem hne (bddAbove_image A)
  obtain ⟨X, hX, hXeq⟩ := hmem
  exact ⟨X, hX, hXeq ▸ isLUB_csSup hne (bddAbove_image A)⟩

/-- **Maximality of the optimal point.** -/
theorem exists_maximizer (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ X : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD X ∧
      ∀ Z : Matrix (Fin n) (Fin n) ℝ, ModernConvex.Relaxations.IsUnitDiagPSD Z →
        ModernConvex.Relaxations.maxcutRelaxationObjective A Z
          ≤ ModernConvex.Relaxations.maxcutRelaxationObjective A X := by
  obtain ⟨X, hX, hlub⟩ := exists_optimal A
  exact ⟨X, hX, fun Z hZ => hlub.1 ⟨Z, hZ, rfl⟩⟩

/-! ## 6. Elementary consequences -/

/-- Every feasible point gives a lower bound. -/
theorem le_value_of_feasible {A : Matrix (Fin n) (Fin n) ℝ} {v : ℝ}
    (hv : ModernConvex.Relaxations.IsMaxcutSDPValue A v)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    ModernConvex.Relaxations.maxcutRelaxationObjective A X ≤ v :=
  hv.1 ⟨X, hX, rfl⟩

/-- For entrywise nonnegative `A` the SDP value is nonnegative (the identity is feasible). -/
theorem value_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) {v : ℝ}
    (hv : ModernConvex.Relaxations.IsMaxcutSDPValue A v) : 0 ≤ v := by
  have hobj : (0 : ℝ) ≤ ModernConvex.Relaxations.maxcutRelaxationObjective A 1 := by
    unfold ModernConvex.Relaxations.maxcutRelaxationObjective
    refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => ?_)
    rcases eq_or_ne i j with h | h
    · subst h
      simp
    · have hone : (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0 := by
        simp [h]
      rw [hone]
      nlinarith [hA i j]
  have := le_value_of_feasible hv isUnitDiagPSD_one
  linarith

/-- The SDP value is monotone in the weight matrix. -/
theorem value_mono {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : ∀ i j, A i j ≤ B i j)
    {v w : ℝ} (hv : ModernConvex.Relaxations.IsMaxcutSDPValue A v)
    (hw : ModernConvex.Relaxations.IsMaxcutSDPValue B w) : v ≤ w := by
  refine hv.2 ?_
  rintro _ ⟨X, hX, rfl⟩
  refine le_trans ?_ (hw.1 ⟨X, hX, rfl⟩)
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  refine mul_le_mul_of_nonneg_right (hAB i j) ?_
  linarith [apply_le_one hX.1 hX.2 i j]

/-! ## 7. The three finite / compact optimisation values of the sign-relaxation file

`IsMaxcutValue` and `IsSignQPValue` range over finite sets (sign vectors), and `IsSignSDPValue`
ranges over the same compact feasible set as the max-cut SDP.  Each of them therefore has a
value as well; the proofs are short but they are needed wherever those values are used. -/

/-- A finite nonempty set of reals has a least upper bound. -/
theorem exists_isLUB_of_finite {s : Set ℝ} (hne : s.Nonempty) (hf : s.Finite) :
    ∃ v : ℝ, IsLUB s v :=
  ⟨sSup s, isLUB_csSup hne hf.bddAbove⟩

theorem signVectors_finite : (ModernConvex.Relaxations.signVectors n).Finite := by
  have h : ModernConvex.Relaxations.signVectors n ⊆
      {x : Fin n → ℝ | ∀ i, x i ∈ ({1, -1} : Set ℝ)} := by
    intro x hx i
    simpa using hx i
  exact (Set.Finite.pi' (fun _ => (Set.finite_singleton (-1 : ℝ)).insert 1)).subset h

theorem signVectors_nonempty : (ModernConvex.Relaxations.signVectors n).Nonempty :=
  ⟨fun _ => 1, fun _ => Or.inl rfl⟩

theorem signSquares_finite : ({x : Fin n → ℝ | ∀ i, x i ^ 2 = 1} : Set _).Finite := by
  have h : {x : Fin n → ℝ | ∀ i, x i ^ 2 = 1} ⊆
      {x : Fin n → ℝ | ∀ i, x i ∈ ({1, -1} : Set ℝ)} := by
    intro x hx i
    have h1 : x i ^ 2 = 1 := hx i
    have h2 : x i = 1 ∨ x i = -1 := sq_eq_one_iff.mp h1
    simpa using h2
  exact (Set.Finite.pi' (fun _ => (Set.finite_singleton (-1 : ℝ)).insert 1)).subset h

theorem signSquares_nonempty : ({x : Fin n → ℝ | ∀ i, x i ^ 2 = 1} : Set _).Nonempty :=
  ⟨fun _ => 1, fun _ => by norm_num⟩

/-- The MAX-CUT optimum `OPT` of (4.3.14) exists. -/
theorem exists_isMaxcutValue (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : ℝ, ModernConvex.Relaxations.IsMaxcutValue A v :=
  exists_isLUB_of_finite (signSquares_nonempty.image _) (signSquares_finite.image _)

/-- The sign quadratic-programming value `OPT` of (4.3.17) exists. -/
theorem exists_isSignQPValue (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : ℝ, ModernConvex.Relaxations.IsSignQPValue A v :=
  exists_isLUB_of_finite (signVectors_nonempty.image _) (signVectors_finite.image _)

/-- The trace objective of the SDP is bounded above on the feasible set. -/
theorem trace_mul_le_bound {A X : Matrix (Fin n) (Fin n) ℝ}
    (hX : ModernConvex.Relaxations.IsUnitDiagPSD X) :
    (A * X).trace ≤ ∑ i, ∑ j, |A i j| := by
  have htrace : (A * X).trace = ∑ i, ∑ j, A i j * X j i := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [htrace]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  calc A i j * X j i ≤ |A i j * X j i| := le_abs_self _
    _ = |A i j| * |X j i| := abs_mul _ _
    _ ≤ |A i j| * 1 := mul_le_mul_of_nonneg_left (abs_apply_le_one hX j i) (abs_nonneg _)
    _ = |A i j| := mul_one _

theorem continuous_trace_mul (A : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun X : Matrix (Fin n) (Fin n) ℝ => (A * X).trace := by
  fun_prop

theorem isCompact_trace_image (A : Matrix (Fin n) (Fin n) ℝ) :
    IsCompact ((fun X : Matrix (Fin n) (Fin n) ℝ => (A * X).trace) ''
      {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X}) :=
  isCompact_feasible.image (continuous_trace_mul A)

/-- The SDP value `SDP` of (4.3.18) exists. -/
theorem exists_isSignSDPValue (A : Matrix (Fin n) (Fin n) ℝ) :
    ∃ v : ℝ, ModernConvex.Relaxations.IsSignSDPValue A v := by
  have hne : ((fun X : Matrix (Fin n) (Fin n) ℝ => (A * X).trace) ''
      {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X}).Nonempty :=
    feasible_nonempty.image _
  have hb : BddAbove ((fun X : Matrix (Fin n) (Fin n) ℝ => (A * X).trace) ''
      {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X}) :=
    ⟨∑ i, ∑ j, |A i j|, by rintro _ ⟨X, hX, rfl⟩; exact trace_mul_le_bound hX⟩
  exact ⟨_, isLUB_csSup hne hb⟩

/-! ## 8. The leaf-level instance

`weightMatrix` is written out exactly as in `Check_LeafB.lean` (there called `wMatrix`), so that
the two are interchangeable by `simp`/`rfl` during assembly.  Because
`exists_isMaxcutSDPValue` holds for an *arbitrary* matrix, the leaf's `hS` hypothesis follows
immediately. -/

/-- The weight matrix appearing in the leaf statement. -/
noncomputable def weightMatrix (G : QuantumMaxCutEnergy.Input) : Matrix (Fin G.n) (Fin G.n) ℝ :=
  Matrix.of fun i j : Fin G.n =>
    if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
    else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0

theorem weightMatrix_apply (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    weightMatrix G i j = (if h : i < j then (G.weights ⟨(i, j), h⟩ : ℝ)
      else if h : j < i then (G.weights ⟨(j, i), h⟩ : ℝ) else 0) := rfl

/-- The leaf's hypothesis `hS : ∀ G, ∃ S, IsMaxcutSDPValue (wMatrix G) S`, discharged. -/
theorem forall_input_exists :
    ∀ G : QuantumMaxCutEnergy.Input,
      ∃ S : ℝ, ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S :=
  fun G => exists_isMaxcutSDPValue (weightMatrix G)

theorem weightMatrix_nonneg (G : QuantumMaxCutEnergy.Input) (i j : Fin G.n) :
    0 ≤ weightMatrix G i j := by
  rw [weightMatrix_apply]
  split_ifs <;> positivity

/-- For every input graph the SDP value exists and is nonnegative. -/
theorem forall_input_exists_nonneg :
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S ∧ 0 ≤ S := by
  intro G
  obtain ⟨S, hS⟩ := exists_isMaxcutSDPValue (weightMatrix G)
  exact ⟨S, hS, value_nonneg (weightMatrix_nonneg G) hS⟩

/-! ### 8b. The total weight of the double sum

`∑ᵢ ∑ⱼ Aᵢⱼ = 2W` for the weight matrix `A = weightMatrix G` of a weighted graph with `W` the
total edge weight.  (This is the same identity as `QMCLeafB.V_wMatrix` in `Check_LeafB.lean`,
reproved here so that this file needs no import outside the platform surface.) -/

theorem sum_weightMatrix (G : QuantumMaxCutEnergy.Input) :
    (∑ i : Fin G.n, ∑ j : Fin G.n, weightMatrix G i j) =
      2 * ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
  classical
  set U : Fin G.n × Fin G.n → ℝ :=
    fun p => if h : p.1 < p.2 then (G.weights ⟨(p.1, p.2), h⟩ : ℝ) else 0 with hU
  set L : Fin G.n × Fin G.n → ℝ :=
    fun p => if h : p.2 < p.1 then (G.weights ⟨(p.2, p.1), h⟩ : ℝ) else 0 with hL
  have hpt : ∀ i j : Fin G.n, weightMatrix G i j = U (i, j) + L (i, j) := by
    intro i j
    rw [weightMatrix_apply, hU, hL]
    rcases lt_trichotomy i j with h | h | h
    · simp [dif_pos h, dif_neg (not_lt.mpr h.le)]
    · subst h; simp
    · simp [dif_pos h, dif_neg (not_lt.mpr h.le)]
  have hprod : (∑ p : Fin G.n × Fin G.n, weightMatrix G p.1 p.2) =
      ∑ i, ∑ j, weightMatrix G i j :=
    Fintype.sum_prod_type (f := fun p : Fin G.n × Fin G.n => weightMatrix G p.1 p.2)
  have hupper : ∑ p : Fin G.n × Fin G.n, U p =
      ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
    simp only [hU]
    exact (Fintype.sum_of_injective (fun e : QuantumMaxCutEnergy.Edge G.n =>
        (e.val : Fin G.n × Fin G.n))
      (fun a b hab => Subtype.ext hab) (fun e => (G.weights e : ℝ))
      (fun p => if h : p.1 < p.2 then (G.weights ⟨(p.1, p.2), h⟩ : ℝ) else 0)
      (fun p hp => by
        have hlt : ¬ p.1 < p.2 := fun h => hp ⟨⟨p, h⟩, rfl⟩
        rw [dif_neg hlt])
      (fun e => by rw [dif_pos e.2])).symm
  have hswap : ∑ p : Fin G.n × Fin G.n, L p = ∑ p : Fin G.n × Fin G.n, U p := by
    have hcongr : ∀ p : Fin G.n × Fin G.n, L p = U (p.2, p.1) := by
      intro p
      rw [hL, hU]
    rw [Finset.sum_congr rfl (fun p _ => hcongr p)]
    exact Equiv.sum_comp (Equiv.prodComm (Fin G.n) (Fin G.n)) U
  rw [← hprod]
  have h2 : ∑ p : Fin G.n × Fin G.n, weightMatrix G p.1 p.2 =
      (∑ p, U p) + (∑ p, L p) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => hpt p.1 p.2
  rw [h2, hswap, hupper]
  ring

theorem objectiveBound_weightMatrix (G : QuantumMaxCutEnergy.Input) :
    objectiveBound (weightMatrix G) =
      ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
  unfold objectiveBound
  have habs : ∀ i j : Fin G.n, |weightMatrix G i j| = weightMatrix G i j :=
    fun i j => abs_of_nonneg (weightMatrix_nonneg G i j)
  simp only [habs]
  have h2 : ∀ i : Fin G.n, ∑ j, 2 * weightMatrix G i j = 2 * ∑ j, weightMatrix G i j :=
    fun i => (Finset.mul_sum (s := Finset.univ) (f := fun j => weightMatrix G i j) (a := 2)).symm
  rw [Finset.sum_congr rfl (fun i _ => h2 i), ← Finset.mul_sum, sum_weightMatrix]
  ring

/-- The SDP value of a weighted graph is at most the total edge weight. -/
theorem value_le_totalWeight (G : QuantumMaxCutEnergy.Input) {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S) :
    S ≤ ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
  refine hS.2 ?_
  rintro _ ⟨X, hX, rfl⟩
  have h := objective_le_bound (A := weightMatrix G) hX
  rw [objectiveBound_weightMatrix] at h
  exact h

/-- The identity matrix evaluates to half the total edge weight. -/
theorem objective_one_weightMatrix (G : QuantumMaxCutEnergy.Input) :
    ModernConvex.Relaxations.maxcutRelaxationObjective (weightMatrix G)
      (1 : Matrix (Fin G.n) (Fin G.n) ℝ) =
      (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ)) / 2 := by
  have h1 : ∀ i : Fin G.n,
      ∑ j, weightMatrix G i j * (1 - (1 : Matrix (Fin G.n) (Fin G.n) ℝ) i j) =
        ∑ j, weightMatrix G i j := by
    intro i
    refine Finset.sum_congr rfl fun j _ => ?_
    rcases eq_or_ne i j with h | h
    · subst h; simp [weightMatrix_apply]
    · have hone : (1 : Matrix (Fin G.n) (Fin G.n) ℝ) i j = 0 := by simp [h]
      rw [hone, sub_zero, mul_one]
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  rw [Finset.sum_congr rfl (fun i _ => h1 i), sum_weightMatrix]
  ring

/-- The SDP value of a weighted graph is at least half the total edge weight. -/
theorem half_totalWeight_le_value (G : QuantumMaxCutEnergy.Input) {S : ℝ}
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S) :
    (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ)) / 2 ≤ S := by
  have h := le_value_of_feasible hS (isUnitDiagPSD_one (n := G.n))
  rw [objective_one_weightMatrix] at h
  exact h

/-- **The value of the max-cut SDP of an input graph is sandwiched between half the total edge
weight and the total edge weight.**  Existence, nonnegativity and both bounds in one statement. -/
theorem forall_input_value_sandwich :
    ∀ G : QuantumMaxCutEnergy.Input, ∃ S : ℝ,
      ModernConvex.Relaxations.IsMaxcutSDPValue (weightMatrix G) S ∧
        0 ≤ S ∧
        (∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ)) / 2 ≤ S ∧
        S ≤ ∑ e : QuantumMaxCutEnergy.Edge G.n, (G.weights e : ℝ) := by
  intro G
  obtain ⟨S, hS⟩ := exists_isMaxcutSDPValue (weightMatrix G)
  exact ⟨S, hS, value_nonneg (weightMatrix_nonneg G) hS,
    half_totalWeight_le_value G hS, value_le_totalWeight G hS⟩

/-! ## 9. The value as a function of the weight matrix, and its stability -/

/-- The max-cut SDP value, as a function of the weight matrix. -/
noncomputable def sdpValue (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sSup (ModernConvex.Relaxations.maxcutRelaxationObjective A ''
    {X : Matrix (Fin n) (Fin n) ℝ | ModernConvex.Relaxations.IsUnitDiagPSD X})

theorem isMaxcutSDPValue_sdpValue (A : Matrix (Fin n) (Fin n) ℝ) :
    ModernConvex.Relaxations.IsMaxcutSDPValue A (sdpValue A) :=
  isLUB_csSup (feasible_nonempty.image _) (bddAbove_image A)

/-- Any matrix satisfying `IsMaxcutSDPValue` is `sdpValue`. -/
theorem eq_sdpValue {A : Matrix (Fin n) (Fin n) ℝ} {v : ℝ}
    (hv : ModernConvex.Relaxations.IsMaxcutSDPValue A v) : v = sdpValue A :=
  hv.unique (isMaxcutSDPValue_sdpValue A)

theorem sdpValue_nonneg {A : Matrix (Fin n) (Fin n) ℝ} (hA : ∀ i j, 0 ≤ A i j) :
    0 ≤ sdpValue A :=
  value_nonneg hA (isMaxcutSDPValue_sdpValue A)

theorem sdpValue_mono {A B : Matrix (Fin n) (Fin n) ℝ} (hAB : ∀ i j, A i j ≤ B i j) :
    sdpValue A ≤ sdpValue B :=
  value_mono hAB (isMaxcutSDPValue_sdpValue A) (isMaxcutSDPValue_sdpValue B)

/-- The relaxation objective is additive in the weight matrix. -/
theorem objective_add (A C : Matrix (Fin n) (Fin n) ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    ModernConvex.Relaxations.maxcutRelaxationObjective (A + C) X =
      ModernConvex.Relaxations.maxcutRelaxationObjective A X +
        ModernConvex.Relaxations.maxcutRelaxationObjective C X := by
  unfold ModernConvex.Relaxations.maxcutRelaxationObjective
  simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
  ring

/-- **Subadditivity of the value in the weight matrix.** -/
theorem sdpValue_add_le (A C : Matrix (Fin n) (Fin n) ℝ) :
    sdpValue (A + C) ≤ sdpValue A + objectiveBound C := by
  refine (isMaxcutSDPValue_sdpValue (A + C)).2 ?_
  rintro _ ⟨X, hX, rfl⟩
  rw [objective_add]
  have h1 : ModernConvex.Relaxations.maxcutRelaxationObjective A X ≤ sdpValue A :=
    le_value_of_feasible (isMaxcutSDPValue_sdpValue A) hX
  have h2 : ModernConvex.Relaxations.maxcutRelaxationObjective C X ≤ objectiveBound C :=
    objective_le_bound hX
  linarith

/-- **Stability of the value under a change of weights:** perturbing the weight matrix by `E`
moves the SDP value by at most `objectiveBound E`. -/
theorem abs_sdpValue_sub_le (A B : Matrix (Fin n) (Fin n) ℝ) :
    |sdpValue A - sdpValue B| ≤ objectiveBound (A - B) := by
  have h1 : sdpValue A ≤ sdpValue B + objectiveBound (A - B) := by
    have h := sdpValue_add_le B (A - B)
    rwa [add_sub_cancel] at h
  have h2 : sdpValue B ≤ sdpValue A + objectiveBound (B - A) := by
    have h := sdpValue_add_le A (B - A)
    rwa [add_sub_cancel] at h
  have h3 : objectiveBound (B - A) = objectiveBound (A - B) := by
    unfold objectiveBound
    congr 2
    ext i
    congr 1
    ext j
    rw [Matrix.sub_apply, Matrix.sub_apply, abs_sub_comm]
  rw [abs_le]
  constructor <;> linarith

/-- The same stability statement in the leaf's terms: `sdpValue` is `½ ∑ᵢ ∑ⱼ |Aᵢⱼ - Bᵢⱼ|`
Lipschitz. -/
theorem abs_sdpValue_sub_le' (A B : Matrix (Fin n) (Fin n) ℝ) :
    |sdpValue A - sdpValue B| ≤ (1 / 2) * ∑ i, ∑ j, |A i j - B i j| := by
  refine (abs_sdpValue_sub_le A B).trans_eq ?_
  unfold objectiveBound
  simp only [Matrix.sub_apply]
  have h : ∀ i : Fin n, ∑ j, (2 * |A i j - B i j|) = 2 * ∑ j, |A i j - B i j| :=
    fun i => by rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl (fun i _ => h i), ← Finset.mul_sum]
  ring

end QMCLeafBExistence


/-! #### merged from `Check_CastBridge.lean` -/

/-!
# `brick-cast-bridge`: the ℚ → ℝ transfer layer for the leaf-B certified pair

`Check_LeafB.lean` reduces the numerical content of
`QuantumMaxCutEnergy.agm_classical_sdp_lower_value_program` to a family of certified
primal/dual pairs, and phrases every hypothesis over `ℝ`:

* the dual condition is `(diagonal y + A).PosSemidef` (`Matrix.PosSemidef` over `ℝ`),
* the primal condition is `X.PosSemidef` with `X i i = 1`,
* the gap is `∑ i, y i + (A * X).trace ≤ V A / 5000`.

Every brick that *certifies* these conditions works over `ℚ` (exact arithmetic:
Gram factorisations, `L D Lᵀ` eliminations, rational ellipsoid iterates).  This file is
the missing transfer: it takes the rational data and reads it in the reals, so that
* a rational Gram/PSD *test* validates the real `PosSemidef` hypothesis, and
* a real violation always has a *rational* witness (so an exact-arithmetic separation
  oracle never needs to leave `ℚ`), and
* determinant / inverse bookkeeping survives the cast (the ellipsoid step needs `A⁻¹`).

Nothing here uses certificate data structures, sums of squares, or spectral theory: the
whole point is that the real statement follows from rational *tests* by density of `ℚⁿ`
in `ℝⁿ`.

Main results:
* `castM_qf` : `(xᵀ M x : ℚ)` cast to `ℝ` is `xᵀ (castM M) x`;
* `posSemidef_of_rat_tests` : symmetry + `∀ x : Fin n → ℚ, 0 ≤ xᵀ M x` ⟹
  `(castM M).PosSemidef` over `ℝ`;
* `exists_rat_qf_neg` : a real vector with `xᵀ (castM M) x < 0` yields a rational one;
* `posDef_of_rat_tests` : the same plus `M.det ≠ 0` gives `(castM M).PosDef`;
* `realDualFeasible` : the exact hypothesis shape consumed by `Check_LeafB.weak_duality`.
-/

open scoped BigOperators
open Matrix

namespace QMCLeafB.CastBridge

variable {n : ℕ}

/-! ## 1. The cast functor -/

/-- The entrywise view of a rational matrix as a real matrix. -/
noncomputable def castM (M : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  M.map (Rat.castHom ℝ)

theorem castM_apply (M : Matrix (Fin n) (Fin n) ℚ) (i j : Fin n) :
    castM M i j = (M i j : ℝ) := rfl

theorem castM_eq_mapMatrix (M : Matrix (Fin n) (Fin n) ℚ) :
    castM M = (Rat.castHom ℝ).mapMatrix M := by
  rw [RingHom.mapMatrix_apply]
  rfl

theorem castM_add (M N : Matrix (Fin n) (Fin n) ℚ) :
    castM (M + N) = castM M + castM N := by
  simp only [castM_eq_mapMatrix, map_add]

theorem castM_sub (M N : Matrix (Fin n) (Fin n) ℚ) :
    castM (M - N) = castM M - castM N := by
  simp only [castM_eq_mapMatrix, map_sub]

theorem castM_neg (M : Matrix (Fin n) (Fin n) ℚ) : castM (-M) = -castM M := by
  simp only [castM_eq_mapMatrix, map_neg]

theorem castM_mul (M N : Matrix (Fin n) (Fin n) ℚ) :
    castM (M * N) = castM M * castM N := by
  simp only [castM_eq_mapMatrix, map_mul]

theorem castM_one : castM (1 : Matrix (Fin n) (Fin n) ℚ) = 1 := by
  simp only [castM_eq_mapMatrix, map_one]

theorem castM_smul (c : ℚ) (M : Matrix (Fin n) (Fin n) ℚ) :
    castM (c • M) = (c : ℝ) • castM M := by
  ext i j
  simp [castM]

theorem castM_transpose (M : Matrix (Fin n) (Fin n) ℚ) :
    castM Mᵀ = (castM M)ᵀ := by
  simp only [castM]
  exact Matrix.transpose_map

theorem castM_diagonal (y : Fin n → ℚ) :
    castM (diagonal y) = diagonal (fun i => (y i : ℝ)) := by
  simp only [castM]
  exact Matrix.diagonal_map (by simp)

theorem castM_trace (M : Matrix (Fin n) (Fin n) ℚ) :
    (castM M).trace = (M.trace : ℝ) := by
  simp [castM, Matrix.trace]

theorem castM_det (M : Matrix (Fin n) (Fin n) ℚ) :
    (castM M).det = (M.det : ℝ) := by
  rw [castM_eq_mapMatrix]
  exact (RingHom.map_det (Rat.castHom ℝ) M).symm

theorem castM_adjugate (M : Matrix (Fin n) (Fin n) ℚ) :
    (castM M).adjugate = castM M.adjugate := by
  have h := RingHom.map_adjugate (Rat.castHom ℝ) M
  rw [castM_eq_mapMatrix, castM_eq_mapMatrix]
  simpa only [RingHom.mapMatrix_apply] using h.symm

theorem castM_inv (M : Matrix (Fin n) (Fin n) ℚ) :
    castM M⁻¹ = (castM M)⁻¹ := by
  rw [Matrix.inv_def, Matrix.inv_def, castM_smul, castM_adjugate, castM_det]
  congr 1
  rw [Ring.inverse_eq_inv, Ring.inverse_eq_inv, Rat.cast_inv]

theorem castM_det_ne_zero_iff (M : Matrix (Fin n) (Fin n) ℚ) :
    (castM M).det ≠ 0 ↔ M.det ≠ 0 := by
  rw [castM_det]
  constructor
  · intro h h0
    exact h (by simp [h0])
  · intro h h0
    exact h (by exact_mod_cast h0)

/-! ## 2. The quadratic form and its cast -/

/-- The rational quadratic form `xᵀ M x`. -/
def qf (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) : ℚ := x ⬝ᵥ (M *ᵥ x)

/-- The real quadratic form `xᵀ M x`. -/
def qfR (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ := x ⬝ᵥ (M *ᵥ x)

theorem qf_eq_sum (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    qf M x = ∑ i, ∑ j, x i * (M i j * x j) := by
  simp only [qf, dotProduct, Matrix.mulVec, Finset.mul_sum]

theorem qfR_eq_sum (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qfR M x = ∑ i, ∑ j, x i * (M i j * x j) := by
  simp only [qfR, dotProduct, Matrix.mulVec, Finset.mul_sum]

/-- Evaluating the rational quadratic form and then casting is evaluating the cast matrix. -/
theorem castM_qf (M : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ) :
    ((qf M x : ℚ) : ℝ) = qfR (castM M) (fun i => (x i : ℝ)) := by
  rw [qf_eq_sum, qfR_eq_sum]
  push_cast
  rfl

theorem continuous_qfR (M : Matrix (Fin n) (Fin n) ℝ) :
    Continuous fun x : Fin n → ℝ => qfR M x := by
  have h : (fun x : Fin n → ℝ => qfR M x) = fun x => ∑ i, ∑ j, x i * (M i j * x j) := by
    funext x
    exact qfR_eq_sum M x
  rw [h]
  continuity

/-! ## 3. Completeness of rational tests for real positive semidefiniteness -/

theorem symm_of_transpose_eq {M : Matrix (Fin n) (Fin n) ℚ} (h : Mᵀ = M) :
    ∀ i j, M j i = M i j := by
  intro i j
  have h' := congrFun (congrFun h i) j
  simpa [Matrix.transpose_apply] using h'

/-- The rational points of `ℝⁿ`, viewed as a subset, are dense. -/
theorem denseRange_rat_pi :
    DenseRange (fun x : Fin n → ℚ => fun i => (x i : ℝ)) :=
  DenseRange.piMap (ι := Fin n) (X := fun _ => ℚ) (Y := fun _ => ℝ)
    (f := fun _ => (Rat.cast : ℚ → ℝ)) (fun _ => Rat.denseRange_cast (𝕜 := ℝ))

/-- **Completeness of rational tests.** A symmetric rational matrix whose quadratic form is
nonnegative on *every rational vector* is positive semidefinite as a real matrix. -/
theorem posSemidef_of_rat_tests (M : Matrix (Fin n) (Fin n) ℚ) (hsym : Mᵀ = M)
    (h : ∀ x : Fin n → ℚ, 0 ≤ qf M x) : (castM M).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  have hs : ∀ i j, M j i = M i j := symm_of_transpose_eq hsym
  refine ⟨?_, ?_⟩
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial, castM_apply]
    rw [hs]
  · intro y
    have hclosed : IsClosed {y : Fin n → ℝ | 0 ≤ qfR (castM M) y} :=
      isClosed_le continuous_const (continuous_qfR _)
    have hsub : Set.range (fun x : Fin n → ℚ => fun i => (x i : ℝ)) ⊆
        {y : Fin n → ℝ | 0 ≤ qfR (castM M) y} := by
      rintro _ ⟨x, rfl⟩
      rw [Set.mem_ofPred_eq, ← castM_qf]
      exact_mod_cast h x
    have huniv : Set.univ ⊆ {y : Fin n → ℝ | 0 ≤ qfR (castM M) y} := by
      have := closure_minimal hsub hclosed
      rwa [denseRange_rat_pi.closure_range] at this
    have hmem := huniv (Set.mem_univ y)
    simpa [qfR, star_trivial] using hmem

/-- The easy direction: a real PSD matrix passes every rational test. -/
theorem rat_tests_of_posSemidef (M : Matrix (Fin n) (Fin n) ℚ)
    (hM : (castM M).PosSemidef) : ∀ x : Fin n → ℚ, 0 ≤ qf M x := by
  intro x
  have h1 : 0 ≤ qfR (castM M) (fun i => (x i : ℝ)) := by
    simpa only [qfR, star_trivial] using hM.dotProduct_mulVec_nonneg (fun i => (x i : ℝ))
  rw [← castM_qf] at h1
  exact_mod_cast h1

/-- **Rational witness.** If some real vector makes the quadratic form negative, then some
rational vector does too: an exact-arithmetic separation oracle always has a rational cut. -/
theorem exists_rat_qf_neg (M : Matrix (Fin n) (Fin n) ℚ) (hsym : Mᵀ = M)
    (h : ∃ y : Fin n → ℝ, qfR (castM M) y < 0) : ∃ x : Fin n → ℚ, qf M x < 0 := by
  by_contra hcon
  have hall : ∀ x : Fin n → ℚ, 0 ≤ qf M x := by
    intro x
    by_contra hx
    exact hcon ⟨x, not_le.mp hx⟩
  obtain ⟨y, hy⟩ := h
  have hpsd := posSemidef_of_rat_tests M hsym hall
  have hnn : 0 ≤ qfR (castM M) y := by
    simpa only [qfR, star_trivial] using hpsd.dotProduct_mulVec_nonneg y
  linarith

/-- **A rational certificate of positive definiteness.** Symmetry, rational nonnegativity and a
nonzero determinant give a real positive definite matrix — the SPD input that the ellipsoid
step needs when the matrix is produced by exact rational arithmetic. -/
theorem posDef_of_rat_tests (M : Matrix (Fin n) (Fin n) ℚ) (hsym : Mᵀ = M)
    (h : ∀ x : Fin n → ℚ, 0 ≤ qf M x) (hdet : M.det ≠ 0) : (castM M).PosDef := by
  have hpsd := posSemidef_of_rat_tests M hsym h
  rw [hpsd.posDef_iff_det_ne_zero, castM_det]
  intro h0
  exact hdet (by exact_mod_cast h0)

/-! ## 4. Reading the certified pair in `ℝ` -/

/-- The trace pairing of rational matrices transfers: the real duality gap is the cast of the
rational one. -/
theorem castM_trace_mul (A X : Matrix (Fin n) (Fin n) ℚ) :
    (castM A * castM X).trace = ((A * X).trace : ℝ) := by
  rw [← castM_mul, castM_trace]

/-- A unit diagonal survives the cast. -/
theorem castM_diag_eq_one (X : Matrix (Fin n) (Fin n) ℚ) (h : ∀ i, X i i = 1) :
    ∀ i, castM X i i = 1 := by
  intro i
  rw [castM_apply, h i]
  norm_num

/-- The exact hypothesis shape consumed by `Check_LeafB.weak_duality`: a rational dual
certificate `diagonal y + A` satisfying rational tests is a real dual feasible point. -/
theorem realDualFeasible (A : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ)
    (hsym : (diagonal y + A)ᵀ = diagonal y + A)
    (htest : ∀ x : Fin n → ℚ, 0 ≤ qf (diagonal y + A) x) :
    (diagonal (fun i => (y i : ℝ)) + castM A).PosSemidef := by
  have hcast : castM (diagonal y + A) = diagonal (fun i => (y i : ℝ)) + castM A := by
    rw [castM_add, castM_diagonal]
  rw [← hcast]
  exact posSemidef_of_rat_tests _ hsym htest

/-- The companion shape for the primal point: rational PSD data plus a unit diagonal is a real
feasible primal point. -/
theorem realPrimalFeasible (X : Matrix (Fin n) (Fin n) ℚ) (hsym : Xᵀ = X)
    (htest : ∀ x : Fin n → ℚ, 0 ≤ qf X x) (hdiag : ∀ i, X i i = 1) :
    (castM X).PosSemidef ∧ ∀ i, castM X i i = 1 :=
  ⟨posSemidef_of_rat_tests X hsym htest, castM_diag_eq_one X hdiag⟩

/-- **Packaged equivalence.** Over a symmetric rational matrix, real positive semidefiniteness
is *decidable by rational tests*: no real analysis is needed to check the hypothesis. -/
theorem posSemidef_iff_rat_tests (M : Matrix (Fin n) (Fin n) ℚ) (hsym : Mᵀ = M) :
    (castM M).PosSemidef ↔ ∀ x : Fin n → ℚ, 0 ≤ qf M x :=
  ⟨rat_tests_of_posSemidef M, posSemidef_of_rat_tests M hsym⟩

/-- **Robust (shifted) transfer.** An `ε`-margin rational certificate — `-ε‖x‖² ≤ xᵀMx` on every
rational vector — transfers to the same inequality over `ℝ`. This is the real-valued reading of
the `ε`-robust PSD certificates: approximate rational data still gives a usable real bound. -/
theorem shifted_transfer (M : Matrix (Fin n) (Fin n) ℚ) (_hsym : Mᵀ = M) (eps : ℚ)
    (h : ∀ x : Fin n → ℚ, -(eps * ∑ i, x i * x i) ≤ qf M x) :
    ∀ y : Fin n → ℝ, -((eps : ℝ) * ∑ i, y i * y i) ≤ qfR (castM M) y := by
  intro y
  have hclosed : IsClosed {y : Fin n → ℝ | -((eps : ℝ) * ∑ i, y i * y i) ≤ qfR (castM M) y} := by
    apply isClosed_le _ (continuous_qfR _)
    continuity
  have hsub : Set.range (fun x : Fin n → ℚ => fun i => (x i : ℝ)) ⊆
      {y : Fin n → ℝ | -((eps : ℝ) * ∑ i, y i * y i) ≤ qfR (castM M) y} := by
    rintro _ ⟨x, rfl⟩
    rw [Set.mem_ofPred_eq, ← castM_qf]
    have hx := h x
    have hcast : ((-(eps * ∑ i, x i * x i) : ℚ) : ℝ)
        = -((eps : ℝ) * ∑ i, (x i : ℝ) * (x i : ℝ)) := by
      push_cast
      try ring
    have hle : ((-(eps * ∑ i, x i * x i) : ℚ) : ℝ) ≤ ((qf M x : ℚ) : ℝ) := by
      exact_mod_cast hx
    rwa [hcast] at hle
  have huniv : Set.univ ⊆ {y : Fin n → ℝ | -((eps : ℝ) * ∑ i, y i * y i) ≤ qfR (castM M) y} := by
    have := closure_minimal hsub hclosed
    rwa [denseRange_rat_pi.closure_range] at this
  exact huniv (Set.mem_univ y)

/-! ## 5. The duality gap over `ℚ` implies the gap over `ℝ` -/

/-- The duality gap is the cast of the rational duality gap, so a rational gap bound implies the
real one: with a rational primal point `X` and dual point `y`,
`∑ i, y i + tr (A X) ≤ B` over `ℚ` gives the same bound over `ℝ`. -/
theorem realGap_of_ratGap (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) (B : ℚ)
    (h : (∑ i, y i) + (A * X).trace ≤ B) :
    (∑ i, (y i : ℝ)) + (castM A * castM X).trace ≤ (B : ℝ) := by
  rw [castM_trace_mul]
  have h' : ((∑ i, y i) + (A * X).trace : ℚ) ≤ B := h
  have := (Rat.cast_le (K := ℝ)).mpr h'
  push_cast at this ⊢
  linarith

/-- **The leaf's rational value is the real value.**  The lower value attached to a rational
primal point, `(∑ᵢ ∑ⱼ Aᵢⱼ - tr (A X)) / 4`, is computed identically in `ℚ` and in `ℝ`, so the
rational program's output *is* the real lower bound `Check_LeafB.lowerValue`. -/
theorem cast_lowerValue (A X : Matrix (Fin n) (Fin n) ℚ) :
    ((((∑ i, ∑ j, A i j) - (A * X).trace) / 4 : ℚ) : ℝ)
      = (((∑ i, ∑ j, castM A i j) - (castM A * castM X).trace) / 4) := by
  have hT : ((A * X).trace : ℝ) = (castM A * castM X).trace := (castM_trace_mul A X).symm
  rw [← hT]
  simp only [castM_apply]
  push_cast; rfl

/-! ## 6. Axiom audit -/

#print axioms QMCLeafB.CastBridge.posSemidef_of_rat_tests
#print axioms QMCLeafB.CastBridge.exists_rat_qf_neg
#print axioms QMCLeafB.CastBridge.posDef_of_rat_tests
#print axioms QMCLeafB.CastBridge.shifted_transfer
#print axioms QMCLeafB.CastBridge.realDualFeasible
#print axioms QMCLeafB.CastBridge.realPrimalFeasible
#print axioms QMCLeafB.CastBridge.realGap_of_ratGap
#print axioms QMCLeafB.CastBridge.cast_lowerValue
#print axioms QMCLeafB.CastBridge.castM_inv

end QMCLeafB.CastBridge


/-! #### merged from `Check_IterBound.lean` -/

/-!
# `brick-iterbound`: how many iterations the shallow-cut loop needs

The leaf-B solver has to *stop*.  Whatever search it runs (shallow-cut ellipsoid, interior
point), its loop is driven by a positive potential that contracts geometrically, and the
polynomial-time claim needs an explicit count of the iterations before the potential drops
below the accuracy target `E`.

This file supplies that count with **no logarithms and no exponentials**: everything is a
rational inequality plus `ℚ`-arithmetic, so an exact-arithmetic implementation can evaluate
the stopping rule itself.

The engine is the elementary estimate `((m-1)/m)^m ≤ 1/2` (`m ≥ 2`): a factor of
`1 - 1/m` per step halves the potential every `m` steps.  It is proved from Bernoulli's
inequality `1 + n·x ≤ (1+x)^n`, i.e. ultimately from the binomial expansion
`2(m-1)^m ≤ m^m`, and it is the reason the GLS shallow-cut determinant argument gives
`O(d · log(Φ₀/E))` iterations with `m = 4d`: the loop count is `K · 4d` where `2^K` clears
the ratio `Φ₀/E`.

Division of labour: this file counts iterations; the *cost of one iteration* is
`brick-tm2-size`'s business, and the per-step determinant decrease is
`brick-ellipsoid-analysis`'s.

Main results:
* `pow_pred_div_self_le_half` : `((m-1)/m)^m ≤ 1/2` for `m ≥ 2`;
* `potential_le_pow_mul`     : geometric contraction `Φ(k+1) ≤ c·Φ(k)` gives `Φ k ≤ c^k·Φ 0`;
* `potential_halves`         : hence `Φ (k*m) ≤ (1/2)^k · Φ 0`;
* `potential_lt_of_ratio`    : any `K` with `Φ 0 < E · 2^K` gives `Φ (K*m) < E`;
* `exists_potential_lt`      : such a `K` always exists (Archimedean, no log needed);
* `potential_halves_of_gamma` : a per-step factor `1 - γ` with `γ ≥ 1/m` (the form a
  determinant ratio `1 - 1/(4d)` arrives in);
* `potential_sub_gap`         : additive progress `Φ(k+1) ≤ Φ k - γ` gives `Φ k ≤ Φ 0 - k·γ`;
* `gls_iterations`           : the `m = 4d` shape of the GLS shallow-cut count;
* `nat_measure_step`         : the `ℕ`-valued measure version (exact, rounding-free).
-/

namespace QMCLeafB.IterBound

/-! ## 1. The contraction factor -/

/-- Bernoulli's inequality instance behind the halving estimate: for `m ≥ 2`,
`2·(m-1)^m ≤ m^m` over `ℚ`.  Proof: `(1 + 1/(m-1))^m ≥ 1 + m/(m-1) ≥ 2`. -/
theorem two_mul_pow_pred_le_pow (m : ℕ) (hm : 2 ≤ m) :
    (2 : ℚ) * ((m - 1 : ℕ) : ℚ) ^ m ≤ (m : ℚ) ^ m := by
  have hm1 : (0 : ℚ) < ((m - 1 : ℕ) : ℚ) := by
    have h : 0 < m - 1 := by omega
    exact_mod_cast h
  have hcast : ((m - 1 : ℕ) : ℚ) + 1 = (m : ℚ) := by
    push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
    ring
  have hbern : 1 + (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) ≤ (1 + 1 / ((m - 1 : ℕ) : ℚ)) ^ m :=
    one_add_mul_le_pow (by
      have h : (0 : ℚ) < 1 / ((m - 1 : ℕ) : ℚ) := by positivity
      linarith) m
  have hgeom : (1 + 1 / ((m - 1 : ℕ) : ℚ)) = (m : ℚ) / ((m - 1 : ℕ) : ℚ) := by
    rw [← hcast]
    field_simp
  rw [hgeom] at hbern
  have hmdiv : (1 : ℚ) ≤ (m : ℚ) * (1 / ((m - 1 : ℕ) : ℚ)) := by
    rw [mul_one_div, le_div_iff₀ hm1]
    linarith
  have hratio : (2 : ℚ) ≤ ((m : ℚ) / ((m - 1 : ℕ) : ℚ)) ^ m := by linarith
  have hmul := mul_le_mul_of_nonneg_right hratio (le_of_lt (pow_pos hm1 m))
  have hcancel : ((m : ℚ) / ((m - 1 : ℕ) : ℚ)) ^ m * ((m - 1 : ℕ) : ℚ) ^ m = (m : ℚ) ^ m := by
    rw [div_pow]
    exact div_mul_cancel₀ _ (pow_ne_zero m (ne_of_gt hm1))
  rw [hcancel] at hmul
  calc (2 : ℚ) * ((m - 1 : ℕ) : ℚ) ^ m
      = (((m - 1 : ℕ) : ℚ) ^ m) * 2 := by ring
    _ ≤ (m : ℚ) ^ m := by linarith [hmul]

/-- **The halving factor**: `((m-1)/m)^m ≤ 1/2` for `m ≥ 2`. -/
theorem pow_pred_div_self_le_half (m : ℕ) (hm : 2 ≤ m) :
    (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m ≤ 1 / 2 := by
  have hm0 : (0 : ℚ) < (m : ℚ) := by
    have h : 0 < m := by omega
    exact_mod_cast h
  rw [div_pow, div_le_iff₀ (pow_pos hm0 m)]
  have h := two_mul_pow_pred_le_pow m hm
  linarith

/-! ## 2. Contracting potentials -/

/-- A geometrically contracting potential is bounded by its geometric series. -/
theorem potential_le_pow_mul (Φ : ℕ → ℚ) (c : ℚ) (hc : 0 ≤ c)
    (hstep : ∀ k, Φ (k + 1) ≤ c * Φ k) (_h0 : 0 ≤ Φ 0) :
    ∀ k, Φ k ≤ c ^ k * Φ 0 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      calc Φ (n + 1) ≤ c * Φ n := hstep n
        _ ≤ c * (c ^ n * Φ 0) := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (n + 1) * Φ 0 := by ring

/-- **Halving every `m` steps**: a per-step factor `(m-1)/m` gives `Φ (k·m) ≤ (1/2)^k Φ 0`. -/
theorem potential_halves (Φ : ℕ → ℚ) (m : ℕ) (hm : 2 ≤ m)
    (hstep : ∀ k, Φ (k + 1) ≤ (((m - 1 : ℕ) : ℚ) / (m : ℚ)) * Φ k) (h0 : 0 ≤ Φ 0) :
    ∀ k, Φ (k * m) ≤ (1 / 2) ^ k * Φ 0 := by
  intro k
  have hm0 : (0 : ℚ) < (m : ℚ) := by
    have : 0 < m := by omega
    exact_mod_cast this
  have hc : (0 : ℚ) ≤ ((m - 1 : ℕ) : ℚ) / (m : ℚ) := by positivity
  have hfirst := potential_le_pow_mul Φ _ hc hstep h0 (k * m)
  have hpow : (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ (k * m)
      = ((((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m) ^ k := by
    rw [← pow_mul, Nat.mul_comm]
  calc Φ (k * m) ≤ (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ (k * m) * Φ 0 := hfirst
    _ = ((((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m) ^ k * Φ 0 := by rw [hpow]
    _ ≤ (1 / 2) ^ k * Φ 0 := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        exact pow_le_pow_left₀ (pow_nonneg hc m) (pow_pred_div_self_le_half m hm) k

/-- **The stopping rule.** If `K` clears the potential ratio, `Φ 0 < E · 2^K`, then after
`K·m` iterations of the `(m-1)/m` contraction the potential is below the target `E`. -/
theorem potential_lt_of_ratio (Φ : ℕ → ℚ) (m : ℕ) (hm : 2 ≤ m) (E : ℚ) (_hE : 0 < E)
    (hstep : ∀ k, Φ (k + 1) ≤ (((m - 1 : ℕ) : ℚ) / (m : ℚ)) * Φ k) (h0 : 0 ≤ Φ 0)
    {K : ℕ} (hK : Φ 0 < E * 2 ^ K) : Φ (K * m) < E := by
  have hhalf := potential_halves Φ m hm hstep h0 K
  have h2 : (1 / 2 : ℚ) ^ K * Φ 0 < E := by
    have hpos : (0 : ℚ) < (1 / 2) ^ K := by positivity
    have hstep' : (1 / 2 : ℚ) ^ K * Φ 0 < (1 / 2 : ℚ) ^ K * (E * 2 ^ K) :=
      mul_lt_mul_of_pos_left hK hpos
    have heq : (1 / 2 : ℚ) ^ K * (E * 2 ^ K) = E := by
      have h1 : (1 / 2 : ℚ) ^ K * (2 : ℚ) ^ K = 1 := by
        rw [← mul_pow]; norm_num
      calc (1 / 2 : ℚ) ^ K * (E * 2 ^ K) = E * ((1 / 2 : ℚ) ^ K * 2 ^ K) := by ring
        _ = E := by rw [h1, mul_one]
    linarith
  linarith

/-- Such a `K` always exists: no logarithms needed, just the Archimedean property. -/
theorem exists_potential_lt (Φ : ℕ → ℚ) (m : ℕ) (hm : 2 ≤ m) (E : ℚ) (hE : 0 < E)
    (hstep : ∀ k, Φ (k + 1) ≤ (((m - 1 : ℕ) : ℚ) / (m : ℚ)) * Φ k) (h0 : 0 ≤ Φ 0) :
    ∃ k, Φ (k * m) < E := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (Φ 0 / E) (by norm_num : (1 : ℚ) < 2)
  refine ⟨K, potential_lt_of_ratio Φ m hm E hE hstep h0 ?_⟩
  rw [div_lt_iff₀ hE] at hK
  linarith

/-- **General contraction factor.**  A per-step factor `1 - γ` with `γ ≥ 1/m` halves the
potential every `m` steps: this is the form a one-step analysis (e.g. a determinant ratio
`det A' ≤ (1 - 1/(4d)) det A`) feeds into. -/
theorem potential_halves_of_gamma (Φ : ℕ → ℚ) (m : ℕ) (hm : 2 ≤ m) (γ : ℚ)
    (hγ : 1 / (m : ℚ) ≤ γ) (hγ1 : γ ≤ 1)
    (hstep : ∀ k, Φ (k + 1) ≤ (1 - γ) * Φ k) (h0 : 0 ≤ Φ 0) :
    ∀ k, Φ (k * m) ≤ (1 / 2) ^ k * Φ 0 := by
  have hm0 : (0 : ℚ) < (m : ℚ) := by
    have h : 0 < m := by omega
    exact_mod_cast h
  have hc0 : (0 : ℚ) ≤ 1 - γ := by linarith
  have hcm : 1 - γ ≤ (((m - 1 : ℕ) : ℚ) / (m : ℚ)) := by
    have h1 : (1 : ℚ) / (m : ℚ) = 1 / (m : ℚ) := rfl
    have hsub : ((m - 1 : ℕ) : ℚ) / (m : ℚ) = 1 - 1 / (m : ℚ) := by
      have hmne : ((m : ℕ) : ℚ) ≠ 0 := ne_of_gt hm0
      field_simp
      push_cast [Nat.cast_sub (by omega : 1 ≤ m)]
      ring
    rw [hsub]
    linarith
  intro k
  have hfirst := potential_le_pow_mul Φ (1 - γ) hc0 hstep h0 (k * m)
  calc Φ (k * m) ≤ (1 - γ) ^ (k * m) * Φ 0 := hfirst
    _ = ((1 - γ) ^ m) ^ k * Φ 0 := by
        rw [← pow_mul, Nat.mul_comm]
    _ ≤ (1 / 2) ^ k * Φ 0 := by
        refine mul_le_mul_of_nonneg_right ?_ h0
        refine pow_le_pow_left₀ ?_ ?_ k
        · exact pow_nonneg hc0 m
        · calc (1 - γ) ^ m ≤ (((m - 1 : ℕ) : ℚ) / (m : ℚ)) ^ m :=
                pow_le_pow_left₀ hc0 hcm m
            _ ≤ 1 / 2 := pow_pred_div_self_le_half m hm

/-- **Additive progress.**  A potential that drops by a fixed rational `γ > 0` per step drops
linearly: `Φ k ≤ Φ 0 - k·γ`, so `k·γ > Φ 0 - E` iterations suffice to reach `E`. -/
theorem potential_sub_gap (Φ : ℕ → ℚ) (γ : ℚ) (hstep : ∀ k, Φ (k + 1) ≤ Φ k - γ) :
    ∀ k, Φ k ≤ Φ 0 - k * γ := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have h1 := hstep n
      have hcast : ((n + 1 : ℕ) : ℚ) * γ = n * γ + γ := by push_cast; ring
      rw [hcast]
      linarith

/-- Consequence of additive progress: once `k·γ` clears `Φ 0 - E`, the potential is below `E`. -/
theorem potential_sub_gap_lt (Φ : ℕ → ℚ) (γ : ℚ) (E : ℚ)
    (hstep : ∀ k, Φ (k + 1) ≤ Φ k - γ) {k : ℕ} (h : Φ 0 - E < k * γ) : Φ k < E := by
  have := potential_sub_gap Φ γ hstep k
  linarith

/-! ## 3. The GLS shallow-cut shape -/

/-- **The shallow-cut iteration count.** With the GLS per-step determinant factor
`1 - 1/(4d)` (admissible for `d ≥ 1`), the potential is below `E` after `K·(4d)` iterations,
where `2^K` clears `Φ 0 / E`.  This is the `O(d · log(Φ₀/E))` count of the volume argument,
stated with no logarithms: for `d`-dimensional ellipsoids the loop length is `4d·K`. -/
theorem gls_iterations (Φ : ℕ → ℚ) (d : ℕ) (hd : 1 ≤ d) (E : ℚ) (hE : 0 < E)
    (hstep : ∀ k, Φ (k + 1) ≤ (((4 * d - 1 : ℕ) : ℚ) / ((4 * d : ℕ) : ℚ)) * Φ k)
    (h0 : 0 ≤ Φ 0) {K : ℕ} (hK : Φ 0 < E * 2 ^ K) : Φ (K * (4 * d)) < E := by
  have hm : 2 ≤ 4 * d := by omega
  exact potential_lt_of_ratio Φ (4 * d) hm E hE hstep h0 hK

/-- The same count in existence form. -/
theorem gls_exists_iterations (Φ : ℕ → ℚ) (d : ℕ) (hd : 1 ≤ d) (E : ℚ) (hE : 0 < E)
    (hstep : ∀ k, Φ (k + 1) ≤ (((4 * d - 1 : ℕ) : ℚ) / ((4 * d : ℕ) : ℚ)) * Φ k)
    (h0 : 0 ≤ Φ 0) : ∃ k, Φ (k * (4 * d)) < E :=
  exists_potential_lt Φ (4 * d) (by omega) E hE hstep h0

/-! ## 4. The rounding-free `ℕ`-valued measure -/

/-- A strictly decreasing `ℕ`-valued measure loses at least one unit per step, so after `k`
steps it is at most `φ 0 - k`: an exact-arithmetic implementation gets its iteration bound
with no rationals at all. -/
theorem nat_measure_step (φ : ℕ → ℕ) (h : ∀ k, φ (k + 1) < φ k) :
    ∀ k, φ k + k ≤ φ 0 := by
  intro k
  induction k with
  | zero => simp
  | succ n ih =>
      have h1 : φ (n + 1) + 1 ≤ φ n := h n
      have : φ (n + 1) + (n + 1) ≤ φ n + n := by omega
      omega

/-- Consequence: the loop cannot run for `φ 0` steps or more. -/
theorem nat_measure_iterations (φ : ℕ → ℕ) (h : ∀ k, φ (k + 1) < φ k) (k : ℕ) :
    k ≤ φ 0 := by
  have := nat_measure_step φ h k
  omega

/-! ## 5. Axiom audit -/

#print axioms QMCLeafB.IterBound.pow_pred_div_self_le_half
#print axioms QMCLeafB.IterBound.potential_halves
#print axioms QMCLeafB.IterBound.potential_lt_of_ratio
#print axioms QMCLeafB.IterBound.exists_potential_lt
#print axioms QMCLeafB.IterBound.gls_iterations
#print axioms QMCLeafB.IterBound.potential_halves_of_gamma
#print axioms QMCLeafB.IterBound.potential_sub_gap_lt
#print axioms QMCLeafB.IterBound.nat_measure_step

end QMCLeafB.IterBound


/-! ## Integration probe (m8): the assembled rational endgame -/

namespace QMCLeafB.IntegrationProbe

open Matrix

variable {n : ℕ}

/-- `V` of a cast matrix is the cast of the rational double sum. -/
theorem V_castM (A : Matrix (Fin n) (Fin n) ℚ) :
    QMCLeafB.V (CastBridge.castM A) = ((∑ i, ∑ j, A i j : ℚ) : ℝ) := by
  have h1 : (∑ i, ∑ j, CastBridge.castM A i j) = ((∑ i, ∑ j, A i j : ℚ) : ℝ) := by
    push_cast
    simp only [CastBridge.castM_apply]
  rw [QMCLeafB.V, h1]

/-- Rational gap bound casts to the real gap bound against `V (castM A)`. -/
theorem gapR (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ)
    (hgap : (∑ i, y i) + (A * X).trace ≤ (∑ i, ∑ j, A i j) / 5000) :
    (∑ i, (y i : ℝ)) + (CastBridge.castM A * CastBridge.castM X).trace
      ≤ QMCLeafB.V (CastBridge.castM A) / 5000 := by
  have h := CastBridge.realGap_of_ratGap A X y ((∑ i, ∑ j, A i j) / 5000) hgap
  rw [V_castM]
  have hcast : (((∑ i, ∑ j, A i j) / 5000 : ℚ) : ℝ) = ((∑ i, ∑ j, A i j : ℚ) : ℝ) / 5000 := by
    rw [Rat.cast_div]
    norm_num
  rw [hcast] at h
  exact h

/-- **The assembled rational endgame.**  Rational primal/dual data — a symmetric matrix whose
quadratic form is nonnegative on every rational vector with unit diagonal, a symmetric rational
slack `diagonal y + A` likewise nonnegative on rational vectors, and the rational gap bound —
give exactly the real sandwich of `QMCLeafB.sandwich`. -/
theorem rat_sandwich (A X : Matrix (Fin n) (Fin n) ℚ) (y : Fin n → ℚ) (S : ℝ)
    (hXsym : Xᵀ = X) (hXtest : ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf X x)
    (hXdiag : ∀ i, X i i = 1)
    (hysym : (diagonal y + A)ᵀ = diagonal y + A)
    (hytest : ∀ x : Fin n → ℚ, 0 ≤ CastBridge.qf (diagonal y + A) x)
    (hgap : (∑ i, y i) + (A * X).trace ≤ (∑ i, ∑ j, A i j) / 5000)
    (hS : ModernConvex.Relaxations.IsMaxcutSDPValue (CastBridge.castM A) S) :
    QMCLeafB.lowerValue (CastBridge.castM A) (CastBridge.castM X) ≤ S ∧
      S - QMCLeafB.lowerValue (CastBridge.castM A) (CastBridge.castM X)
        ≤ QMCLeafB.V (CastBridge.castM A) / 20000 := by
  obtain ⟨hXpsd, hXdiagR⟩ := CastBridge.realPrimalFeasible X hXsym hXtest hXdiag
  have hypsd := CastBridge.realDualFeasible A y hysym hytest
  exact QMCLeafB.sandwich hXpsd hXdiagR hypsd (gapR A X y hgap) hS

end QMCLeafB.IntegrationProbe


