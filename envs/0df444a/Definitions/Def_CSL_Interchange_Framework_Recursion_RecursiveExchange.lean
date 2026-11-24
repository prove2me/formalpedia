-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchange
-- name    : CSL_Interchange_Framework_Recursion_RecursiveExchange
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:40:33.456812+00:00
-- url     : https://prove2.me/theorems/3a5bb507-54c8-42d5-b8a5-a0abb113f8ad
-- title:
--   Coded sorting library: Interchange / Framework / Recursion / RecursiveExchange
-- statement:
--   Module `CodedSorting.Interchange.Framework.Recursion.RecursiveExchange` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # The concrete rank-indexed recursion schedule
--
--   The child indices below are the ones in the proved partial-permutation
--   factorization of each ACTUAL physical edge difference. In particular the
--   last edge into every sink is included. A single specialization contains
--   both node labels and edge factorizations before its prime is chosen.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Recursion.RecursiveExchange

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Labels_Framework_StageLabels
import Definitions.Def_CSL_Circuit_Framework_CodedSimulation
import Definitions.Def_CSL_Circuit_Framework_UniformFactorization
import Definitions.Def_CSL_Interchange_Framework_Recursion_ArbitrarySchedule
import Definitions.Def_CSL_Shared_Memory_Streams
import Definitions.Def_CSL_Interchange_Framework_Fields_BinaryPaddingScan
import Definitions.Def_CSL_Interchange_Framework_Fields_FieldPacking

/-!
# The concrete rank-indexed recursion schedule

The child indices below are the ones in the proved partial-permutation
factorization of each ACTUAL physical edge difference. In particular the
last edge into every sink is included. A single specialization contains
both node labels and edge factorizations before its prime is chosen.
-/

namespace CSL.RecursiveExchange

open Circuit CircuitProgram ProgramNetwork TensorLabels StageLabels
open MatrixFactorization CodedSimulation Address
open scoped BigOperators

noncomputable section

abbrev Reg := GlobalReg Parameters.d
abbrev Node := Vertex Reg (globalProgram Parameters.d).length
abbrev Edge := Wire Reg (globalProgram Parameters.d).length
abbrev Index := H Parameters.d

def roleEnumeration : Reg ≃ Fin Parameters.W :=
  Fintype.equivFinOfCardEq actual_sessions_card

noncomputable instance indexOrder : LinearOrder Index :=
  LinearOrder.lift' (Fintype.equivFin Index) (Fintype.equivFin Index).injective

def edgeMatrix (e : Edge) : Matrix Index Index ℚ :=
  actualLabel Parameters.d (wireHead (globalProgram Parameters.d) e) -
    actualLabel Parameters.d (wireTail (globalProgram Parameters.d) e)

theorem edge_rank_sum : (∑ e : Edge, (edgeMatrix e).rank) = Parameters.S :=
  actual_edgeRank_eq_S

/-- This finite family includes node labels as well as all physical edge
differences. Therefore reduction preserves their mutual identities. -/
def rationalFamily : Node ⊕ Edge → Matrix Index Index ℚ
  | .inl v => actualLabel Parameters.d v
  | .inr e => edgeMatrix e

def uniform : UniformLowerFactorization rationalFamily :=
  uniformLowerFactorization rationalFamily

@[reducible] def radix : ℕ := uniform.specialization.prime

theorem radix_prime : radix.Prime := uniform.specialization.prime_is_prime
theorem radix_odd : Odd radix := uniform.specialization.prime_is_odd

abbrev Scalar (f : ℕ) := ZMod (radix ^ f)
abbrev Field (f : ℕ) := Index → Scalar f

instance scalarModulusNeZero (f : ℕ) : NeZero (radix ^ f) :=
  ⟨pow_ne_zero _ radix_prime.ne_zero⟩

instance radixNeZero : NeZero radix := ⟨radix_prime.ne_zero⟩

def nodeMatrix (f : ℕ) (v : Node) : Matrix Index Index (Scalar f) :=
  uniform.matrix f (.inl v) 0

def reducedEdgeMatrix (f : ℕ) (e : Edge) : Matrix Index Index (Scalar f) :=
  uniform.matrix f (.inr e) 0

private theorem specialization_sub {K I : Type*} [Fintype K] [Fintype I]
    [DecidableEq I] {A : K → Matrix I I ℚ} (F : SpecializedFamily A)
    (i j k : K) (h : A i - A j = A k) (f : ℕ) :
    F.matrix f i - F.matrix f j = F.matrix f k := by
  have hlocal : F.coefficients i - F.coefficients j = F.coefficients k := by
    apply F.rational_embedding_injective
    simpa only [map_sub, F.lift_correct] using h
  simpa only [SpecializedFamily.matrix, map_sub] using
    congrArg ((F.reduce f).mapMatrix) hlocal

private theorem specialization_sub_one {K I : Type*} [Fintype K] [Fintype I]
    [DecidableEq I] {A : K → Matrix I I ℚ} (F : SpecializedFamily A)
    (i j : K) (h : A i - A j = 1) (f : ℕ) :
    F.matrix f i - F.matrix f j = 1 := by
  have hlocal : F.coefficients i - F.coefficients j = 1 := by
    apply F.rational_embedding_injective
    simpa only [map_sub, map_one, F.lift_correct] using h
  simpa only [SpecializedFamily.matrix, map_sub, map_one] using
    congrArg ((F.reduce f).mapMatrix) hlocal

theorem reduced_edge_difference (f : ℕ) (e : Edge) :
    nodeMatrix f (wireHead (globalProgram Parameters.d) e) -
      nodeMatrix f (wireTail (globalProgram Parameters.d) e) = reducedEdgeMatrix f e := by
  apply specialization_sub uniform.specialization
  simp [expandedFamily, rationalFamily, edgeMatrix]

theorem reduced_endpoint_identity (f : ℕ) (r : Reg) :
    nodeMatrix f (.sink (globalSwap r)) - nodeMatrix f (.source r) = 1 := by
  apply specialization_sub_one uniform.specialization
  simpa [expandedFamily, rationalFamily] using actual_endpoint_identity r

/-- A child is an actual nonzero pivot position of an actual physical edge.
The row and column specify precisely which two short fields it exchanges. -/
abbrev EdgeChild (e : Edge) := OnePosition (uniform.data (.inr e)).pivot
abbrev Child := (e : Edge) × EdgeChild e

def childRow (c : Child) : Index := oneRow c.2
def childCol (c : Child) : Index := oneCol c.2

theorem edge_child_count (e : Edge) :
    Fintype.card (EdgeChild e) = (edgeMatrix e).rank := by
  rw [← partialPermutation_rank _ (uniform.data (.inr e)).pivot_sparse
    (uniform.data (.inr e)).pivot_zero_one, (uniform.data (.inr e)).rank_eq]
  rfl

theorem child_count : Fintype.card Child = Parameters.S := by
  rw [Fintype.card_sigma]
  simp_rw [edge_child_count]
  exact edge_rank_sum

/-- The emitted list of elementary shears is exactly the list whose entries
define the child index. Its length is the rational edge rank for every f. -/
theorem edge_short_shears (e : Edge) (f : ℕ) {Value : Type*}
    (stream : Field f × Field f → Value) :
    (unitShears (uniform.data (.inr e)).pivot (Scalar f)).length = (edgeMatrix e).rank ∧
      applyShears ((unitShears (uniform.data (.inr e)).pivot (Scalar f)).map Matrix.mulVec)
        stream = matrixPhi (uniform.matrix f (.inr e) 2) stream :=
  uniform.sparse_step (.inr e) f stream

/-- The coordinate changes and the rank-many short shears realize this
physical edge's actual target-minus-source layout conversion. -/
theorem edge_address_update (e : Edge) (f : ℕ) (h d : Field f) :
    ((uniform.matrix f (.inr e) 1).mulVec
      ((uniform.matrix f (.inr e) 4).mulVec h +
        (uniform.matrix f (.inr e) 2).mulVec ((uniform.matrix f (.inr e) 3).mulVec d)),
      (uniform.matrix f (.inr e) 5).mulVec ((uniform.matrix f (.inr e) 3).mulVec d)) =
      (h + (nodeMatrix f (wireHead (globalProgram Parameters.d) e) -
        nodeMatrix f (wireTail (globalProgram Parameters.d) e)).mulVec d, d) := by
  rw [reduced_edge_difference]
  exact uniform.address_update (.inr e) f h d

abbrev TerminalChild (r : Reg) := EdgeChild (sinkWire (globalProgram Parameters.d) r)

theorem terminal_child_count (r : Reg) :
    Fintype.card (TerminalChild r) =
      (actualLabel Parameters.d (.sink r) -
        actualLabel Parameters.d (wireTail (globalProgram Parameters.d)
          (sinkWire (globalProgram Parameters.d) r))).rank := by
  rw [edge_child_count]
  simp only [edgeMatrix, sinkWire_head]

section EdgeExecution

variable {Prefix Gap Suffix : Type*}

abbrev LongAddress (f : ℕ) := FullAddress Prefix (Field f) Gap Suffix

/-- A recursive child is exposed by preserving the order of all remaining
coordinates: H before i joins the prefix, H after i and D before j the gap,
and D after j the suffix. -/
def childRepack (f : ℕ) (c : Child) :=
  SingleCoordinate.repack (Prefix := Prefix) (R := Scalar f)
    (Gap := Gap) (Suffix := Suffix) (childRow c) (childCol c)

def edgePivots (e : Edge) : List (EdgeChild e) := Finset.univ.toList

theorem edgePivots_length (e : Edge) : (edgePivots e).length = (edgeMatrix e).rank := by
  simp only [edgePivots, Finset.length_toList, Finset.card_univ, edge_child_count]

def shortStep (f : ℕ) (e : Edge)
    (child : EdgeChild e → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (p : EdgeChild e) (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  SingleCoordinate.afterScan (oneRow p) (oneCol p)
    (child p (SingleCoordinate.beforeScan (oneRow p) (oneCol p) a))

def sparseProgram (f : ℕ) (e : Edge)
    (child : EdgeChild e → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (ps : List (EdgeChild e))
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  ps.foldl (fun state p => shortStep f e child p state) a

theorem sparseProgram_correct (f : ℕ) (e : Edge)
    (child : EdgeChild e → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (hchild : ∀ p a, child p a = SingleCoordinate.shortExchange (oneRow p) (oneCol p) a)
    (ps : List (EdgeChild e))
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :
    sparseProgram f e child ps a =
      matrixLocation ((ps.map (fun p => unitEntry (Scalar f) (oneRow p) (oneCol p))).sum) a := by
  induction ps generalizing a with
  | nil =>
    cases a
    simp [sparseProgram, matrixLocation, mapPairEquiv, mapPair, shear]
  | cons p ps ih =>
    change sparseProgram f e child ps (shortStep f e child p a) = _
    rw [ih]
    have hs : shortStep f e child p a =
        matrixLocation (unitEntry (Scalar f) (oneRow p) (oneCol p)) a := by
      unfold shortStep
      rw [hchild]
      have hdec : (fun x y : Index => @LinearOrder.toDecidableEq Index indexOrder x y) =
          (inferInstance : DecidableEq Index) := Subsingleton.elim _ _
      rw [SingleCoordinate.one_short_exchange_matrix (oneRow p) (oneCol p) a]
      simp only [matrixLocation]
      congr
    rw [hs]
    cases a
    simp only [List.map_cons, List.sum_cons, matrixLocation, mapPairEquiv, mapPair,
      shear, Equiv.coe_fn_mk, Matrix.add_mulVec]
    congr 1
    abel

theorem reduced_pivot (f : ℕ) (e : Edge) :
    uniform.matrix f (.inr e) 2 =
      patternMatrix (uniform.data (.inr e)).pivot (Scalar f) := by
  have hp := uniform.specialization.partialPermutation_pattern (.inr e, 2)
    (by simpa [expandedFamily] using (uniform.data (.inr e)).pivot_zero_one) f
  first
  | exact hp
  | (have h_sx := hp; simp only [UniformLowerFactorization.matrix, expandedFamily, Fin.reduceFinMk,
    Fin.isValue, ↓reduceIte] at h_sx ⊢; exact h_sx)
  | (have h_sx := hp; simp only [UniformLowerFactorization.matrix, expandedFamily, Fin.reduceFinMk,
    Fin.isValue, ↓reduceIte] at h_sx; exact h_sx)
  | (simp only [UniformLowerFactorization.matrix, expandedFamily, Fin.reduceFinMk,
    Fin.isValue, ↓reduceIte]; exact hp)

theorem sparseProgram_all (f : ℕ) (e : Edge)
    (child : EdgeChild e → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (hchild : ∀ p a, child p a = SingleCoordinate.shortExchange (oneRow p) (oneCol p) a)
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :
    sparseProgram f e child (edgePivots e) a =
      matrixLocation (uniform.matrix f (.inr e) 2) a := by
  rw [sparseProgram_correct f e child hchild]
  change matrixLocation (unitShears (uniform.data (.inr e)).pivot (Scalar f)).sum a = _
  rw [unitShears_sum, reduced_pivot]
  try rfl

def beforeCoordinates (f : ℕ) (e : Edge)
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  FullAddress.mk a.prefixCoord ((uniform.matrix f (.inr e) 4).mulVec a.high) a.gap
    ((uniform.matrix f (.inr e) 3).mulVec a.low) a.suffix

def afterCoordinates (f : ℕ) (e : Edge)
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  FullAddress.mk a.prefixCoord ((uniform.matrix f (.inr e) 1).mulVec a.high) a.gap
    ((uniform.matrix f (.inr e) 5).mulVec a.low) a.suffix

/-- The actual factorization program: two coordinate changes, rank-many
selected-coordinate child exchanges with their scalar scans, then restore. -/
def edgeProgram (f : ℕ) (e : Edge)
    (child : EdgeChild e → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  afterCoordinates f e (sparseProgram f e child (edgePivots e) (beforeCoordinates f e a))

theorem edgeProgram_correct (f : ℕ) (e : Edge)
    (child : EdgeChild e → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f →
      LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (hchild : ∀ p a, child p a = SingleCoordinate.shortExchange (oneRow p) (oneCol p) a)
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :
    edgeProgram f e child a = matrixLocation (reducedEdgeMatrix f e) a := by
  rw [edgeProgram]
  erw [sparseProgram_all f e child hchild]
  cases a with
  | mk p h g d s =>
    have hu := uniform.address_update (.inr e) f h d
    simp only [afterCoordinates, beforeCoordinates, matrixLocation, mapPairEquiv,
      mapPair, shear, Equiv.coe_fn_mk]
    congr 1
    · exact congrArg Prod.fst hu
    · exact congrArg Prod.snd hu

end EdgeExecution

section StreamEdgeExecution

variable {Prefix Gap Suffix Value : Type*}

def selectedPermutation (f : ℕ) (i j : Index) (op : Equiv.Perm (Scalar f × Scalar f)) :
    Equiv.Perm (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) where
  toFun := SingleCoordinate.modifySelected i j op
  invFun := SingleCoordinate.modifySelected i j op.symm
  left_inv a := by
    rw [SingleCoordinate.modifySelected_comp]
    have hc : (op.symm ∘ op) = id := by funext x; exact op.symm_apply_apply x
    rw [hc]
    exact SingleCoordinate.modifySelected_id i j a
  right_inv a := by
    rw [SingleCoordinate.modifySelected_comp]
    have hc : (op ∘ op.symm) = id := by funext x; exact op.apply_symm_apply x
    rw [hc]
    exact SingleCoordinate.modifySelected_id i j a

def shortBefore (f : ℕ) (i j : Index) :
    Equiv.Perm (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  selectedPermutation f i j lowerSubtractEquiv.symm

def shortAfter (f : ℕ) (i j : Index) :
    Equiv.Perm (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :=
  selectedPermutation f i j lowerReflectEquiv

theorem short_comp (f : ℕ) (i j : Index) :
    (shortBefore (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f i j).trans
      ((SingleCoordinate.shortExchange i j).trans (shortAfter f i j)) =
      matrixLocation (unitEntry (Scalar f) i j) := by
  apply Equiv.ext
  intro a
  change SingleCoordinate.afterScan i j
    (SingleCoordinate.shortExchange i j (SingleCoordinate.beforeScan i j a)) = _
  have hdec : (fun x y : Index => @LinearOrder.toDecidableEq Index indexOrder x y) =
      (inferInstance : DecidableEq Index) := Subsingleton.elim _ _
  rw [SingleCoordinate.one_short_exchange_matrix i j a]
  simp only [matrixLocation]
  congr

/-- Unlike a destination-only specification, this operation actually invokes
the supplied recursive transformer on the data between its two scans. -/
def shortStreamStep (f : ℕ) (e : Edge)
    (child : EdgeChild e →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value))
    (p : EdgeChild e)
    (F : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) :=
  transport (shortAfter f (oneRow p) (oneCol p))
    (child p (transport (shortBefore f (oneRow p) (oneCol p)) F))

theorem shortStreamStep_correct (f : ℕ) (e : Edge)
    (child : EdgeChild e →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value))
    (hchild : ∀ p F, child p F = transport (SingleCoordinate.shortExchange (oneRow p) (oneCol p)) F)
    (p : EdgeChild e)
    (F : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) :
    shortStreamStep f e child p F =
      transport (matrixLocation (unitEntry (Scalar f) (oneRow p) (oneCol p))) F := by
  unfold shortStreamStep
  rw [hchild, transport_comp, transport_comp]
  have hc := short_comp (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f (oneRow p) (oneCol p)
  rw [hc]

def sparseStreamProgram (f : ℕ) (e : Edge)
    (child : EdgeChild e →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value))
    (ps : List (EdgeChild e))
    (F : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) :=
  ps.foldl (fun state p => shortStreamStep f e child p state) F

theorem sparseStreamProgram_correct (f : ℕ) (e : Edge)
    (child : EdgeChild e →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value))
    (hchild : ∀ p F, child p F = transport (SingleCoordinate.shortExchange (oneRow p) (oneCol p)) F)
    (ps : List (EdgeChild e))
    (F : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) :
    sparseStreamProgram f e child ps F =
      transport (matrixLocation ((ps.map (fun p => unitEntry (Scalar f) (oneRow p) (oneCol p))).sum)) F := by
  induction ps generalizing F with
  | nil =>
    funext a
    cases a
    simp [sparseStreamProgram, transport, matrixLocation, mapPairEquiv, mapPair, shear]
  | cons p ps ih =>
    change sparseStreamProgram f e child ps (shortStreamStep f e child p F) = _
    rw [ih, shortStreamStep_correct f e child hchild, transport_comp]
    apply congrArg (fun perm => transport perm F)
    apply Equiv.ext
    intro a
    cases a
    simp only [Equiv.trans_apply, List.map_cons, List.sum_cons, matrixLocation,
      mapPairEquiv, mapPair, shear, Equiv.coe_fn_mk, Matrix.add_mulVec]
    congr 1
    abel

def coordinatePermutation (f : ℕ) (e : Edge) :
    Equiv.Perm (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) where
  toFun := beforeCoordinates f e
  invFun := afterCoordinates f e
  left_inv a := by
    cases a
    simp only [beforeCoordinates, afterCoordinates]
    erw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      (uniform.left_inverse (.inr e) f).1, (uniform.right_inverse (.inr e) f).2,
      Matrix.one_mulVec, Matrix.one_mulVec]
    all_goals rfl
  right_inv a := by
    cases a
    simp only [beforeCoordinates, afterCoordinates]
    erw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
      (uniform.left_inverse (.inr e) f).2, (uniform.right_inverse (.inr e) f).1,
      Matrix.one_mulVec]
    all_goals (try erw [Matrix.one_mulVec])
    all_goals rfl

/-- Array-level factorized edge implementation. Every child transformer is
called on the current full payload stream, exactly once per pivot position. -/
def edgeStreamProgram (f : ℕ) (e : Edge)
    (child : EdgeChild e →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value))
    (F : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) :=
  transport (coordinatePermutation f e).symm
    (sparseStreamProgram f e child (edgePivots e)
      (transport (coordinatePermutation f e) F))

theorem edgeStreamProgram_correct (f : ℕ) (e : Edge)
    (child : EdgeChild e →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value))
    (hchild : ∀ p F, child p F = transport (SingleCoordinate.shortExchange (oneRow p) (oneCol p)) F)
    (F : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Value) :
    edgeStreamProgram f e child F = transport (matrixLocation (reducedEdgeMatrix f e)) F := by
  unfold edgeStreamProgram
  rw [sparseStreamProgram_correct f e child hchild]
  change transport (coordinatePermutation f e).symm
    (transport (matrixLocation (unitShears (uniform.data (.inr e)).pivot (Scalar f)).sum)
      (transport (coordinatePermutation f e) F)) = _
  rw [unitShears_sum, ← reduced_pivot, transport_comp, transport_comp]
  apply congrArg (fun perm => transport perm F)
  apply Equiv.ext
  intro a
  have h := edgeProgram_correct f e (fun p => SingleCoordinate.shortExchange (oneRow p) (oneCol p))
    (fun _ _ => rfl) a
  rw [edgeProgram] at h
  erw [sparseProgram_all f e _ (fun _ _ => rfl)] at h
  exact h

end StreamEdgeExecution

section PhysicalExecution

variable {Prefix Gap Suffix : Type*}

private theorem matrixLocation_after_inverse (f : ℕ)
    (Ms Mt : Matrix Index Index (Scalar f))
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :
    matrixLocation Ms ((matrixLocation Mt).symm a) =
      (matrixLocation (Mt-Ms)).symm a := by
  cases a
  simp only [matrixLocation, mapPairEquiv, mapPair, shear, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, Matrix.sub_mulVec]
  congr 1
  abel

private theorem matrixLocation_inverse_edge (f : ℕ)
    (Ms Mt : Matrix Index Index (Scalar f))
    (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) :
    (matrixLocation Ms).symm ((matrixLocation (Mt-Ms)).symm a) =
      (matrixLocation Mt).symm a := by
  rw [← matrixLocation_after_inverse]
  exact (matrixLocation Ms).symm_apply_apply _

abbrev DiskState (f : ℕ) :=
  Edge → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit

def logicalInput (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (i : Reg) (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) : Bit :=
  input i (matrixLocation (nodeMatrix f (.source i)) a)

def idealWire (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (e : Edge) (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) : Bit :=
  NetworkProtocol.edgeValue (actualNetwork Parameters.d) (actualCode Parameters.d)
    (fun i => logicalInput f input i
      ((matrixLocation (nodeMatrix f (wireHead (globalProgram Parameters.d) e))).symm a)) e

/-- One physical edge operation reads its tail node's already available
input streams, performs the actual local XOR map, and changes storage order
by this edge's actual matrix difference. -/
def physicalWire (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (e : Edge) (a : LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f) : Bit :=
  let old := (matrixLocation (reducedEdgeMatrix f e)).symm a
  (actualCode Parameters.d).localMap ((actualNetwork Parameters.d).tail e)
    (fun port => match port with
      | .inl i => input i.val old
      | .inr incoming => stored incoming.val old) ⟨e,rfl⟩

theorem incoming_index_lt (e incoming : Edge)
    (h : wireHead (globalProgram Parameters.d) incoming =
      wireTail (globalProgram Parameters.d) e) : incoming.1.val < e.1.val := by
  have ht := (actualNetwork Parameters.d).forward incoming
  change vertexRank (globalProgram Parameters.d) (wireTail (globalProgram Parameters.d) incoming) <
    vertexRank (globalProgram Parameters.d) (wireHead (globalProgram Parameters.d) incoming) at ht
  rw [h, rank_wireTail, rank_wireTail] at ht
  exact ht

theorem physicalWire_correct (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (e : Edge)
    (hprevious : ∀ incoming, incoming.1.val < e.1.val → stored incoming = idealWire f input incoming) :
    physicalWire f input stored e = idealWire f input e := by
  funext a
  unfold physicalWire idealWire
  rw [NetworkProtocol.edgeValue_local]
  apply congrArg (fun values => (actualCode Parameters.d).localMap
    ((actualNetwork Parameters.d).tail e) values ⟨e,rfl⟩)
  funext port
  cases port with
  | inl i =>
    change input i.val ((matrixLocation (reducedEdgeMatrix f e)).symm a) =
      logicalInput f input i.val
        ((matrixLocation (nodeMatrix f (wireHead (globalProgram Parameters.d) e))).symm a)
    unfold logicalInput
    have hi : Vertex.source i.val = wireTail (globalProgram Parameters.d) e := i.property
    rw [hi, matrixLocation_after_inverse, reduced_edge_difference]
  | inr incoming =>
    try dsimp only
    have hi : wireHead (globalProgram Parameters.d) incoming.val =
        wireTail (globalProgram Parameters.d) e := incoming.property
    rw [hprevious incoming.val (incoming_index_lt e incoming.val hi)]
    unfold idealWire
    rw [hi, ← reduced_edge_difference, matrixLocation_inverse_edge]

/-- Eager topological execution: layer t computes exactly the edges with
wire index t, retains every other disk stream, then advances to t+1. -/
def executeLayers (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) :
    ℕ → DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f
  | 0 => fun _ _ => 0
  | t+1 => fun e => if e.1.val = t then physicalWire f input (executeLayers f input t) e
      else executeLayers f input t e

theorem executeLayers_correct (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (t : ℕ) (e : Edge) (he : e.1.val < t) :
    executeLayers f input t e = idealWire f input e := by
  induction t generalizing e with
  | zero => omega
  | succ t ih =>
    unfold executeLayers
    split_ifs with hi
    · apply physicalWire_correct
      intro incoming hin
      exact ih incoming (by omega)
    · exact ih e (by omega)

def executePhysical (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) :=
  executeLayers f input ((globalProgram Parameters.d).length+1)

theorem executePhysical_correct (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (e : Edge) : executePhysical f input e = idealWire f input e :=
  executeLayers_correct f input _ e e.1.isLt

/-- Read the actual designated sink edge, with its terminal conversion
included in the eager execution. -/
def physicalOutput (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (i : Reg) := executePhysical f input (sinkWire (globalProgram Parameters.d) (globalSwap i))

theorem physicalOutput_correct (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (i : Reg) :
    physicalOutput f input i = transport
      (matrixLocation (1 : Matrix Index Index (Scalar f))) (input i) := by
  funext a
  rw [physicalOutput, executePhysical_correct]
  unfold idealWire
  rw [sinkWire_head]
  have hc := actualCode_correct Parameters.d
    (fun j => logicalInput f input j
      ((matrixLocation (nodeMatrix f (.sink (globalSwap i)))).symm a)) i
  change NetworkProtocol.edgeValue (actualNetwork Parameters.d) (actualCode Parameters.d)
    (fun j => logicalInput f input j
      ((matrixLocation (nodeMatrix f (.sink (globalSwap i)))).symm a))
    (sinkWire (globalProgram Parameters.d) (globalSwap i)) = _ at hc
  rw [hc]
  unfold logicalInput transport
  rw [matrixLocation_after_inverse, reduced_endpoint_identity]

/-- The edge-transformer interface is invoked on complete bit streams;
the actual gate computation supplies its input, not an assumed transcript. -/
def physicalWireWith (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)) (e : Edge) :=
  move e (fun a => (actualCode Parameters.d).localMap ((actualNetwork Parameters.d).tail e)
    (fun port => match port with
      | .inl i => input i.val a
      | .inr incoming => stored incoming.val a) ⟨e,rfl⟩)

theorem physicalWireWith_eq (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (stored : DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f)
    (move : Edge →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit))
    (hmove : ∀ e F, move e F = transport (matrixLocation (reducedEdgeMatrix f e)) F)
    (e : Edge) : physicalWireWith f input stored move e = physicalWire f input stored e := by
  unfold physicalWireWith
  rw [hmove]
  rfl

def executeLayersWith (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (move : Edge →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)) :
    ℕ → DiskState (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f
  | 0 => fun _ _ => 0
  | t+1 => fun e => if e.1.val = t then
      physicalWireWith f input (executeLayersWith f input move t) move e
      else executeLayersWith f input move t e

theorem executeLayersWith_eq (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (move : Edge →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit))
    (hmove : ∀ e F, move e F = transport (matrixLocation (reducedEdgeMatrix f e)) F)
    (t : ℕ) : executeLayersWith f input move t = executeLayers f input t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext e
    simp only [executeLayersWith, executeLayers, ih, physicalWireWith_eq f input _ move hmove]

/-- Every physical edge in the eager topological execution invokes the
factorized array program, which in turn really calls each short child. -/
def executeFactored (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (child : Child →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)) :=
  executeLayersWith f input (fun e => edgeStreamProgram f e (fun p => child ⟨e,p⟩))
    ((globalProgram Parameters.d).length+1)

theorem executeFactored_correct (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (child : Child →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit))
    (hchild : ∀ c F, child c F = transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F) :
    executeFactored f input child = executePhysical f input := by
  apply executeLayersWith_eq
  intro e F
  apply edgeStreamProgram_correct
  intro p stream
  exact hchild ⟨e,p⟩ stream

theorem factored_sink_correct (f : ℕ)
    (input : Reg → LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit)
    (child : Child →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit) →
      (LongAddress (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) f → Bit))
    (hchild : ∀ c F, child c F = transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F)
    (i : Reg) :
    executeFactored f input child (sinkWire (globalProgram Parameters.d) (globalSwap i)) =
      transport (matrixLocation (1 : Matrix Index Index (Scalar f))) (input i) := by
  rw [executeFactored_correct f input child hchild]
  exact physicalOutput_correct f input i

/-- At layer t the eager evaluator invokes each edge (t,r) once. Expanding
its list of pivot calls gives exactly the same physical rank budget S. -/
theorem eager_child_count :
    (∑ t : Fin ((globalProgram Parameters.d).length+1),
      ∑ r : Reg, (edgePivots (t,r)).length) = Parameters.S := by
  simp_rw [edgePivots_length]
  simpa only [Edge, Wire, Fintype.sum_prod_type] using edge_rank_sum

end PhysicalExecution

section WholeLevel

variable {Rows : ℕ} {Gap Suffix : Type*}

/-- Cyclic distribution of complete prefix segments; internal coordinates
are unchanged, and role i is the remainder modulo W. -/
def splitPrefix (f : ℕ) :
    FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix ≃
      Reg × FullAddress (Fin Rows) (Field f) Gap Suffix where
  toFun a := (roleEnumeration.symm a.prefixCoord.modNat,
    ⟨a.prefixCoord.divNat,a.high,a.gap,a.low,a.suffix⟩)
  invFun a := ⟨finProdFinEquiv (a.2.prefixCoord,roleEnumeration a.1),
    a.2.high,a.2.gap,a.2.low,a.2.suffix⟩
  left_inv a := by
    cases a with
    | mk p h g d s =>
      simp only [Equiv.apply_symm_apply]
      exact congrArg (fun x => FullAddress.mk x h g d s) (finProdFinEquiv.apply_symm_apply p)
  right_inv a := by
    rcases a with ⟨r,p,h,g,d,s⟩
    have hs := finProdFinEquiv.symm_apply_apply (p,roleEnumeration r)
    have hp : (finProdFinEquiv (p,roleEnumeration r)).divNat = p := congrArg Prod.fst hs
    have hr : (finProdFinEquiv (p,roleEnumeration r)).modNat = roleEnumeration r := congrArg Prod.snd hs
    simp only [hp,hr,Equiv.symm_apply_apply]

def splitInput (f : ℕ)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :
    Reg → FullAddress (Fin Rows) (Field f) Gap Suffix → Bit :=
  fun r a => F ((splitPrefix f).symm (r,a))

def gatherOutput (f : ℕ)
    (output : Reg → FullAddress (Fin Rows) (Field f) Gap Suffix → Bit) :
    FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit :=
  fun a => output ((splitPrefix f) a).1 ((splitPrefix f) a).2

theorem gather_splitInput (f : ℕ)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :
    gatherOutput f (splitInput f F) = F := by
  funext a
  exact congrArg F ((splitPrefix f).symm_apply_apply a)

theorem gather_transported_split (f : ℕ) (M : Matrix Index Index (Scalar f))
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :
    gatherOutput f (fun r => transport (matrixLocation M) (splitInput f F r)) =
      transport (matrixLocation M) F := by
  funext a
  cases a with
  | mk p h g d s =>
    simp only [gatherOutput, splitInput, splitPrefix, transport, matrixLocation,
      mapPairEquiv, mapPair, shear, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      Equiv.apply_symm_apply]
    exact congrArg (fun x => F ⟨x,h-M.mulVec d,g,d,s⟩)
      (finProdFinEquiv.apply_symm_apply p)

def factoredMiddle (f : ℕ)
    (child : Child →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit) →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit))
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :=
  gatherOutput f (fun i => executeFactored f (splitInput f F) child
    (sinkWire (globalProgram Parameters.d) (globalSwap i)))

theorem factoredMiddle_correct (f : ℕ)
    (child : Child →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit) →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit))
    (hchild : ∀ c F, child c F = transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :
    factoredMiddle f child F = transport (matrixLocation (1 : Matrix Index Index (Scalar f))) F := by
  unfold factoredMiddle
  simp_rw [factored_sink_correct f _ child hchild]
  exact gather_transported_split f 1 F

def factoredFullExchange (f : ℕ)
    (child : Child →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit) →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit))
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :=
  transport (mapPairEquiv lowerReflectEquiv)
    (factoredMiddle f child (transport (mapPairEquiv lowerSubtractEquiv) F))

theorem factoredFullExchange_correct (f : ℕ)
    (child : Child →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit) →
      (FullAddress (Fin Rows) (Field f) Gap Suffix → Bit))
    (hchild : ∀ c F, child c F = transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F)
    (F : FullAddress (Fin (Rows * Parameters.W)) (Field f) Gap Suffix → Bit) :
    factoredFullExchange f child F = transport exchangeEquiv F := by
  unfold factoredFullExchange
  rw [factoredMiddle_correct f child hchild, matrixLocation_one,
    transport_comp, transport_comp, full_three_step_exchange]

end WholeLevel

/-- The literal gate frame list after the joint modular specialization. -/
def gateFrames (f : ℕ) (t : ℕ) : Matrix Index Index (Scalar f) :=
  if ht : t < (globalProgram Parameters.d).length then nodeMatrix f (.gate ⟨t, ht⟩) else 0

section OneLevel

variable {Prefix Gap Suffix : Type*} {Rows : ℕ}

/-- Execute all three updates using the actual XOR gate list, actual
specialized node frames, source conversion and final sink conversion. -/
def oneLevel (f : ℕ)
    (F : Fin (Rows * Parameters.W) → FullAddress Prefix (Field f) Gap Suffix → Bit) :
    Fin (Rows * Parameters.W) → FullAddress Prefix (Field f) Gap Suffix → Bit :=
  exchangeViaFiniteProgramTo roleEnumeration
    (matrixStages (globalProgram Parameters.d) (gateFrames f))
    (fun r => rowMatrixLocation (nodeMatrix f (.source r)))
    (fun r => rowMatrixLocation (nodeMatrix f (.sink r))) globalSwap F

theorem oneLevel_correct (f : ℕ)
    (F : Fin (Rows * Parameters.W) → FullAddress Prefix (Field f) Gap Suffix → Bit) :
    oneLevel f F = Streams.insideRows exchangeEquiv F := by
  apply matrixFiniteProgram_exchange_correct
  · intro s
    change runProgram (globalProgram Parameters.d) s = fun r => s (globalSwap r)
    exact globalProgram_correct s
  · exact reduced_endpoint_identity f

end OneLevel

theorem short_field_card (f : ℕ) : Fintype.card (Scalar f) = radix ^ f :=
  ZMod.card _

theorem long_field_card (f : ℕ) : Fintype.card (Field f) = radix ^ (Parameters.m * f) := by
  simp only [Field, Fintype.card_fun, short_field_card, actual_matrix_card]
  rw [← pow_mul, Nat.mul_comm]

theorem child_width (f : ℕ) : (Parameters.m * f) / Parameters.m = f := by
  exact Nat.mul_div_cancel_left f (by norm_num [Parameters.m_value])

section Reshaping

variable {P H G S P' H' G' S' α β Value : Type*}

/-- Rename dimensions independently. The same field equivalence is applied
to H and D, so this reshaping commutes with their complete exchange. -/
def addressShape (ep : P ≃ P') (eh : H ≃ H') (eg : G ≃ G') (es : S ≃ S') :
    FullAddress P H G S ≃ FullAddress P' H' G' S' where
  toFun a := ⟨ep a.prefixCoord,eh a.high,eg a.gap,eh a.low,es a.suffix⟩
  invFun a := ⟨ep.symm a.prefixCoord,eh.symm a.high,eg.symm a.gap,eh.symm a.low,es.symm a.suffix⟩
  left_inv a := by cases a; simp only [Equiv.symm_apply_apply]
  right_inv a := by cases a; simp only [Equiv.apply_symm_apply]

theorem addressShape_exchange (ep : P ≃ P') (eh : H ≃ H') (eg : G ≃ G') (es : S ≃ S')
    (a : FullAddress P H G S) :
    addressShape ep eh eg es (exchange a) = exchange (addressShape ep eh eg es a) := rfl

/-- Execute a transformer in a different, explicitly equivalent coordinate
description. This applies the transformer to the actual data array. -/
def viaShape (e : α ≃ β) (op : (β → Value) → (β → Value)) (F : α → Value) : α → Value :=
  fun a => op (fun b => F (e.symm b)) (e a)

theorem viaShape_transport (e : α ≃ β) (perm : Equiv.Perm β) (F : α → Value) :
    viaShape e (transport perm) F = transport (e.trans (perm.trans e.symm)) F := rfl

theorem viaShape_exchange (ep : P ≃ P') (eh : H ≃ H') (eg : G ≃ G') (es : S ≃ S')
    (F : FullAddress P H G S → Value) :
    viaShape (addressShape ep eh eg es) (transport exchangeEquiv) F = transport exchangeEquiv F := by
  funext a
  cases a
  simp only [viaShape, addressShape, transport, exchangeEquiv, exchange, Equiv.coe_fn_mk,
    Equiv.coe_fn_symm_mk, Equiv.symm_apply_apply]

theorem viaShape_shortExchange (f : ℕ) (c : Child)
    (F : LongAddress (Prefix := P) (Gap := G) (Suffix := S) f → Value) :
    viaShape (childRepack f c) (transport exchangeEquiv) F =
      transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) F := by
  rw [viaShape_transport]
  unfold childRepack
  rw [SingleCoordinate.shortExchange_eq_regrouped]

end Reshaping

/-! Canonical field and prefix packing for the recursive function. The
finite-function packer puts earlier coordinates at higher significance. -/

def blockPacking (f : ℕ) : Field f ≃ Scalar (Parameters.m * f) :=
  (FieldPacking.vectorFinPacking Index radix f).trans
    ((finCongr (by rw [actual_matrix_card, ← pow_mul, Nat.mul_comm f Parameters.m])).trans
      (ZMod.finEquiv (radix ^ (Parameters.m * f))).toEquiv)

def splitLongField (baseWidth k : ℕ) :
    Scalar (baseWidth * Parameters.m ^ (k+1)) ≃ Field (baseWidth * Parameters.m ^ k) :=
  (Equiv.cast (congrArg Scalar (show baseWidth * Parameters.m ^ (k+1) =
    Parameters.m * (baseWidth * Parameters.m ^ k) by rw [pow_succ]; ring))).trans
      (blockPacking (baseWidth * Parameters.m ^ k)).symm

def beforeCard (f : ℕ) (i : Index) :=
  (radix ^ f) ^ Fintype.card (SingleCoordinate.Before i)

def childPrefixLayout (baseWidth k rows : ℕ) (c : Child) :
    SingleCoordinate.ShortPrefix (Prefix := Fin (rows * Parameters.W ^ k))
      (R := Scalar (baseWidth * Parameters.m ^ k)) (childRow c) ≃
    Fin ((rows * beforeCard (baseWidth * Parameters.m ^ k) (childRow c)) * Parameters.W ^ k) :=
  (Equiv.prodCongr (Equiv.refl _)
    (FieldPacking.vectorFinPacking (SingleCoordinate.Before (childRow c)) radix
      (baseWidth * Parameters.m ^ k))).trans
    (finProdFinEquiv.trans (finCongr (by unfold beforeCard; ring)))

def parentPrefixLayout {Prefix : Type*} (k rows : ℕ)
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ (k+1))) :
    Prefix ≃ Fin ((rows * Parameters.W ^ k) * Parameters.W) :=
  layout.trans (finCongr (by rw [pow_succ, Nat.mul_assoc]))

/-- The recursive array algorithm at exact scales. Prefix divisibility is
encoded by its explicit layout type. In a branch, children are actual calls
at depth k on the two selected scalar fields, with canonically regrouped
prefixes. Every spectator remains in its original relative order. -/
def recursiveExchange (baseWidth : ℕ) :
    (k rows : ℕ) → {Prefix Gap Suffix : Type} →
    (Prefix ≃ Fin (rows * Parameters.W ^ k)) →
    (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) →
    (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit)
  | 0, _, _, _, _, _, F => transport exchangeEquiv F
  | k+1, rows, _, Gap, Suffix, layout, F =>
      let f := baseWidth * Parameters.m ^ k
      let child : Child →
          (FullAddress (Fin (rows * Parameters.W^k)) (Field f) Gap Suffix → Bit) →
          (FullAddress (Fin (rows * Parameters.W^k)) (Field f) Gap Suffix → Bit) :=
        fun c => viaShape (childRepack f c)
        (recursiveExchange baseWidth k (rows * beforeCard f (childRow c))
          (childPrefixLayout baseWidth k rows c))
      viaShape (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
        (Equiv.refl _) (Equiv.refl _)) (factoredFullExchange f child) F

/-- Functional correctness is proved by induction on actual smaller-width
calls; no correct child exchange is supplied as an external hypothesis. -/
theorem recursiveExchange_correct (baseWidth k rows : ℕ) {Prefix Gap Suffix : Type}
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) :
    recursiveExchange baseWidth k rows layout F = transport exchangeEquiv F := by
  induction k generalizing rows Prefix Gap Suffix with
  | zero => rfl
  | succ k ih =>
    let f := baseWidth * Parameters.m ^ k
    let child : Child →
        (FullAddress (Fin (rows * Parameters.W^k)) (Field f) Gap Suffix → Bit) →
        (FullAddress (Fin (rows * Parameters.W^k)) (Field f) Gap Suffix → Bit) :=
      fun c => viaShape (childRepack f c)
        (recursiveExchange baseWidth k (rows * beforeCard f (childRow c))
          (childPrefixLayout baseWidth k rows c))
    have hc : ∀ c stream, child c stream =
        transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) stream := by
      intro c stream
      have hh : recursiveExchange baseWidth k (rows * beforeCard f (childRow c))
          (Gap := SingleCoordinate.ShortGap (Gap := Gap) (R := Scalar f) (childRow c) (childCol c))
          (Suffix := SingleCoordinate.ShortSuffix (Suffix := Suffix) (R := Scalar f) (childCol c))
          (childPrefixLayout baseWidth k rows c) = transport exchangeEquiv := by
        funext input
        exact ih _ _ input
      change viaShape (childRepack f c) _ stream = _
      rw [hh]
      exact viaShape_shortExchange f c stream
    change viaShape (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
      (Equiv.refl Gap) (Equiv.refl Suffix)) (factoredFullExchange f child) F = _
    have hl : factoredFullExchange f child = transport
        (exchangeEquiv : Equiv.Perm (FullAddress (Fin ((rows * Parameters.W^k) * Parameters.W))
          (Field f) Gap Suffix)) := by
      funext stream
      exact factoredFullExchange_correct f child hc stream
    rw [hl]
    exact viaShape_exchange _ _ _ _ F

/-! Address cardinalities refer to the very dependent shapes passed to
`recursiveExchange`, including all spectators. -/

def fullAddressTuple {P H G S : Type} :
    FullAddress P H G S ≃ P × H × G × H × S where
  toFun a := (a.prefixCoord,a.high,a.gap,a.low,a.suffix)
  invFun x := ⟨x.1,x.2.1,x.2.2.1,x.2.2.2.1,x.2.2.2.2⟩
  left_inv a := by cases a; rfl
  right_inv x := by rcases x with ⟨p,h,g,d,s⟩; rfl

instance fullAddressFintype {P H G S : Type}
    [Fintype P] [Fintype H] [Fintype G] [Fintype S] :
    Fintype (FullAddress P H G S) :=
  Fintype.ofEquiv (P × H × G × H × S) fullAddressTuple.symm

theorem fullAddress_card {P H G S : Type}
    [Fintype P] [Fintype H] [Fintype G] [Fintype S] :
    Fintype.card (FullAddress P H G S) =
      Fintype.card P * Fintype.card H * Fintype.card G * Fintype.card H * Fintype.card S := by
  rw [Fintype.card_congr fullAddressTuple]
  simp only [Fintype.card_prod]
  ring

theorem recursive_volume_multiple (baseWidth k rows : ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k)) :
    Parameters.W ^ k ∣
      Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) := by
  have hp : Fintype.card Prefix = rows * Parameters.W ^ k := by
    simpa only [Fintype.card_fin] using Fintype.card_congr layout
  rw [fullAddress_card, hp]
  refine ⟨rows * Fintype.card (Scalar (baseWidth * Parameters.m ^ k)) *
    Fintype.card Gap * Fintype.card (Scalar (baseWidth * Parameters.m ^ k)) * Fintype.card Suffix, ?_⟩
  ring

abbrev RecursiveChildAddress (baseWidth k rows : ℕ) (Gap Suffix : Type) (c : Child) :=
  FullAddress
    (SingleCoordinate.ShortPrefix (Prefix := Fin (rows * Parameters.W ^ k))
      (R := Scalar (baseWidth * Parameters.m ^ k)) (childRow c))
    (Scalar (baseWidth * Parameters.m ^ k))
    (SingleCoordinate.ShortGap (Gap := Gap) (R := Scalar (baseWidth * Parameters.m ^ k))
      (childRow c) (childCol c))
    (SingleCoordinate.ShortSuffix (Suffix := Suffix) (R := Scalar (baseWidth * Parameters.m ^ k))
      (childCol c))

/-- This is the partition actually used by the recursive interpreter:
canonical parent field splitting, cyclic role splitting, then ordered
regrouping around the selected short fields. -/
def recursivePartition (baseWidth k rows : ℕ) {Prefix Gap Suffix : Type}
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ (k+1))) (c : Child) :
    FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ (k+1))) Gap Suffix ≃
      Reg × RecursiveChildAddress baseWidth k rows Gap Suffix c :=
  (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
    (Equiv.refl _) (Equiv.refl _)).trans
    ((splitPrefix (baseWidth * Parameters.m ^ k)).trans
      (Equiv.prodCongr (Equiv.refl Reg) (childRepack (baseWidth * Parameters.m ^ k) c)))

theorem recursive_child_volume (baseWidth k rows : ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ (k+1))) (c : Child) :
    Fintype.card (RecursiveChildAddress baseWidth k rows Gap Suffix c) =
      Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ (k+1))) Gap Suffix) /
        Parameters.W := by
  letI : Fintype (RecursiveChildAddress baseWidth k rows Gap Suffix c) := inferInstance
  have h := Fintype.card_congr (recursivePartition baseWidth k rows (Gap := Gap) (Suffix := Suffix) layout c)
  rw [Fintype.card_prod, actual_sessions_card] at h
  rw [h]
  exact (Nat.mul_div_cancel_left _ (by norm_num [Parameters.W_value])).symm

/-- This explicit finite list visits every physical edge, including source,
pass and terminal edges, and emits its actual pivot positions in order. -/
def childSchedule : List Child :=
  (Finset.univ : Finset Edge).toList.flatMap fun e =>
    (Finset.univ : Finset (EdgeChild e)).toList.map (Sigma.mk e)

theorem childSchedule_length : childSchedule.length = Parameters.S := by
  simp only [childSchedule, List.length_flatMap, List.length_map, Finset.length_toList]
  rw [Finset.sum_map_toList]
  simp only [Finset.card_univ]
  simpa only [Fintype.card_sigma] using child_count

theorem childSchedule_mem (c : Child) : c ∈ childSchedule := by
  rcases c with ⟨e,c⟩
  apply List.mem_flatMap.mpr
  refine ⟨e, by simp, ?_⟩
  exact List.mem_map.mpr ⟨c, by simp, rfl⟩

theorem childSchedule_nodup : childSchedule.Nodup := by
  change ((Finset.univ : Finset Edge).toList.sigma
    (fun e => (Finset.univ : Finset (EdgeChild e)).toList)).Nodup
  exact List.Nodup.sigma (Finset.nodup_toList _) (fun _ => Finset.nodup_toList _)

theorem childSchedule_count (c : Child) : childSchedule.count c = 1 := by
  classical
  exact List.count_eq_one_of_mem childSchedule_nodup (childSchedule_mem c)

section Volumes

variable {Inner : Type*} [Fintype Inner]

/-- Every child acts on one complete role stream, including all spectator
coordinates. Its cardinality is a consequence of the row splitter. -/
def childVolume (rows : ℕ) (_ : Child) : ℕ := Fintype.card (Fin rows × Inner)

def parentVolume (rows : ℕ) : ℕ := Fintype.card (Fin (rows * Parameters.W) × Inner)

theorem child_volume_eq_div (rows : ℕ) (c : Child) :
    childVolume (Inner := Inner) rows c = parentVolume (Inner := Inner) rows / Parameters.W := by
  apply Streams.role_stream_card_eq_div
  norm_num [Parameters.W_value]

theorem all_children_volume (rows : ℕ) :
    (∑ c : Child, childVolume (Inner := Inner) rows c) =
      Parameters.S * (parentVolume (Inner := Inner) rows / Parameters.W) := by
  simp_rw [child_volume_eq_div]
  simp only [Finset.sum_const, Finset.card_univ, child_count, smul_eq_mul]

end Volumes

/-! The tree retains the actual edge/pivot identity on every branch. Costs
are read from the primitive implementation supplied to its leaves and local
nodes; they are not defined to satisfy a desired recurrence. -/

inductive CallTree where
  | stop (width volume charge : ℕ)
  | level (width volume localCharge : ℕ) (children : Child → CallTree)

namespace CallTree

def cost : CallTree → ℕ
  | .stop _ _ charge => charge
  | .level _ _ localCharge children => localCharge + ∑ c, cost (children c)

def leafCount : CallTree → ℕ
  | .stop _ _ _ => 1
  | .level _ _ _ children => ∑ c, leafCount (children c)

def build (baseWidth : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) : ℕ → ℕ → CallTree
  | 0, volume => .stop baseWidth volume (baseCharge volume)
  | k+1, volume => .level (baseWidth * Parameters.m^(k+1)) volume
      (levelCharge k volume)
      (fun _ => build baseWidth baseCharge levelCharge k (volume / Parameters.W))

/-- This cost equation is obtained by traversing the concrete rank-indexed
tree. The multiplier S is proved from the real edge labels above. -/
theorem build_cost_succ (baseWidth : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (k volume : ℕ) :
    cost (build baseWidth baseCharge levelCharge (k+1) volume) =
      levelCharge k volume + Parameters.S *
        cost (build baseWidth baseCharge levelCharge k (volume / Parameters.W)) := by
  simp only [build, cost, Finset.sum_const, Finset.card_univ, child_count, smul_eq_mul]

theorem build_leaf_count (baseWidth : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (k volume : ℕ) :
    leafCount (build baseWidth baseCharge levelCharge k volume) = Parameters.S ^ k := by
  induction k generalizing volume with
  | zero => simp [build, leafCount]
  | succ k ih =>
    simp only [build, leafCount, ih, Finset.sum_const, Finset.card_univ, child_count,
      smul_eq_mul, pow_succ]
    exact Nat.mul_comm _ _

def scaledVolume (bottomVolume depth : ℕ) : ℕ := bottomVolume * Parameters.W ^ depth

theorem scaledVolume_child (bottomVolume depth : ℕ) :
    scaledVolume bottomVolume (depth+1) / Parameters.W = scaledVolume bottomVolume depth := by
  unfold scaledVolume
  rw [pow_succ, ← Nat.mul_assoc]
  exact Nat.mul_div_cancel _ (by norm_num [Parameters.W_value])

def normalizedCost (baseWidth bottomVolume : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (depth : ℕ) : ℝ :=
  (cost (build baseWidth baseCharge levelCharge depth (scaledVolume bottomVolume depth)) : ℝ) /
    (scaledVolume bottomVolume depth : ℝ)

/-- Derived normalized recurrence for the actual branch schedule. The only
remaining cost premise is a local bound on the primitive implementation's
charge; there is no assumed global recursive cost inequality. -/
theorem normalizedCost_step (baseWidth bottomVolume : ℕ) (hV : 0 < bottomVolume)
    (baseCharge : ℕ → ℕ) (levelCharge : ℕ → ℕ → ℕ) (C : ℝ)
    (hlocal : ∀ k, (levelCharge k (scaledVolume bottomVolume (k+1)) : ℝ) ≤
      C * (scaledVolume bottomVolume (k+1) : ℝ)) (k : ℕ) :
    normalizedCost baseWidth bottomVolume baseCharge levelCharge (k+1) ≤
      ((Parameters.S : ℝ) / (Parameters.W : ℝ)) *
        normalizedCost baseWidth bottomVolume baseCharge levelCharge k + C := by
  have hW : (0 : ℝ) < (Parameters.W : ℝ) := by norm_num [Parameters.W_value]
  have hv : (0 : ℝ) < (scaledVolume bottomVolume k : ℝ) := by
    exact_mod_cast Nat.mul_pos hV (pow_pos (by norm_num [Parameters.W_value]) k)
  have hs : (scaledVolume bottomVolume (k+1) : ℝ) =
      (scaledVolume bottomVolume k : ℝ) * (Parameters.W : ℝ) := by
    simp only [scaledVolume, pow_succ, Nat.cast_mul, Nat.cast_pow]
    ring
  unfold normalizedCost
  rw [build_cost_succ, scaledVolume_child]
  push_cast
  rw [hs]
  have hl := hlocal k
  rw [hs] at hl
  apply (div_le_iff₀ (mul_pos hv hW)).2
  have hid : (((Parameters.S : ℝ) / Parameters.W) *
      ((cost (build baseWidth baseCharge levelCharge k (scaledVolume bottomVolume k)) : ℝ) /
        scaledVolume bottomVolume k) + C) *
      ((scaledVolume bottomVolume k : ℝ) * Parameters.W) =
      (Parameters.S : ℝ) *
        cost (build baseWidth baseCharge levelCharge k (scaledVolume bottomVolume k)) +
        C * ((scaledVolume bottomVolume k : ℝ) * Parameters.W) := by
    field_simp
    try ring
  rw [hid]
  linarith

/-- The local bound hstep is proved by traversing the concrete edge and pivot tree, then supplied to the recurrence theorem. 
-/
theorem normalizedCost_power_bound (baseWidth bottomVolume : ℕ) (hV : 0 < bottomVolume)
    (baseCharge : ℕ → ℕ) (levelCharge : ℕ → ℕ → ℕ)
    (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : (baseCharge bottomVolume : ℝ) ≤ A * bottomVolume)
    (hlocal : ∀ k, (levelCharge k (scaledVolume bottomVolume (k+1)) : ℝ) ≤
      C * (scaledVolume bottomVolume (k+1) : ℝ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k,
      normalizedCost baseWidth bottomVolume baseCharge levelCharge k ≤
        K * (Parameters.m : ℝ)^((k : ℝ) * (1 - (Parameters.epsilon : ℝ))) := by
  apply Recurrence.paper_normalized_recurrence_bound _ C A hC hA
  · unfold normalizedCost
    simp only [scaledVolume, pow_zero, Nat.mul_one, build, cost]
    exact (div_le_iff₀ (show (0 : ℝ) < bottomVolume by exact_mod_cast hV)).2 hbase
  · exact normalizedCost_step baseWidth bottomVolume hV baseCharge levelCharge C hlocal

/-- A single constant works for every bottom volume and hence every
actual shape. Only local primitive bounds are hypotheses. -/
def uniformConstant (C A : ℝ) : ℝ := A + C /
  ((Parameters.m : ℝ)^(1-(Parameters.epsilon : ℝ)) - (Parameters.S : ℝ)/Parameters.W)

theorem uniform_power_bound (baseWidth : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : ∀ V, (baseCharge V : ℝ) ≤ A * V)
    (hlocal : ∀ k V, (levelCharge k V : ℝ) ≤ C * V)
    (bottom : ℕ) (hV : 0 < bottom) (k : ℕ) :
    normalizedCost baseWidth bottom baseCharge levelCharge k ≤
      uniformConstant C A * (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) := by
  let R : ℝ := (Parameters.m : ℝ)^(1-(Parameters.epsilon : ℝ))
  let lam : ℝ := (Parameters.S : ℝ)/Parameters.W
  have hgap : lam < R := Parameters.strict_exponent_gap
  have hden : 0 < R-lam := sub_pos.mpr hgap
  have hdiv : 0 ≤ C/(R-lam) := div_nonneg hC hden.le
  have hbaseF : normalizedCost baseWidth bottom baseCharge levelCharge 0 ≤ A := by
    unfold normalizedCost
    simp only [scaledVolume, pow_zero, Nat.mul_one, build, cost]
    exact (div_le_iff₀ (show (0 : ℝ) < bottom by exact_mod_cast hV)).2 (hbase bottom)
  have hbudget : C ≤ uniformConstant C A * (R-lam) := by
    have hc : C/(R-lam)*(R-lam)=C := div_mul_cancel₀ C hden.ne'
    have ha := mul_nonneg hA hden.le
    change C ≤ (A+C/(R-lam))*(R-lam)
    nlinarith
  have hR : 1 ≤ R := Real.one_le_rpow
    (by norm_num [Parameters.m_value])
    (by have he := Parameters.epsilon_lt_one; exact_mod_cast sub_nonneg.mpr he.le)
  have hb : normalizedCost baseWidth bottom baseCharge levelCharge 0 ≤ uniformConstant C A :=
    hbaseF.trans (le_add_of_nonneg_right hdiv)
  have h := Recurrence.power_bound
    (normalizedCost baseWidth bottom baseCharge levelCharge) lam C (uniformConstant C A) R
    (by positivity) hC hR hb hbudget
    (normalizedCost_step baseWidth bottom hV baseCharge levelCharge C
      (fun j => hlocal j _) ) k
  have hp : (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) = R^k := by
    try dsimp only [R]
    rw [mul_comm, Real.rpow_mul_natCast (by positivity)]
  rw [hp]
  exact h

theorem uniformConstant_nonneg (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A) :
    0 ≤ uniformConstant C A :=
  add_nonneg hA (div_nonneg hC (sub_pos.mpr Parameters.strict_exponent_gap).le)

/-- Stop an actual call once its entire data fits the reserved in-memory
region. Parent and child volumes are still recorded separately. -/
def prunedBuild (baseWidth cutoff : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) : ℕ → ℕ → CallTree
  | 0, V => .stop baseWidth V (baseCharge V)
  | k+1, V => if V ≤ cutoff then .stop (baseWidth * Parameters.m^(k+1)) V (baseCharge V)
      else .level (baseWidth * Parameters.m^(k+1)) V (levelCharge k V)
        (fun _ => prunedBuild baseWidth cutoff baseCharge levelCharge k (V / Parameters.W))

end CallTree

/-- The functional transformer and its resource tree are emitted together.
Local primitive charges remain explicit until scan implementations supply them. -/
structure ChargedExchange (Addr : Type) where
  run : (Addr → Bit) → (Addr → Bit)
  calls : CallTree

/-- Instrumentation of the actual recursive interpreter. In particular the
child used in the parent's array computation and the child whose cost is
recorded below are the same recursively compiled object. -/
def chargedExchange (baseWidth : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) :
    (k rows : ℕ) → {Prefix Gap Suffix : Type} →
    [Fintype Prefix] → [Fintype Gap] → [Fintype Suffix] →
    (Prefix ≃ Fin (rows * Parameters.W ^ k)) →
    ChargedExchange (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix)
  | 0, _, Prefix, Gap, Suffix, _, _, _, _ =>
      let volume := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ 0)) Gap Suffix)
      ⟨transport exchangeEquiv, .stop baseWidth volume (baseCharge volume)⟩
  | k+1, rows, Prefix, Gap, Suffix, _, _, _, layout =>
      let f := baseWidth * Parameters.m ^ k
      let children : (c : Child) → ChargedExchange (RecursiveChildAddress baseWidth k rows Gap Suffix c) :=
        fun c => chargedExchange baseWidth baseCharge levelCharge k
          (rows * beforeCard f (childRow c)) (childPrefixLayout baseWidth k rows c)
      let volume := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ (k+1))) Gap Suffix)
      ⟨viaShape (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
          (Equiv.refl _) (Equiv.refl _))
        (factoredFullExchange f (fun c => viaShape (childRepack f c) (children c).run)),
        .level (baseWidth * Parameters.m^(k+1)) volume (levelCharge k volume)
          (fun c => (children c).calls)⟩

theorem chargedExchange_run (baseWidth k rows : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k)) :
    (chargedExchange baseWidth baseCharge levelCharge k rows layout).run =
      (recursiveExchange baseWidth k rows layout :
        (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) → _) := by
  induction k generalizing rows Prefix Gap Suffix with
  | zero => rfl
  | succ k ih =>
    try dsimp only [chargedExchange, recursiveExchange]
    simp only [ih]

theorem chargedExchange_correct (baseWidth k rows : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) :
    (chargedExchange baseWidth baseCharge levelCharge k rows layout).run F =
      transport exchangeEquiv F := by
  rw [chargedExchange_run]
  exact recursiveExchange_correct baseWidth k rows layout F

/-- Erasing the actual dependent address shapes yields the numerical tree,
with V/W justified by the concrete partition equivalence at every node. -/
theorem chargedExchange_calls (baseWidth k rows : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k)) :
    (chargedExchange baseWidth baseCharge levelCharge k rows layout
      (Gap := Gap) (Suffix := Suffix)).calls =
      CallTree.build baseWidth baseCharge levelCharge k
        (Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix)) := by
  induction k generalizing rows Prefix Gap Suffix with
  | zero => rfl
  | succ k ih =>
    try dsimp only [chargedExchange, CallTree.build]
    congr 1
    funext c
    rw [ih]
    rw [recursive_child_volume baseWidth k rows layout c]

/-- The recurrence bounds the cost of the same program that performs the recursive array transformation, for every permitted array shape. 
-/
theorem chargedExchange_cost_bound (baseWidth k rows : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (C A : ℝ) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : ∀ V, (baseCharge V : ℝ) ≤ A * V)
    (hlocal : ∀ j V, (levelCharge j V : ℝ) ≤ C * V)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (hV : 0 < Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix)) :
    (CallTree.cost (chargedExchange baseWidth baseCharge levelCharge k rows layout
      (Gap := Gap) (Suffix := Suffix)).calls : ℝ) ≤
      CallTree.uniformConstant C A *
        (Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) : ℝ) *
        (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) := by
  let V := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix)
  let bottom := V / Parameters.W^k
  have hs : CallTree.scaledVolume bottom k = V :=
    Nat.div_mul_cancel (recursive_volume_multiple baseWidth k rows layout)
  have hb : 0 < bottom := by
    by_contra h
    have hz : bottom = 0 := Nat.eq_zero_of_not_pos h
    rw [CallTree.scaledVolume, hz, zero_mul] at hs
    exact (Nat.ne_of_gt hV) hs.symm
  have h := CallTree.uniform_power_bound baseWidth baseCharge levelCharge C A hC hA hbase hlocal bottom hb k
  unfold CallTree.normalizedCost at h
  rw [hs] at h
  have hvR : (0 : ℝ) < V := by exact_mod_cast hV
  have hm := (div_le_iff₀ hvR).mp h
  rw [chargedExchange_calls]
  change (CallTree.cost (CallTree.build baseWidth baseCharge levelCharge k V) : ℝ) ≤ _
  calc
    _ ≤ (CallTree.uniformConstant C A *
        (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) * V := hm
    _ = _ := by ring

/-- The in-memory cutoff is decided on the complete data volume, rather
than on the selected field width alone. -/
def cutoffExchange (baseWidth cutoff : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) :
    (k rows : ℕ) → {Prefix Gap Suffix : Type} →
    [Fintype Prefix] → [Fintype Gap] → [Fintype Suffix] →
    (Prefix ≃ Fin (rows * Parameters.W ^ k)) →
    ChargedExchange (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix)
  | 0, _, Prefix, Gap, Suffix, _, _, _, _ =>
      let V := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ 0)) Gap Suffix)
      ⟨transport exchangeEquiv, .stop baseWidth V (baseCharge V)⟩
  | k+1, rows, Prefix, Gap, Suffix, _, _, _, layout =>
      let V := Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ (k+1))) Gap Suffix)
      if V ≤ cutoff then ⟨transport exchangeEquiv,
        .stop (baseWidth * Parameters.m^(k+1)) V (baseCharge V)⟩
      else
        let f := baseWidth * Parameters.m ^ k
        let children : (c : Child) → ChargedExchange (RecursiveChildAddress baseWidth k rows Gap Suffix c) :=
          fun c => cutoffExchange baseWidth cutoff baseCharge levelCharge k
            (rows * beforeCard f (childRow c)) (childPrefixLayout baseWidth k rows c)
        ⟨viaShape (addressShape (parentPrefixLayout k rows layout) (splitLongField baseWidth k)
            (Equiv.refl _) (Equiv.refl _))
          (factoredFullExchange f (fun c => viaShape (childRepack f c) (children c).run)),
          .level (baseWidth * Parameters.m^(k+1)) V (levelCharge k V)
            (fun c => (children c).calls)⟩

theorem cutoffExchange_correct (baseWidth cutoff k rows : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k))
    (F : FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix → Bit) :
    (cutoffExchange baseWidth cutoff baseCharge levelCharge k rows layout).run F =
      transport exchangeEquiv F := by
  induction k generalizing rows Prefix Gap Suffix with
  | zero => rfl
  | succ k ih =>
    rw [cutoffExchange]
    split_ifs with hfit
    · rfl
    · try dsimp only
      have hc : ∀ (c : Child)
          (stream : FullAddress (Fin (rows * Parameters.W^k)) (Field (baseWidth * Parameters.m^k)) Gap Suffix → Bit),
          viaShape (childRepack (baseWidth * Parameters.m^k) c)
            (cutoffExchange baseWidth cutoff baseCharge levelCharge k
              (rows * beforeCard (baseWidth * Parameters.m^k) (childRow c))
              (childPrefixLayout baseWidth k rows c)).run stream =
            transport (SingleCoordinate.shortExchange (childRow c) (childCol c)) stream := by
        intro c stream
        have hh : (cutoffExchange baseWidth cutoff baseCharge levelCharge k
            (rows * beforeCard (baseWidth * Parameters.m^k) (childRow c))
            (Gap := SingleCoordinate.ShortGap (Gap := Gap) (R := Scalar (baseWidth * Parameters.m^k))
              (childRow c) (childCol c))
            (Suffix := SingleCoordinate.ShortSuffix (Suffix := Suffix) (R := Scalar (baseWidth * Parameters.m^k))
              (childCol c))
            (childPrefixLayout baseWidth k rows c)).run = transport exchangeEquiv := by
          funext input
          exact ih _ _ input
        rw [hh]
        exact viaShape_shortExchange _ c stream
      have hl := funext (factoredFullExchange_correct (baseWidth * Parameters.m^k) _ hc)
      rw [hl]
      exact viaShape_exchange _ _ _ _ F

theorem cutoffExchange_calls (baseWidth cutoff k rows : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) {Prefix Gap Suffix : Type}
    [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k)) :
    (cutoffExchange baseWidth cutoff baseCharge levelCharge k rows layout
      (Gap := Gap) (Suffix := Suffix)).calls =
      CallTree.prunedBuild baseWidth cutoff baseCharge levelCharge k
        (Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix)) := by
  induction k generalizing rows Prefix Gap Suffix with
  | zero => rfl
  | succ k ih =>
    try dsimp only [cutoffExchange, CallTree.prunedBuild]
    split_ifs
    · rfl
    · try dsimp only
      congr 1
      funext c
      rw [ih, recursive_child_volume baseWidth k rows layout c]

namespace CallTree

/-- The cutoff guarantees that every recursively generated child is at
least one block. Its startup cost may therefore be absorbed locally. -/
theorem pruned_child_at_least_block (cutoff block V : ℕ)
    (hcut : Parameters.W * block ≤ cutoff) (hlarge : cutoff < V) :
    block ≤ V / Parameters.W :=
  Recurrence.child_at_least_one_block V Parameters.W block
    (by norm_num [Parameters.W_value]) (hcut.trans hlarge.le)

/-- Resource induction on the actual pruned tree. No global recursive
cost inequality is assumed, and no startup charge is discarded. -/
theorem pruned_cost_power (baseWidth cutoff block : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (C K R : ℝ)
    (hcut : Parameters.W * block ≤ cutoff) (hC : 0 ≤ C) (hK : 0 ≤ K) (hR : 1 ≤ R)
    (hbudget : C ≤ K * (R - (Parameters.S : ℝ)/Parameters.W))
    (hbase : ∀ V, block ≤ V → (baseCharge V : ℝ) * block ≤ K * V)
    (hlocal : ∀ j V, cutoff < V → (levelCharge j V : ℝ) * block ≤ C * V)
    (k V : ℕ) (hV : block ≤ V) :
    (cost (prunedBuild baseWidth cutoff baseCharge levelCharge k V) : ℝ) * block ≤
      K * V * R^k := by
  have hR0 : 0 ≤ R := (by norm_num : (0 : ℝ) ≤ 1).trans hR
  have hW : (0 : ℝ) < (Parameters.W : ℝ) := by norm_num [Parameters.W_value]
  induction k generalizing V with
  | zero => simpa only [prunedBuild,cost,pow_zero,mul_one] using hbase V hV
  | succ k ih =>
    rw [prunedBuild]
    split_ifs with hfit
    · try dsimp only [cost]
      exact (hbase V hV).trans
        (le_mul_of_one_le_right (mul_nonneg hK (Nat.cast_nonneg V)) (one_le_pow₀ hR))
    · have hvchild : block ≤ V / Parameters.W :=
        pruned_child_at_least_block cutoff block V hcut (Nat.lt_of_not_ge hfit)
      have hc := ih (V / Parameters.W) hvchild
      have hvc : ((V / Parameters.W : ℕ) : ℝ) ≤ (V : ℝ)/Parameters.W := by
        apply (le_div_iff₀ hW).2
        exact_mod_cast Nat.div_mul_le_self V Parameters.W
      have hchildren : (Parameters.S : ℝ) *
          ((cost (prunedBuild baseWidth cutoff baseCharge levelCharge k (V / Parameters.W)) : ℝ) * block) ≤
          ((Parameters.S : ℝ)/Parameters.W) * K * V * R^k := by
        calc
          _ ≤ (Parameters.S : ℝ) * (K * (V / Parameters.W : ℕ) * R^k) :=
            mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg _)
          _ ≤ (Parameters.S : ℝ) * (K * ((V : ℝ)/Parameters.W) * R^k) := by
            gcongr
          _ = _ := by ring
      have hloc := hlocal k V (Nat.lt_of_not_ge hfit)
      have hp : 1 ≤ R^k := one_le_pow₀ hR
      have hcscale : C * V ≤ C * ((V : ℝ) * R^k) := by
        nlinarith [mul_le_mul_of_nonneg_left hp (mul_nonneg hC (Nat.cast_nonneg V))]
      have hbud := mul_le_mul_of_nonneg_right hbudget
        (mul_nonneg (Nat.cast_nonneg V) (pow_nonneg hR0 k))
      simp only [cost, Finset.sum_const, Finset.card_univ, child_count, smul_eq_mul]
      push_cast
      calc
        _ = (levelCharge k V : ℝ) * block + (Parameters.S : ℝ) *
            ((cost (prunedBuild baseWidth cutoff baseCharge levelCharge k (V / Parameters.W)) : ℝ) * block) := by ring
        _ ≤ C * V + ((Parameters.S : ℝ)/Parameters.W) * K * V * R^k :=
          add_le_add hloc hchildren
        _ ≤ C * ((V : ℝ) * R^k) + ((Parameters.S : ℝ)/Parameters.W) * K * V * R^k :=
          add_le_add_left hcscale _
        _ ≤ (K * (R - (Parameters.S : ℝ)/Parameters.W)) * ((V : ℝ) * R^k) +
            ((Parameters.S : ℝ)/Parameters.W) * K * V * R^k := add_le_add_left hbud _
        _ = _ := by rw [pow_succ]; ring

end CallTree

namespace CallTree

def growthBase : ℝ := (Parameters.m : ℝ)^(1-(Parameters.epsilon : ℝ))

theorem growthBase_ge_one : 1 ≤ growthBase :=
  Real.one_le_rpow (by norm_num [Parameters.m_value])
    (by have he := Parameters.epsilon_lt_one; exact_mod_cast sub_nonneg.mpr he.le)

theorem growthBase_power (k : ℕ) :
    growthBase^k = (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) := by
  try dsimp only [growthBase]
  rw [mul_comm, Real.rpow_mul_natCast (by positivity)]

theorem uniformConstant_ge (C A : ℝ) (hC : 0 ≤ C) : A ≤ uniformConstant C A :=
  le_add_of_nonneg_right (div_nonneg hC (sub_pos.mpr Parameters.strict_exponent_gap).le)

theorem uniformConstant_budget (C A : ℝ) (hA : 0 ≤ A) :
    C ≤ uniformConstant C A * (growthBase - (Parameters.S : ℝ)/Parameters.W) := by
  have hd : 0 < growthBase - (Parameters.S : ℝ)/Parameters.W :=
    sub_pos.mpr Parameters.strict_exponent_gap
  have hc := div_mul_cancel₀ C hd.ne'
  have ha := mul_nonneg hA hd.le
  unfold uniformConstant
  change C ≤ (A+C/(growthBase-(Parameters.S : ℝ)/Parameters.W)) *
    (growthBase-(Parameters.S : ℝ)/Parameters.W)
  nlinarith

theorem pruned_cost_bound (baseWidth cutoff block : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (C A : ℝ)
    (hcut : Parameters.W * block ≤ cutoff) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : ∀ V, block ≤ V → (baseCharge V : ℝ) * block ≤ A * V)
    (hlocal : ∀ j V, cutoff < V → (levelCharge j V : ℝ) * block ≤ C * V)
    (k V : ℕ) (hV : block ≤ V) :
    (cost (prunedBuild baseWidth cutoff baseCharge levelCharge k V) : ℝ) * block ≤
      uniformConstant C A * V *
        (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) := by
  rw [← growthBase_power]
  exact pruned_cost_power baseWidth cutoff block baseCharge levelCharge C
    (uniformConstant C A) growthBase hcut hC (uniformConstant_nonneg C A hC hA)
    growthBase_ge_one (uniformConstant_budget C A hA)
    (fun n hn => (hbase n hn).trans
      (mul_le_mul_of_nonneg_right (uniformConstant_ge C A hC) (Nat.cast_nonneg n))) hlocal k V hV

/-- The outermost array may be smaller than one block. It stops immediately;
all genuinely recursive children satisfy the large-volume bound above. -/
theorem pruned_cost_with_startup (baseWidth cutoff block : ℕ) (baseCharge : ℕ → ℕ)
    (levelCharge : ℕ → ℕ → ℕ) (C A : ℝ)
    (hcut : Parameters.W * block ≤ cutoff) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : ∀ V, (baseCharge V : ℝ) * block ≤ A * (block + V))
    (hlocal : ∀ j V, cutoff < V → (levelCharge j V : ℝ) * block ≤ C * V)
    (k V : ℕ) :
    (cost (prunedBuild baseWidth cutoff baseCharge levelCharge k V) : ℝ) * block ≤
      uniformConstant C (2*A) * (block + V *
        (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  have h2A : 0 ≤ 2*A := mul_nonneg (by norm_num) hA
  have hK := uniformConstant_nonneg C (2*A) hC h2A
  by_cases hV : block ≤ V
  · have h := pruned_cost_bound baseWidth cutoff block baseCharge levelCharge C (2*A)
      hcut hC h2A (fun n hn => by
        have hb := hbase n
        have hv : (block : ℝ) ≤ n := by exact_mod_cast hn
        nlinarith) hlocal k V hV
    apply h.trans
    nlinarith [mul_nonneg hK (Nat.cast_nonneg block)]
  · have hfit : V ≤ cutoff := by
      have hw : 1 ≤ Parameters.W := by norm_num [Parameters.W_value]
      have hb : block ≤ Parameters.W * block := by nlinarith
      exact (Nat.le_of_lt (Nat.lt_of_not_ge hV)).trans (hb.trans hcut)
    have hstop : cost (prunedBuild baseWidth cutoff baseCharge levelCharge k V) = baseCharge V := by
      cases k <;> simp only [prunedBuild, if_pos hfit, cost]
    rw [hstop]
    have hAK : A ≤ uniformConstant C (2*A) :=
      (by linarith : A ≤ 2*A).trans (uniformConstant_ge C (2*A) hC)
    have hcoef : A * (block + V) ≤ uniformConstant C (2*A) * (block + V) :=
      mul_le_mul_of_nonneg_right hAK (by positivity)
    have hpow : 1 ≤ (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ))) := by
      rw [← growthBase_power]
      exact one_le_pow₀ growthBase_ge_one
    apply (hbase V).trans (hcoef.trans _)
    apply mul_le_mul_of_nonneg_left _ hK
    nlinarith [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg V)]

end CallTree

/-- Complete resource conclusion for the pruned interpreter, with the
startup term retained and the global recurrence proved from its call tree.
The premises concern only implementations of local scans and leaves. -/
theorem cutoffExchange_cost_bound (baseWidth cutoff block k rows : ℕ)
    (baseCharge : ℕ → ℕ) (levelCharge : ℕ → ℕ → ℕ) (C A : ℝ)
    (hcut : Parameters.W * block ≤ cutoff) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : ∀ V, (baseCharge V : ℝ) * block ≤ A * (block + V))
    (hlocal : ∀ j V, cutoff < V → (levelCharge j V : ℝ) * block ≤ C * V)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k)) :
    (CallTree.cost (cutoffExchange baseWidth cutoff baseCharge levelCharge k rows layout
      (Gap := Gap) (Suffix := Suffix)).calls : ℝ) * block ≤
      CallTree.uniformConstant C (2*A) *
        (block + Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) *
        (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  rw [cutoffExchange_calls]
  exact CallTree.pruned_cost_with_startup baseWidth cutoff block baseCharge levelCharge C A
    hcut hC hA hbase hlocal k _

theorem cutoffExchange_transfer_bound (baseWidth cutoff block k rows : ℕ)
    (baseCharge : ℕ → ℕ) (levelCharge : ℕ → ℕ → ℕ) (C A : ℝ)
    (hblock : 0 < block) (hcut : Parameters.W * block ≤ cutoff) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hbase : ∀ V, (baseCharge V : ℝ) * block ≤ A * (block + V))
    (hlocal : ∀ j V, cutoff < V → (levelCharge j V : ℝ) * block ≤ C * V)
    {Prefix Gap Suffix : Type} [Fintype Prefix] [Fintype Gap] [Fintype Suffix]
    (layout : Prefix ≃ Fin (rows * Parameters.W ^ k)) :
    (CallTree.cost (cutoffExchange baseWidth cutoff baseCharge levelCharge k rows layout
      (Gap := Gap) (Suffix := Suffix)).calls : ℝ) ≤
      CallTree.uniformConstant C (2*A) *
        (1 + ((Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) : ℝ) / block) *
          (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) := by
  have hb : (0 : ℝ) < block := by exact_mod_cast hblock
  apply (mul_le_mul_iff_of_pos_right hb).mp
  calc
    _ ≤ CallTree.uniformConstant C (2*A) *
        (block + Fintype.card (FullAddress Prefix (Scalar (baseWidth * Parameters.m ^ k)) Gap Suffix) *
          (Parameters.m : ℝ)^((k : ℝ)*(1-(Parameters.epsilon : ℝ)))) :=
      cutoffExchange_cost_bound baseWidth cutoff block k rows baseCharge levelCharge C A
        hcut hC hA hbase hlocal layout
    _ = _ := by field_simp

end
end CSL.RecursiveExchange


