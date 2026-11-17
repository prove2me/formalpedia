-- Prove2me | Definitions.Def_AsymSpecConn_Supplement_nonCrossing
-- name    : AsymSpecConn_Supplement_nonCrossing
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T01:23:30.17361+00:00
-- url     : https://prove2.me/theorems/f7fb46d4-b0c5-4393-8d97-15a3a93e913f
-- title:
--   Non-crossing bipartitions, merge maps, and repeated interpolation
-- statement:
--   An unordered bipartition is encoded by its unique nonempty proper side not containing a distinguished last leg. A finite family is non-crossing exactly when these canonical sides are pairwise nested or disjoint. For each bipartition $b$, $R_b$ is its flattening rank and $A_{S_b}$ is the corresponding subset-irreducibility locus.
--
--   The module defines the merge operation along a labelled set partition and a complete relational encoding of the repeated interpolant of §6.5. Its witness records every coarsest common refinement, every partial merge, the accumulated weights and normalized parameters, and the exact $F_w$ equation at each stage.
--
--   **Formalization Note** Set partitions have finite labels and merge maps regroup chosen product bases; these choices change no tensor-equivalence class. The `toNNReal` conversion is applied to `Fw` only at stages where Theorem 2.10 proves the extended value finite.
-- source:
--   Vrana and Zuiddam, The asymptotic spectrum of tensors is connected, preprint (STOC 2027 submission, version of November 2, 2026, sha256 85a0b2ac698c902a02f2df11dd0671a5d9ca373aed822ae44b7e2640fc152c7d), §6.1–6.5, pp.42–47

import Mathlib
import Definitions.Def_mme_tensor_quotient
import Definitions.Def_mme_flattening
import Definitions.Def_AsymSpecConn_tensorPreorder
import Definitions.Def_AsymSpecConn_Fw
import Definitions.Def_AsymSpecConn_Supplement_basicMM
import Definitions.Def_AsymSpecConn_Supplement_logValueSet

set_option autoImplicit false

open PiTensorProduct BigOperators
open scoped NNReal ENNReal

namespace AsymSpecConn.Supplement

/-- A bipartition of the legs, encoded by its unique nonempty proper part that does not contain
the distinguished last leg.  This is the convention `S_b` of Section 6.1 (p.42). -/
structure Bipartition (k : ℕ) (root : Fin k) where
  side : Finset (Fin k)
  side_nonempty : side.Nonempty
  compl_nonempty : sideᶜ.Nonempty
  root_not_mem : root ∉ side

/-- Main exported package for Sections 6.1--6.5: canonical bipartitions and the associated
non-crossing/repeated-interpolation constructions. -/
abbrev nonCrossing := Bipartition

instance {k : ℕ} {root : Fin k} : DecidableEq (Bipartition k root) :=
  fun b c => decidable_of_iff (b.side = c.side) ⟨fun h => by cases b; cases c; simp_all,
    fun h => congrArg Bipartition.side h⟩

/-- Two canonical sides are non-crossing exactly when they are nested or disjoint. -/
def NonCrossing {k : ℕ} {root : Fin k} (B : Finset (Bipartition k root)) : Prop :=
  ∀ b ∈ B, ∀ c ∈ B,
    b.side ⊆ c.side ∨ c.side ⊆ b.side ∨ Disjoint b.side c.side

/-- The split belonging to a canonical bipartition side. -/
def Bipartition.split {k : ℕ} {root : Fin k} (b : Bipartition k root) : MME.Split (Fin k) where
  S := b.side
  hS := b.side_nonempty
  hSc := b.compl_nonempty

/-- Flattening rank for an arbitrary bipartition, descended to tensor-equivalence classes. -/
noncomputable def bipartitionRankQ {K : Type*} [Field K] {k : ℕ} {root : Fin k}
    (b : Bipartition k root) : MME.TensorQ K k → ℕ :=
  Quotient.lift (MME.flatteningRank b.split) (fun _ _ h =>
    le_antisymm (MME.flatteningRank_mono _ h.1) (MME.flatteningRank_mono _ h.2))

/-- Regroup a concrete tensor's legs according to a surjective block labelling `p`.

The definition expands in chosen product bases and then regroups every basis tensor.  The result
is independent, up to mutual restriction, of the chosen bases and of the representative.  This is
the paper's `merge_p` construction from Section 6.3 (pp.43--44). -/
noncomputable def mergeObj {K : Type*} [Field K] {k m : ℕ} (p : Fin k → Fin m)
    (X : MME.TensorObj K k) : MME.TensorObj K m where
  V a := PiTensorProduct K (fun i : {i : Fin k // p i = a} => X.V i.1)
  fin _ := inferInstance
  t :=
    let basis := fun i => Module.Free.chooseBasis K (X.V i)
    let productBasis := Basis.piTensorProduct basis
    ∑ x : ∀ i, Module.Free.ChooseBasisIndex K (X.V i),
      (productBasis.repr X.t x) •
        tprod K (fun a => tprod K (fun i : {i : Fin k // p i = a} => basis i.1 (x i.1)))

/-- The merging operation on tensor-equivalence classes.  `Quotient.out` only selects a concrete
representative on which to perform the basis regrouping in `mergeObj`; the resulting class is the
source's representative-independent `merge_p`. -/
noncomputable def mergeQ {K : Type*} [Field K] {k m : ℕ} (p : Fin k → Fin m) :
    MME.TensorQ K k → MME.TensorQ K m :=
  fun s => MME.TensorQ.toQ (mergeObj p (Quotient.out s))

/-- `S`-irreducibility from Section 6.3, encoded as ordinary irreducibility of the first leg after
merging the two parts of the bipartition.  Concisifying the merged representative replaces its
first leg by `supp_S(t)`, so this is exactly the source definition. -/
def SubsetIrreducible {k : ℕ} {root : Fin k} (b : Bipartition k root)
    (s : MME.TensorQ ℂ k) : Prop :=
  FieldIrreducible (by norm_num) (0 : Fin 2)
    (mergeQ (fun i => if i ∈ b.side then (0 : Fin 2) else 1) s)

/-- The weighted geometric average `w_θ = ∏_b R_b^{θ(b)}` of Section 6.2, with the
paper's convention `0^0 = 1`. -/
noncomputable def nonCrossingRankWeight {k : ℕ} {root : Fin k}
    (B : Finset (Bipartition k root)) (θ : ↑B → ℝ) : MME.TensorQ ℂ k → ℝ≥0 :=
  fun s => ∏ b : ↑B, (bipartitionRankQ b.1 s : ℝ≥0) ^ θ b

/-- An allowed enumeration of the positive-weight bipartitions in Section 6.5: every positive
weight occurs exactly once, and larger canonical sides precede the sides they contain. -/
structure AllowedEnumeration {k : ℕ} {root : Fin k}
    (B : Finset (Bipartition k root)) (θ : ↑B → ℝ) where
  N : ℕ
  order : Fin N ≃ {b : ↑B // 0 < θ b}
  decreasing : ∀ i j : Fin N,
    (order j).1.1.side ⊆ (order i).1.1.side → i ≤ j

namespace AllowedEnumeration

variable {k : ℕ} {root : Fin k} {B : Finset (Bipartition k root)} {θ : ↑B → ℝ}

def bipart (e : AllowedEnumeration B θ) (j : Fin e.N) : Bipartition k root :=
  (e.order j).1.1

def weight (e : AllowedEnumeration B θ) (j : Fin e.N) : ℝ :=
  θ (e.order j).1

end AllowedEnumeration

/-- The labelled coarsest common refinement `p_j` of the first `j+1` bipartitions in an allowed
enumeration.  The equivalence in `exact_blocks` says that two original legs are merged precisely
when none of those bipartitions separates them. -/
structure InterpolationStage {k : ℕ} {root : Fin k}
    {B : Finset (Bipartition k root)} {θ : ↑B → ℝ}
    (e : AllowedEnumeration B θ) (j : Fin e.N) where
  m : ℕ
  hm : 2 ≤ m
  block : Fin k → Fin m
  block_surjective : Function.Surjective block
  exact_blocks : ∀ x y,
    block x = block y ↔
      ∀ l : Fin e.N, l ≤ j →
        (x ∈ (e.bipart l).side ↔ y ∈ (e.bipart l).side)

/-- The current canonical side is one leg of the common-refinement tensor. -/
noncomputable def InterpolationStage.currentLeg {k : ℕ} {root : Fin k}
    {B : Finset (Bipartition k root)} {θ : ↑B → ℝ}
    {e : AllowedEnumeration B θ} {j : Fin e.N} (p : InterpolationStage e j) : Fin p.m :=
  p.block (e.bipart j).side_nonempty.choose

/-- The accumulated weight `θ_{≤j}` (zero-based stage index). -/
noncomputable def accumulatedWeight {k : ℕ} {root : Fin k}
    {B : Finset (Bipartition k root)} {θ : ↑B → ℝ}
    (e : AllowedEnumeration B θ) (j : Fin e.N) : ℝ :=
  ∑ l : Fin e.N, if l ≤ j then e.weight l else 0

/-- The predecessor of a noninitial finite index. -/
def finPred {N : ℕ} (j : Fin N) (hj : 0 < j.1) : Fin N :=
  ⟨j.1 - 1, by omega⟩

/-- A full witness for the recursive construction of the repeated interpolant in Section 6.5.
It records the exact common-refinement tensors, the partial unmerging maps, each normalized
interpolation parameter `τ_j`, and the defining `F_w` equation at every stage. -/
structure RepeatedInterpolationWitness {k : ℕ} {root : Fin k}
    (hk : 2 ≤ k) (B : Finset (Bipartition k root)) (θ : ↑B → ℝ)
    (e : AllowedEnumeration B θ) (f : MME.TensorQ ℂ k → ℝ≥0) where
  positive_length : 0 < e.N
  stage : ∀ j : Fin e.N, InterpolationStage e j
  transition : ∀ (j : Fin e.N) (hj : 0 < j.1),
    Fin (stage j).m → Fin (stage (finPred j hj)).m
  transition_factor : ∀ (j : Fin e.N) (hj : 0 < j.1) (x : Fin k),
    transition j hj ((stage j).block x) = (stage (finPred j hj)).block x
  g : ∀ j : Fin e.N, MME.TensorQ ℂ (stage j).m → ℝ≥0
  initial : ∀ (j : Fin e.N), j.1 = 0 →
    g j = fun s => ((AsymSpecConn.flatRankQ (stage j).hm (stage j).currentLeg s : ℕ) : ℝ≥0)
  step : ∀ (j : Fin e.N) (hj : 0 < j.1) (s : MME.TensorQ ℂ (stage j).m),
    let prev := finPred j hj
    let h : MME.TensorQ ℂ (stage j).m → ℝ≥0 :=
      fun x => g prev (mergeQ (transition j hj) x)
    let rank : MME.TensorQ ℂ (stage j).m → ℝ≥0 :=
      fun x => (AsymSpecConn.flatRankQ (stage j).hm (stage j).currentLeg x : ℝ≥0)
    let τ := e.weight j / accumulatedWeight e j
    g j s = (AsymSpecConn.Fw (AsymSpecConn.tensorPreorder ℂ (stage j).hm)
      {x | FieldIrreducible (stage j).hm (stage j).currentLeg x}
      (fun x => h x ^ (1 - τ) * rank x ^ τ) s).toNNReal
  output : ∀ s,
    f s = g ⟨e.N - 1, by omega⟩
      (mergeQ (stage ⟨e.N - 1, by omega⟩).block s)

/-- `f` is the repeated interpolant for the specified allowed enumeration precisely when it has
the stage-by-stage construction witness of Section 6.5. -/
def IsRepeatedInterpolant {k : ℕ} {root : Fin k} (hk : 2 ≤ k)
    (B : Finset (Bipartition k root)) (θ : ↑B → ℝ)
    (e : AllowedEnumeration B θ) (f : MME.TensorQ ℂ k → ℝ≥0) : Prop :=
  Nonempty (RepeatedInterpolationWitness hk B θ e f)

end AsymSpecConn.Supplement


