-- Prove2me | Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
-- name    : ProbabilityTheory_chapter_01_def_1_2_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-12T07:41:25.881572+00:00
-- url     : https://prove2.me/theorems/099e5b63-d780-48ac-ba62-0f4b79c20792
-- title:
--   Definition 1.2: Riemann–Stieltjes integrability
-- statement:
--   Constructs a Riemann–Stieltjes integral using partitions, upper and lower Darboux sums, and tagged sums; exports integrability as the existence of a common-limit witness.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/def_1_2.lean

import Mathlib.Tactic

open scoped BigOperators Pointwise

noncomputable section

def SourceHypotheses (a b : ℝ) (f alpha : ℝ → ℝ) : Prop :=
  a < b ∧
  BddAbove (f '' Set.Icc a b) ∧
  BddBelow (f '' Set.Icc a b) ∧
  MonotoneOn alpha (Set.Icc a b)

structure Partition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : Fin (n + 1) → ℝ
  pts_start : pts 0 = a
  pts_end : pts (Fin.last n) = b
  strict_mono : StrictMono pts

def Partition.mesh {a b : ℝ} (P : Partition a b) : ℝ :=
  Finset.sup' (Finset.univ : Finset (Fin P.n))
    ⟨⟨0, P.hn⟩, Finset.mem_univ _⟩
    fun i => P.pts i.succ - P.pts i.castSucc

def Partition.subinterval {a b : ℝ} (P : Partition a b) (i : Fin P.n)
  : Set ℝ :=
  Set.Icc (P.pts i.castSucc) (P.pts i.succ)

def upperStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sSup (f '' Partition.subinterval P i)

def lowerStep {a b : ℝ} (P : Partition a b) (f : ℝ → ℝ) (i : Fin P.n) : ℝ :=
  sInf (f '' Partition.subinterval P i)

def taggedSum {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ)
    (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    f (tags i) * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

def tagsInPartition {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) : Prop :=
  ∀ i : Fin P.n, tags i ∈ Partition.subinterval P i

example {a b : ℝ} (P : Partition a b) (tags : Fin P.n → ℝ) :
  tagsInPartition P tags ↔ ∀ i : Fin P.n, tags i ∈ Set.Icc (P.pts i.castSucc) (P.pts i.succ)
  := by rfl

def upperSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    upperStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

def lowerSum {a b : ℝ} (P : Partition a b) (f alpha : ℝ → ℝ) : ℝ :=
  ∑ i : Fin P.n,
    lowerStep P f i * (alpha (P.pts i.succ) - alpha (P.pts i.castSucc))

def UpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b,
      P.mesh < delta →
        |upperSum P f alpha - L| < eps ∧ |lowerSum P f alpha - L| < eps

def RSIntegrableOnInterval (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ L, UpperLowerCommonLimit a b f alpha L

def TaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  SourceHypotheses a b f alpha ∧
    ∀ eps > 0, ∃ delta > 0, ∀ P : Partition a b, ∀ tags : Fin P.n → ℝ,
      tagsInPartition P tags →
      P.mesh < delta →
      |taggedSum P tags f alpha - L| < eps

def rsUpperLowerCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  UpperLowerCommonLimit a b f alpha L

def rsTaggedCommonLimit (a b : ℝ) (f alpha : ℝ → ℝ) (L : ℝ) : Prop :=
  TaggedCommonLimit a b f alpha L

structure RSIntegralWitness (f alpha : ℝ → ℝ) (a b : ℝ) where
  value : ℝ
  source_limit : rsUpperLowerCommonLimit a b f alpha value
  tagged_limit : rsTaggedCommonLimit a b f alpha value

def RSIntegrable (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  Nonempty (RSIntegralWitness f alpha a b)

noncomputable def rsIntegral (f alpha : ℝ → ℝ) (a b : ℝ)
    (h : RSIntegrable f alpha a b) : ℝ :=
  (Classical.choice h).value

theorem rsIntegral_source_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).source_limit

theorem rsIntegral_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  (Classical.choice h).tagged_limit

theorem rsIntegral_source_and_tagged_spec {f alpha : ℝ → ℝ} {a b : ℝ}
    (h : RSIntegrable f alpha a b) :
    rsUpperLowerCommonLimit a b f alpha (rsIntegral f alpha a b h) ∧
      rsTaggedCommonLimit a b f alpha (rsIntegral f alpha a b h) :=
  ⟨rsIntegral_source_spec h, rsIntegral_spec h⟩

def def_1_2 (f alpha : ℝ → ℝ) (a b : ℝ) : Prop :=
  RSIntegrable f alpha a b

def rsIntegrableFamily (alpha : ℝ → ℝ) (a b : ℝ) : Set (ℝ → ℝ) :=
  {f | RSIntegrable f alpha a b}
section RS_integral_uniqueness

theorem leftTagsInPartition {a b : ℝ} (P : Partition a b) :
    tagsInPartition P (fun i => P.pts i.castSucc) := by
  intro i
  constructor
  · exact le_rfl
  · simp only
    apply le_of_lt
    exact P.strict_mono (Fin.castSucc_lt_succ)

def uniformPartition (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    Partition a b where
  n := n
  hn := hn
  pts := fun i => a + ((i : ℝ) / (n : ℝ)) * (b - a)
  pts_start := by simp
  pts_end := by
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)

    change a + ((Fin.last n).val : ℝ) / (n : ℝ) * (b - a) = b
    rw [Fin.val_last]
    field_simp [hn0]
    ring
  strict_mono := by

    intro i j hij
    dsimp
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hba : 0 < b - a := sub_pos.mpr hab
    have hijR : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij

    have h1 : (i : ℝ) / (n : ℝ) < (j : ℝ) / (n : ℝ) := by
      exact mul_lt_mul_of_pos_right hijR (inv_pos.mpr hnR)

    have h2 : ((i : ℝ) / (n : ℝ)) * (b - a) < ((j : ℝ) / (n : ℝ)) * (b - a) :=
      mul_lt_mul_of_pos_right h1 hba

    linarith [h2]

theorem uniformPartition_mesh_eq (a b : ℝ) (hab : a < b) (n : ℕ) (hn : 0 < n) :
    (uniformPartition a b hab n hn).mesh = (b - a) / (n : ℝ) := by
  unfold Partition.mesh uniformPartition
  apply Finset.sup'_eq_of_forall
  intro i hi
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  norm_num [Nat.cast_add, Nat.cast_one]
  field_simp [ne_of_gt hnR]
  ring

end RS_integral_uniqueness


