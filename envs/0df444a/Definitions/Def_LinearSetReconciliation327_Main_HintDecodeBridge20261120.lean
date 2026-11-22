-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintDecodeBridge20261120
-- name    : LinearSetReconciliation327_Main_HintDecodeBridge20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:33:03.867592+00:00
-- url     : https://prove2.me/theorems/8888a9cc-2730-4a0e-bdc8-354f611c24f2
-- title:
--   LinearSetReconciliation327 — HintDecodeBridge (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintDecodeBridge20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_NodeValidity
import Theorems.Thm_LinearSetReconciliation327_Main_hint_decode_correct
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
namespace HintCanonicalDecode
open Finset

lemma zmod2_eq_zero_or_one (z : ZMod 2) : z = 0 ∨ z = 1 := by
  have h : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  exact h z

lemma mem_rowsWhere {sch : RowScheme} (P : Fin sch.m → Prop) (j : Fin sch.m) :
    j.val ∈ sch.rowsWhere P ↔ P j := by
  classical
  unfold RowScheme.rowsWhere
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j', hj', hv⟩
    have hP : P j' := by
      have h2 := hj'
      simp only [Finset.mem_filter] at h2
      exact h2.2
    have hjj : j' = j := Fin.ext hv
    rwa [hjj] at hP
  · intro h
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, h⟩

lemma rowsWhere_subset_range (sch : RowScheme) (P : Fin sch.m → Prop) :
    sch.rowsWhere P ⊆ Finset.range sch.m := by
  intro a ha
  unfold RowScheme.rowsWhere at ha
  rw [Finset.mem_image] at ha
  obtain ⟨j, -, rfl⟩ := ha
  exact Finset.mem_range.mpr j.isLt

lemma column_subset_range (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr x s ⊆ range sch.m := by
  intro v hv
  unfold RowScheme.column RowScheme.rowsWhere at hv
  rw [mem_image] at hv
  obtain ⟨j, -, rfl⟩ := hv
  exact mem_range.mpr j.isLt

lemma symmDiff_subset_range {N : ℕ} {A B : Finset ℕ}
    (hA : A ⊆ Finset.range N) (hB : B ⊆ Finset.range N) :
    symmDiff A B ⊆ Finset.range N := by
  intro a ha
  rcases Finset.mem_symmDiff.mp ha with ⟨h, -⟩ | ⟨h, -⟩
  · exact hA h
  · exact hB h

lemma mem_column_iff (sch : RowScheme) (lr : sch.LocalSeed) (x : Finset ℕ) (s : Fin sch.ℓ)
    (j : Fin sch.m) :
    j.val ∈ sch.column lr x s ↔ sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := by
  classical
  unfold RowScheme.column
  exact mem_rowsWhere _ j

lemma card_fin_filter_eq {m : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range m) :
    (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).card = S.card := by
  classical
  have himg : (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).image
      (fun j : Fin m => j.val) = S := by
    ext a
    rw [Finset.mem_image]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have h2 := hj
      simp only [Finset.mem_filter] at h2
      exact h2.2
    · intro ha
      refine ⟨⟨a, Finset.mem_range.mp (hS ha)⟩, ?_, rfl⟩
      simp only [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ha⟩
  have hc : ((Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).image
      (fun j : Fin m => j.val)).card
      = (Finset.univ.filter fun j : Fin m => (j.val : ℕ) ∈ S).card :=
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h)
  rw [← hc, himg]

lemma filter_congr_dec {α : Type} (p : α → Prop) (d₁ d₂ : DecidablePred p) (s : Finset α) :
    @Finset.filter α p d₁ s = @Finset.filter α p d₂ s := by
  ext a
  rw [@Finset.mem_filter α p d₁ s a, @Finset.mem_filter α p d₂ s a]

lemma exactHint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ) (s : Fin sch.ℓ) :
    (sch.exactHint lr x J s).card = sch.U lr x J s := by
  have key : ∀ (d : DecidablePred fun j : Fin sch.m => sch.exactPred lr x J s j = none),
      (sch.exactHint lr x J s).card
        = (@Finset.filter (Fin sch.m)
            (fun j => sch.exactPred lr x J s j = none) d Finset.univ).card := by
    intro d
    unfold RowScheme.exactHint RowScheme.rowsWhere
    rw [← show (@Finset.filter (Fin sch.m)
          (fun j => sch.exactPred lr x J s j = none)
          (fun a => Classical.propDecidable (sch.exactPred lr x J s a = none))
          Finset.univ).card
        = (@Finset.filter (Fin sch.m)
            (fun j => sch.exactPred lr x J s j = none) d Finset.univ).card from
      congrArg Finset.card (filter_congr_dec _ _ d Finset.univ)]
    exact Finset.card_image_of_injective _ (fun a b h => Fin.ext h)
  unfold RowScheme.U
  exact key _

lemma zmod2_ne_iff_not_iff (b c : ZMod 2) :
    b ≠ c ↔ ¬ ((c = 1) ↔ (b = 1)) := by
  rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    rcases zmod2_eq_zero_or_one c with rfl | rfl <;> simp

lemma symmDiff_sdiff_hint_iff (p : Option (ZMod 2)) (c : ZMod 2) :
    (¬ ((c = 1) ↔ (p = some 1)) ∧ p ≠ none) ↔ ∃ b, p = some b ∧ b ≠ c := by
  constructor
  · rintro ⟨hiff, hne⟩
    obtain ⟨b, hb⟩ : ∃ b, p = some b := by
      cases p with
      | none => exact absurd rfl hne
      | some b => exact ⟨b, rfl⟩
    refine ⟨b, hb, ?_⟩
    rw [hb, Option.some.injEq] at hiff
    exact (zmod2_ne_iff_not_iff b c).mpr hiff
  · rintro ⟨b, hb, hne⟩
    subst hb
    refine ⟨?_, by simp⟩
    rw [Option.some.injEq]
    exact (zmod2_ne_iff_not_iff b c).mp hne

lemma exactChild_diff_hint_card (sch : RowScheme) (lr : sch.LocalSeed) (x J : Finset ℕ)
    (s : Fin sch.ℓ) :
    ((sch.exactChildInput lr x J s) \ (sch.exactHint lr x J s)).card = sch.V lr x J s := by
  classical
  have hD : (sch.exactChildInput lr x J s \ sch.exactHint lr x J s) ⊆ Finset.range sch.m :=
    fun a ha => (symmDiff_subset_range (column_subset_range sch lr x s)
      (rowsWhere_subset_range sch _)) (Finset.mem_sdiff.mp ha).1
  have hstep : ∀ j : Fin sch.m,
      (j.val ∈ sch.exactChildInput lr x J s \ sch.exactHint lr x J s) ↔
        ∃ b, sch.exactPred lr x J s j = some b ∧
          b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s := by
    intro j
    have hcol : j.val ∈ sch.column lr x s ↔
        sch.code j (lr.2 j) (sch.rowOf lr x j) s = 1 := mem_column_iff sch lr x s j
    have hP : j.val ∈ sch.exactP lr x J s ↔ sch.exactPred lr x J s j = some 1 := by
      unfold RowScheme.exactP
      exact mem_rowsWhere _ j
    have hH : j.val ∈ sch.exactHint lr x J s ↔ sch.exactPred lr x J s j = none := by
      unfold RowScheme.exactHint
      exact mem_rowsWhere _ j
    have hs : (j.val ∈ symmDiff (sch.column lr x s) (sch.exactP lr x J s)) ↔
        ¬ ((j.val ∈ sch.column lr x s) ↔ (j.val ∈ sch.exactP lr x J s)) := by
      rw [Finset.mem_symmDiff]
      tauto
    unfold RowScheme.exactChildInput
    rw [Finset.mem_sdiff, hs, hcol, hP, hH]
    exact symmDiff_sdiff_hint_iff _ _
  rw [← card_fin_filter_eq hD]
  have hVdef : sch.V lr x J s =
      (Finset.univ.filter fun j : Fin sch.m => ∃ b, sch.exactPred lr x J s j = some b ∧
        b ≠ sch.code j (lr.2 j) (sch.rowOf lr x j) s).card := rfl
  rw [hVdef]
  exact congrArg Finset.card (Finset.ext fun j => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hstep j)

theorem allValid_of_valid :
    ∀ (T : Node), ∀ (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ),
      Node.WF T X Y → Node.AllBounds T r x J → Node.Valid T.N X Y x J →
        AllValid X Y T r x J := by
  intro T
  induction T with
  | store N =>
      intro X Y r x J _ _ _
      trivial
  | cr N t =>
      intro X Y r x J _ _ hV
      exact hV
  | direct sch t =>
      intro X Y r x J _ _ hV
      exact hV
  | recursive sch t Xs Ys child ih =>
      intro X Y r x J hWF hB hV
      obtain ⟨htN, hWFc⟩ := hWF
      obtain ⟨hZ, hUV⟩ := hB
      refine ⟨hV, ?_⟩
      intro s
      apply ih s (Xs s) (Ys s) (r.2 s) (sch.exactChildInput r.1 x J s)
        (sch.exactHint r.1 x J s) (hWFc s).2 (hUV s).2.2
      rw [(hWFc s).1]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact symmDiff_subset_range (column_subset_range sch r.1 x s)
          (rowsWhere_subset_range sch _)
      · exact rowsWhere_subset_range sch _
      · have h1 := exactHint_card sch r.1 x J s
        have h2 := (hUV s).1
        omega
      · have h1 := exactChild_diff_hint_card sch r.1 x J s
        have h2 := (hUV s).2.1
        omega

end HintCanonicalDecode

/-- Reuse the published decoder-correctness theorem with its canonical validity
    definition; root validity and exact-execution bounds discharge AllValid. -/
theorem hintNodeDecode_correct_of_valid (CR : CRFamily) (hRec : CR.Recovers)
    (T : Node) (X Y : ℕ) (r : Node.Seed T) (x J : Finset ℕ)
    (hWF : Node.WF T X Y) (hBounds : Node.AllBounds T r x J) (hValid : Node.Valid T.N X Y x J) :
    Node.decode CR T r (Node.sketch CR T r x) J = some x := by
  exact hint_decode_correct CR hRec T X Y r x J hWF hBounds
    (HintCanonicalDecode.allValid_of_valid T X Y r x J hWF hBounds hValid)

end LinearSetReconciliation327.Main
#print axioms LinearSetReconciliation327.Main.HintCanonicalDecode.allValid_of_valid
#print axioms LinearSetReconciliation327.Main.hintNodeDecode_correct_of_valid


