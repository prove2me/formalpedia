-- Prove2me | Definitions.Def_InfoLossLAR_NativeBundle_07_Part_2_Subpart_1
-- name    : InfoLossLAR_NativeBundle_07_Part_2_Subpart_1
-- status  : Definition
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-14T15:10:02.317842+00:00
-- url     : https://prove2.me/theorems/96c409e2-87f6-4a06-bc91-faadfb2d8283
-- title:
--   Cycle and selected-root data
-- statement:
--   This package defines cycle selection and forest counting interfaces, complete cycle kernels and joint likelihoods, centered and mixture cycle densities, protected cycle parameters, uniform selection and root expansion data.
--
--   These finite data interfaces describe the full closed-cycle and shared-background experiments used in the affine response construction. They retain the distinction between joint laws and individual marginals. Supporting constructor identities are preserved from the original source; subsequent analytic bounds and sampler guarantees remain separate theorems.
-- source:
--   Local manuscript proof repository commit 5c3becb254daaa8738368b474349766c1769c2a0. Complete original data source units Definitions.Def_InfoLossLAR_Native_CurrentAFT_CycleForestCounting, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CycleKernel, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CycleJointLikelihood, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CenteredCycleDensity, Definitions.Def_InfoLossLAR_Native_CurrentAFT_RareMixture, Definitions.Def_InfoLossLAR_Native_CurrentAFT_PairCycleDensity, Definitions.Def_InfoLossLAR_Native_CurrentAFT_SupportedHoeffding, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CycleDensity, Definitions.Def_InfoLossLAR_Native_CurrentAFT_CycleRootParameters. Scope wrappers and source-body hashes are recorded in compact_part2_split/manifest.json. SHA256 654703662af751fe3c80c3694c8c046c1c6f2d193c7e066fbbffcba5fe613414.

import Definitions.Def_InfoLossLAR_NativeBundle_07_Part_1

section





/-!
# Counting non-isolated selections by their oriented path forests

For each selected vertex, record its selected predecessor, if one exists.
A proper selected subset of one cycle cannot contain a directed cycle.
Consequently this predecessor pattern is a union of directed paths, and
its root positions determine the complete embedding. A non-isolated
pattern has at most half as many roots as vertices. The finite encoding
therefore counts rare selections with the required full-order exponent.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Every selected vertex has another selected cyclic neighbor. -/
def NoIsolated {body order : ℕ} (sites : Selection body order) : Prop :=
  ∀ slot, ∃ other, other ≠ slot ∧ Adjacent body (sites slot) (sites other)

/-- The oriented selected predecessor, with `none` at the start of each path. -/
def predecessorPattern {body order : ℕ} (sites : Selection body order) (slot : Fin order) : Option (Fin order) :=
  if h : ∃ previous, sites previous = (finRotate body).symm (sites slot) then
    some (Classical.choose h) else none

theorem predecessorPattern_some {body order : ℕ} (sites : Selection body order)
    (slot previous : Fin order) :
    predecessorPattern sites slot = some previous ↔
      sites previous = (finRotate body).symm (sites slot) := by
  unfold predecessorPattern
  split_ifs with h
  · constructor
    · intro hequal
      have hlabels := Option.some.inj hequal
      rw [← hlabels]
      exact Classical.choose_spec h
    · intro hprevious
      apply congrArg some
      exact sites.injective ((Classical.choose_spec h).trans hprevious.symm)
  · constructor
    · intro hnone
      cases hnone
    · intro hprevious
      exact False.elim (h ⟨previous, hprevious⟩)

theorem predecessorPattern_none {body order : ℕ} (sites : Selection body order) (slot : Fin order) :
    predecessorPattern sites slot = none ↔
      ¬∃ previous, sites previous = (finRotate body).symm (sites slot) := by
  unfold predecessorPattern
  split_ifs with h <;> simp only [h, not_true_eq_false, not_false_eq_true, Option.some_ne_none, eq_self_iff_true]

abbrev PatternRoots {order : ℕ} (pattern : Fin order → Option (Fin order)) :=
  {slot : Fin order // pattern slot = none}

/-- A path root in a non-isolated selection has a selected successor. -/
theorem root_has_child {body order : ℕ} (sites : Selection body order)
    (hno : NoIsolated sites) (slot : Fin order) (hroot : predecessorPattern sites slot = none) :
    ∃ child, predecessorPattern sites child = some slot := by
  obtain ⟨other, _, hadjacent⟩ := hno slot
  rcases hadjacent with hnext | hprevious
  · refine ⟨other, (predecessorPattern_some sites other slot).2 ?_⟩
    rw [hnext, Equiv.symm_apply_apply]
  · have hforbidden := (predecessorPattern_none sites slot).1 hroot
    apply False.elim
    apply hforbidden
    refine ⟨other, ?_⟩
    apply (finRotate body).injective
    simpa only [Equiv.apply_symm_apply] using hprevious.symm

/-- Different roots inject into different non-root successors. -/
theorem noIsolated_roots_card {body order : ℕ} (sites : Selection body order) (hno : NoIsolated sites) :
    Fintype.card (PatternRoots (predecessorPattern sites)) ≤ order / 2 := by
  let child := fun root : PatternRoots (predecessorPattern sites) =>
    Classical.choose (root_has_child sites hno root root.property)
  have hchild (root : PatternRoots (predecessorPattern sites)) :
      predecessorPattern sites (child root) = some root.val :=
    Classical.choose_spec (root_has_child sites hno root root.property)
  let map : PatternRoots (predecessorPattern sites) →
      {slot : Fin order // predecessorPattern sites slot ≠ none} :=
    fun root => ⟨child root, by rw [hchild]; simp⟩
  have hinjective : Function.Injective map := by
    intro first second hequal
    have hvalues := congrArg Subtype.val hequal
    have hfirst := hchild first
    have hsecond := hchild second
    change child first = child second at hvalues
    rw [hvalues] at hfirst
    apply Subtype.ext
    exact Option.some.inj (hfirst.symm.trans hsecond)
  have hcount := Fintype.card_le_of_injective map hinjective
  rw [Fintype.card_subtype_compl, Fintype.card_fin] at hcount
  dsimp only [PatternRoots] at hcount ⊢
  omega

/-- A nonempty subset closed under cyclic predecessor is the whole body.
This proves that proper selected subsets have no directed cycle. -/
theorem predecessor_closed_eq_univ (body : ℕ) (hbody : 2 ≤ body)
    (vertices : Finset (Fin body)) (hnonempty : vertices.Nonempty)
    (hclosed : ∀ vertex ∈ vertices, (finRotate body).symm vertex ∈ vertices) :
    vertices = Finset.univ := by
  obtain ⟨start, hstart⟩ := hnonempty
  apply Finset.eq_univ_of_forall
  intro target
  have hcycle := (isCycle_finRotate_of_le hbody).inv
  obtain ⟨steps, hsteps⟩ := hcycle.exists_pow_eq
    (ProtectedCycle.cycle_predecessor_ne body hbody start)
    (ProtectedCycle.cycle_predecessor_ne body hbody target)
  have hpowers : ∀ steps : ℕ, ((finRotate body)⁻¹ ^ steps) start ∈ vertices := by
    intro steps
    induction steps with
    | zero => simpa only [pow_zero, Equiv.Perm.one_apply] using hstart
    | succ steps ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      exact hclosed _ ih
  simpa only [hsteps] using hpowers steps

/-- For proper selections the selected predecessor pattern and the positions
of its roots determine every selected body position. -/
theorem embedding_eq_of_pattern_roots {body order : ℕ} (hbody : 2 ≤ body) (hproper : order < body)
    (first second : Selection body order)
    (hpattern : predecessorPattern first = predecessorPattern second)
    (hroots : ∀ slot, predecessorPattern first slot = none → first slot = second slot) :
    first = second := by
  by_contra hne
  have hlabel : ∃ slot, first slot ≠ second slot := by
    by_contra hnone
    apply hne
    apply DFunLike.ext
    intro slot
    exact not_not.mp (not_exists.mp hnone slot)
  let bad := Finset.univ.filter (fun slot : Fin order => first slot ≠ second slot)
  let vertices := bad.image first
  have hnonempty : vertices.Nonempty := by
    obtain ⟨slot, hslot⟩ := hlabel
    exact ⟨first slot, Finset.mem_image.mpr ⟨slot, by simp [bad, hslot], rfl⟩⟩
  have hclosed : ∀ vertex ∈ vertices, (finRotate body).symm vertex ∈ vertices := by
    intro vertex hvertex
    obtain ⟨slot, hbad, rfl⟩ := Finset.mem_image.mp hvertex
    have hbad' : first slot ≠ second slot := (Finset.mem_filter.mp hbad).2
    cases hparent : predecessorPattern first slot with
    | none => exact False.elim (hbad' (hroots slot hparent))
    | some previous =>
      have hfirst := (predecessorPattern_some first slot previous).1 hparent
      have hsecond : second previous = (finRotate body).symm (second slot) := by
        apply (predecessorPattern_some second slot previous).1
        rw [← hpattern]
        exact hparent
      have hpreviousBad : previous ∈ bad := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hagree
        apply hbad'
        apply (finRotate body).symm.injective
        exact hfirst.symm.trans (hagree.trans hsecond)
      exact Finset.mem_image.mpr ⟨previous, hpreviousBad, hfirst⟩
  have huniv := predecessor_closed_eq_univ body hbody vertices hnonempty hclosed
  have hcardImage : vertices.card ≤ bad.card := Finset.card_image_le
  have hbadCard : bad.card ≤ order := by
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcardImage
  omega

/-- Counting the actual predecessor-pattern fibers. Every path contributes
one free root position, and all remaining positions are forced successors. -/
theorem noIsolated_selection_card_le (body order : ℕ) (hbody : 2 ≤ body) (hproper : order < body) :
    Fintype.card {sites : Selection body order // NoIsolated sites} ≤
      (order + 1) ^ order * body ^ (order / 2) := by
  let Good := {sites : Selection body order // NoIsolated sites}
  let Patterns := Fin order → Option (Fin order)
  let parent : Good → Patterns := fun sites => predecessorPattern sites.val
  have hfiber (pattern : Patterns) :
      Fintype.card {sites : Good // parent sites = pattern} ≤ body ^ (order / 2) := by
    by_cases hnonempty : Nonempty {sites : Good // parent sites = pattern}
    · let witness := Classical.choice hnonempty
      have hwitness : predecessorPattern witness.val.val = pattern := witness.property
      have hrootsCount : Fintype.card (PatternRoots pattern) ≤ order / 2 := by
        rw [← hwitness]
        exact noIsolated_roots_card witness.val.val witness.val.property
      let rootPositions : {sites : Good // parent sites = pattern} →
          (PatternRoots pattern → Fin body) := fun sites root => sites.val.val root.val
      have hinjective : Function.Injective rootPositions := by
        intro first second hequal
        apply Subtype.ext
        apply Subtype.ext
        have hfirst : predecessorPattern first.val.val = pattern := first.property
        have hsecond : predecessorPattern second.val.val = pattern := second.property
        apply embedding_eq_of_pattern_roots hbody hproper first.val.val second.val.val
          (hfirst.trans hsecond.symm)
        intro slot hroot
        have hpatternRoot : pattern slot = none := by rw [← hfirst]; exact hroot
        exact congrFun hequal ⟨slot, hpatternRoot⟩
      have hcount := Fintype.card_le_of_injective rootPositions hinjective
      rw [Fintype.card_fun, Fintype.card_fin] at hcount
      exact hcount.trans (pow_le_pow_right₀ (by omega : 1 ≤ body) hrootsCount)
    · haveI : IsEmpty {sites : Good // parent sites = pattern} := not_nonempty_iff.mp hnonempty
      simp
  have hdecompose : Fintype.card Good =
      ∑ pattern : Patterns, Fintype.card {sites : Good // parent sites = pattern} := by
    rw [← Fintype.card_sigma]
    exact (Fintype.card_congr (Equiv.sigmaFiberEquiv parent)).symm
  change Fintype.card Good ≤ _
  rw [hdecompose]
  calc
    _ ≤ ∑ _pattern : Patterns, body ^ (order / 2) :=
      Finset.sum_le_sum (fun pattern _ => hfiber pattern)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Patterns, Fintype.card_fun, Fintype.card_option, Fintype.card_fin, Nat.cast_id]

/-- Exact finite uniform normalization for the no-isolated event. -/
theorem selectionLaw_noIsolated_mass (body order : ℕ) (horder : order ≤ body) :
    (selectionLaw body order horder).eventMass NoIsolated =
      (Fintype.card {sites : Selection body order // NoIsolated sites} : ℝ) /
        (body.descFactorial order : ℝ) := by
  change (∑ sites : Selection body order, if NoIsolated sites then
    (Fintype.card (Selection body order) : ℝ)⁻¹ else 0) = _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← Fintype.card_subtype, selection_card]
  rfl

/-- Uniformly selected distinct roots have the full fixed-order rare-event
exponent. Its constant depends only on the selected order. -/
theorem selectionLaw_noIsolated_probability (body order : ℕ) (horder : 1 ≤ order)
    (hbody : 2 * order ≤ body) :
    (selectionLaw body order (by omega)).eventMass NoIsolated ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) / (body : ℝ) ^ ((order + 1) / 2) := by
  have hbodyTwo : 2 ≤ body := by omega
  have hproper : order < body := by omega
  have hbodyPositive : (0 : ℝ) < body := by exact_mod_cast (by omega : 0 < body)
  have hcount :
      (Fintype.card {sites : Selection body order // NoIsolated sites} : ℝ) ≤
        ((order + 1 : ℕ) : ℝ) ^ order * (body : ℝ) ^ (order / 2) := by
    exact_mod_cast noIsolated_selection_card_le body order hbodyTwo hproper
  have hfactorLower : (body : ℝ) / 2 ≤ ((body + 1 - order : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : order ≤ body + 1), Nat.cast_add, Nat.cast_one]
    have htwice : 2 * (order : ℝ) ≤ body := by exact_mod_cast hbody
    linarith
  have hdenominatorLower : ((body : ℝ) / 2) ^ order ≤ (body.descFactorial order : ℝ) := by
    apply (pow_le_pow_left₀ (by positivity) hfactorLower order).trans
    exact_mod_cast Nat.pow_sub_le_descFactorial body order
  have hdenominatorPositive : 0 < (body.descFactorial order : ℝ) :=
    lt_of_lt_of_le (pow_pos (by positivity) order) hdenominatorLower
  rw [selectionLaw_noIsolated_mass]
  calc
    _ ≤ (((order + 1 : ℕ) : ℝ) ^ order * (body : ℝ) ^ (order / 2)) /
        ((body : ℝ) / 2) ^ order := by
      exact (div_le_div_of_nonneg_right hcount hdenominatorPositive.le).trans
        (div_le_div_of_nonneg_left (by positivity) (pow_pos (by positivity) order) hdenominatorLower)
    _ = _ := by
      have hexponents : order / 2 + (order + 1) / 2 = order := by omega
      have hpowers : (body : ℝ) ^ order =
          (body : ℝ) ^ (order / 2) * (body : ℝ) ^ ((order + 1) / 2) := by
        rw [← pow_add, hexponents]
      push_cast
      rw [div_pow, mul_pow, hpowers]
      field_simp [hbodyPositive.ne']

end

end CurrentAFT.CycleSelections

end

section





/-!
# Finite Cauchy--Schwarz for the complete cycle partition function

The cyclic tensor contraction is a trace of a product of actual finite
matrices. At least two factors suffice for the Frobenius product bound;
there is no dimension factor and an unconstrained rank-one factor has
energy one. The expansion below keeps the closing edge explicitly.
-/

namespace CurrentAFT.CycleKernel

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Scalar : Type*} [Fintype Scalar]

def energy (matrix : Matrix Scalar Scalar ℝ) : ℝ :=
  ∑ first, ∑ second, matrix first second ^ 2

theorem energy_nonneg (matrix : Matrix Scalar Scalar ℝ) : 0 ≤ energy matrix :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem energy_mul_le (first second : Matrix Scalar Scalar ℝ) :
    energy (first * second) ≤ energy first * energy second := by
  unfold energy
  simp only [Matrix.mul_apply]
  calc
    _ ≤ ∑ start, ∑ ending, (∑ middle, first start middle ^ 2) *
        ∑ middle, second middle ending ^ 2 := by
      apply Finset.sum_le_sum
      intro start _
      apply Finset.sum_le_sum
      intro ending _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = (∑ start, ∑ middle, first start middle ^ 2) *
        ∑ ending, ∑ middle, second middle ending ^ 2 := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    _ = _ := by rw [Finset.sum_comm (f := fun ending middle => second middle ending ^ 2)]

/-- Product of a nonempty finite matrix sequence, avoiding any norm of the
identity matrix. -/
def chainProduct : (length : ℕ) → (Fin (length + 1) → Matrix Scalar Scalar ℝ) → Matrix Scalar Scalar ℝ
  | 0, matrices => matrices 0
  | length + 1, matrices => matrices 0 * chainProduct length (fun index => matrices index.succ)

theorem energy_chainProduct_le (length : ℕ) (matrices : Fin (length + 1) → Matrix Scalar Scalar ℝ) :
    energy (chainProduct length matrices) ≤ ∏ index, energy (matrices index) := by
  induction length with
  | zero => simp [chainProduct]
  | succ length ih =>
    apply (energy_mul_le (matrices 0) (chainProduct length (fun index => matrices index.succ))).trans
    rw [Fin.prod_univ_succ]
    exact mul_le_mul_of_nonneg_left (ih _) (energy_nonneg _)

/-- A trace pairs two matrices in their Frobenius inner product. -/
theorem trace_mul_sq_le (first second : Matrix Scalar Scalar ℝ) :
    Matrix.trace (first * second) ^ 2 ≤ energy first * energy second := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Scalar × Scalar))
    (fun pair => first pair.1 pair.2) (fun pair => second pair.2 pair.1)
  simp only [Fintype.sum_prod_type] at hcs
  have htrace : Matrix.trace (first * second) = ∑ start, ∑ ending, first start ending * second ending start := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [htrace]
  unfold energy
  rw [Finset.sum_comm (f := fun start ending => second ending start ^ 2)] at hcs
  exact hcs

/-- The complete cyclic product always contains at least two factors. -/
def cycleValue (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) : ℝ :=
  Matrix.trace (matrices 0 * chainProduct length (fun index => matrices index.succ))

/-- Complete squared cyclic contraction bound, without a palette-size loss. -/
theorem cycleValue_sq_le (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) :
    cycleValue length matrices ^ 2 ≤ ∏ index, energy (matrices index) := by
  apply (trace_mul_sq_le (matrices 0) (chainProduct length (fun index => matrices index.succ))).trans
  rw [Fin.prod_univ_succ]
  exact mul_le_mul_of_nonneg_left (energy_chainProduct_le length _) (energy_nonneg _)

/-- Exact open-chain expansion with every intermediate latent value summed. -/
theorem chainProduct_expansion (length : ℕ) (matrices : Fin (length + 1) → Matrix Scalar Scalar ℝ)
    (first last : Scalar) :
    chainProduct length matrices first last =
      ∑ middle : Fin length → Scalar,
        ∏ index : Fin (length + 1),
          matrices index ((Fin.cons first middle : Fin (length + 1) → Scalar) index) ((Fin.snoc middle last : Fin (length + 1) → Scalar) index) := by
  induction length generalizing first last with
  | zero => simp [chainProduct, Fin.snoc_zero]
  | succ length ih =>
    rw [chainProduct, Matrix.mul_apply]
    simp_rw [ih]
    conv_rhs =>
      rw [← (PathLikelihood.latentConsEquiv length).sum_comp, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro next _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro middle _
    simp only [PathLikelihood.latentConsEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
      ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- The matrix trace is exactly the complete independent-latent cycle sum,
including the last-to-first closing edge. -/
theorem cycleValue_expansion (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) :
    cycleValue length matrices =
      ∑ latent : Fin (length + 2) → Scalar,
        ∏ index : Fin (length + 2), matrices index (latent index) (latent (finRotate (length + 2) index)) := by
  unfold cycleValue Matrix.trace
  simp only [Matrix.diag_apply, Matrix.mul_apply]
  simp_rw [chainProduct_expansion]
  simp only [Finset.mul_sum]
  conv_rhs =>
    rw [← (PathLikelihood.latentConsEquiv (length + 1)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro first _
  conv_rhs =>
    rw [← (PathLikelihood.latentConsEquiv length).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro next _
  apply Finset.sum_congr rfl
  intro middle _
  have hrotate (index : Fin (length + 2)) :
      (Fin.cons first (Fin.cons next middle) : Fin (length + 2) → Scalar) (finRotate (length + 2) index) =
        (Fin.snoc (Fin.cons next middle) first : Fin (length + 2) → Scalar) index :=
    congrFun (Fin.snoc_eq_cons_rotate (Fin.cons next middle) first).symm index
  simp only [PathLikelihood.latentConsEquiv, Equiv.coe_fn_mk]
  simp_rw [hrotate]
  simp only [Fin.prod_univ_succ, ← Fin.cons_snoc_eq_snoc_cons, Fin.cons_zero, Fin.cons_succ]

/-- Finner's degree-two cycle inequality in its explicit finite sum form. -/
theorem cycle_partition_sq_le (length : ℕ) (matrices : Fin (length + 2) → Matrix Scalar Scalar ℝ) :
    (∑ latent : Fin (length + 2) → Scalar,
      ∏ index : Fin (length + 2), matrices index (latent index)
        (latent (finRotate (length + 2) index))) ^ 2 ≤
      ∏ index, energy (matrices index) := by
  rw [← cycleValue_expansion]
  exact cycleValue_sq_le length matrices

end

end CurrentAFT.CycleKernel

end

section







/-!
# Complete selected-cycle likelihood from its actual transfer matrices

Unselected edges use the rank-one boundary matrix and cost energy one.
Selected edges use their true one-difference response. The finite cyclic
Cauchy--Schwarz bound is applied to the whole cycle before any averaging.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Extend selected scalar factors by one off their actual embedding. -/
def embeddedFactor {Selected Pool : Type*} (embedding : Selected ↪ Pool)
    (factor : Selected → ℝ) (point : Pool) : ℝ :=
  if h : ∃ slot, embedding slot = point then factor (Classical.choose h) else 1

theorem embeddedFactor_at {Selected Pool : Type*} (embedding : Selected ↪ Pool)
    (factor : Selected → ℝ) (slot : Selected) :
    embeddedFactor embedding factor (embedding slot) = factor slot := by
  unfold embeddedFactor
  split_ifs with h
  · apply congrArg factor
    exact embedding.injective (Classical.choose_spec h)
  · exact False.elim (h ⟨slot, rfl⟩)

theorem embeddedFactor_absent {Selected Pool : Type*} (embedding : Selected ↪ Pool)
    (factor : Selected → ℝ) (point : Pool) (habsent : ¬∃ slot, embedding slot = point) :
    embeddedFactor embedding factor point = 1 := by
  unfold embeddedFactor
  rw [dif_neg habsent]

/-- Products through an embedding keep every selected factor exactly once. -/
theorem embeddedFactor_product {Selected Pool : Type*} [Fintype Selected] [Fintype Pool]
    (embedding : Selected ↪ Pool) (factor : Pool → Selected → ℝ) :
    (∏ point, embeddedFactor embedding (factor point) point) =
      ∏ slot, factor (embedding slot) slot := by
  have houtside (point : Pool) (_ : point ∈ (Finset.univ : Finset Pool))
      (hnot : point ∉ Finset.univ.map embedding) : embeddedFactor embedding (factor point) point = 1 := by
    apply embeddedFactor_absent
    intro hexists
    obtain ⟨slot, hslot⟩ := hexists
    exact hnot (Finset.mem_map.mpr ⟨slot, Finset.mem_univ _, hslot⟩)
  have hproduct := Finset.prod_subset (Finset.subset_univ (Finset.univ.map embedding)) houtside
  rw [← hproduct, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro slot _
  exact embeddedFactor_at embedding (factor (embedding slot)) slot

variable {Scalar Difference : Type*} [Fintype Scalar] [Fintype Difference]

/-- Exact cyclic feature law. For integer subtraction this is the protected
cycle, with the same latent scalar used at both adjacent roots. -/
def selectedFeatureLaw (body order : ℕ) (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order) :
    FiniteDist (Fin order → Difference) :=
  (FiniteDist.independent (fun _ : Fin body => source)).map (fun latent slot =>
    difference (latent ((finRotate body).symm (sites slot))) (latent (sites slot)))

/-- An unconstrained edge keeps the rank-one boundary matrix. -/
def constraintMatrix {body order : ℕ} (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order)
    (output : Fin order → Difference) (vertex : Fin body) : Matrix Scalar Scalar ℝ :=
  fun first second => PathLikelihood.boundary source first * PathLikelihood.boundary source second *
    embeddedFactor sites (fun slot => if difference first second = output slot then 1 else 0) vertex

/-- Every matrix has its actual marginal energy, or one for an unselected edge. -/
theorem constraintMatrix_energy {body order : ℕ} (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order)
    (output : Fin order → Difference) (vertex : Fin body) :
    CycleKernel.energy (constraintMatrix source difference sites output vertex) =
      embeddedFactor sites (fun slot => (PathLikelihood.marginal source difference).weight (output slot)) vertex := by
  by_cases hexists : ∃ slot, sites slot = vertex
  · obtain ⟨slot, rfl⟩ := hexists
    rw [embeddedFactor_at]
    have hmatrix : constraintMatrix source difference sites output (sites slot) =
        PathLikelihood.transfer source difference (output slot) := by
      ext first second
      unfold constraintMatrix PathLikelihood.transfer
      rw [embeddedFactor_at]
      split_ifs <;> ring
    rw [hmatrix]
    exact PathLikelihood.transfer_square_sum source difference (output slot)
  · have hfactor (factor : Fin order → ℝ) : embeddedFactor sites factor vertex = 1 :=
      embeddedFactor_absent sites factor vertex hexists
    unfold CycleKernel.energy constraintMatrix
    simp_rw [hfactor, mul_one, mul_pow, PathLikelihood.boundary_sq]
    simp only [← Finset.mul_sum, source.sum_one, mul_one]

/-- The exact selected joint mass is the full cyclic matrix partition sum. -/
theorem selectedFeatureLaw_partition (body order : ℕ) (source : FiniteDist Scalar)
    (difference : Scalar → Scalar → Difference) (sites : Selection body order)
    (output : Fin order → Difference) :
    (selectedFeatureLaw body order source difference sites).weight output =
      ∑ latent : Fin body → Scalar, ∏ index : Fin body,
        constraintMatrix source difference sites output (finRotate body index)
          (latent index) (latent (finRotate body index)) := by
  unfold selectedFeatureLaw
  simp only [FiniteDist.map_weight]
  apply Finset.sum_congr rfl
  intro latent _
  have hboundary :
      (∏ index : Fin body, PathLikelihood.boundary source (latent index) *
        PathLikelihood.boundary source (latent (finRotate body index))) =
      ∏ index : Fin body, source.weight (latent index) := by
    rw [Finset.prod_mul_distrib]
    rw [Equiv.prod_comp (finRotate body) (fun index => PathLikelihood.boundary source (latent index))]
    rw [← pow_two, ← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro index _
    exact PathLikelihood.boundary_sq source _
  have hconstraints :
      (∏ index : Fin body, embeddedFactor sites
        (fun slot => if difference (latent index) (latent (finRotate body index)) = output slot then (1 : ℝ) else 0)
        (finRotate body index)) =
      if (fun slot => difference (latent ((finRotate body).symm (sites slot))) (latent (sites slot))) = output
        then 1 else 0 := by
    have hreindex := Equiv.prod_comp (finRotate body) (fun vertex => embeddedFactor sites
      (fun slot => if difference (latent ((finRotate body).symm vertex)) (latent vertex) = output slot then (1 : ℝ) else 0) vertex)
    apply Eq.trans (by simpa only [Equiv.symm_apply_apply] using hreindex)
    rw [embeddedFactor_product, Fintype.prod_ite_zero, Finset.prod_const_one]
    simp only [funext_iff]
    congr 1
  symm
  change (∏ index, (PathLikelihood.boundary source (latent index) *
    PathLikelihood.boundary source (latent (finRotate body index))) * _) = _
  rw [Finset.prod_mul_distrib]
  rw [hboundary, hconstraints]
  split_ifs <;> simp [FiniteDist.independent]

/-- Genuine complete joint-mass bound for every fixed selection. Independence
is used only for the latent scalar table, never for the roots themselves. -/
theorem selectedFeatureLaw_weight_sq_le (body order : ℕ) (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (difference : Scalar → Scalar → Difference)
    (sites : Selection body order) (output : Fin order → Difference) :
    (selectedFeatureLaw body order source difference sites).weight output ^ 2 ≤
      ∏ slot, (PathLikelihood.marginal source difference).weight (output slot) := by
  have henergy :
      (∏ index : Fin body, CycleKernel.energy
        (constraintMatrix source difference sites output (finRotate body index))) =
      ∏ slot, (PathLikelihood.marginal source difference).weight (output slot) := by
    simp_rw [constraintMatrix_energy]
    rw [Equiv.prod_comp (finRotate body)]
    exact embeddedFactor_product sites (fun _ slot => (PathLikelihood.marginal source difference).weight (output slot))
  rw [selectedFeatureLaw_partition]
  rw [← henergy]
  cases body with
  | zero => omega
  | succ body =>
    cases body with
    | zero => omega
    | succ length =>
      exact CycleKernel.cycle_partition_sq_le length
        (fun index => constraintMatrix source difference sites output (finRotate (length + 2) index))

end

end CurrentAFT.CycleSelections

end

section





/-!
# Isolated selected cycle roots cancel under centering

The proof splits the actual independent latent edge product into the two
edges used by one isolated root and all remaining edges. Other selected
roots retain their full joint dependence. A centered test at the isolated
root therefore has zero expectation against every joint test of the others.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Assemble selected and complementary latent coordinates. -/
def assemble {Index Scalar : Type*} [DecidableEq Index] (selected : Finset Index)
    (chosen : selected → Scalar) (rest : {index : Index // index ∉ selected} → Scalar)
    (index : Index) : Scalar :=
  if h : index ∈ selected then chosen ⟨index, h⟩ else rest ⟨index, h⟩

@[simp] theorem assemble_selected {Index Scalar : Type*} [DecidableEq Index] (selected : Finset Index)
    (chosen : selected → Scalar) (rest : {index : Index // index ∉ selected} → Scalar)
    (index : Index) (hindex : index ∈ selected) :
    assemble selected chosen rest index = chosen ⟨index, hindex⟩ := by
  simp only [assemble, dif_pos hindex]

@[simp] theorem assemble_rest {Index Scalar : Type*} [DecidableEq Index] (selected : Finset Index)
    (chosen : selected → Scalar) (rest : {index : Index // index ∉ selected} → Scalar)
    (index : Index) (hindex : index ∉ selected) :
    assemble selected chosen rest index = rest ⟨index, hindex⟩ := by
  simp only [assemble, dif_neg hindex]

/-- Exact finite Fubini for a coordinate partition of the independent latent
product. The outer average fixes all unselected coordinates. -/
theorem product_partition_expectation {Index Scalar : Type*}
    [Fintype Index] [DecidableEq Index] [Fintype Scalar]
    (source : Index → FiniteDist Scalar) (selected : Finset Index)
    (test : (Index → Scalar) → ℝ) :
    (FiniteDist.independent source).expectation test =
      ∑ rest : {index : Index // index ∉ selected} → Scalar,
        (∏ index : {index : Index // index ∉ selected}, (source index).weight (rest index)) *
          ∑ chosen : selected → Scalar,
            (∏ index : selected, (source index).weight (chosen index)) *
              test (assemble selected chosen rest) := by
  let split := Equiv.piEquivPiSubtypeProd (fun index => index ∈ selected) (fun _ : Index => Scalar)
  unfold FiniteDist.expectation FiniteDist.independent
  rw [← split.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro rest _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chosen _
  have hweight : (∏ index, (source index).weight (split.symm (chosen, rest) index)) =
      (∏ index : selected, (source index).weight (chosen index)) *
        ∏ index : {index : Index // index ∉ selected}, (source index).weight (rest index) := by
    rw [← Fintype.prod_subtype_mul_prod_subtype (fun index => index ∈ selected)]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr (by ext; simp)
      intro index _
      change (source index).weight (if h : (index : Index) ∈ selected then chosen ⟨index, h⟩ else rest ⟨index, h⟩) = _
      simp only [dif_pos index.property]
    · apply Finset.prod_congr (by ext; simp)
      intro index _
      change (source index).weight (if h : (index : Index) ∈ selected then chosen ⟨index, h⟩ else rest ⟨index, h⟩) = _
      simp only [dif_neg index.property]
  change (∏ index, (source index).weight (split.symm (chosen, rest) index)) *
    test (assemble selected chosen rest) = _
  rw [hweight]
  ring

abbrev OtherSlots {order : ℕ} (slot : Fin order) := {other : Fin order // other ≠ slot}

/-- An isolated root is independent of the complete tuple of remaining
selected roots, in the exact centered-test formulation. -/
theorem isolated_centered_test_zero {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) (hisolated : Isolated sites slot)
    (test : ZMod modulus → ℝ)
    (hcentered : (ProtectedCycle.differenceLaw source value).expectation test = 0)
    (otherTest : (OtherSlots slot → ZMod modulus) → ℝ) :
    (selectedLaw body order modulus source value sites).expectation
      (fun root => test (root slot) * otherTest (fun other => root other)) = 0 := by
  haveI : Nonempty Scalar := by
    by_contra hnonempty
    haveI : IsEmpty Scalar := not_nonempty_iff.mp hnonempty
    have h := source.sum_one
    simp at h
  let support := latentSupport (sites slot)
  let first : support := ⟨sites slot, Finset.mem_insert_self _ _⟩
  let second : support := ⟨(finRotate body).symm (sites slot),
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩
  have hdistinct : second ≠ first := by
    intro hequal
    have hvalues := congrArg Subtype.val hequal
    exact ProtectedCycle.cycle_predecessor_ne body hbody (sites slot) hvalues
  have hpair := ProtectedCycle.independent_pair_expectation
    (fun _ : support => source) first second hdistinct
    (fun firstValue secondValue => test (value firstValue - value secondValue))
  have hdifference :
      (ProtectedCycle.differenceLaw source value).expectation test =
        ∑ firstValue, ∑ secondValue, source.weight firstValue * source.weight secondValue *
          test (value firstValue - value secondValue) := by
    rw [ProtectedCycle.differenceLaw, FiniteDist.expectation_map]
    simp only [FiniteDist.expectation, FiniteDist.prod_weight, Fintype.sum_prod_type, Function.comp_apply]
  have hselected :
      (∑ chosen : support → Scalar, (∏ index : support, source.weight (chosen index)) *
        test (value (chosen first) - value (chosen second))) = 0 := by
    simpa only [FiniteDist.expectation, FiniteDist.independent] using
      (hpair.trans hdifference.symm).trans hcentered
  unfold selectedLaw ProtectedCycle.cycleLaw
  rw [FiniteDist.expectation_map, FiniteDist.expectation_map]
  change (FiniteDist.independent (fun _ : Fin body => source)).expectation
    (fun latent => test (PublicCharge.cycleDifference (fun vertex => value (latent vertex)) (sites slot)) *
      otherTest (fun other => PublicCharge.cycleDifference
        (fun vertex => value (latent vertex)) (sites other))) = 0
  rw [product_partition_expectation (fun _ : Fin body => source) support]
  apply Finset.sum_eq_zero
  intro rest _
  let defaultChosen : support → Scalar := fun _ => Classical.choice inferInstance
  let otherValue := otherTest (fun other : OtherSlots slot => PublicCharge.cycleDifference
    (fun vertex => value (assemble support defaultChosen rest vertex)) (sites other))
  have hother (chosen : support → Scalar) :
      otherTest (fun other : OtherSlots slot => PublicCharge.cycleDifference
        (fun vertex => value (assemble support chosen rest vertex)) (sites other)) = otherValue := by
    apply congrArg otherTest
    funext other
    apply isolated_other_roots_unchanged sites slot other other.property hisolated
    intro vertex hnot
    have hnot' : vertex ∉ support := hnot
    rw [assemble_rest support chosen rest vertex hnot',
      assemble_rest support defaultChosen rest vertex hnot']
  have hroot (chosen : support → Scalar) :
      PublicCharge.cycleDifference (fun vertex => value (assemble support chosen rest vertex))
        (sites slot) = value (chosen first) - value (chosen second) := by
    dsimp only [PublicCharge.cycleDifference]
    rw [assemble_selected support chosen rest (sites slot) first.property,
      assemble_selected support chosen rest ((finRotate body).symm (sites slot)) second.property]
  simp_rw [hother, hroot, ← mul_assoc]
  rw [← Finset.sum_mul, hselected, zero_mul, mul_zero]



/-- The exact centered atom used to express a joint likelihood's full
coordinate-centering projection on product-reference support. -/
def centeredRootAtom {Color : Type*} [Fintype Color] (reference : FiniteDist Color)
    (input output : Color) : ℝ :=
  (if input = output then 1 else 0) / reference.weight output - 1

theorem centeredRootAtom_mean_zero {Color : Type*} [Fintype Color]
    (reference : FiniteDist Color) (output : Color) (houtput : reference.weight output ≠ 0) :
    reference.expectation (fun input => centeredRootAtom reference input output) = 0 := by
  unfold FiniteDist.expectation centeredRootAtom
  calc
    _ = (∑ input, if input = output then reference.weight input else 0) / reference.weight output -
        ∑ input, reference.weight input := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro input _
      by_cases h : input = output <;> simp only [h, if_true, if_false] <;> ring
    _ = 0 := by simp [reference.sum_one, houtput]

/-- The actual fully centered joint-density response, as its finite centered
atom formula. It keeps the complete selected-root joint law. -/
def centeredRootDensity {Index Color : Type*} [Fintype Index] [DecidableEq Index] [Fintype Color]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color)
    (output : Index → Color) : ℝ :=
  joint.expectation (fun input => ∏ index, centeredRootAtom (reference index) (input index) (output index))

/-- Any isolated selected site annihilates the whole centered joint-root
coefficient. The others may remain arbitrarily dependent through the cycle. -/
theorem isolated_centeredRootDensity_zero {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (slot : Fin order) (hisolated : Isolated sites slot)
    (output : Fin order → ZMod modulus)
    (houtput : (ProtectedCycle.differenceLaw source value).weight (output slot) ≠ 0) :
    centeredRootDensity (selectedLaw body order modulus source value sites)
      (fun _ => ProtectedCycle.differenceLaw source value) output = 0 := by
  have hzero := isolated_centered_test_zero body order modulus hbody source value sites slot hisolated
    (fun color => centeredRootAtom (ProtectedCycle.differenceLaw source value) color (output slot))
    (centeredRootAtom_mean_zero _ _ houtput)
    (fun other => ∏ index : OtherSlots slot,
      centeredRootAtom (ProtectedCycle.differenceLaw source value) (other index) (output index))
  unfold centeredRootDensity
  convert hzero using 1
  apply congrArg (selectedLaw body order modulus source value sites).expectation
  funext input
  exact Fintype.prod_eq_mul_prod_subtype_ne _ slot

end

end CurrentAFT.CycleSelections

end

section





/-!
# Finite L2 averaging supported on a rare public event

If every conditional coefficient vanishes outside a public event, its
mixture norm costs the event probability itself. Squared Cauchy--Schwarz
is applied before and after the reference average, so no square root of
that probability is lost.
-/

namespace CurrentAFT

open AFT
open scoped BigOperators Classical

noncomputable section

/-- Cauchy--Schwarz for a test supported on a finite event. -/
theorem weighted_event_square {Choice : Type*} [Fintype Choice]
    (law : FiniteDist Choice) (event : Choice → Prop) (test : Choice → ℝ)
    (hzero : ∀ choice, ¬event choice → test choice = 0) :
    law.expectation test ^ 2 ≤ law.eventMass event * law.expectation (fun choice => test choice ^ 2) := by
  let first := fun choice => Real.sqrt (law.weight choice) * (if event choice then (1 : ℝ) else 0)
  let second := fun choice => Real.sqrt (law.weight choice) * test choice
  have hdot : (∑ choice, first choice * second choice) = law.expectation test := by
    unfold FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro choice _
    by_cases hevent : event choice
    · simp only [first, second, if_pos hevent, mul_one]
      calc
        _ = Real.sqrt (law.weight choice) ^ 2 * test choice := by ring
        _ = _ := by rw [Real.sq_sqrt (law.nonneg choice)]
    · simp [first, second, hevent, hzero choice hevent]
  have hfirst : (∑ choice, first choice ^ 2) = law.eventMass event := by
    unfold FiniteDist.eventMass
    apply Finset.sum_congr rfl
    intro choice _
    by_cases hevent : event choice
    · simp only [first, if_pos hevent, mul_one, Real.sq_sqrt (law.nonneg choice)]
    · simp [first, hevent]
  have hsecond : (∑ choice, second choice ^ 2) = law.expectation (fun choice => test choice ^ 2) := by
    unfold FiniteDist.expectation
    apply Finset.sum_congr rfl
    intro choice _
    simp only [second, mul_pow, Real.sq_sqrt (law.nonneg choice)]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ first second
  rwa [hdot, hfirst, hsecond] at hcs

/-- Rare-event averaging in a real finite reference Hilbert space. Vanishing
is required only on reference support; zero atoms are allowed throughout. -/
theorem rare_mixture_l2Sq {Choice Output : Type*} [Fintype Choice] [Fintype Output]
    (law : FiniteDist Choice) (reference : FiniteDist Output)
    (event : Choice → Prop) (coefficient : Choice → Output → ℝ) (bound : ℝ)
    (hzero : ∀ choice, ¬event choice → ∀ output, reference.weight output ≠ 0 → coefficient choice output = 0)
    (hbound : ∀ choice, reference.l2Sq (coefficient choice) ≤ bound ^ 2) :
    reference.l2Sq (fun output => law.expectation (fun choice => coefficient choice output)) ≤
      law.eventMass event ^ 2 * bound ^ 2 := by
  let probability := law.eventMass event
  have hprobability : 0 ≤ probability := law.eventMass_nonneg event
  have hpoint (output : Output) :
      reference.weight output * law.expectation (fun choice => coefficient choice output) ^ 2 ≤
        reference.weight output *
          (probability * law.expectation (fun choice => coefficient choice output ^ 2)) := by
    by_cases hweight : reference.weight output = 0
    · simp [hweight]
    · exact mul_le_mul_of_nonneg_left
        (weighted_event_square law event (fun choice => coefficient choice output)
          (fun choice hevent => hzero choice hevent output hweight)) (reference.nonneg output)
  have hswap :
      (∑ output, reference.weight output *
        (probability * law.expectation (fun choice => coefficient choice output ^ 2))) =
      probability * law.expectation (fun choice => reference.l2Sq (coefficient choice)) := by
    simp only [FiniteDist.expectation, FiniteDist.l2Sq]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro choice _
    apply Finset.sum_congr rfl
    intro output _
    ring
  have hconditional (choice : Choice) :
      reference.l2Sq (coefficient choice) ≤ if event choice then bound ^ 2 else 0 := by
    by_cases hevent : event choice
    · simpa only [if_pos hevent] using hbound choice
    · rw [if_neg hevent]
      apply le_of_eq
      unfold FiniteDist.l2Sq FiniteDist.expectation
      apply Finset.sum_eq_zero
      intro output _
      by_cases hweight : reference.weight output = 0
      · simp [hweight]
      · change reference.weight output * coefficient choice output ^ 2 = 0
        rw [hzero choice hevent output hweight]
        ring
  have haverage : law.expectation (fun choice => reference.l2Sq (coefficient choice)) ≤
      probability * bound ^ 2 := by
    unfold FiniteDist.expectation
    calc
      _ ≤ ∑ choice, law.weight choice * (if event choice then bound ^ 2 else 0) :=
        Finset.sum_le_sum (fun choice _ =>
          mul_le_mul_of_nonneg_left (hconditional choice) (law.nonneg choice))
      _ = _ := by
        unfold probability FiniteDist.eventMass
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro choice _
        by_cases hevent : event choice <;> simp [hevent]
  have hsum := Finset.sum_le_sum (fun output (_ : output ∈ Finset.univ) => hpoint output)
  change reference.l2Sq (fun output => law.expectation (fun choice => coefficient choice output)) ≤ _ at hsum
  rw [hswap] at hsum
  apply hsum.trans
  calc
    _ ≤ probability * (probability * bound ^ 2) :=
      mul_le_mul_of_nonneg_left haverage hprobability
    _ = _ := by ring

end

end CurrentAFT

end

section









/-!
# A genuine two-root likelihood bound

Any finite coupling of a reference law with itself has likelihood energy
at most the number of reference-support atoms. This gives a stronger
second-order bound than the length-two path estimate, while higher orders
still require the path and forest analysis.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color : Type*} [Fintype Color]

/-- Positive reference support, counted before any norm bound. -/
def referenceSupport (reference : FiniteDist Color) : Finset Color :=
  Finset.univ.filter (fun color => 0 < reference.weight color)





























/-- Actual residue root reference from the protected finite Gaussian. -/
def gaussianRootReference (width : ℝ) (cutoff modulus : ℕ) [NeZero modulus] :
    FiniteDist (ZMod modulus) :=
  ProtectedCycle.differenceLaw (GaussianSource.windowGaussian width cutoff)
    (fun scalar => ((scalar : ℤ) : ZMod modulus))

/-- Reducing integer differences modulo the modulus cannot create more
support atoms than the actual integer difference interval. -/
theorem gaussianRootReference_support_card (width : ℝ) (cutoff modulus : ℕ) [NeZero modulus] :
    (referenceSupport (gaussianRootReference width cutoff modulus)).card ≤ 4 * cutoff + 1 := by
  let possible := Finset.univ.image
    (fun difference : GaussianSource.Window (2 * cutoff) => ((difference : ℤ) : ZMod modulus))
  have hsubset : referenceSupport (gaussianRootReference width cutoff modulus) ⊆ possible := by
    intro color hcolor
    by_contra hnot
    have hzero : (gaussianRootReference width cutoff modulus).weight color = 0 := by
      unfold gaussianRootReference ProtectedCycle.differenceLaw
      simp only [FiniteDist.map_weight, Fintype.sum_prod_type]
      apply Finset.sum_eq_zero
      intro first _
      apply Finset.sum_eq_zero
      intro second _
      have hne : ((first : ℤ) : ZMod modulus) - ((second : ℤ) : ZMod modulus) ≠ color := by
        intro hequal
        apply hnot
        change color ∈ Finset.univ.image
          (fun difference : GaussianSource.Window (2 * cutoff) => ((difference : ℤ) : ZMod modulus))
        refine Finset.mem_image.mpr ⟨PathLikelihood.windowDifference cutoff second first, Finset.mem_univ _, ?_⟩
        simpa only [PathLikelihood.windowDifference_val, Int.cast_sub] using hequal
      simp [hne]
    have hpositive := (Finset.mem_filter.mp hcolor).2
    rw [hzero] at hpositive
    exact (lt_irrefl 0) hpositive
  calc
    _ ≤ possible.card := Finset.card_le_card hsubset
    _ ≤ Fintype.card (GaussianSource.Window (2 * cutoff)) := by
      exact (Finset.card_image_le).trans_eq (Finset.card_univ)
    _ = _ := PathLikelihood.windowDifference_card cutoff



/-- Full centered-density coefficients are linear in the actual joint law. -/
theorem centeredRootDensity_mix {Choice Index Color : Type*}
    [Fintype Choice] [Fintype Index] [DecidableEq Index] [Fintype Color]
    (law : FiniteDist Choice) (channel : Choice → FiniteDist (Index → Color))
    (reference : Index → FiniteDist Color) (output : Index → Color) :
    centeredRootDensity (law.mix channel) reference output =
      law.expectation (fun choice => centeredRootDensity (channel choice) reference output) := by
  unfold centeredRootDensity FiniteDist.expectation
  simp only [FiniteDist.mix_weight, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro choice _
  apply Finset.sum_congr rfl
  intro input _
  ring





end

end CurrentAFT.CycleSelections

end

section







/-!
# Exact centering contraction with zero reference atoms

Full positivity of the reference palette is unnecessary. It suffices that
every input with nonzero signed mass lies on product-reference support.
The actual selected-root law has that property by its exact marginals.
-/

namespace CurrentAFT.SupportedHoeffding

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color Index : Type*} [Fintype Color] [Fintype Index]

/-- Only the source atom must be positive for its centered atom to average
zero. Other reference atoms may vanish. -/
theorem centeredAtom_mean_of_source_positive (reference : FiniteDist Color)
    (source : Color) (hsource : 0 < reference.weight source) :
    (∑ output, reference.weight output * Hoeffding.centeredAtom reference source output) = 0 := by
  simp only [Hoeffding.centeredAtom, mul_sub, mul_one, Finset.sum_sub_distrib, reference.sum_one]
  have hpoint (output : Color) :
      reference.weight output * (if source = output then (reference.weight output)⁻¹ else 0) =
        if source = output then (1 : ℝ) else 0 := by
    by_cases hequal : source = output
    · subst output
      simp [hsource.ne']
    · simp [hequal]
  simp_rw [hpoint]
  simp

/-- Canonicality of the actual component under support-only positivity. -/
theorem densityComponent_canonical_of_support (reference : Index → FiniteDist Color)
    (mass : (Index → Color) → ℝ)
    (hsupport : ∀ input, mass input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (selected : Finset Index) :
    Hoeffding.Canonical reference selected (Hoeffding.densityComponent reference mass selected) := by
  constructor
  · intro first second hagree
    unfold Hoeffding.densityComponent
    apply Finset.sum_congr rfl
    intro input _
    congr 1
    apply Finset.prod_congr rfl
    intro index hindex
    rw [hagree index hindex]
  · intro index hindex output
    simp only [Hoeffding.densityComponent, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro input _
    by_cases hzero : mass input = 0
    · simp [hzero]
    · have hproduct (color : Color) :
          (∏ other ∈ selected, Hoeffding.centeredAtom (reference other)
            (input other) (Function.update output index color other)) =
          Hoeffding.centeredAtom (reference index) (input index) color *
            ∏ other ∈ selected.erase index,
              Hoeffding.centeredAtom (reference other) (input other) (output other) := by
        rw [← Finset.mul_prod_erase _ _ hindex]
        simp only [Function.update_self]
        congr 1
        apply Finset.prod_congr rfl
        intro other hother
        rw [Function.update_of_ne (Finset.mem_erase.mp hother).1]
      simp_rw [hproduct]
      have hterm (color : Color) :
          (reference index).weight color * (mass input *
            (Hoeffding.centeredAtom (reference index) (input index) color *
              ∏ other ∈ selected.erase index,
                Hoeffding.centeredAtom (reference other) (input other) (output other))) =
          (mass input * ∏ other ∈ selected.erase index,
            Hoeffding.centeredAtom (reference other) (input other) (output other)) *
              ((reference index).weight color * Hoeffding.centeredAtom (reference index) (input index) color) := by ring
      simp_rw [hterm]
      rw [← Finset.mul_sum,
        centeredAtom_mean_of_source_positive (reference index) (input index) (hsupport input hzero index), mul_zero]

/-- Full finite Parseval now permits zero atoms, provided the signed input
is supported by the product reference. -/
theorem densityComponent_parseval_of_support (reference : Index → FiniteDist Color)
    (mass : (Index → Color) → ℝ)
    (hsupport : ∀ input, mass input ≠ 0 → ∀ index, 0 < (reference index).weight (input index)) :
    (FiniteDist.independent reference).l2Sq
      (fun output => mass output / (FiniteDist.independent reference).weight output) =
        ∑ selected : Finset Index, (FiniteDist.independent reference).l2Sq
          (Hoeffding.densityComponent reference mass selected) := by
  have h := Hoeffding.canonical_sum_l2Sq reference Finset.univ
    (Hoeffding.densityComponent reference mass)
    (fun selected _ => densityComponent_canonical_of_support reference mass hsupport selected)
  simpa only [Hoeffding.densityComponent_sum] using h

/-- The exact orthogonal-projection contraction used for full root centering. -/
theorem canonical_component_energy_le (reference : Index → FiniteDist Color)
    (mass : (Index → Color) → ℝ)
    (hsupport : ∀ input, mass input ≠ 0 → ∀ index, 0 < (reference index).weight (input index))
    (selected : Finset Index) :
    (FiniteDist.independent reference).l2Sq (Hoeffding.densityComponent reference mass selected) ≤
      (FiniteDist.independent reference).l2Sq
        (fun output => mass output / (FiniteDist.independent reference).weight output) := by
  rw [densityComponent_parseval_of_support reference mass hsupport]
  exact Finset.single_le_sum (fun _ _ => FiniteDist.l2Sq_nonneg _ _) (Finset.mem_univ selected)

/-- The current coefficient's atom formula agrees with the established
Hoeffding projection, including its convention at zero reference atoms. -/
theorem centeredRootAtom_eq (reference : FiniteDist Color) (input output : Color) :
    CycleSelections.centeredRootAtom reference input output = Hoeffding.centeredAtom reference input output := by
  unfold CycleSelections.centeredRootAtom Hoeffding.centeredAtom
  by_cases hequal : input = output <;> simp [hequal, div_eq_mul_inv]

/-- Pointwise identity of the actual current centered coefficient and the
full Hoeffding component of its genuine joint law. -/
theorem centeredRootDensity_eq_component [DecidableEq Index]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color) (output : Index → Color) :
    CycleSelections.centeredRootDensity joint reference output =
      Hoeffding.densityComponent reference joint.weight Finset.univ output := by
  unfold CycleSelections.centeredRootDensity FiniteDist.expectation Hoeffding.densityComponent
  simp only [centeredRootAtom_eq]
  apply Finset.sum_congr (by ext; simp)
  intro input _
  congr 1

/-- Full centered-density contraction for the actual joint probability law,
with no pointwise positivity requirement outside its genuine support. -/
theorem centeredRootDensity_energy_le [DecidableEq Index]
    (joint : FiniteDist (Index → Color)) (reference : Index → FiniteDist Color)
    (hsupport : ∀ input, joint.weight input ≠ 0 → ∀ index, 0 < (reference index).weight (input index)) :
    (FiniteDist.independent reference).l2Sq (CycleSelections.centeredRootDensity joint reference) ≤
      (FiniteDist.independent reference).l2Sq
        (fun output => joint.weight output / (FiniteDist.independent reference).weight output) := by
  have hfunction : CycleSelections.centeredRootDensity joint reference =
      Hoeffding.densityComponent reference joint.weight Finset.univ :=
    funext (centeredRootDensity_eq_component joint reference)
  rw [hfunction]
  have h := canonical_component_energy_le reference joint.weight hsupport Finset.univ
  convert h using 1 <;>
    unfold FiniteDist.l2Sq FiniteDist.expectation FiniteDist.independent <;>
    apply Finset.sum_congr (by ext; simp) <;> intro output _ <;> rfl

end

end CurrentAFT.SupportedHoeffding

end

section











/-!
# Complete fixed-order protected-cycle root bound

The conditional law is the actual cyclic-difference pushforward. Its full
likelihood energy is bounded before centering, and the public selection
average gains the probability of having no isolated selected vertex.
-/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

variable {Color Index : Type*} [Fintype Color] [Fintype Index] [DecidableEq Index]

/-- Positive words are exactly words in the positive one-coordinate support. -/
def supportWordEquiv (reference : FiniteDist Color) :
    {word : Index → Color // ∀ index, 0 < reference.weight (word index)} ≃
      (Index → {color : Color // 0 < reference.weight color}) where
  toFun word index := ⟨word.val index, word.property index⟩
  invFun word := ⟨fun index => (word index).val, fun index => (word index).property⟩
  left_inv word := by rfl
  right_inv word := by rfl

/-- A complete pointwise squared-mass bound controls the full likelihood
energy by the support cardinality, without a smallest-atom loss. -/
theorem likelihoodEnergy_le_support_power (joint : FiniteDist (Index → Color))
    (reference : FiniteDist Color)
    (hpointwise : ∀ output, joint.weight output ^ 2 ≤ ∏ index, reference.weight (output index)) :
    (FiniteDist.independent (fun _ : Index => reference)).l2Sq
      (fun output => joint.weight output / (FiniteDist.independent (fun _ : Index => reference)).weight output) ≤
        ((referenceSupport reference).card : ℝ) ^ Fintype.card Index := by
  let product := FiniteDist.independent (fun _ : Index => reference)
  have hterm (output : Index → Color) :
      product.weight output * (joint.weight output / product.weight output) ^ 2 ≤
        if ∀ index, 0 < reference.weight (output index) then (1 : ℝ) else 0 := by
    by_cases hzero : product.weight output = 0
    · simp only [hzero, div_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
      split_ifs <;> norm_num
    · have hpositive : 0 < product.weight output :=
        lt_of_le_of_ne (product.nonneg output) (Ne.symm hzero)
      have hcoordinates : ∀ index, 0 < reference.weight (output index) := by
        intro index
        apply lt_of_le_of_ne (reference.nonneg _)
        intro hequal
        apply hzero
        change (∏ i, reference.weight (output i)) = 0
        exact Finset.prod_eq_zero (Finset.mem_univ index) hequal.symm
      rw [if_pos hcoordinates]
      have hmass : joint.weight output ^ 2 ≤ product.weight output := hpointwise output
      calc
        _ = joint.weight output ^ 2 / product.weight output := by field_simp
        _ ≤ 1 := (div_le_one hpositive).mpr hmass
  have hsum := Finset.sum_le_sum (fun output (_ : output ∈ Finset.univ) => hterm output)
  change product.l2Sq (fun output => joint.weight output / product.weight output) ≤ _ at hsum
  apply hsum.trans_eq
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, ← Fintype.card_subtype]
  rw [Fintype.card_congr (supportWordEquiv (Index := Index) reference), Fintype.card_fun]
  rw [Fintype.card_subtype]
  simp only [Nat.cast_pow, referenceSupport]

/-- The current cyclic feature definition agrees exactly with the protected
root law. No endpoint-independence assertion is used. -/
theorem selectedFeatureLaw_sub_eq {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (source : FiniteDist Scalar)
    (value : Scalar → ZMod modulus) (sites : Selection body order) :
    selectedFeatureLaw body order source (fun first second => value second - value first) sites =
      selectedLaw body order modulus source value sites := by
  unfold selectedFeatureLaw selectedLaw ProtectedCycle.cycleLaw
  rw [FiniteDist.map_map]
  rfl

/-- Swapping the two iid scalars reverses the convention for subtraction. -/
theorem marginal_sub_eq {Scalar : Type*} [Fintype Scalar]
    (source : FiniteDist Scalar) {modulus : ℕ} [NeZero modulus]
    (value : Scalar → ZMod modulus) :
    PathLikelihood.marginal source (fun first second => value second - value first) =
      ProtectedCycle.differenceLaw source value := by
  ext output
  unfold PathLikelihood.marginal ProtectedCycle.differenceLaw
  simp only [FiniteDist.map_weight, Fintype.sum_prod_type, FiniteDist.prod_weight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  split_ifs <;> ring

/-- The true selected root probability satisfies the full joint bound. -/
theorem selectedLaw_weight_sq_le {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (output : Fin order → ZMod modulus) :
    (selectedLaw body order modulus source value sites).weight output ^ 2 ≤
      ∏ slot, (ProtectedCycle.differenceLaw source value).weight (output slot) := by
  have h := selectedFeatureLaw_weight_sq_le body order hbody source
    (fun first second => value second - value first) sites output
  rwa [selectedFeatureLaw_sub_eq, marginal_sub_eq] at h

/-- The whole selected law is supported on the actual product reference. -/
theorem selectedLaw_reference_support {Scalar : Type*} [Fintype Scalar]
    (body order modulus : ℕ) [NeZero modulus] (hbody : 2 ≤ body)
    (source : FiniteDist Scalar) (value : Scalar → ZMod modulus)
    (sites : Selection body order) (input : Fin order → ZMod modulus)
    (hinput : (selectedLaw body order modulus source value sites).weight input ≠ 0) :
    ∀ slot, 0 < (ProtectedCycle.differenceLaw source value).weight (input slot) := by
  have hbound := selectedLaw_weight_sq_le body order modulus hbody source value sites input
  have hproduct : 0 < ∏ slot, (ProtectedCycle.differenceLaw source value).weight (input slot) :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hinput) hbound
  intro slot
  apply lt_of_le_of_ne ((ProtectedCycle.differenceLaw source value).nonneg _)
  intro hequal
  have hzero : (∏ i, (ProtectedCycle.differenceLaw source value).weight (input i)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ slot) hequal.symm
  linarith

/-- Complete conditional centered root energy for the concrete Gaussian
cycle, valid at every order and with every zero residue atom retained. -/
theorem selected_centered_energy_le (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (hbody : 2 ≤ body) (sites : Selection body order) :
    (FiniteDist.independent (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites)
        (fun _ => gaussianRootReference width cutoff modulus)) ≤ (4 * cutoff + 1 : ℝ) ^ order := by
  apply (SupportedHoeffding.centeredRootDensity_energy_le _ _
    (selectedLaw_reference_support body order modulus hbody _ _ sites)).trans
  apply (likelihoodEnergy_le_support_power _ _
    (selectedLaw_weight_sq_le body order modulus hbody _ _ sites)).trans
  simp only [Fintype.card_fin]
  exact pow_le_pow_left₀ (by positivity)
    (by exact_mod_cast gaussianRootReference_support_card width cutoff modulus) order

/-- Full fixed-order root smallness for the actual Gaussian cycle and the
actual uniform distinct public placement. The rare-event probability is
gained before taking the output norm. -/
theorem averaged_centered_norm_le (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * Real.sqrt ((4 * cutoff + 1 : ℝ) ^ order) /
        (body : ℝ) ^ ((order + 1) / 2) := by
  have hbodyTwo : 2 ≤ body := by omega
  let rootReference := gaussianRootReference width cutoff modulus
  let reference := FiniteDist.independent (fun _ : Fin order => rootReference)
  let placements := selectionLaw body order (by omega : order ≤ body)
  let coefficient := fun (sites : Selection body order) (output : Fin order → ZMod modulus) =>
    centeredRootDensity
      (selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites) (fun _ => rootReference) output
  let bound : ℝ := Real.sqrt ((4 * cutoff + 1 : ℝ) ^ order)
  have hboundNonneg : 0 ≤ bound := Real.sqrt_nonneg _
  have hboundSquare : bound ^ 2 = (4 * cutoff + 1 : ℝ) ^ order := Real.sq_sqrt (by positivity)
  have henergy (sites : Selection body order) : reference.l2Sq (coefficient sites) ≤ bound ^ 2 := by
    rw [hboundSquare]
    exact selected_centered_energy_le body order modulus cutoff width hbodyTwo sites
  have hzero (sites : Selection body order) (hnot : ¬NoIsolated sites)
      (output : Fin order → ZMod modulus) (houtput : reference.weight output ≠ 0) :
      coefficient sites output = 0 := by
    obtain ⟨slot, hslot⟩ := not_forall.mp hnot
    have hisolated : Isolated sites slot := by
      intro other hother hadjacent
      exact hslot ⟨other, hother, hadjacent⟩
    have hslotOutput : rootReference.weight (output slot) ≠ 0 := by
      intro hzero
      apply houtput
      change (∏ index, rootReference.weight (output index)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ slot) hzero
    exact isolated_centeredRootDensity_zero body order modulus hbodyTwo
      (GaussianSource.windowGaussian width cutoff)
      (fun scalar => ((scalar : ℤ) : ZMod modulus)) sites slot hisolated output hslotOutput
  have haverage := CurrentAFT.rare_mixture_l2Sq placements reference NoIsolated coefficient bound hzero henergy
  let average := centeredRootDensity
    (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
      (fun scalar => ((scalar : ℤ) : ZMod modulus))) (fun _ => rootReference)
  have havg : average = fun output => placements.expectation (fun sites => coefficient sites output) := by
    funext output
    exact centeredRootDensity_mix placements
      (selectedLaw body order modulus (GaussianSource.windowGaussian width cutoff)
        (fun scalar => ((scalar : ℤ) : ZMod modulus))) (fun _ => rootReference) output
  have haverageEnergy : reference.l2Sq average ≤ placements.eventMass NoIsolated ^ 2 * bound ^ 2 := by
    rw [havg]
    exact haverage
  have hprobability := placements.eventMass_nonneg NoIsolated
  have hprobabilityBound : placements.eventMass NoIsolated ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) / (body : ℝ) ^ ((order + 1) / 2) :=
    selectionLaw_noIsolated_probability body order horder hbody
  have hsquare := Real.sq_sqrt (reference.l2Sq_nonneg average)
  have hrootNonneg := Real.sqrt_nonneg (reference.l2Sq average)
  have hproductNonneg : 0 ≤ placements.eventMass NoIsolated * bound := mul_nonneg hprobability hboundNonneg
  have hrootBound : Real.sqrt (reference.l2Sq average) ≤ placements.eventMass NoIsolated * bound := by
    nlinarith
  change Real.sqrt (reference.l2Sq average) ≤
    (((2 * (order + 1) : ℕ) : ℝ) ^ order) * bound / (body : ℝ) ^ ((order + 1) / 2)
  calc
    _ ≤ placements.eventMass NoIsolated * bound := hrootBound
    _ ≤ ((((2 * (order + 1) : ℕ) : ℝ) ^ order) / (body : ℝ) ^ ((order + 1) / 2)) * bound :=
      mul_le_mul_of_nonneg_right hprobabilityBound hboundNonneg
    _ = _ := by ring

/-- Square roots commute with the natural powers used by the root bound. -/
theorem sqrt_nat_power (value : ℝ) (hvalue : 0 ≤ value) (order : ℕ) :
    Real.sqrt (value ^ order) = Real.sqrt value ^ order := by
  apply (Real.sqrt_eq_iff_eq_sq (pow_nonneg hvalue _) (pow_nonneg (Real.sqrt_nonneg _) _)).mpr
  rw [← pow_mul, Nat.mul_comm order 2, pow_mul, Real.sq_sqrt hvalue]





/-- The parity exponent in the exact counting estimate is at least the
half-order exponent in the root tag. -/
theorem root_ratio_bound (size : ℝ) (hsize : 1 ≤ size) (width : ℝ) (hwidth : 0 ≤ width) (order : ℕ) :
    Real.sqrt (width ^ order) / size ^ ((order + 1) / 2) ≤
      (Real.sqrt width / Real.sqrt size) ^ order := by
  have hsizePositive : 0 < size := lt_of_lt_of_le zero_lt_one hsize
  have hsqrtPositive : 0 < Real.sqrt size := Real.sqrt_pos.mpr hsizePositive
  have hpower : (Real.sqrt size ^ order) ^ 2 = size ^ order := by
    rw [← pow_mul, Nat.mul_comm order 2, pow_mul, Real.sq_sqrt hsizePositive.le]
  have hpowerBound : size ^ order ≤ (size ^ ((order + 1) / 2)) ^ 2 := by
    rw [← pow_mul]
    exact pow_le_pow_right₀ hsize (by omega)
  have hdenominator : Real.sqrt size ^ order ≤ size ^ ((order + 1) / 2) := by
    have hn := pow_nonneg (Real.sqrt_nonneg size) order
    have hm := pow_nonneg hsizePositive.le ((order + 1) / 2)
    nlinarith
  rw [div_pow, ← sqrt_nat_power width hwidth order]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (pow_pos hsqrtPositive _) hdenominator

/-- A root-tag form of the actual complete fixed-order estimate. -/
theorem averaged_centered_norm_le_tag (body order modulus cutoff : ℕ) [NeZero modulus]
    (width : ℝ) (horder : 1 ≤ order) (hbody : 2 * order ≤ body) :
    Real.sqrt ((FiniteDist.independent
      (fun _ : Fin order => gaussianRootReference width cutoff modulus)).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw body order modulus (by omega) (GaussianSource.windowGaussian width cutoff)
          (fun scalar => ((scalar : ℤ) : ZMod modulus)))
        (fun _ => gaussianRootReference width cutoff modulus))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) *
        (Real.sqrt (4 * cutoff + 1 : ℝ) / Real.sqrt (body : ℝ)) ^ order := by
  apply (averaged_centered_norm_le body order modulus cutoff width horder hbody).trans
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left
    (root_ratio_bound (body : ℝ) (by exact_mod_cast (by omega : 1 ≤ body)) _ (by positivity) order)
    (by positivity)



end

end CurrentAFT.CycleSelections

end

section





namespace CurrentAFT
end CurrentAFT
namespace CurrentAFT.CycleSelections
end CurrentAFT.CycleSelections
namespace CurrentAFT.CycleSelections.integerAveragedSelectedLaw
end CurrentAFT.CycleSelections.integerAveragedSelectedLaw




/-! # Protected-cycle root bound at the current public parameters -/

namespace CurrentAFT.CycleSelections

open AFT
open scoped BigOperators Classical

noncomputable section

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- The root-tag scale used in the current manuscript. -/
def currentRootTag (security : ℕ) : ℝ :=
  (Parameters.base security : ℝ) / (Parameters.scale security : ℝ) ^ 10

/-- Actual integer-difference support width at the chosen edge cutoff. -/
theorem current_root_support_width (security : ℕ) :
    4 * DiffuseProfiles.edgeCutoff security + 1 ≤ 2 * Parameters.base security ^ 2 := by
  unfold DiffuseProfiles.edgeCutoff Parameters.sourceCutoff
  have hdivision := Nat.div_mul_le_self (Parameters.base security ^ 2 - 1) 2
  have hbase := Parameters.base_ge_two security
  have hpower : 1 ≤ Parameters.base security ^ 2 := one_le_pow₀ (by omega)
  omega

attribute [local irreducible] Parameters.base Parameters.scale Parameters.bodySize
  Parameters.sourceWidth Parameters.sourceCutoff DiffuseProfiles.edgeCutoff

/-- The current body is larger than the root-support width at exactly the
root-tag scale, without a modulus-asymptotic assumption. -/
theorem current_root_ratio (security : ℕ) :
    Real.sqrt (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) /
      Real.sqrt (Parameters.bodySize security : ℝ) ≤ currentRootTag security := by
  have hbase : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  have hscale : (0 : ℝ) < Parameters.scale security := by
    unfold Parameters.scale
    exact_mod_cast pow_pos (Parameters.base_pos security) 8
  have hmodulus : (0 : ℝ) < Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).2.pos
  have hbody : (0 : ℝ) < Parameters.bodySize security := by
    unfold Parameters.bodySize
    push_cast
    positivity
  have hmodulusLower : 65536 * (Parameters.scale security : ℝ) ^ 8 ≤ Parameters.modulus security := by
    exact_mod_cast (Parameters.modulus_spec security).1
  have hwidth : (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) ≤
      2 * (Parameters.base security : ℝ) ^ 2 := by exact_mod_cast current_root_support_width security
  have hbodyLower : 2 * (Parameters.scale security : ℝ) ^ 20 ≤ Parameters.bodySize security := by
    have h := mul_le_mul_of_nonneg_right hmodulusLower
      (pow_nonneg hscale.le 12)
    have hp : (Parameters.scale security : ℝ) ^ 8 * (Parameters.scale security : ℝ) ^ 12 =
        (Parameters.scale security : ℝ) ^ 20 := by rw [← pow_add]
    rw [mul_assoc, hp] at h
    rw [Parameters.bodySize, Nat.cast_mul, Nat.cast_pow]
    nlinarith [pow_nonneg hscale.le 20]
  have hsqrtBody := Real.sq_sqrt hbody.le
  have hsqrtWidth := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 4 * DiffuseProfiles.edgeCutoff security + 1)
  have hscaled : (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) *
      ((Parameters.scale security : ℝ) ^ 10) ^ 2 ≤
        (Parameters.base security : ℝ) ^ 2 * Parameters.bodySize security := by
    rw [← pow_mul]
    calc
      _ ≤ (2 * (Parameters.base security : ℝ) ^ 2) * (Parameters.scale security : ℝ) ^ 20 :=
        mul_le_mul_of_nonneg_right hwidth (by positivity)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hbodyLower (sq_nonneg (Parameters.base security : ℝ))]
  have hcross : Real.sqrt (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) *
      (Parameters.scale security : ℝ) ^ 10 ≤
        Parameters.base security * Real.sqrt (Parameters.bodySize security : ℝ) := by
    have hfirst : 0 ≤ Real.sqrt (4 * DiffuseProfiles.edgeCutoff security + 1 : ℝ) *
        (Parameters.scale security : ℝ) ^ 10 := by positivity
    have hsecond : 0 ≤ (Parameters.base security : ℝ) * Real.sqrt (Parameters.bodySize security : ℝ) := by positivity
    nlinarith
  unfold currentRootTag
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hbody) (pow_pos hscale 10)).mpr
  exact hcross

/-- The explicit threshold `security ≥ 2D` simultaneously supplies enough
body vertices for every fixed order at most `D`. -/
theorem current_body_fixed_orders (maximum security : ℕ) (hsecurity : 2 * maximum ≤ security) :
    ∀ order ≤ maximum, 2 * order ≤ Parameters.bodySize security := by
  intro order horder
  have hbaseBody : Parameters.base security ≤ Parameters.bodySize security := by
    have hp : Parameters.base security ≤ Parameters.base security ^ 96 :=
      Nat.le_self_pow (by decide) _
    have hm : 1 ≤ Parameters.modulus security := (Parameters.modulus_spec security).2.one_le
    rw [Parameters.bodySize_eq]
    exact hp.trans (by simpa using Nat.mul_le_mul_right (Parameters.base security ^ 96) hm)
  have hsecurityBase : security ≤ Parameters.base security := by simp [Parameters.base]
  omega

/-- Actual current protected residue-root density at every admissible
fixed order, bounded by the manuscript's root tag. -/
theorem current_averaged_centered_norm_le (security order : ℕ)
    [NeZero (Parameters.modulus security)] (horder : 1 ≤ order)
    (hbody : 2 * order ≤ Parameters.bodySize security) :
    Real.sqrt ((FiniteDist.independent (fun _ : Fin order =>
      gaussianRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security)
        (Parameters.modulus security))).l2Sq
      (centeredRootDensity
        (averagedSelectedLaw (Parameters.bodySize security) order (Parameters.modulus security)
          (by omega) (DiffuseProfiles.edgeLaw security)
          (fun scalar => ((scalar : ℤ) : ZMod (Parameters.modulus security))))
        (fun _ => gaussianRootReference (Parameters.sourceWidth security) (DiffuseProfiles.edgeCutoff security)
          (Parameters.modulus security)))) ≤
      (((2 * (order + 1) : ℕ) : ℝ) ^ order) * currentRootTag security ^ order := by
  apply (averaged_centered_norm_le_tag (Parameters.bodySize security) order (Parameters.modulus security)
    (DiffuseProfiles.edgeCutoff security) (Parameters.sourceWidth security) horder hbody).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) (current_root_ratio security) order) (by positivity)





/-- The chosen root tag is exactly the indicated negative base power. -/
theorem currentRootTag_eq (security : ℕ) :
    currentRootTag security = 1 / (Parameters.base security : ℝ) ^ 79 := by
  have hb : (0 : ℝ) < Parameters.base security := by exact_mod_cast Parameters.base_pos security
  rw [currentRootTag, Parameters.scale, Nat.cast_pow, ← pow_mul]
  field_simp













end

end CurrentAFT.CycleSelections

end


