-- Prove2me | Definitions.Def_OAIErdos3B109
-- name    : OAIErdos3B109
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-09T01:48:49.181472+00:00
-- url     : https://prove2.me/theorems/1354b681-f315-4146-ab16-2d4615990438
-- title:
--   OpenAI Erdős-3 split, definitions bundle 110 of 132
-- statement:
--   Definitions bundle 110 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B108`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 110 available.
--
--   Modules: `OAI.Erdos3.VectorPolynomial.RationalTagConstraint`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.BudgetLE`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.BudgetLE.mono`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.exists_rationalSpace_spanning`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.member`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.rationalSpace`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.rationalSpace_of_ne`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.rationalSpace_self`, `OAI.Erdos3.VectorPolynomial.RationalTagConstraint.retained_le_span`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.empty`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.exists_bounded_tag_bases`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.exists_bounded_tag_bases_univ`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.inter`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.monoB`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.singleton`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.subset`, `OAI.Erdos3.VectorPolynomial.RationalTaggedConstraintCertificate.trans`, `OAI.Erdos3.VectorPolynomial.exists_finite_rational_stage_branches`, `OAI.Erdos3.VectorPolynomial.exists_finite_rational_tag_constraint_lists`, `OAI.Erdos3.VectorPolynomial.exists_finite_rational_tag_constraints`, `OAI.Erdos3.VectorPolynomial.exists_finite_rational_tagged_certificate_sets`, `OAI.Erdos3.VectorPolynomial.exists_rationalTagConstraintList_basis`, `OAI.Erdos3.VectorPolynomial.rationalTagConstraintIntersection`, `OAI.Erdos3.VectorPolynomial.rationalTagConstraintList_basis_member_iff`, `_private.Linear.RationalTagConstraintBasis.0.OAI.Erdos3.VectorPolynomial.constraint_realSpaces_member_iff`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B117

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure RationalTagConstraint {m : ℕ} (J : Fin m → Type*) where
  tag : Fin m
  count : ℕ
  generators : Fin count → J tag → ℚ

namespace RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*}

def member (c : RationalTagConstraint J) {X : Type*}
    (point : (X ⊕ (Σ j, J j)) → ℝ) : Prop :=
  (fun i => point (Sum.inr ⟨c.tag, i⟩)) ∈
    Submodule.span ℝ (Set.range (fun a i => (c.generators a i : ℝ)))

def BudgetLE (c : RationalTagConstraint J) (B : ℝ) : Prop :=
  (c.count : ℝ) ≤ B ∧ ∀ a i, rationalLogHeight (c.generators a i) ≤ B

theorem BudgetLE.mono {c : RationalTagConstraint J} {B B' : ℝ}
    (h : c.BudgetLE B) (hBB' : B ≤ B') : c.BudgetLE B' :=
  ⟨h.1.trans hBB', fun a i => (h.2 a i).trans hBB'⟩

end RationalTagConstraint

def RationalTaggedConstraintCertificate {m : ℕ} (J : Fin m → Type*) {X : Type*}
    (Kinitial K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (B : ℝ) (Cblocks : ℕ) : Prop :=
  ∃ cs : List (RationalTagConstraint J), cs.length ≤ Cblocks ∧
    (∀ c ∈ cs, c.BudgetLE B) ∧
    K = Kinitial ∩ {t | ∀ c ∈ cs, c.member t}

namespace RationalTaggedConstraintCertificate

variable {m : ℕ} {J : Fin m → Type*} {X : Type*}
  {K₀ K₁ K₂ : Set ((X ⊕ (Σ j, J j)) → ℝ)} {B B' : ℝ} {C C₁ C₂ : ℕ}

theorem empty (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (B : ℝ) :
    RationalTaggedConstraintCertificate J K K B 0 := by
  refine ⟨[], le_rfl, ?_, ?_⟩
  · simp
  · simp

theorem monoB (h : RationalTaggedConstraintCertificate J K₀ K₁ B C)
    (hBB' : B ≤ B') : RationalTaggedConstraintCertificate J K₀ K₁ B' C := by
  obtain ⟨cs, hlength, hbudget, hK⟩ := h
  exact ⟨cs, hlength, fun c hc => (hbudget c hc).mono hBB', hK⟩

theorem subset (h : RationalTaggedConstraintCertificate J K₀ K₁ B C) : K₁ ⊆ K₀ := by
  obtain ⟨cs, _, _, rfl⟩ := h
  exact Set.inter_subset_left

theorem singleton (c : RationalTagConstraint J) (hc : c.BudgetLE B)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) :
    RationalTaggedConstraintCertificate J K (K ∩ {t | c.member t}) B 1 := by
  refine ⟨[c], le_rfl, ?_, ?_⟩
  · simpa using hc
  · simp

theorem trans (h₁ : RationalTaggedConstraintCertificate J K₀ K₁ B C₁)
    (h₂ : RationalTaggedConstraintCertificate J K₁ K₂ B C₂) :
    RationalTaggedConstraintCertificate J K₀ K₂ B (C₁ + C₂) := by
  obtain ⟨cs, hcs, hcb, hK₁⟩ := h₁
  obtain ⟨ds, hds, hdb, hK₂⟩ := h₂
  refine ⟨cs ++ ds, ?_, ?_, ?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hcs hds
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcb c hc
    · exact hdb c hc
  · rw [hK₂, hK₁]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_append,
      or_imp, forall_and]
    exact and_assoc

theorem inter (h₁ : RationalTaggedConstraintCertificate J K₀ K₁ B C₁)
    (h₂ : RationalTaggedConstraintCertificate J K₀ K₂ B C₂) :
    RationalTaggedConstraintCertificate J K₀ (K₁ ∩ K₂) B (C₁ + C₂) := by
  obtain ⟨cs, hcs, hcb, hK₁⟩ := h₁
  obtain ⟨ds, hds, hdb, hK₂⟩ := h₂
  refine ⟨cs ++ ds, ?_, ?_, ?_⟩
  · simpa only [List.length_append] using Nat.add_le_add hcs hds
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcb c hc
    · exact hdb c hc
  · rw [hK₁, hK₂]
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_append,
      or_imp, forall_and]
    tauto

end RationalTaggedConstraintCertificate

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*} {X : Type*}

theorem retained_le_span (c : RationalTagConstraint J)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)}
    (hretained : ∀ point, (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ U j) → point ∈ K)
    (hmember : ∀ point ∈ K, c.member point) :
    U c.tag ≤ Submodule.span ℝ (Set.range (fun a i => (c.generators a i : ℝ))) := by
  classical
  intro v hv
  let tags : ∀ j, J j → ℝ := Function.update (fun j => (0 : J j → ℝ)) c.tag v
  let point : (X ⊕ (Σ j, J j)) → ℝ := Sum.elim 0 (fun a => tags a.1 a.2)
  have hpoint : point ∈ K := by
    apply hretained
    intro j
    change tags j ∈ U j
    by_cases hj : j = c.tag
    · subst j
      simpa only [tags, Function.update_self] using hv
    · simpa only [tags, Function.update_of_ne hj] using (U j).zero_mem
  have hc := hmember point hpoint
  simpa only [member, point, Sum.elim_inr, tags, Function.update_self] using hc

end Erdos3.VectorPolynomial.RationalTagConstraint

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_finite_rational_tag_constraints
    (p : ℝ) (_hp : 0 ≤ p) (d : ℕ) (hJ : ∀ j, Fintype.card (J j) ≤ d) :
    ∃ n : ℕ,
      n ≤ m * (⌊p⌋₊ + 1) *
        (((2 * ⌈Real.exp p⌉₊ + 1) * (⌈Real.exp p⌉₊ + 1)) ^ (⌊p⌋₊ * d)) ∧
      ∃ candidate : Fin n → RationalTagConstraint J,
        (∀ i, (candidate i).BudgetLE p) ∧
        ∀ c : RationalTagConstraint J, c.BudgetLE p → ∃ i, candidate i = c := by
  classical
  let N := ⌊p⌋₊
  let H := ⌈Real.exp p⌉₊
  let R := boundedRationalCandidates H
  let Code := Σ j : Fin m, Σ n : Fin (N + 1), (Fin n.val × J j → R)
  let raw : Code → RationalTagConstraint J := fun c =>
    { tag := c.1, count := c.2.1.val,
      generators := fun a i => (c.2.2 (a, i)).val }
  have hR : R.card ≤ (2 * H + 1) * (H + 1) := boundedRationalCandidates_card H
  have hcard : Fintype.card Code ≤
      m * (N + 1) * (((2 * H + 1) * (H + 1)) ^ (N * d)) := by
    dsimp only [Code]
    simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_prod,
      Fintype.card_fin, Fintype.card_coe]
    calc
      _ ≤ ∑ _j : Fin m, ∑ _n : Fin (N + 1),
          ((2 * H + 1) * (H + 1)) ^ (N * d) := by
        apply Finset.sum_le_sum
        intro j _
        apply Finset.sum_le_sum
        intro n _
        exact (Nat.pow_le_pow_left hR _).trans
          (Nat.pow_le_pow_right (by positivity)
            (Nat.mul_le_mul (Nat.le_of_lt_succ n.isLt) (hJ j)))
      _ = _ := by simp [Nat.mul_assoc]
  let e := Fintype.equivFin Code
  let candidates := fun i : Fin (Fintype.card Code) => raw (e.symm i)
  have hcover (c : RationalTagConstraint J) (hc : c.BudgetLE p) :
      ∃ i, candidates i = c := by
    have hcN : c.count ≤ N := Nat.le_floor hc.1
    let v : Code := ⟨c.tag, ⟨c.count, Nat.lt_succ_of_le hcN⟩,
      fun a => ⟨c.generators a.1 a.2,
        mem_boundedRationalCandidates (rationalHeightLE_ceil_exp (hc.2 a.1 a.2))⟩⟩
    refine ⟨e v, ?_⟩
    simp only [candidates, Equiv.symm_apply_apply]
    rfl
  obtain ⟨n, hn, candidate, hvalid, _, hcomplete⟩ :=
    exists_filtered_finite_enumeration candidates (fun c => c.BudgetLE p)
  exact ⟨n, hn.trans hcard, candidate, hvalid, fun c hc => hcomplete c hc (hcover c hc)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_finite_rational_tag_constraint_lists
    (p : ℝ) (hp : 0 ≤ p) (N : ℕ)
    (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hN : (N : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 8) ^ 8) ∧
      ∃ candidate : Fin n → List (RationalTagConstraint J),
        (∀ i, (candidate i).length ≤ N) ∧
        (∀ i c, c ∈ candidate i → c.BudgetLE p) ∧
        ∀ cs : List (RationalTagConstraint J), cs.length ≤ N →
          (∀ c ∈ cs, c.BudgetLE p) → ∃ i, candidate i = cs := by
  classical
  let d := Fintype.card (Σ j, J j)
  have hdim (j : Fin m) : Fintype.card (J j) ≤ d :=
    Fintype.card_le_of_injective (Sigma.mk j) sigma_mk_injective
  obtain ⟨M, hM, entries, hentries, hcover⟩ :=
    exists_finite_rational_tag_constraints p hp d hdim
  obtain ⟨n, hn, candidate, hlen, hvalid, hcomplete⟩ :=
    exists_finite_bounded_list_enumeration entries (fun c => c.BudgetLE p) hentries hcover N
  have hcount : (n : ℝ) ≤ Real.exp ((p + 8) ^ 8) := by
    apply le_trans _ (rationalConstraint_list_count_le_exp_of_le M m ⌊p⌋₊ d N
      hp hm (Nat.floor_le hp) hJ hN hM)
    exact_mod_cast hn.trans (Nat.pow_le_pow_right (by omega : 0 < M + 1) (Nat.le_succ N))
  exact ⟨n, hcount, candidate, hlen, hvalid, hcomplete⟩

theorem exists_finite_rational_tagged_certificate_sets
    {X : Type*} (Kinitial : Set ((X ⊕ (Σ j, J j)) → ℝ))
    (p : ℝ) (hp : 0 ≤ p) (N : ℕ)
    (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hN : (N : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((p + 8) ^ 8) ∧
      ∃ candidate : Fin n → Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ i, RationalTaggedConstraintCertificate J Kinitial (candidate i) p N) ∧
        ∀ K, RationalTaggedConstraintCertificate J Kinitial K p N →
          ∃ i, candidate i = K := by
  obtain ⟨n, hn, lists, hlen, hvalid, hcomplete⟩ :=
    exists_finite_rational_tag_constraint_lists p hp N hm hJ hN
  let sets := fun i : Fin n => Kinitial ∩ {t | ∀ c ∈ lists i, c.member t}
  refine ⟨n, hn, sets, ?_, ?_⟩
  · intro i
    exact ⟨lists i, hlen i, hvalid i, rfl⟩
  · intro K hK
    obtain ⟨cs, hcs, hbudget, hidentity⟩ := hK
    obtain ⟨i, hi⟩ := hcomplete cs hcs hbudget
    refine ⟨i, ?_⟩
    dsimp only [sets]
    rw [hi]
    exact hidentity.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

theorem exists_finite_rational_stage_branches {X : Type*}
    (Kinitial : Set ((X ⊕ (Σ j, J j)) → ℝ)) (p qlog : ℝ) (hp : 0 ≤ p)
    (N : ℕ) (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hN : (N : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (qlog + (p + 8) ^ 8) ∧
      ∃ candidate : Fin n → ℕ × Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ i, 0 < (candidate i).1 ∧ (candidate i).1 ≤ ⌊Real.exp qlog⌋₊ ∧
          RationalTaggedConstraintCertificate J Kinitial (candidate i).2 p N) ∧
        ∀ (q : ℕ) K, 0 < q → (q : ℝ) ≤ Real.exp qlog →
          RationalTaggedConstraintCertificate J Kinitial K p N →
          ∃ i, candidate i = (q, K) := by
  classical
  obtain ⟨nK, hnK, spaces, hspace, hcover⟩ :=
    exists_finite_rational_tagged_certificate_sets Kinitial p hp N hm hJ hN
  let Q : ℕ := ⌊Real.exp qlog⌋₊
  let Index := Fin Q × Fin nK
  let e : Index ≃ Fin (Fintype.card Index) := Fintype.equivFin Index
  let candidate := fun i : Fin (Fintype.card Index) =>
    ((e.symm i).1.val + 1, spaces (e.symm i).2)
  refine ⟨Fintype.card Index, ?_, candidate, ?_, ?_⟩
  · have hQ : (Q : ℝ) ≤ Real.exp qlog := Nat.floor_le (Real.exp_nonneg _)
    change ((Fintype.card (Fin Q × Fin nK) : ℕ) : ℝ) ≤ _
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Nat.cast_mul]
    exact (mul_le_mul hQ hnK (Nat.cast_nonneg _) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm
  · intro i
    refine ⟨Nat.succ_pos _, ?_, hspace _⟩
    exact (e.symm i).1.isLt
  · intro q K hq hqcap hK
    obtain ⟨j, hj⟩ := hcover K hK
    have hqQ : q ≤ Q := Nat.le_floor hqcap
    let code : Index := (⟨q - 1, by omega⟩, j)
    refine ⟨e code, ?_⟩
    change ((e.symm (e code)).1.val + 1, spaces (e.symm (e code)).2) = (q, K)
    rw [Equiv.symm_apply_apply]
    exact Prod.ext (by dsimp [code]; omega) hj

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial.RationalTagConstraint

open Module

variable {m : ℕ} {J : Fin m → Type*}

noncomputable def rationalSpace (c : RationalTagConstraint J) (j : Fin m) :
    Submodule ℚ (J j → ℚ) :=
  if h : j = c.tag then h.symm ▸ Submodule.span ℚ (Set.range c.generators) else ⊤

@[simp] theorem rationalSpace_self (c : RationalTagConstraint J) :
    c.rationalSpace c.tag = Submodule.span ℚ (Set.range c.generators) := by
  simp [rationalSpace]

theorem rationalSpace_of_ne (c : RationalTagConstraint J) {j : Fin m} (hj : j ≠ c.tag) :
    c.rationalSpace j = ⊤ := by
  simp only [rationalSpace, dif_neg hj]

theorem exists_rationalSpace_spanning [∀ j, Fintype (J j)]
    (c : RationalTagConstraint J) (j : Fin m) {p : ℝ} (hp : 0 ≤ p) (hc : c.BudgetLE p) :
    ∃ w : Fin (Fintype.card (J j)) → J j → ℚ,
      Submodule.span ℚ (Set.range w) = c.rationalSpace j ∧
      ∀ a i, rationalLogHeight (w a i) ≤ p := by
  classical
  by_cases hj : j = c.tag
  · subst j
    rw [rationalSpace_self]
    exact exists_function_spanning_logHeight _ c.generators rfl hp hc.2
  · rw [c.rationalSpace_of_ne hj]
    apply exists_function_spanning_logHeight ⊤ (Pi.basisFun ℚ (J j))
      (Pi.basisFun ℚ (J j)).span_eq hp
    intro a i
    by_cases hai : i = a
    · subst i
      simpa [Pi.basisFun_apply, rationalLogHeight] using hp
    · simpa [Pi.basisFun_apply, Pi.single_apply, hai, rationalLogHeight] using hp

end Erdos3.VectorPolynomial.RationalTagConstraint

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalTagConstraintBasis
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {η B κ : Type*} [Fintype η] [Fintype B]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open Module

variable {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]

noncomputable def rationalTagConstraintIntersection (cs : List (RationalTagConstraint J))
    (j : Fin m) : Submodule ℚ (J j → ℚ) :=
  ⨅ i : Fin cs.length, (cs.get i).rationalSpace j

theorem exists_rationalTagConstraintList_basis
    (cs : List (RationalTagConstraint J)) (j : Fin m) {p : ℝ}
    (hp : 0 ≤ p) (hdim : (Fintype.card (J j) : ℝ) ≤ p)
    (hlen : (cs.length : ℝ) ≤ p) (hcs : ∀ c ∈ cs, c.BudgetLE p) :
    ∃ n : ℕ, n ≤ Fintype.card (J j) ∧
      ∃ b : Basis (Fin n) ℚ (rationalTagConstraintIntersection cs j),
        ∀ a i, rationalLogHeight ((b a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63 := by
  classical
  choose v hv hheight using fun i : Fin cs.length =>
    (cs.get i).exists_rationalSpace_spanning j hp (hcs _ (List.get_mem _ _))
  obtain ⟨n, hn, b, hb⟩ := exists_submodule_intersection_basis_logHeight
    (Pi.basisFun ℚ (J j)) (fun i : Fin cs.length => (cs.get i).rationalSpace j)
    v hv hp hdim (by simpa only [Fintype.card_fin] using hdim)
    (by simpa only [Fintype.card_fin] using hlen) hheight
  exact ⟨n, hn, b, hb⟩

theorem constraint_realSpaces_member_iff {X : Type*}
    (c : RationalTagConstraint J) (point : (X ⊕ (Σ j, J j)) → ℝ) :
    (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈ realRationalCoordinateSpan (c.rationalSpace j)) ↔
      c.member point := by
  constructor
  · intro h
    simpa only [RationalTagConstraint.rationalSpace_self, realRationalCoordinateSpan_span,
      RationalTagConstraint.member] using h c.tag
  · intro h j
    by_cases hj : j = c.tag
    · subst j
      simpa only [RationalTagConstraint.rationalSpace_self, realRationalCoordinateSpan_span,
        RationalTagConstraint.member] using h
    · rw [c.rationalSpace_of_ne hj, realRationalCoordinateSpan_top]
      trivial

theorem rationalTagConstraintList_basis_member_iff {X : Type*}
    (cs : List (RationalTagConstraint J)) (n : Fin m → ℕ)
    (b : ∀ j, Basis (Fin (n j)) ℚ (rationalTagConstraintIntersection cs j))
    (point : (X ⊕ (Σ j, J j)) → ℝ) :
    (∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))) ↔
      ∀ c ∈ cs, c.member point := by
  have hspan (j : Fin m) :
      Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ))) =
        ⨅ k : Fin cs.length, realRationalCoordinateSpan ((cs.get k).rationalSpace j) :=
    realRationalCoordinateSpan_iInf_basis
      (fun k : Fin cs.length => (cs.get k).rationalSpace j) (b j)
  simp_rw [hspan, Submodule.mem_iInf]
  constructor
  · intro h c hc
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    apply (constraint_realSpaces_member_iff c point).mp
    intro j
    simpa only [hk] using h j k
  · intro h j k
    exact (constraint_realSpaces_member_iff (cs.get k) point).mpr
      (h _ (List.get_mem _ _)) j

theorem RationalTaggedConstraintCertificate.exists_bounded_tag_bases {X : Type*}
    {Kinitial K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Kinitial K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (b : ∀ j, Basis (Fin (n j)) ℚ (W j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = Kinitial ∩ {point | ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
        Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))} := by
  classical
  obtain ⟨cs, hlen, hbudget, hK⟩ := hcert
  have hl : (cs.length : ℝ) ≤ p := (Nat.cast_le.mpr hlen).trans hblocks
  choose n hn b hb using fun j =>
    exists_rationalTagConstraintList_basis cs j hp (hdim j) hl hbudget
  refine ⟨rationalTagConstraintIntersection cs, n, b, hn, hb, ?_⟩
  rw [hK]
  ext point
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
    rationalTagConstraintList_basis_member_iff cs n b point]

theorem RationalTaggedConstraintCertificate.exists_bounded_tag_bases_univ {X : Type*}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p : ℝ} {Cblocks : ℕ}
    (hcert : RationalTaggedConstraintCertificate J Set.univ K p Cblocks)
    (hp : 0 ≤ p) (hdim : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hblocks : (Cblocks : ℝ) ≤ p) :
    ∃ (W : ∀ j, Submodule ℚ (J j → ℚ)) (n : Fin m → ℕ)
      (b : ∀ j, Basis (Fin (n j)) ℚ (W j)),
      (∀ j, n j ≤ Fintype.card (J j)) ∧
      (∀ j a i, rationalLogHeight ((b j a : J j → ℚ) i) ≤ ((p + 2) ^ 2 + 2) ^ 63) ∧
      K = {point | ∀ j, (fun i => point (Sum.inr ⟨j, i⟩)) ∈
        Submodule.span ℝ (Set.range (fun a i => ((b j a : J j → ℚ) i : ℝ)))} := by
  obtain ⟨W, n, b, hn, hb, hK⟩ := hcert.exists_bounded_tag_bases hp hdim hblocks
  exact ⟨W, n, b, hn, hb, by simpa only [Set.univ_inter] using hK⟩

end Erdos3.VectorPolynomial

end

end OAI

end


