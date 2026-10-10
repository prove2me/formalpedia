-- Prove2me | solution 1 for ArtinPrimitiveRoots.norm_memMomentD_le_of_opBound_edgeOp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-10T01:38:07.654293+00:00
-- url     : https://prove2.me/submissions/e9e9cc40-ba8d-4a0a-8e19-a89af86e1858

import Mathlib
import Definitions.Def_ArtinMinorOperator
import Definitions.Def_ArtinMemoryModel
import Definitions.Def_ArtinSieve
import Definitions.Def_ArtinMarkedSquare
import Definitions.Def_ArtinMinorSquare
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals
import Theorems.Thm_ArtinPrimitiveRoots_opBound_ghost_of_norm_le_ghostCoeff
import Theorems.Thm_ArtinPrimitiveRoots_opBound_edge_of_norm_le_edgeCoeff
import Theorems.Thm_ArtinPrimitiveRoots_sum_norm_edgeCoeff_mul_pow_le

section
/-! # L102D_OpDefs — alias of the bundle `Def_ArtinMinorOperator` (round 5)

The operator model now lives in `Definitions/Def_ArtinMinorOperator.lean` (same declarations, same
names). This module re-exports it and keeps `listProd`, which only the proofs use. -/

namespace ArtinPrimitiveRoots

end ArtinPrimitiveRoots
end

section
/-! # L102D_MemDefs — alias of the bundle `Def_ArtinMemoryModel` (round 5)

The memory model (root coordinates, `pathPhi`, `rootIL`, the memory space, `ghostOp`, `edgeOp`,
`memMomentD`, `dyadParams`, and `MemParams.RootIn`) now lives in
`Definitions/Def_ArtinMemoryModel.lean` (same declarations, same names). -/
end

section
/-! # L102D: generic chains of choice operators with birth records (for D7e)

A `BOp R α Sl` is an operator in the row convention, `(O f)(s) = ∑_{c ∈ ch} coeff(s,c) f(out(s,c))`,
together with the values `birth s c : Sl → Option ℕ` born at its slots. A list of them is a chain
(op `k` of the list carries index `k₀ + k`). `rchain mult` runs the chain on states augmented by the
record `π : ℕ → Sl → Option ℕ` of all births so far, with an extra multiplier `mult k π v` at op `k`
(`v` = the births of the op). Lemmas: linearity in the final function, pushing a factor of the final
function into the op where it is determined (`rchain_push`), dropping a passive record
(`rchain_drop`), the absolute bound, monotonicity and weighted row iteration. -/

namespace ArtinPrimitiveRoots.L102D

open Finset

/-- A birth-op over the scalars `R`. -/
structure BOp (R α Sl : Type) where
  γ : Type
  ch : Finset γ
  coeff : α → γ → R
  out : α → γ → α
  birth : α → γ → Sl → Option ℕ

variable {R α Sl : Type}

/-- Records: op index ↦ slot ↦ born value. -/
abbrev Rec (Sl : Type) := ℕ → Sl → Option ℕ

/-- Write the births `v` of op `k` into the record. -/
def recUpd (π : Rec Sl) (k : ℕ) (v : Sl → Option ℕ) : Rec Sl :=
  fun k' => if k' = k then v else π k'

lemma recUpd_lt {π : Rec Sl} {k k' : ℕ} {v : Sl → Option ℕ} (h : k' < k) :
    recUpd π k v k' = π k' := by
  unfold recUpd; rw [if_neg h.ne]

lemma recUpd_self (π : Rec Sl) (k : ℕ) (v : Sl → Option ℕ) : recUpd π k v k = v := by
  unfold recUpd; rw [if_pos rfl]

section Semiring

variable [CommSemiring R]

/-- The record chain with multipliers. -/
def rchain (mult : ℕ → Rec Sl → (Sl → Option ℕ) → R) :
    ℕ → List (BOp R α Sl) → (α → Rec Sl → R) → α → Rec Sl → R
  | _, [], f => f
  | k, o :: os, f => fun s π => ∑ c ∈ o.ch, o.coeff s c * mult k π (o.birth s c) *
      rchain mult (k + 1) os f (o.out s c) (recUpd π k (o.birth s c))

/-- The plain chain with per-op multipliers depending only on the births. -/
def mchain (m : ℕ → (Sl → Option ℕ) → R) : ℕ → List (BOp R α Sl) → (α → R) → α → R
  | _, [], f => f
  | k, o :: os, f => fun s => ∑ c ∈ o.ch, o.coeff s c * m k (o.birth s c) *
      mchain m (k + 1) os f (o.out s c)

lemma rchain_add (mult : ℕ → Rec Sl → (Sl → Option ℕ) → R) (k : ℕ) (os : List (BOp R α Sl))
    (f g : α → Rec Sl → R) (s : α) (π : Rec Sl) :
    rchain mult k os (fun s π => f s π + g s π) s π =
      rchain mult k os f s π + rchain mult k os g s π := by
  induction os generalizing k s π with
  | nil => rfl
  | cons o os ih =>
    simp only [rchain]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun c _ => ?_
    rw [ih]; ring

lemma rchain_smul (mult : ℕ → Rec Sl → (Sl → Option ℕ) → R) (k : ℕ) (os : List (BOp R α Sl))
    (a : R) (f : α → Rec Sl → R) (s : α) (π : Rec Sl) :
    rchain mult k os (fun s π => a * f s π) s π = a * rchain mult k os f s π := by
  induction os generalizing k s π with
  | nil => rfl
  | cons o os ih =>
    simp only [rchain]
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [ih]; ring

lemma rchain_sum {ι : Type} (mult : ℕ → Rec Sl → (Sl → Option ℕ) → R) (k : ℕ)
    (os : List (BOp R α Sl)) (T : Finset ι) (f : ι → α → Rec Sl → R) (s : α) (π : Rec Sl) :
    rchain mult k os (fun s π => ∑ i ∈ T, f i s π) s π = ∑ i ∈ T, rchain mult k os (f i) s π := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [sum_empty]
    induction os generalizing k s π with
    | nil => rfl
    | cons o os ih => simp only [rchain]; exact sum_eq_zero fun c _ => by rw [ih]; ring
  | insert i T hi ih =>
    simp only [sum_insert hi]
    rw [rchain_add, ih]

/-- The final function only matters on records agreeing with the start below the start index. -/
lemma rchain_congr (mult : ℕ → Rec Sl → (Sl → Option ℕ) → R) (k : ℕ) (os : List (BOp R α Sl))
    (f g : α → Rec Sl → R) (π₀ : Rec Sl)
    (h : ∀ s π, (∀ k' < k, π k' = π₀ k') → f s π = g s π) (s : α) :
    rchain mult k os f s π₀ = rchain mult k os g s π₀ := by
  induction os generalizing k π₀ s with
  | nil => exact h s π₀ fun _ _ => rfl
  | cons o os ih =>
    simp only [rchain]
    refine sum_congr rfl fun c _ => ?_
    congr 1
    refine ih (k + 1) _ (fun s' π hπ => h s' π fun k' hk' => ?_) _
    rw [hπ k' (by omega), recUpd_lt hk']

/-- A multiplier `ψ k π v` is *local* if it depends on `π` only below `k`. -/
def Local (ψ : ℕ → Rec Sl → (Sl → Option ℕ) → R) : Prop :=
  ∀ k (π π' : Rec Sl) v, (∀ k' < k, π k' = π' k') → ψ k π v = ψ k π' v

/-- **Pushing factors of the final function into the ops.** -/
lemma rchain_push (mult ψ : ℕ → Rec Sl → (Sl → Option ℕ) → R) (hψ : Local ψ) :
    ∀ (os : List (BOp R α Sl)) (k : ℕ) (f : α → Rec Sl → R) (s : α) (π : Rec Sl),
      rchain mult k os (fun s π => f s π * ∏ i ∈ range os.length, ψ (k + i) π (π (k + i))) s π =
        rchain (fun k π v => mult k π v * ψ k π v) k os f s π := by
  intro os
  induction os with
  | nil => intro k f s π; simp [rchain]
  | cons o os ih =>
    intro k f s π
    simp only [rchain]
    refine sum_congr rfl fun c _ => ?_
    set v := o.birth s c
    -- split off the factor of op `k`
    have hsplit : ∀ π', ∏ i ∈ range (o :: os).length, ψ (k + i) π' (π' (k + i)) =
        ψ k π' (π' k) * ∏ i ∈ range os.length, ψ (k + 1 + i) π' (π' (k + 1 + i)) := by
      intro π'
      rw [List.length_cons, prod_range_succ']
      simp only [add_zero]
      rw [mul_comm]
      congr 1
      refine prod_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring]
    simp only [hsplit]
    -- the factor of op `k` is constant along the rest of the chain
    have hconst : rchain mult (k + 1) os
        (fun s' π' => f s' π' * (ψ k π' (π' k) *
          ∏ i ∈ range os.length, ψ (k + 1 + i) π' (π' (k + 1 + i))))
        (o.out s c) (recUpd π k v) =
        ψ k π v * rchain mult (k + 1) os
          (fun s' π' => f s' π' * ∏ i ∈ range os.length, ψ (k + 1 + i) π' (π' (k + 1 + i)))
          (o.out s c) (recUpd π k v) := by
      rw [← rchain_smul]
      refine rchain_congr mult (k + 1) os _ _ _ (fun s' π' hπ' => ?_) _
      have h1 : π' k = v := by rw [hπ' k (by omega), recUpd_self]
      have h2 : ψ k π' (π' k) = ψ k π v := by
        rw [h1]
        refine hψ k π' π v fun k' hk' => ?_
        rw [hπ' k' (by omega), recUpd_lt hk']
      rw [h2]; ring
    rw [hconst, ih]
    ring

/-- **Dropping a passive record.** -/
lemma rchain_drop (m : ℕ → (Sl → Option ℕ) → R) :
    ∀ (os : List (BOp R α Sl)) (k : ℕ) (f : α → R) (s : α) (π : Rec Sl),
      rchain (fun k _ v => m k v) k os (fun s _ => f s) s π = mchain m k os f s := by
  intro os
  induction os with
  | nil => intro k f s π; rfl
  | cons o os ih =>
    intro k f s π
    simp only [rchain, mchain]
    exact sum_congr rfl fun c _ => by rw [ih]

end Semiring

/-! ## Absolute values -/

/-- The op with the norms of the coefficients. -/
noncomputable def BOp.abs (o : BOp ℂ α Sl) : BOp ℝ α Sl :=
  { o with coeff := fun s c => ‖o.coeff s c‖ }

lemma norm_rchain_le (mult : ℕ → Rec Sl → (Sl → Option ℕ) → ℂ) :
    ∀ (os : List (BOp ℂ α Sl)) (k : ℕ) (f : α → Rec Sl → ℂ) (s : α) (π : Rec Sl),
      ‖rchain mult k os f s π‖ ≤
        rchain (fun k π v => ‖mult k π v‖) k (os.map BOp.abs) (fun s π => ‖f s π‖) s π := by
  intro os
  induction os with
  | nil => intro k f s π; rfl
  | cons o os ih =>
    intro k f s π
    simp only [rchain, List.map_cons]
    refine (norm_sum_le _ _).trans (sum_le_sum fun c _ => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (ih _ _ _ _) (by positivity)

/-- Nonnegative real chains are nonnegative. -/
lemma rchain_nonneg (mult : ℕ → Rec Sl → (Sl → Option ℕ) → ℝ) (hm : ∀ k π v, 0 ≤ mult k π v) :
    ∀ (os : List (BOp ℝ α Sl)), (∀ o ∈ os, ∀ s c, 0 ≤ o.coeff s c) →
      ∀ (k : ℕ) (f : α → Rec Sl → ℝ), (∀ s π, 0 ≤ f s π) → ∀ s π, 0 ≤ rchain mult k os f s π := by
  intro os
  induction os with
  | nil => intro _ k f hf s π; exact hf s π
  | cons o os ih =>
    intro hos k f hf s π
    simp only [rchain]
    exact sum_nonneg fun c _ => mul_nonneg (mul_nonneg (hos o (by simp) s c) (hm _ _ _))
      (ih (fun o' ho' => hos o' (by simp [ho'])) _ _ hf _ _)

/-- Monotonicity in the multipliers and the final function. -/
lemma rchain_mono (mult mult' : ℕ → Rec Sl → (Sl → Option ℕ) → ℝ)
    (hm : ∀ k π v, 0 ≤ mult k π v) (hmm : ∀ k π v, mult k π v ≤ mult' k π v) :
    ∀ (os : List (BOp ℝ α Sl)), (∀ o ∈ os, ∀ s c, 0 ≤ o.coeff s c) →
      ∀ (k : ℕ) (f g : α → Rec Sl → ℝ), (∀ s π, 0 ≤ f s π) → (∀ s π, f s π ≤ g s π) →
        ∀ s π, rchain mult k os f s π ≤ rchain mult' k os g s π := by
  intro os
  induction os with
  | nil => intro _ k f g _ hfg s π; exact hfg s π
  | cons o os ih =>
    intro hos k f g hf hfg s π
    simp only [rchain]
    refine sum_le_sum fun c _ => ?_
    have hc := hos o (by simp) s c
    have hos' : ∀ o' ∈ os, ∀ s c, 0 ≤ o'.coeff s c := fun o' ho' => hos o' (by simp [ho'])
    have h1 := ih hos' (k + 1) f g hf hfg (o.out s c) (recUpd π k (o.birth s c))
    have h0 := rchain_nonneg mult hm os hos' (k + 1) f hf (o.out s c) (recUpd π k (o.birth s c))
    calc o.coeff s c * mult k π (o.birth s c) *
          rchain mult (k + 1) os f (o.out s c) (recUpd π k (o.birth s c)) ≤
        o.coeff s c * mult' k π (o.birth s c) *
          rchain mult (k + 1) os f (o.out s c) (recUpd π k (o.birth s c)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hmm _ _ _) hc) h0
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (mul_nonneg hc ((hm _ _ _).trans (hmm _ _ _)))

/-! ## Born sets and validity -/

section BornSet

variable [Fintype Sl] [DecidableEq Sl]

/-- The values born in `v`. -/
def bvals (v : Sl → Option ℕ) : Finset ℕ :=
  (univ.filter fun q => v q ≠ none).image fun q => (v q).getD 0

lemma mem_bvals {v : Sl → Option ℕ} {p : ℕ} : p ∈ bvals v ↔ ∃ q, v q = some p := by
  unfold bvals
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨q, ?_⟩
    cases h : v q with
    | none => exact absurd h hq
    | some p => simp
  · rintro ⟨q, hq⟩; exact ⟨q, by rw [hq]; simp, by rw [hq]; rfl⟩

/-- An op's births are valid against the born set `B`: injective, below `Q`, and new. -/
def ValidOp (Q : ℕ) (v : Sl → Option ℕ) (B : Finset ℕ) : Prop :=
  (∀ q q', v q ≠ none → v q = v q' → q = q') ∧ (∀ q p, v q = some p → p < Q ∧ p ∉ B)

/-- The values born at ops `< n`. -/
def valsBelow (π : Rec Sl) (n : ℕ) : Finset ℕ := (range n).biUnion fun k => bvals (π k)

/-- The record is valid below `n`: within-op injective, below `Q`, no repeats across ops. -/
def ValidBelow (Q : ℕ) (π : Rec Sl) (n : ℕ) : Prop :=
  (∀ k < n, ∀ q q', π k q ≠ none → π k q = π k q' → q = q') ∧
    (∀ k < n, ∀ q p, π k q = some p → p < Q) ∧
    (∀ k k', k < k' → k' < n → ∀ q q' p, π k q = some p → π k' q' = some p → False)

lemma valsBelow_succ (π : Rec Sl) (k : ℕ) (v : Sl → Option ℕ) :
    valsBelow (recUpd π k v) (k + 1) = valsBelow π k ∪ bvals v := by
  unfold valsBelow
  rw [Finset.range_add_one, biUnion_insert, recUpd_self, union_comm]
  congr 1
  refine biUnion_congr rfl fun k' hk' => ?_
  rw [recUpd_lt (mem_range.1 hk')]

lemma validBelow_succ (Q : ℕ) (π : Rec Sl) (k : ℕ) (v : Sl → Option ℕ) :
    ValidBelow Q (recUpd π k v) (k + 1) ↔ ValidBelow Q π k ∧ ValidOp Q v (valsBelow π k) := by
  have hlt : ∀ k' < k, recUpd π k v k' = π k' := fun k' h => recUpd_lt h
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨fun k' hk' => ?_, fun k' hk' => ?_, fun k₁ k₂ h12 hk₂ => ?_⟩, ?_, ?_⟩
    · have := h1 k' (by omega); rwa [hlt k' hk'] at this
    · have := h2 k' (by omega); rwa [hlt k' hk'] at this
    · have := h3 k₁ k₂ h12 (by omega); rwa [hlt k₁ (by omega), hlt k₂ hk₂] at this
    · have := h1 k (by omega); rwa [recUpd_self] at this
    · intro q p hq
      have hv : recUpd π k v k q = some p := by rw [recUpd_self]; exact hq
      refine ⟨h2 k (by omega) q p hv, fun hp => ?_⟩
      unfold valsBelow at hp
      rw [mem_biUnion] at hp
      obtain ⟨k', hk', hp'⟩ := hp
      obtain ⟨q', hq'⟩ := mem_bvals.1 hp'
      have hk'' := mem_range.1 hk'
      exact h3 k' k hk'' (by omega) q' q p (by rw [hlt k' hk'']; exact hq') hv
  · rintro ⟨⟨h1, h2, h3⟩, hv1, hv2⟩
    refine ⟨fun k' hk' => ?_, fun k' hk' => ?_, fun k₁ k₂ h12 hk₂ => ?_⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
      · rw [hlt k' h]; exact h1 k' h
      · subst h; rw [recUpd_self]; exact hv1
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | h
      · rw [hlt k' h]; exact h2 k' h
      · subst h; rw [recUpd_self]; exact fun q p hq => (hv2 q p hq).1
    · intro q q' p hq hq'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk₂ with h | h
      · rw [hlt k₁ (by omega), hlt k₂ h] at *; exact h3 k₁ k₂ h12 h q q' p hq hq'
      · subst h
        rw [hlt k₁ h12] at hq
        rw [recUpd_self] at hq'
        refine (hv2 q' p hq').2 ?_
        unfold valsBelow
        exact mem_biUnion.2 ⟨k₁, mem_range.2 h12, mem_bvals.2 ⟨q, hq⟩⟩

variable [CommSemiring R]

open Classical in
/-- The chain with born-set checks: each op's births must be valid against the born set. -/
noncomputable def bschain (Q : ℕ) : List (BOp R α Sl) → (α → R) → α → Finset ℕ → R
  | [], f => fun s _ => f s
  | o :: os, f => fun s B => ∑ c ∈ o.ch, o.coeff s c *
      (if ValidOp Q (o.birth s c) B then 1 else 0) * bschain Q os f (o.out s c) (B ∪ bvals (o.birth s c))

open Classical in
/-- **The born-set chain is the record chain with a final validity check.** -/
lemma bschain_eq_rchain (Q : ℕ) :
    ∀ (os : List (BOp R α Sl)) (k : ℕ) (f : α → R) (s : α) (π : Rec Sl),
      (if ValidBelow Q π k then 1 else 0) * bschain Q os f s (valsBelow π k) =
        rchain (fun _ _ _ => 1) k os
          (fun s π' => f s * (if ValidBelow Q π' (k + os.length) then 1 else 0)) s π := by
  intro os
  induction os with
  | nil => intro k f s π; simp [bschain, rchain, mul_comm]
  | cons o os ih =>
    intro k f s π
    simp only [bschain, rchain, mul_one]
    rw [mul_sum]
    refine sum_congr rfl fun c _ => ?_
    have h := ih (k + 1) f (o.out s c) (recUpd π k (o.birth s c))
    rw [valsBelow_succ, show k + 1 + os.length = k + (o :: os).length by simp; ring] at h
    rw [← h]
    by_cases hv : ValidBelow Q π k
    · by_cases hop : ValidOp Q (o.birth s c) (valsBelow π k)
      · rw [if_pos hv, if_pos hop, if_pos ((validBelow_succ Q π k _).2 ⟨hv, hop⟩)]; ring
      · rw [if_pos hv, if_neg hop, if_neg (fun h' => hop ((validBelow_succ Q π k _).1 h').2)]
        ring
    · rw [if_neg hv, if_neg (fun h' => hv ((validBelow_succ Q π k _).1 h').1)]; ring

end BornSet

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: membership in the memory model's finite sets, in closed form

`(Finset.mem_product.1 h).2` on `h : x ∈ P.edgeChoices` (or `P.stSet`, `P.ghostChoices`) makes the
elaborator unify through the membership instances down to `Multiset.bind` of `zSet` (≈ 1 s per use,
measured). These closed-form iff lemmas avoid it. -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable (P : MemParams)

lemma mem_edgeChoices_iff' (c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)) :
    c ∈ P.edgeChoices ↔ c.1 ∈ (univ : Finset (Finset (Fin P.K))) ∧ c.2.1 ∈ P.zSet ∧
      c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ (univ : Finset Bool) := by
  rw [MemParams.edgeChoices, mem_product, mem_product]

lemma tg_mem_of_mem_edgeChoices {c : Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)}
    (hc : c ∈ P.edgeChoices) :
    c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ (univ : Finset Bool) :=
  ((mem_edgeChoices_iff' P c).1 hc).2.2

lemma mem_stSet_iff' (s : P.MState) :
    s ∈ P.stSet ↔ s.1 ∈ P.zSet ∧ s.2.1 ∈ listCands P.x P.a P.J ∧ s.2.2 ∈ P.memSet := by
  rw [MemParams.stSet, mem_product, mem_product]

lemma mem_ghostChoices_iff' (c : P.Mem × P.Mem) :
    c ∈ P.ghostChoices ↔ c.1 ∈ P.memSet ∧ c.2 ∈ P.memSet := by
  rw [MemParams.ghostChoices, mem_product]

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the chain of `memMomentD` as birth-ops (for D7e)

Slots `Fin K × Fin (J+1+B)`: the initial entries `(i, k)`, the ghost births of group `i` in increasing
order `(i, h)`, the fresh label of group `i` at an edge `(i, 0)`. The ops `initOp`, `ghostBOp`,
`symBOp`, `edgeBOp` and the list `fullL = init · G₀ S E₀ S G₁ ⋯ G_N`.

**(I1)** `memMomentD_eq_bschain`: `memMomentD` is the born-set chain of `fullL`; with
`bschain_eq_rchain` it is the record chain with the final validity check. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section Slots

variable (P : MemParams)

/-- The slots of an op. -/
abbrev DSlot := Fin P.K × Fin (P.J + 1 + P.B)

/-- A bound above every group prime. -/
noncomputable def qBound : ℕ := P.gPrimes.sup id + 1

lemma lt_qBound {p : ℕ} (hp : p ∈ P.gPrimes) : p < qBound P := by
  unfold qBound
  have : p ≤ P.gPrimes.sup id := le_sup (f := id) hp
  omega

/-- The multiset of values born at the slots. -/
def slotMs {Sl : Type} [Fintype Sl] (v : Sl → Option ℕ) : Multiset ℕ :=
  ∑ q, match v q with
    | none => 0
    | some p => {p}

lemma count_slotMs {Sl : Type} [Fintype Sl] [DecidableEq Sl] (v : Sl → Option ℕ) (p : ℕ) :
    Multiset.count p (slotMs v) = (univ.filter fun q => v q = some p).card := by
  unfold slotMs
  rw [Multiset.count_sum', card_eq_sum_ones, sum_filter]
  refine sum_congr rfl fun q _ => ?_
  cases h : v q with
  | none => simp
  | some p' =>
    simp only [Multiset.count_singleton, Option.some.injEq]
    by_cases hp : p' = p
    · subst hp; simp
    · rw [if_neg (Ne.symm hp), if_neg hp]

lemma mem_slotMs {Sl : Type} [Fintype Sl] [DecidableEq Sl] (v : Sl → Option ℕ) (p : ℕ) :
    p ∈ slotMs v ↔ ∃ q, v q = some p := by
  rw [← Multiset.count_pos, count_slotMs, card_pos]
  simp [Finset.Nonempty]

lemma inj_iff_slotMs_nodup {Sl : Type} [Fintype Sl] [DecidableEq Sl] (v : Sl → Option ℕ) :
    (∀ q q', v q ≠ none → v q = v q' → q = q') ↔ (slotMs v).Nodup := by
  rw [Multiset.nodup_iff_count_le_one]
  simp only [count_slotMs]
  constructor
  · intro h p
    rw [card_le_one]
    intro q hq q' hq'
    simp only [mem_filter, mem_univ, true_and] at hq hq'
    exact h q q' (by rw [hq]; simp) (hq.trans hq'.symm)
  · intro h q q' hq hqq'
    cases hv : v q with
    | none => exact absurd hv hq
    | some p =>
      have := card_le_one.1 (h p) q (by simp [hv]) q' (by simp [← hqq', hv])
      exact this

lemma bvals_eq_slotMs {Sl : Type} [Fintype Sl] [DecidableEq Sl] (v : Sl → Option ℕ) :
    bvals v = (slotMs v).toFinset := by
  ext p; rw [mem_bvals, Multiset.mem_toFinset, mem_slotMs]

lemma validOp_iff {Sl : Type} [Fintype Sl] [DecidableEq Sl] (Q : ℕ) (v : Sl → Option ℕ)
    (B : Finset ℕ) (hQ : ∀ p ∈ slotMs v, p < Q) :
    ValidOp Q v B ↔ (slotMs v).Nodup ∧ ∀ p ∈ slotMs v, p ∉ B := by
  unfold ValidOp
  rw [inj_iff_slotMs_nodup]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun p hp => ?_⟩
    obtain ⟨q, hq⟩ := (mem_slotMs v p).1 hp
    exact (h2 q p hq).2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun q p hq => ⟨hQ p ((mem_slotMs v p).2 ⟨q, hq⟩),
      h2 p ((mem_slotMs v p).2 ⟨q, hq⟩)⟩⟩

/-- Summing the list entries over enough slots. -/
lemma sum_getElem?_eq (l : List ℕ) (A : ℕ) (hl : l.length ≤ A) :
    (∑ h : Fin A, match l[h.val]? with
      | none => (0 : Multiset ℕ)
      | some p => {p}) = (l : Multiset ℕ) := by
  induction l generalizing A with
  | nil => simp
  | cons x l ih =>
    obtain ⟨A', rfl⟩ : ∃ A', A = A' + 1 := ⟨A - 1, by simp at hl; omega⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getElem?_cons_zero, Fin.val_succ, List.getElem?_cons_succ]
    rw [ih A' (by simp at hl; omega)]
    simp

lemma coe_flatten_ofFn {n : ℕ} (f : Fin n → List ℕ) :
    (((List.ofFn f).flatten : List ℕ) : Multiset ℕ) = ∑ i, ((f i : List ℕ) : Multiset ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, ← Multiset.coe_add, ih, Fin.sum_univ_succ]

/-! ### Births -/

/-- The initial entries. -/
def initBirth (ℓ : P.Lst) (q : DSlot P) : Option ℕ :=
  if h : q.2.val < P.J + 1 then some (ℓ q.1 ⟨q.2.val, h⟩) else none

/-- The primes born in group `i`. -/
noncomputable def groupBorn (b : P.Mem) (i : Fin P.K) : Multiset ℕ :=
  ∑ y : P.PT, if y.1.1 = i then b y • ({y.1.2.1} : Multiset ℕ) else 0

/-- The ghost births: the primes of group `i` in increasing order. -/
noncomputable def ghostBirth (b : P.Mem) (q : DSlot P) : Option ℕ :=
  ((groupBorn P b q.1).sort (· ≤ ·))[q.2.val]?

/-- The fresh label of group `i` at an edge. -/
def edgeBirth (tg : Fin P.K → ℕ × Bool) (q : DSlot P) : Option ℕ :=
  if q.2.val = 0 ∧ (tg q.1).2 = false then some (tg q.1).1 else none

lemma slotMs_initBirth (ℓ : P.Lst) :
    slotMs (initBirth P ℓ) = ((MemParams.allEntries P ℓ : List ℕ) : Multiset ℕ) := by
  unfold slotMs initBirth MemParams.allEntries
  rw [Fintype.sum_prod_type]
  rw [coe_flatten_ofFn]
  refine sum_congr rfl fun i _ => ?_
  have := sum_getElem?_eq (List.ofFn (ℓ i)) (P.J + 1 + P.B) (by simp)
  rw [← this]
  refine sum_congr rfl fun h _ => ?_
  by_cases hh : h.val < P.J + 1
  · rw [dif_pos hh, List.getElem?_ofFn]; simp [hh]
  · rw [dif_neg hh, List.getElem?_ofFn]; simp [hh]

lemma sum_groupBorn (b : P.Mem) : ∑ i, groupBorn P b i = MemParams.bornPrimes P b := by
  unfold groupBorn MemParams.bornPrimes
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_ite_eq]; simp

lemma card_groupBorn_le (b : P.Mem) (i : Fin P.K) :
    Multiset.card (groupBorn P b i) ≤ P.memSize b := by
  unfold groupBorn MemParams.memSize
  rw [Multiset.card_sum]
  refine sum_le_sum fun y _ => ?_
  split_ifs <;> simp

lemma slotMs_ghostBirth (b : P.Mem) (hb : P.memSize b ≤ P.B) :
    slotMs (ghostBirth P b) = MemParams.bornPrimes P b := by
  unfold slotMs ghostBirth
  rw [Fintype.sum_prod_type, ← sum_groupBorn]
  refine sum_congr rfl fun i _ => ?_
  dsimp only
  rw [sum_getElem?_eq _ _ (by rw [Multiset.length_sort]; have := card_groupBorn_le P b i; omega),
    Multiset.sort_eq]

lemma sum_fresh (n : ℕ) (tg : Fin n → ℕ × Bool) :
    (∑ x, if (tg x).2 = false then ({(tg x).1} : Multiset ℕ) else 0) =
      ((((List.finRange n).filter fun i => !(tg i).2).map fun i => (tg i).1 : List ℕ) :
        Multiset ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_succ, ih (fun x => tg x.succ), List.finRange_succ, List.filter_cons]
    rw [List.filter_map]
    by_cases h : (tg 0).2 = false
    · simp [h, Function.comp_def, List.map_map]
    · simp [h, Function.comp_def, List.map_map]

lemma slotMs_edgeBirth (tg : Fin P.K → ℕ × Bool) :
    slotMs (edgeBirth P tg) = ((MemParams.freshPrimes P tg : List ℕ) : Multiset ℕ) := by
  unfold slotMs edgeBirth MemParams.freshPrimes
  rw [Fintype.sum_prod_type]
  have h1 : ∀ i : Fin P.K, (∑ h : Fin (P.J + 1 + P.B),
      match (if h.val = 0 ∧ (tg i).2 = false then some (tg i).1 else none) with
      | none => (0 : Multiset ℕ)
      | some p => {p}) = if (tg i).2 = false then {(tg i).1} else 0 := by
    intro i
    rw [sum_eq_single (⟨0, by omega⟩ : Fin (P.J + 1 + P.B))]
    · by_cases h : (tg i).2 = false <;> simp [h]
    · intro h _ hne
      have : h.val ≠ 0 := fun h0 => hne (Fin.ext h0)
      simp [this]
    · intro h; exact absurd (mem_univ _) h
  simp only [h1]
  exact sum_fresh P.K tg

end Slots

/-! ## The ops -/

section Ops

variable (P : MemParams)

/-- The initial op (from a dummy state): choose the initial state with weight `μ(s) b(s)`. -/
noncomputable def initOp : BOp ℂ P.MState (DSlot P) where
  γ := P.MState
  ch := P.stSet
  coeff := fun _ s => (P.stWeight s : ℂ) * P.bVec s
  out := fun _ s => s
  birth := fun _ s => initBirth P s.2.1

open Classical in
/-- The ghost `G_j`. -/
noncomputable def ghostBOp (j : ℕ) : BOp ℂ P.MState (DSlot P) where
  γ := P.Mem × P.Mem
  ch := P.ghostChoices
  coeff := fun s c => P.ghostCoeff j s c * (if P.ghostOut s c ∈ P.stSet then 1 else 0)
  out := P.ghostOut
  birth := fun _ c => ghostBirth P c.2

/-- The slot symmetrization. -/
noncomputable def symBOp : BOp ℂ P.MState (DSlot P) where
  γ := Fin P.K → Equiv.Perm (Fin (P.J + 1))
  ch := univ
  coeff := fun _ _ => ((((P.J + 1).factorial ^ P.K : ℕ) : ℂ))⁻¹
  out := fun s pr => (s.1, fun i => s.2.1 i ∘ pr i, s.2.2)
  birth := fun _ _ _ => none

open Classical in
/-- The ordered edge `E_j^{ord}`. -/
noncomputable def edgeBOp (ω : ℝ × ℝ × ℝ) (j : ℕ) : BOp ℂ P.MState (DSlot P) where
  γ := Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)
  ch := P.edgeChoices
  coeff := fun s c => P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then 1 else 0)
  out := P.edgeOut
  birth := fun _ c => edgeBirth P c.2.2

/-- `G_{N−k} S E_{N−k} S ⋯ G_N`. -/
noncomputable def tailL (ω : ℝ × ℝ × ℝ) : ℕ → List (BOp ℂ P.MState (DSlot P))
  | 0 => [ghostBOp P P.N]
  | k + 1 => ghostBOp P (P.N - (k + 1)) :: symBOp P :: edgeBOp P ω (P.N - (k + 1)) :: symBOp P ::
      tailL ω k

/-- The full chain `init · G₀ S E₀ S ⋯ G_N`. -/
noncomputable def fullL (ω : ℝ × ℝ × ℝ) : List (BOp ℂ P.MState (DSlot P)) :=
  initOp P :: tailL P ω P.N

lemma length_tailL (ω : ℝ × ℝ × ℝ) (k : ℕ) : (tailL P ω k).length = 4 * k + 1 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tailL, List.length_cons, ih]; ring

lemma length_fullL (ω : ℝ × ℝ × ℝ) : (fullL P ω).length = 4 * P.N + 2 := by
  simp only [fullL, List.length_cons, length_tailL]

/-! ## (I1): `memMomentD` as a born-set chain -/

lemma mem_gPrimes_of_part (y : P.PT) : y.1.2.1 ∈ P.gPrimes := by
  have h := y.2
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range] at h
  obtain ⟨i, p, hp, l, _, he⟩ := h
  rw [← he]
  simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
  exact ⟨i, hp⟩

lemma bornPrimes_lt (b : P.Mem) : ∀ p ∈ MemParams.bornPrimes P b, p < qBound P := by
  intro p hp
  unfold MemParams.bornPrimes at hp
  rw [Multiset.mem_sum] at hp
  obtain ⟨y, _, hy⟩ := hp
  have := Multiset.mem_of_mem_nsmul hy
  rw [Multiset.mem_singleton] at this
  rw [this]
  exact lt_qBound P (mem_gPrimes_of_part P y)

lemma memSize_le_of_mem {m : P.Mem} (hm : m ∈ P.memSet) : P.memSize m ≤ P.B :=
  (mem_filter.1 hm).2

open Classical in
lemma ghostOpD_eq (j : ℕ) (g : P.MState × Finset ℕ → ℂ) (s : P.MState) (B : Finset ℕ) :
    P.ghostOpD j g (s, B) = ∑ c ∈ (ghostBOp P j).ch, (ghostBOp P j).coeff s c *
      (if ValidOp (qBound P) ((ghostBOp P j).birth s c) B then 1 else 0) *
        g ((ghostBOp P j).out s c, B ∪ bvals ((ghostBOp P j).birth s c)) := by
  unfold MemParams.ghostOpD
  refine sum_congr rfl fun c hc => ?_
  have hb : P.memSize c.2 ≤ P.B := memSize_le_of_mem P ((mem_ghostChoices_iff' P c).1 hc).2
  have hv := validOp_iff (qBound P) (ghostBirth P c.2) B (by
    rw [slotMs_ghostBirth P c.2 hb]; exact bornPrimes_lt P c.2)
  rw [slotMs_ghostBirth P c.2 hb] at hv
  have hb2 : bvals ((ghostBOp P j).birth s c) = (MemParams.bornPrimes P c.2).toFinset := by
    show bvals (ghostBirth P c.2) = _
    rw [bvals_eq_slotMs, slotMs_ghostBirth P c.2 hb]
  rw [hb2]
  by_cases h : (MemParams.bornPrimes P c.2).Nodup ∧ ∀ p ∈ MemParams.bornPrimes P c.2, p ∉ B
  · have hV : ValidOp (qBound P) ((ghostBOp P j).birth s c) B := hv.2 h
    rw [if_pos h, if_pos hV]
    show _ = P.ghostCoeff j s c * (if P.ghostOut s c ∈ P.stSet then 1 else 0) * 1 *
      g (P.ghostOut s c, B ∪ (MemParams.bornPrimes P c.2).toFinset)
    split_ifs <;> simp
  · have hV : ¬ ValidOp (qBound P) ((ghostBOp P j).birth s c) B := fun h' => h (hv.1 h')
    rw [if_neg h, if_neg hV]; simp

open Classical in
open Classical in
lemma symMD_eq (g : P.MState × Finset ℕ → ℂ) (s : P.MState) (B : Finset ℕ) :
    P.symMD g (s, B) = ∑ c ∈ (symBOp P).ch, (symBOp P).coeff s c *
      (if ValidOp (qBound P) ((symBOp P).birth s c) B then 1 else 0) *
        g ((symBOp P).out s c, B ∪ bvals ((symBOp P).birth s c)) := by
  unfold MemParams.symMD MemParams.listSym
  simp only [symBOp]
  have hv : ValidOp (qBound P) (fun _ : DSlot P => (none : Option ℕ)) B :=
    ⟨fun q _ h => absurd rfl h, fun q p h => by simp at h⟩
  have hb : bvals (fun _ : DSlot P => (none : Option ℕ)) = ∅ := by
    ext p; rw [mem_bvals]; simp
  rw [mul_sum]
  refine sum_congr rfl fun pr _ => ?_
  simp [hv, hb]

lemma freshPrimes_lt (tg : Fin P.K → ℕ × Bool)
    (htg : tg ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ) :
    ∀ p ∈ MemParams.freshPrimes P tg, p < qBound P := by
  intro p hp
  unfold MemParams.freshPrimes at hp
  rw [List.mem_map] at hp
  obtain ⟨i, _, rfl⟩ := hp
  have := Fintype.mem_piFinset.1 htg i
  refine lt_qBound P ?_
  simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
  exact ⟨i, (mem_product.1 this).1⟩

set_option maxRecDepth 100000 in
open Classical in
lemma edgeOrdD_eq (ω : ℝ × ℝ × ℝ) (j : ℕ) (g : P.MState × Finset ℕ → ℂ) (s : P.MState)
    (B : Finset ℕ) :
    P.edgeOrdD ω j g (s, B) = ∑ c ∈ (edgeBOp P ω j).ch, (edgeBOp P ω j).coeff s c *
      (if ValidOp (qBound P) ((edgeBOp P ω j).birth s c) B then 1 else 0) *
        g ((edgeBOp P ω j).out s c, B ∪ bvals ((edgeBOp P ω j).birth s c)) := by
  unfold MemParams.edgeOrdD
  refine sum_congr rfl fun c hc => ?_
  have htg : c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ := tg_mem_of_mem_edgeChoices P hc
  have hv := validOp_iff (qBound P) (edgeBirth P c.2.2) B (by
    rw [slotMs_edgeBirth]; intro p hp; exact freshPrimes_lt P c.2.2 htg p (Multiset.mem_coe.1 hp))
  rw [slotMs_edgeBirth, Multiset.coe_nodup] at hv
  simp only [Multiset.mem_coe] at hv
  have hb2 : bvals ((edgeBOp P ω j).birth s c) = (MemParams.freshPrimes P c.2.2).toFinset := by
    show bvals (edgeBirth P c.2.2) = _
    rw [bvals_eq_slotMs, slotMs_edgeBirth, List.toFinset_coe]
  rw [hb2]
  by_cases h : (MemParams.freshPrimes P c.2.2).Nodup ∧
      ∀ p ∈ MemParams.freshPrimes P c.2.2, p ∉ B
  · have hV : ValidOp (qBound P) ((edgeBOp P ω j).birth s c) B := hv.2 h
    rw [if_pos h, if_pos hV]
    show _ = P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then 1 else 0) * 1 *
      g (P.edgeOut s c, B ∪ (MemParams.freshPrimes P c.2.2).toFinset)
    split_ifs <;> simp
  · have hV : ¬ ValidOp (qBound P) ((edgeBOp P ω j).birth s c) B := fun h' => h (hv.1 h')
    rw [if_neg h, if_neg hV]; simp

set_option maxRecDepth 100000 in
lemma bschain_tailL (ω : ℝ × ℝ × ℝ) (f : P.MState → ℂ) :
    ∀ k s B, bschain (qBound P) (tailL P ω k) f s B =
      P.memTailD ω k (fun s' => f s'.1) (s, B) := by
  intro k
  induction k with
  | zero =>
    intro s B
    simp only [tailL, bschain, MemParams.memTailD]
    rw [ghostOpD_eq]
  | succ k ih =>
    intro s B
    simp only [tailL, bschain, MemParams.memTailD, MemParams.edgeOpD]
    rw [ghostOpD_eq]
    refine sum_congr rfl fun c _ => ?_
    congr 1
    rw [symMD_eq]
    refine sum_congr rfl fun c2 _ => ?_
    congr 1
    rw [edgeOrdD_eq]
    refine sum_congr rfl fun c3 _ => ?_
    congr 1
    rw [symMD_eq]
    refine sum_congr rfl fun c4 _ => ?_
    congr 1
    exact ih _ _

lemma allEntries_lt (ℓ : P.Lst) (hℓ : ℓ ∈ listCands P.x P.a P.J) :
    ∀ p ∈ MemParams.allEntries P ℓ, p < qBound P := by
  intro p hp
  unfold MemParams.allEntries at hp
  simp only [List.mem_flatten, List.mem_ofFn] at hp
  obtain ⟨l, ⟨i, rfl⟩, hl⟩ := hp
  rw [List.mem_ofFn] at hl
  obtain ⟨k, rfl⟩ := hl
  simp only [listCands, Fintype.mem_piFinset] at hℓ
  refine lt_qBound P ?_
  simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
  exact ⟨i, hℓ i k⟩

set_option maxRecDepth 100000 in
/-- **(I1)**: `memMomentD` is the born-set chain of `fullL`. -/
lemma memMomentD_eq_bschain (ω : ℝ × ℝ × ℝ) (dummy : P.MState) :
    P.memMomentD ω = bschain (qBound P) (fullL P ω) P.bVec dummy ∅ := by
  classical
  unfold MemParams.memMomentD
  simp only [fullL, bschain, initOp]
  refine sum_congr rfl fun s hs => ?_
  have hℓ : s.2.1 ∈ listCands P.x P.a P.J := ((mem_stSet_iff' P s).1 hs).2.1
  have hv := validOp_iff (qBound P) (initBirth P s.2.1) ∅ (by
    rw [slotMs_initBirth]; intro p hp; exact allEntries_lt P s.2.1 hℓ p (Multiset.mem_coe.1 hp))
  rw [slotMs_initBirth, Multiset.coe_nodup] at hv
  rw [bvals_eq_slotMs, slotMs_initBirth, List.toFinset_coe, empty_union, bschain_tailL]
  by_cases h : (MemParams.allEntries P s.2.1).Nodup
  · rw [if_pos h, if_pos (hv.2 ⟨h, fun p _ => Finset.notMem_empty p⟩)]; ring
  · rw [if_neg h, if_neg (fun h' => h (hv.1 h').1)]; ring

end Ops

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the forest expansion of birth distinctness (for D7e)

For a record `π` on `n` ops and addresses `𝔄 = Fin n × Sl`:
* `validBelow_ind`: `1[valid] = 1[within-op injective, < Q] · ∏_b (1 − Σ_{a: op a < op b} x(a,b))`,
  `x(a,b) = 1[π_a = π_b ≠ ⊥]` (the first cross-op repeat kills the product);
* `prod_forest`: `∏_b (1 − Σ_{a: op a < op b} x(a,b)) = Σ_F ∏_b g_F(b)` over forests
  `F : 𝔄 → Option 𝔄` (`F b = some a` only for `op a < op b`), `g(b) = 1` or `−x(F b, b)`;
* `forest_gen`: `Σ_F z^{rank F} = ∏_b (1 + #{a : op a < op b} z)`;
* the phase identity `x(a,b) = 1[π_a, π_b ≠ ⊥] · Q⁻¹ Σ_{τ < Q} e(τ(π_a − π_b)/Q)` for values `< Q`. -/

namespace ArtinPrimitiveRoots.L102D

open Finset Complex

variable {Sl : Type} [Fintype Sl] [DecidableEq Sl]

/-- The coincidence indicator `x(a, b) = 1[π_a = π_b ≠ ⊥]`. -/
noncomputable def xRel (π : Rec Sl) {n : ℕ} (a b : Fin n × Sl) : ℂ :=
  if π a.1 a.2 ≠ none ∧ π a.1 a.2 = π b.1 b.2 then 1 else 0

/-- Within-op validity: injective on performed slots, values `< Q`. -/
def WithinOK (Q : ℕ) (π : Rec Sl) (n : ℕ) : Prop :=
  (∀ k < n, ∀ q q', π k q ≠ none → π k q = π k q' → q = q') ∧
    (∀ k < n, ∀ q p, π k q = some p → p < Q)

lemma validBelow_iff (Q : ℕ) (π : Rec Sl) (n : ℕ) :
    ValidBelow Q π n ↔ WithinOK Q π n ∧
      ∀ a b : Fin n × Sl, a.1 < b.1 → ¬ (π a.1 a.2 ≠ none ∧ π a.1 a.2 = π b.1 b.2) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h2⟩, fun a b hab hx => ?_⟩
    obtain ⟨hne, heq⟩ := hx
    cases hp : π a.1 a.2 with
    | none => exact hne hp
    | some p => exact h3 a.1 b.1 hab b.1.2 a.2 b.2 p hp (heq ▸ hp)
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, h2, fun k k' hkk' hk' q q' p hq hq' => ?_⟩
    exact h3 (⟨k, by omega⟩, q) (⟨k', hk'⟩, q') hkk' ⟨by rw [hq]; simp, by simp [hq, hq']⟩

open Classical in
/-- **Validity as a product over births** (given within-op validity, the first cross-op repeat has
exactly one earlier partner). -/
lemma validBelow_ind (Q : ℕ) (π : Rec Sl) (n : ℕ) :
    (if ValidBelow Q π n then (1 : ℂ) else 0) =
      (if WithinOK Q π n then 1 else 0) *
        ∏ b : Fin n × Sl, (1 - ∑ a ∈ univ.filter (fun a : Fin n × Sl => a.1 < b.1), xRel π a b) := by
  by_cases hw : WithinOK Q π n
  · rw [if_pos hw, one_mul]
    by_cases hv : ValidBelow Q π n
    · rw [if_pos hv]
      have hc := ((validBelow_iff Q π n).1 hv).2
      symm
      refine prod_eq_one fun b _ => ?_
      rw [sum_eq_zero fun a ha => ?_, sub_zero]
      unfold xRel
      rw [if_neg (hc a b (mem_filter.1 ha).2)]
    · rw [if_neg hv]
      have hbad : ∃ a b : Fin n × Sl, a.1 < b.1 ∧ π a.1 a.2 ≠ none ∧ π a.1 a.2 = π b.1 b.2 := by
        by_contra h
        push Not at h
        exact hv ((validBelow_iff Q π n).2 ⟨hw, fun a b hab hx => h a b hab hx.1 hx.2⟩)
      -- the bad `b` of least op index
      set S := univ.filter fun b : Fin n × Sl =>
        ∃ a : Fin n × Sl, a.1 < b.1 ∧ π a.1 a.2 ≠ none ∧ π a.1 a.2 = π b.1 b.2
      have hS : S.Nonempty := by
        obtain ⟨a, b, h⟩ := hbad
        exact ⟨b, mem_filter.2 ⟨mem_univ _, a, h⟩⟩
      obtain ⟨b₀, hb₀, hmin⟩ := S.exists_min_image (fun b => b.1) hS
      obtain ⟨a₀, ha₀, hne, heq⟩ := (mem_filter.1 hb₀).2
      symm
      refine prod_eq_zero (mem_univ b₀) ?_
      rw [sub_eq_zero, sum_eq_single a₀]
      · unfold xRel; rw [if_pos ⟨hne, heq⟩]
      · intro a ha hne'
        unfold xRel
        rw [if_neg]
        rintro ⟨hna, hea⟩
        have ha1 := (mem_filter.1 ha).2
        -- `a` and `a₀` carry the same value
        rcases lt_trichotomy a.1 a₀.1 with h | h | h
        · -- then `a₀` would be a bad address of smaller op index
          have : a₀ ∈ S := mem_filter.2 ⟨mem_univ _, a, h, hna, hea.trans heq.symm⟩
          exact absurd (hmin a₀ this) (not_le.2 ha₀)
        · -- same op: within-op injectivity
          apply hne'
          have hk : (a.1 : ℕ) < n := a.1.2
          have := hw.1 a.1 hk a.2 a₀.2 hna (by rw [hea, ← heq, h])
          exact Prod.ext h this
        · have : a ∈ S := mem_filter.2 ⟨mem_univ _, a₀, h, hne, heq.trans hea.symm⟩
          exact absurd (hmin a this) (not_le.2 ha1)
      · intro h
        exact absurd (show a₀ ∈ univ.filter (fun a : Fin n × Sl => a.1 < b₀.1) from
          mem_filter.2 ⟨mem_univ _, ha₀⟩) h
  · rw [if_neg hw, zero_mul, if_neg (fun h => hw ((validBelow_iff Q π n).1 h).1)]

/-! ## Forests -/

/-- The forests: each address points to nothing or to an address of an earlier op. -/
noncomputable def forests (n : ℕ) : Finset (Fin n × Sl → Option (Fin n × Sl)) :=
  Fintype.piFinset fun b => insert none ((univ.filter fun a : Fin n × Sl => a.1 < b.1).image some)

/-- The factor of address `b` in the forest `F`. -/
noncomputable def gF (π : Rec Sl) {n : ℕ} (b : Fin n × Sl) (o : Option (Fin n × Sl)) : ℂ :=
  match o with
  | none => 1
  | some a => -xRel π a b

lemma prod_forest (π : Rec Sl) (n : ℕ) :
    ∏ b : Fin n × Sl, (1 - ∑ a ∈ univ.filter (fun a : Fin n × Sl => a.1 < b.1), xRel π a b) =
      ∑ F ∈ forests n, ∏ b, gF π b (F b) := by
  unfold forests
  rw [← prod_univ_sum]
  refine prod_congr rfl fun b _ => ?_
  rw [sum_insert (by simp), sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
  simp only [gF, sum_neg_distrib]
  ring

/-- The rank of a forest. -/
noncomputable def frank {n : ℕ} (F : Fin n × Sl → Option (Fin n × Sl)) : ℕ :=
  (univ.filter fun b => F b ≠ none).card

lemma forest_gen (n : ℕ) (z : ℝ) :
    ∑ F ∈ (forests n : Finset (Fin n × Sl → Option (Fin n × Sl))), z ^ frank F =
      ∏ b : Fin n × Sl, (1 + ((univ.filter fun a : Fin n × Sl => a.1 < b.1).card : ℝ) * z) := by
  classical
  have h1 : ∀ F : Fin n × Sl → Option (Fin n × Sl),
      z ^ frank F = ∏ b, (if F b = none then 1 else z) := by
    intro F
    unfold frank
    rw [prod_ite, prod_const_one, one_mul, prod_const]
  simp only [h1]
  unfold forests
  rw [← prod_univ_sum (f := fun _ (o : Option (Fin n × Sl)) => if o = none then (1 : ℝ) else z)]
  refine prod_congr rfl fun b _ => ?_
  rw [sum_insert (by simp), sum_image (fun _ _ _ _ h => Option.some_injective _ h)]
  simp only [reduceCtorEq, if_false, sum_const, nsmul_eq_mul, if_true]

/-! ## Phases -/

/-- `e(τ v/Q)` at a performed value, `0` at an unperformed one. -/
noncomputable def phA (Q : ℕ) (τ : ℕ) (v : Option ℕ) : ℂ :=
  match v with
  | none => 0
  | some p => exp (2 * Real.pi * I * ((τ : ℝ) * p / Q : ℝ))

/-- `e(−τ v/Q)` at a performed value, `0` at an unperformed one. -/
noncomputable def phB (Q : ℕ) (τ : ℕ) (v : Option ℕ) : ℂ :=
  match v with
  | none => 0
  | some p => exp (-(2 * Real.pi * I * ((τ : ℝ) * p / Q : ℝ)))

lemma norm_phA_le (Q τ : ℕ) (v : Option ℕ) : ‖phA Q τ v‖ ≤ 1 := by
  unfold phA
  cases v with
  | none => simp
  | some p =>
    simp only
    rw [show (2 * Real.pi * I * ((τ : ℝ) * p / Q : ℝ) : ℂ) = (((2 * Real.pi * ((τ : ℝ) * p / Q)) : ℝ) : ℂ) * I
      by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

lemma norm_phB_le (Q τ : ℕ) (v : Option ℕ) : ‖phB Q τ v‖ ≤ 1 := by
  unfold phB
  cases v with
  | none => simp
  | some p =>
    simp only
    rw [show -(2 * Real.pi * I * ((τ : ℝ) * p / Q : ℝ) : ℂ) =
      (((-(2 * Real.pi * ((τ : ℝ) * p / Q))) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]

/-- Orthogonality on `ℤ/Q`. -/
lemma sum_exp_eq (Q : ℕ) (hQ : 0 < Q) (d : ℤ) (hd : |d| < Q) :
    ∑ τ ∈ range Q, exp (2 * Real.pi * I * ((τ : ℝ) * d / Q : ℝ)) = if d = 0 then (Q : ℂ) else 0 := by
  by_cases h0 : d = 0
  · subst h0; simp
  · rw [if_neg h0]
    set r := exp (2 * Real.pi * I * ((d : ℝ) / Q : ℝ))
    have hr : ∀ τ : ℕ, exp (2 * Real.pi * I * ((τ : ℝ) * d / Q : ℝ)) = r ^ τ := by
      intro τ
      rw [← Complex.exp_nat_mul]
      congr 1; push_cast; ring
    simp only [hr]
    have hrQ : r ^ Q = 1 := by
      rw [← Complex.exp_nat_mul]
      have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
      rw [show (Q : ℂ) * (2 * Real.pi * I * (((d : ℝ) / Q : ℝ) : ℂ)) = (d : ℂ) * (2 * Real.pi * I) by
        push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I d
    have hr1 : r ≠ 1 := by
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      have : ((d : ℝ) / Q : ℝ) = m := by
        have h2 : (2 * Real.pi * I * (((d : ℝ) / Q : ℝ) : ℂ)) = ((m : ℂ) * (2 * Real.pi * I)) := hm
        have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by
          simp [Real.pi_ne_zero, I_ne_zero]
        have h3 : (((d : ℝ) / Q : ℝ) : ℂ) = (m : ℂ) := by
          apply mul_left_cancel₀ hpi; rw [h2]; ring
        exact_mod_cast h3
      have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
      have hdm : (d : ℝ) = m * Q := by field_simp at this; linarith
      have hdm' : d = m * Q := by exact_mod_cast hdm
      have : |d| < Q := hd
      rw [hdm', abs_mul] at this
      rcases eq_or_ne m 0 with hm0 | hm0
      · exact h0 (by rw [hdm', hm0, zero_mul])
      · have : (1 : ℤ) ≤ |m| := Int.one_le_abs hm0
        have hQ' : (0 : ℤ) < Q := by exact_mod_cast hQ
        nlinarith [abs_nonneg (Q : ℤ), abs_of_pos hQ']
    rw [geom_sum_eq hr1, hrQ, sub_self, zero_div]

/-- **The phase representation of a coincidence**. -/
lemma xRel_phase (Q : ℕ) (hQ : 0 < Q) (v₁ v₂ : Option ℕ) (h₁ : ∀ p, v₁ = some p → p < Q)
    (h₂ : ∀ p, v₂ = some p → p < Q) :
    (if v₁ ≠ none ∧ v₁ = v₂ then (1 : ℂ) else 0) =
      (Q : ℂ)⁻¹ * ∑ τ ∈ range Q, phA Q τ v₁ * phB Q τ v₂ := by
  have hQc : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  cases v₁ with
  | none => simp [phA]
  | some p =>
    cases v₂ with
    | none => simp [phB]
    | some p' =>
      simp only [phA, phB]
      have hcomb : ∀ τ : ℕ, exp (2 * Real.pi * I * ((τ : ℝ) * p / Q : ℝ)) *
          exp (-(2 * Real.pi * I * ((τ : ℝ) * p' / Q : ℝ))) =
          exp (2 * Real.pi * I * ((τ : ℝ) * ((p : ℤ) - p' : ℤ) / Q : ℝ)) := by
        intro τ; rw [← Complex.exp_add]; congr 1; push_cast; ring
      simp only [hcomb]
      have hp := h₁ p rfl
      have hp' := h₂ p' rfl
      rw [sum_exp_eq Q hQ _ (by rw [abs_lt]; constructor <;> push_cast <;> omega)]
      by_cases hpp : p = p'
      · subst hpp; simp [hQc]
      · have hne : ((p : ℤ) - p' : ℤ) ≠ 0 := by
          intro h; exact hpp (by omega)
        rw [if_neg hne, mul_zero]
        simp [hpp]

/-! ## Forest terms through per-op multipliers -/

section ForestTerms

variable {n : ℕ} (Q : ℕ)

/-- The domain of a forest. -/
noncomputable def fdom (F : Fin n × Sl → Option (Fin n × Sl)) : Finset (Fin n × Sl) :=
  univ.filter fun b => F b ≠ none

/-- The partner of `b` (itself if none). -/
def ftgt (F : Fin n × Sl → Option (Fin n × Sl)) (b : Fin n × Sl) : Fin n × Sl := (F b).getD b

/-- The phase multiplier of op `k`: the `e(+)` factors of partners at op `k` and the `e(−)`
factors of constrained births at op `k`. -/
noncomputable def phMult (F : Fin n × Sl → Option (Fin n × Sl)) (t : Fin n × Sl → ℕ) (k : Fin n)
    (v : Sl → Option ℕ) : ℂ :=
  (∏ b ∈ (fdom F).filter (fun b => (ftgt F b).1 = k), phA Q (t b) (v (ftgt F b).2)) *
    ∏ b ∈ (fdom F).filter (fun b => b.1 = k), phB Q (t b) (v b.2)

lemma norm_phMult_le (F : Fin n × Sl → Option (Fin n × Sl)) (t : Fin n × Sl → ℕ) (k : Fin n)
    (v : Sl → Option ℕ) : ‖phMult Q F t k v‖ ≤ 1 := by
  unfold phMult
  rw [norm_mul, norm_prod, norm_prod]
  exact mul_le_one₀ (prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => norm_phA_le _ _ _)
    (prod_nonneg fun _ _ => norm_nonneg _) (prod_le_one (fun _ _ => norm_nonneg _)
      fun _ _ => norm_phB_le _ _ _)

lemma prod_phMult (F : Fin n × Sl → Option (Fin n × Sl)) (t : Fin n × Sl → ℕ) (π : Rec Sl) :
    ∏ k : Fin n, phMult Q F t k (π k) =
      ∏ b ∈ fdom F, phA Q (t b) (π (ftgt F b).1 (ftgt F b).2) * phB Q (t b) (π b.1 b.2) := by
  unfold phMult
  rw [prod_mul_distrib, prod_mul_distrib]
  congr 1
  · rw [← prod_fiberwise (fdom F) (fun b => (ftgt F b).1)]
    refine prod_congr rfl fun k _ => prod_congr rfl fun b hb => ?_
    rw [(mem_filter.1 hb).2]
  · rw [← prod_fiberwise (fdom F) (fun b => b.1)]
    refine prod_congr rfl fun k _ => prod_congr rfl fun b hb => ?_
    rw [(mem_filter.1 hb).2]

/-- The phase ranges: `range Q` on the domain, `{0}` elsewhere. -/
noncomputable def phRange (F : Fin n × Sl → Option (Fin n × Sl)) : Finset (Fin n × Sl → ℕ) :=
  Fintype.piFinset fun b => if F b ≠ none then range Q else {0}

lemma card_phRange (F : Fin n × Sl → Option (Fin n × Sl)) :
    ((phRange Q F).card : ℝ) = (Q : ℝ) ^ frank F := by
  classical
  unfold phRange frank
  rw [Fintype.card_piFinset]
  push_cast
  rw [show (∏ b : Fin n × Sl, ((if F b ≠ none then range Q else {0} : Finset ℕ).card : ℝ)) =
      ∏ b : Fin n × Sl, (if F b ≠ none then (Q : ℝ) else 1) from
    prod_congr rfl fun b _ => by split_ifs <;> simp]
  rw [prod_ite, prod_const, prod_const_one, mul_one]

/-- **A forest term through phases** (all record values `< Q`). -/
lemma forest_term_phase (hQ : 0 < Q) (F : Fin n × Sl → Option (Fin n × Sl)) (π : Rec Sl)
    (hπ : ∀ k (q : Sl) p, π k q = some p → p < Q) :
    ∏ b, gF π b (F b) = (-(Q : ℂ)⁻¹) ^ frank F *
      ∑ t ∈ phRange Q F, ∏ k : Fin n, phMult Q F t k (π k) := by
  classical
  have hterm : ∀ b : Fin n × Sl, gF π b (F b) =
      ∑ τ ∈ (if F b ≠ none then range Q else {0}),
        (if F b ≠ none then -(Q : ℂ)⁻¹ * (phA Q τ (π (ftgt F b).1 (ftgt F b).2) *
          phB Q τ (π b.1 b.2)) else 1) := by
    intro b
    cases hb : F b with
    | none => simp [gF, hb]
    | some a =>
      simp only [gF, ne_eq, reduceCtorEq, not_false_eq_true, if_true, ftgt, hb, Option.getD_some]
      unfold xRel
      rw [xRel_phase Q hQ _ _ (hπ _ _) (hπ _ _), ← mul_sum]
      ring
  rw [prod_congr rfl fun b _ => hterm b, prod_univ_sum]
  unfold phRange
  rw [mul_sum]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_phMult]
  rw [prod_ite, prod_const_one, mul_one]
  rw [prod_mul_distrib, prod_const]
  rfl

open Classical in
/-- The pointwise absolute bound by membership in the earlier born set. -/
lemma norm_forest_term_le (Q' : ℕ) (F : Fin n × Sl → Option (Fin n × Sl))
    (hF : ∀ b a, F b = some a → a.1 < b.1) (π : Rec Sl) :
    ‖(if WithinOK Q' π n then (1 : ℂ) else 0) * ∏ b, gF π b (F b)‖ ≤
      (if WithinOK Q' π n then 1 else 0) *
        ∏ b ∈ fdom F, (if π b.1 b.2 ≠ none ∧ (π b.1 b.2).getD 0 ∈ valsBelow π b.1 then (1 : ℝ)
          else 0) := by
  rw [norm_mul]
  refine mul_le_mul (by split_ifs <;> simp) ?_ (norm_nonneg _) (by split_ifs <;> simp)
  rw [norm_prod]
  have hsplit : ∏ b, ‖gF π b (F b)‖ = ∏ b ∈ fdom F, ‖gF π b (F b)‖ := by
    refine (prod_subset (subset_univ _) fun b _ hb => ?_).symm
    unfold fdom at hb
    simp only [mem_filter, mem_univ, true_and, not_not] at hb
    simp [gF, hb]
  rw [hsplit]
  refine prod_le_prod (fun _ _ => norm_nonneg _) fun b hb => ?_
  have hb' : F b ≠ none := (mem_filter.1 hb).2
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hb'
  simp only [gF, ha, norm_neg]
  unfold xRel
  split_ifs with h1 h2
  · simp
  · exfalso; apply h2
    refine ⟨fun h => h1.1 (h1.2.trans h), ?_⟩
    have hlt := hF b a ha
    unfold valsBelow
    rw [mem_biUnion]
    refine ⟨a.1, mem_range.2 hlt, mem_bvals.2 ⟨a.2, ?_⟩⟩
    rw [← h1.2]
    cases hv : π a.1 a.2 with
    | none => exact absurd hv h1.1
    | some p => simp [hv] at h1 ⊢
  · simp
  · simp

end ForestTerms

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: generic pieces of the distinctness assembly (for D7e)

* `wk`: the within-op validity check of one op (injective on performed slots, values `< Q`);
  `WithinOK` is the product of the `wk` of the ops.
* `phM`: the phase multiplier of op `k` (`1` beyond the chain).
* `forest_term_chain`: a forest term as `(−1/Q)^{rank}` times a sum over phases of products of
  per-op multipliers.
* `rchain_row_on`: weighted row iteration on an invariant set of states.
* `forest_small_sum`, `forest_large_sum`: the rank sums through the generating function. -/

namespace ArtinPrimitiveRoots.L102D

open Finset

section Gen

variable {Sl : Type} [Fintype Sl] [DecidableEq Sl]

open Classical in
/-- The within-op validity check of one op. -/
noncomputable def wk (Q : ℕ) (v : Sl → Option ℕ) : ℂ :=
  if (∀ q q', v q ≠ none → v q = v q' → q = q') ∧ (∀ q p, v q = some p → p < Q) then 1 else 0

lemma norm_wk_le (Q : ℕ) (v : Sl → Option ℕ) : ‖wk Q v‖ ≤ 1 := by
  unfold wk; split_ifs <;> simp

open Classical in
lemma withinOK_prod (Q : ℕ) (π : Rec Sl) (n : ℕ) :
    (if WithinOK Q π n then (1 : ℂ) else 0) = ∏ k ∈ range n, wk Q (π k) := by
  by_cases h : WithinOK Q π n
  · rw [if_pos h]
    refine (prod_eq_one fun k hk => ?_).symm
    unfold wk
    rw [if_pos ⟨h.1 k (mem_range.1 hk), h.2 k (mem_range.1 hk)⟩]
  · rw [if_neg h]
    have : ∃ k < n, ¬ ((∀ q q', π k q ≠ none → π k q = π k q' → q = q') ∧
        (∀ q p, π k q = some p → p < Q)) := by
      by_contra hc
      push_neg at hc
      exact h ⟨fun k hk => (hc k hk).1, fun k hk => (hc k hk).2⟩
    obtain ⟨k, hk, hk'⟩ := this
    refine (prod_eq_zero (mem_range.2 hk) ?_).symm
    unfold wk; rw [if_neg hk']

/-- The phase multiplier of op `k` (`1` beyond the chain). -/
noncomputable def phM (Q n : ℕ) (F : Fin n × Sl → Option (Fin n × Sl)) (t : Fin n × Sl → ℕ)
    (k : ℕ) (v : Sl → Option ℕ) : ℂ :=
  if h : k < n then phMult Q F t ⟨k, h⟩ v else 1

lemma norm_phM_le (Q n : ℕ) (F : Fin n × Sl → Option (Fin n × Sl)) (t : Fin n × Sl → ℕ)
    (k : ℕ) (v : Sl → Option ℕ) : ‖phM Q n F t k v‖ ≤ 1 := by
  unfold phM; split_ifs
  · exact norm_phMult_le Q F t _ v
  · simp

/-- An op not touched by the forest has phase multiplier `1`. -/
lemma phM_untouched (Q n : ℕ) (F : Fin n × Sl → Option (Fin n × Sl)) (t : Fin n × Sl → ℕ)
    (k : ℕ) (hk : ∀ b ∈ fdom F, (b.1 : ℕ) ≠ k ∧ ((ftgt F b).1 : ℕ) ≠ k) (v : Sl → Option ℕ) :
    phM Q n F t k v = 1 := by
  unfold phM
  split_ifs with h
  · unfold phMult
    rw [prod_eq_one fun b hb => ?_, prod_eq_one fun b hb => ?_, mul_one]
    · exfalso
      obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
      exact (hk b hb1).1 (by rw [hb2])
    · exfalso
      obtain ⟨hb1, hb2⟩ := mem_filter.1 hb
      exact (hk b hb1).2 (by rw [hb2])
  · rfl

open Classical in
/-- **A forest term through phases, op by op.** -/
lemma forest_term_chain (Q : ℕ) (hQ : 0 < Q) {n : ℕ} (F : Fin n × Sl → Option (Fin n × Sl))
    (π : Rec Sl) :
    (if WithinOK Q π n then (1 : ℂ) else 0) * ∏ b, gF π b (F b) =
      (-(Q : ℂ)⁻¹) ^ frank F *
        ∑ t ∈ phRange Q F, ∏ k ∈ range n, (wk Q (π k) * phM Q n F t k (π k)) := by
  by_cases hw : WithinOK Q π n
  · rw [if_pos hw, one_mul]
    set π' : Rec Sl := fun k => if k < n then π k else fun _ => none with hπ'
    have hlt : ∀ k : Fin n, π' k = π k := fun k => by simp [hπ', k.isLt]
    have hπ'Q : ∀ k (q : Sl) p, π' k q = some p → p < Q := by
      intro k q p h
      by_cases hk : k < n
      · simp only [hπ', if_pos hk] at h; exact hw.2 k hk q p h
      · simp [hπ', if_neg hk] at h
    have hg : ∏ b, gF π b (F b) = ∏ b, gF π' b (F b) := by
      refine prod_congr rfl fun b _ => ?_
      cases F b with
      | none => rfl
      | some a => simp only [gF, xRel, hlt]
    rw [hg, forest_term_phase Q hQ F π' hπ'Q]
    congr 1
    refine sum_congr rfl fun t _ => ?_
    have hwk : ∀ k ∈ range n, wk Q (π k) = 1 := by
      intro k hk
      unfold wk
      rw [if_pos ⟨hw.1 k (mem_range.1 hk), hw.2 k (mem_range.1 hk)⟩]
    symm
    rw [prod_congr rfl fun k hk => by rw [hwk k hk, one_mul]]
    rw [← Fin.prod_univ_eq_prod_range (fun k => phM Q n F t k (π k)) n]
    refine prod_congr rfl fun k _ => ?_
    simp only [phM, dif_pos k.isLt, Fin.eta, hlt]
  · rw [if_neg hw, zero_mul]
    have h0 : ∏ k ∈ range n, wk Q (π k) = 0 := by rw [← withinOK_prod, if_neg hw]
    symm
    refine mul_eq_zero_of_right _ (sum_eq_zero fun t _ => ?_)
    rw [prod_mul_distrib, h0, zero_mul]

end Gen

/-! ## Row iteration on an invariant set -/

section RowOn

variable {α Sl : Type}

lemma rchain_row_on (mult : ℕ → Rec Sl → (Sl → Option ℕ) → ℝ) (hm : ∀ k π v, 0 ≤ mult k π v)
    (St : Set α) (w : α → ℝ) (Rk : ℕ → ℝ) (hR : ∀ k, 0 ≤ Rk k) :
    ∀ (os : List (BOp ℝ α Sl)) (k : ℕ), (∀ o ∈ os, ∀ s c, 0 ≤ o.coeff s c) →
      (∀ o ∈ os, ∀ s ∈ St, ∀ c ∈ o.ch, o.coeff s c ≠ 0 → o.out s c ∈ St) →
      (∀ i (hi : i < os.length), ∀ s ∈ St, ∀ π,
        ∑ c ∈ (os.get ⟨i, hi⟩).ch, (os.get ⟨i, hi⟩).coeff s c *
          mult (k + i) π ((os.get ⟨i, hi⟩).birth s c) * w ((os.get ⟨i, hi⟩).out s c) ≤
          Rk (k + i) * w s) →
      ∀ (f : α → Rec Sl → ℝ), (∀ s π, 0 ≤ f s π) → (∀ s ∈ St, ∀ π, f s π ≤ w s) →
        ∀ s ∈ St, ∀ π, rchain mult k os f s π ≤ (∏ i ∈ range os.length, Rk (k + i)) * w s := by
  intro os
  induction os with
  | nil => intro k _ _ _ f _ hfw s hs π; simpa [rchain] using hfw s hs π
  | cons o os ih =>
    intro k hos hinv hrow f hf hfw s hs π
    simp only [rchain]
    have hos' : ∀ o' ∈ os, ∀ s c, 0 ≤ o'.coeff s c := fun o' ho' => hos o' (by simp [ho'])
    have hinv' : ∀ o' ∈ os, ∀ s ∈ St, ∀ c ∈ o'.ch, o'.coeff s c ≠ 0 → o'.out s c ∈ St :=
      fun o' ho' => hinv o' (by simp [ho'])
    have hrow' : ∀ i (hi : i < os.length), ∀ s ∈ St, ∀ π,
        ∑ c ∈ (os.get ⟨i, hi⟩).ch, (os.get ⟨i, hi⟩).coeff s c *
          mult (k + 1 + i) π ((os.get ⟨i, hi⟩).birth s c) * w ((os.get ⟨i, hi⟩).out s c) ≤
          Rk (k + 1 + i) * w s := by
      intro i hi s hs π
      have := hrow (i + 1) (by simp; omega) s hs π
      simp only [List.get_eq_getElem, List.getElem_cons_succ] at this ⊢
      rwa [show k + (i + 1) = k + 1 + i by ring] at this
    have h0 := hrow 0 (by simp) s hs π
    simp only [List.get_eq_getElem, List.getElem_cons_zero, add_zero] at h0
    have hP : 0 ≤ ∏ i ∈ range os.length, Rk (k + 1 + i) := prod_nonneg fun i _ => hR _
    calc ∑ c ∈ o.ch, o.coeff s c * mult k π (o.birth s c) *
          rchain mult (k + 1) os f (o.out s c) (recUpd π k (o.birth s c)) ≤
        ∑ c ∈ o.ch, o.coeff s c * mult k π (o.birth s c) *
          ((∏ i ∈ range os.length, Rk (k + 1 + i)) * w (o.out s c)) := by
          refine sum_le_sum fun c hc => ?_
          by_cases h0c : o.coeff s c = 0
          · rw [h0c]; simp
          · exact mul_le_mul_of_nonneg_left
              (ih (k + 1) hos' hinv' hrow' f hf hfw _ (hinv o (by simp) s hs c hc h0c) _)
              (mul_nonneg (hos o (by simp) s c) (hm _ _ _))
      _ = (∏ i ∈ range os.length, Rk (k + 1 + i)) *
          ∑ c ∈ o.ch, o.coeff s c * mult k π (o.birth s c) * w (o.out s c) := by
          rw [mul_sum]; refine sum_congr rfl fun c _ => by ring
      _ ≤ (∏ i ∈ range os.length, Rk (k + 1 + i)) * (Rk k * w s) :=
          mul_le_mul_of_nonneg_left h0 hP
      _ = (∏ i ∈ range (o :: os).length, Rk (k + i)) * w s := by
          rw [List.length_cons, prod_range_succ']
          simp only [add_zero]
          rw [show (∏ i ∈ range os.length, Rk (k + (i + 1))) =
            ∏ i ∈ range os.length, Rk (k + 1 + i) from
            prod_congr rfl fun i _ => by rw [show k + (i + 1) = k + 1 + i by ring]]
          ring

end RowOn

/-! ## Rank sums -/

section RankSums

variable {Sl : Type} [Fintype Sl] [DecidableEq Sl]

lemma card_lt_le (n : ℕ) (b : Fin n × Sl) :
    ((univ.filter fun a : Fin n × Sl => a.1 < b.1).card : ℝ) ≤ Fintype.card (Fin n × Sl) := by
  exact_mod_cast card_le_univ _

lemma one_add_div_pow_le (A : ℕ) : (1 + 1 / (A : ℝ)) ^ A ≤ Real.exp 1 := by
  rcases Nat.eq_zero_or_pos A with h | h
  · subst h; simp
  · have hA : (0 : ℝ) < A := by exact_mod_cast h
    calc (1 + 1 / (A : ℝ)) ^ A ≤ (Real.exp (1 / (A : ℝ))) ^ A := by
          gcongr
          have := Real.add_one_le_exp (1 / (A : ℝ))
          linarith
      _ = Real.exp 1 := by rw [← Real.exp_nat_mul]; field_simp

/-- `∏_b (1 + #{a < b} z) ≤ e` once `A² z ≤ 1`, `A` the number of addresses. -/
lemma prod_forest_gen_le (n : ℕ) {z : ℝ} (hz : 0 ≤ z)
    (hA : (Fintype.card (Fin n × Sl) : ℝ) ^ 2 * z ≤ 1) :
    ∏ b : Fin n × Sl, (1 + ((univ.filter fun a : Fin n × Sl => a.1 < b.1).card : ℝ) * z) ≤
      Real.exp 1 := by
  set A := Fintype.card (Fin n × Sl)
  rcases Nat.eq_zero_or_pos A with h0 | hpos
  · have : IsEmpty (Fin n × Sl) := Fintype.card_eq_zero_iff.1 h0
    simp only [univ_eq_empty, prod_empty]
    exact Real.one_le_exp zero_le_one
  have hApos : (0 : ℝ) < A := by exact_mod_cast hpos
  have hz' : z ≤ 1 / (A : ℝ) ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  calc ∏ b : Fin n × Sl, (1 + ((univ.filter fun a : Fin n × Sl => a.1 < b.1).card : ℝ) * z) ≤
      ∏ _b : Fin n × Sl, (1 + 1 / (A : ℝ)) := by
        refine prod_le_prod (fun b _ => by positivity) fun b _ => ?_
        have h1 := card_lt_le n b
        have : ((univ.filter fun a : Fin n × Sl => a.1 < b.1).card : ℝ) * z ≤
            (A : ℝ) * (1 / (A : ℝ) ^ 2) := mul_le_mul h1 hz' hz (by positivity)
        have e : (A : ℝ) * (1 / (A : ℝ) ^ 2) = 1 / A := by field_simp
        linarith
    _ = (1 + 1 / (A : ℝ)) ^ A := by rw [prod_const, card_univ]
    _ ≤ Real.exp 1 := one_add_div_pow_le A

/-- **Rank sums**: if `(A² Y)^f ≤ M` whenever `c f`, then `∑_{c(rank F)} Y^{rank F} ≤ e M`. -/
lemma forest_sum_le (n : ℕ) (hA : 0 < Fintype.card (Fin n × Sl)) {Y M : ℝ} (hY : 0 ≤ Y)
    (hM : 0 ≤ M) (c : ℕ → Prop) [DecidablePred c]
    (hc : ∀ f, c f → ((Fintype.card (Fin n × Sl) : ℝ) ^ 2 * Y) ^ f ≤ M) :
    ∑ F ∈ (forests n : Finset (Fin n × Sl → Option (Fin n × Sl))),
      (if c (frank F) then Y ^ frank F else 0) ≤ Real.exp 1 * M := by
  set A := Fintype.card (Fin n × Sl)
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  have hterm : ∀ F : Fin n × Sl → Option (Fin n × Sl),
      (if c (frank F) then Y ^ frank F else 0) ≤ M * (1 / (A : ℝ) ^ 2) ^ frank F := by
    intro F
    split_ifs with h
    · have e : Y ^ frank F = ((A : ℝ) ^ 2 * Y) ^ frank F * (1 / (A : ℝ) ^ 2) ^ frank F := by
        rw [← mul_pow]; congr 1; field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_right (hc _ h) (by positivity)
    · positivity
  calc ∑ F ∈ (forests n : Finset (Fin n × Sl → Option (Fin n × Sl))),
        (if c (frank F) then Y ^ frank F else 0) ≤
      ∑ F ∈ (forests n : Finset (Fin n × Sl → Option (Fin n × Sl))),
        M * (1 / (A : ℝ) ^ 2) ^ frank F := sum_le_sum fun F _ => hterm F
    _ = M * ∏ b : Fin n × Sl,
          (1 + ((univ.filter fun a : Fin n × Sl => a.1 < b.1).card : ℝ) * (1 / (A : ℝ) ^ 2)) := by
        rw [← mul_sum, forest_gen]
    _ ≤ M * Real.exp 1 := by
        refine mul_le_mul_of_nonneg_left (prod_forest_gen_le n (by positivity) ?_) hM
        rw [mul_one_div, div_self (by positivity)]
    _ = Real.exp 1 * M := mul_comm _ _

end RankSums

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102G: the Hilbert-space framework for the edge bound (D7d)

On `H_B = ℓ²(stSet, μ)`, `μ = stWeight`:

* `ipμ g h = Σ_s μ(s) conj(g s) h s`; `opBound_of_bilin`: a bilinear bound gives `OpBound`;
* slot permutations `permS`; `μ` and `stSet` are invariant (`stWeight_permS`, `sum_permS`);
* `symM` is self-adjoint (`ipμ_symM`), a contraction (`wNorm_symM_le`), and its images are
  symmetric (`symM_permS`); `sum_sym_avg` replaces a row sum by its permutation average;
* `ipμ_edgeOp`: `⟨g, E f⟩ = ⟨Sg, E^ord Sf⟩`;
* `piece_bound`: the Cauchy–Schwarz/Schur bound for one piece of a choice-indexed operator.
-/

namespace ArtinPrimitiveRoots.L102G

open Real Finset
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The slot permutations. -/
abbrev SlotPerm := Fin P.K → Equiv.Perm (Fin (P.J + 1))

/-- The action of slot permutations on lists. -/
def permL (pr : SlotPerm P) (ℓ : P.Lst) : P.Lst := fun i => ℓ i ∘ pr i

/-- The action on memory states. -/
def permS (pr : SlotPerm P) (s : P.MState) : P.MState := (s.1, permL P pr s.2.1, s.2.2)

lemma permL_permL (σ pr : SlotPerm P) (ℓ : P.Lst) :
    permL P pr (permL P σ ℓ) = permL P (σ * pr) ℓ := by
  funext i k; rfl

lemma permS_permS (σ pr : SlotPerm P) (s : P.MState) :
    permS P pr (permS P σ s) = permS P (σ * pr) s := by
  simp only [permS, permL_permL]

lemma permS_one (s : P.MState) : permS P 1 s = s := by
  rcases s with ⟨z, ℓ, m⟩; rfl

lemma permS_inv_cancel (pr : SlotPerm P) (s : P.MState) : permS P pr (permS P pr⁻¹ s) = s := by
  rw [permS_permS, inv_mul_cancel, permS_one]

lemma permS_cancel_inv (pr : SlotPerm P) (s : P.MState) : permS P pr⁻¹ (permS P pr s) = s := by
  rw [permS_permS, mul_inv_cancel, permS_one]

lemma listWeight_permL (pr : SlotPerm P) (ℓ : P.Lst) :
    P.listWeight (permL P pr ℓ) = P.listWeight ℓ := by
  unfold MemParams.listWeight permL
  refine prod_congr rfl fun i _ => ?_
  exact Equiv.prod_comp (pr i) (fun k => P.nu i (ℓ i k))

lemma stWeight_permS (pr : SlotPerm P) (s : P.MState) :
    P.stWeight (permS P pr s) = P.stWeight s := by
  unfold MemParams.stWeight permS; rw [listWeight_permL]

lemma mem_listCands_permL (pr : SlotPerm P) (ℓ : P.Lst) :
    permL P pr ℓ ∈ listCands P.x P.a P.J ↔ ℓ ∈ listCands P.x P.a P.J := by
  simp only [listCands, Fintype.mem_piFinset, permL, Function.comp]
  constructor
  · intro h i k; simpa using h i ((pr i).symm k)
  · intro h i k; exact h i _

lemma mem_stSet_permS (pr : SlotPerm P) (s : P.MState) :
    permS P pr s ∈ P.stSet ↔ s ∈ P.stSet := by
  simp only [MemParams.stSet, mem_product, permS, mem_listCands_permL]

lemma sum_permS {M : Type*} [AddCommMonoid M] (pr : SlotPerm P) (φ : P.MState → M) :
    ∑ s ∈ P.stSet, φ (permS P pr s) = ∑ s ∈ P.stSet, φ s := by
  refine sum_nbij' (permS P pr) (permS P pr⁻¹) (fun s hs => (mem_stSet_permS P pr s).2 hs)
    (fun s hs => (mem_stSet_permS P pr⁻¹ s).2 hs) (fun s _ => permS_cancel_inv P pr s)
    (fun s _ => permS_inv_cancel P pr s) (fun s _ => rfl)

/-- The number of slot permutations. -/
lemma card_slotPerm : Fintype.card (SlotPerm P) = (P.J + 1).factorial ^ P.K := by
  rw [Fintype.card_pi, prod_const, card_univ, Fintype.card_fin, Fintype.card_perm,
    Fintype.card_fin]

lemma symM_eq (f : P.MState → ℂ) (s : P.MState) :
    P.symM f s = (((Fintype.card (SlotPerm P) : ℕ) : ℂ))⁻¹ *
      ∑ pr : SlotPerm P, f (permS P pr s) := by
  rw [card_slotPerm]; rfl

/-! ## The weighted inner product -/

/-! ## The slot symmetrization -/

lemma norm_sq_symM_le (f : P.MState → ℂ) (s : P.MState) :
    ‖P.symM f s‖ ^ 2 ≤ ((Fintype.card (SlotPerm P) : ℕ) : ℝ)⁻¹ *
      ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2 := by
  rw [symM_eq]
  set N := ((Fintype.card (SlotPerm P) : ℕ) : ℝ)
  have hN : 0 < N := by
    simp only [N]; exact_mod_cast Fintype.card_pos
  have h1 : ‖(((Fintype.card (SlotPerm P) : ℕ) : ℂ))⁻¹ * ∑ pr : SlotPerm P, f (permS P pr s)‖ ≤
      N⁻¹ * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ := by
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
  have h2 : (∑ pr : SlotPerm P, ‖f (permS P pr s)‖) ^ 2 ≤
      N * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := (univ : Finset (SlotPerm P)))
      (f := fun pr => ‖f (permS P pr s)‖)
    simpa [N] using this
  calc _ ≤ (N⁻¹ * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = N⁻¹ ^ 2 * (∑ pr : SlotPerm P, ‖f (permS P pr s)‖) ^ 2 := by ring
    _ ≤ N⁻¹ ^ 2 * (N * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by field_simp

lemma wNorm_symM_le (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s) (f : P.MState → ℂ) :
    P.wNorm (P.symM f) ≤ P.wNorm f := by
  unfold MemParams.wNorm
  apply Real.sqrt_le_sqrt
  set N := ((Fintype.card (SlotPerm P) : ℕ) : ℝ)
  have hN : 0 < N := by simp only [N]; exact_mod_cast Fintype.card_pos
  calc ∑ s ∈ P.stSet, P.stWeight s * ‖P.symM f s‖ ^ 2 ≤
      ∑ s ∈ P.stSet, P.stWeight s * (N⁻¹ * ∑ pr : SlotPerm P, ‖f (permS P pr s)‖ ^ 2) :=
        sum_le_sum fun s hs => mul_le_mul_of_nonneg_left (norm_sq_symM_le P f s) (hμ s hs)
    _ = N⁻¹ * ∑ pr : SlotPerm P, ∑ s ∈ P.stSet, P.stWeight s * ‖f (permS P pr s)‖ ^ 2 := by
        rw [mul_sum]
        simp_rw [mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun pr _ => sum_congr rfl fun s _ => by ring
    _ = N⁻¹ * ∑ _pr : SlotPerm P, ∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2 := by
        congr 1; refine Fintype.sum_congr _ _ fun pr => ?_
        rw [← sum_permS P pr (fun s => P.stWeight s * ‖f s‖ ^ 2)]
        simp only [stWeight_permS]
    _ = _ := by
        rw [sum_const, card_univ, nsmul_eq_mul]; field_simp; rfl

/-! ## One piece of a choice-indexed operator -/

variable {γ : Type*}

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: reversing an edge (columns are rows of the reversed edge)

For a choice `c = (St, z', tg)` at a state `s = (z, ℓ, m)` with output `s' = (z', ℓ', m')`, the
reversed choice at `s'` is `(I, z, (ℓᵢ(last), i ∈ St))`, `I` the promoted groups: promotions become
stores and stores become promotions. `rev_rev`: reversing twice is the identity;
`edgeOut_rev`: the reversed edge returns to `s`; `econd_rev`: it satisfies the edge conditions;
`weight_rev`: `μ(s) rfac(s,c) ∏_{I} Vᵢ = μ(s') rfac(s',c') ∏_{St} Vᵢ` (the Fock measure identity
`memW(m₀ + δ_y) (m₀(y) + 1) = memW(m₀) λ(y)`, [21] (4.18)). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- Edge choices. -/
abbrev EC := Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool)

/-! ## Lists -/

/-! ## The edge condition and the real factor -/

/-! ## The reversal -/

/-! ## The Fock measure identity -/

end ArtinPrimitiveRoots.L102G
end

section
/-! # L102G: column sums of edge pieces are row sums of the reversed pieces

`coeffP Qc κ` is the edge coefficient restricted to the classes `Qc St I` (stored groups `St`,
promoted groups `I`) with the geometric multiplier replaced by `κ`. `col_via_rev`: the weighted
column sum of `coeffP Qc κ` against `Φ ≥ 0` is at most `3^K` times the row sum of
`coeffP Qc' κ'` against `Φ`, when `Qc St I → Qc' I St` and `‖κ t a b D‖ ≤ ‖κ' (−t) b a D‖`
(`1/2 ≤ Vᵢ ≤ 3/2`, nonnegative `ν`). -/

namespace ArtinPrimitiveRoots.L102G

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

lemma lam_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (y : P.PT) : 0 ≤ P.lam y := by
  have h := y.2
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range] at h
  obtain ⟨i, p, hp, l, _, he⟩ := h
  unfold MemParams.lam; rw [← he]; exact hnu i p hp

lemma stWeight_nonneg (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (s : P.MState) (hs : s ∈ P.stSet) :
    0 ≤ P.stWeight s := by
  simp only [MemParams.stSet, mem_product] at hs
  unfold MemParams.stWeight MemParams.memWeight MemParams.listWeight
  refine mul_nonneg (prod_nonneg fun i _ => prod_nonneg fun k _ => ?_)
    (prod_nonneg fun y _ => by have := lam_nonneg P hnu y; positivity)
  apply hnu
  have := hs.2.1
  simp only [listCands, Fintype.mem_piFinset] at this
  exact this i k

end ArtinPrimitiveRoots.L102G
end

section
/-!
# Elementary divisor-sum estimates
-/

namespace ArtinBV

open Finset

end ArtinBV
end

section
/-! # L102D: the exact outer reduction of (10.9) ([21] §3.1, (3.10)–(3.11))

`Q_Y − Q_Y^maj = Q^sh − Q^{maj,sh} + Q^min`, where `Q^sh`, `Q^{maj,sh}` are the parts of the two
squares over label pairs whose products `a, b` are not coprime, and `Q^min` is the coprime part
of the minor-arc square, with kernel `ψ(t/Y) ∫_{[0,1) ∖ 𝔐} e(θ(t − b + a)) dθ`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary inputs -/

/-! ## The identity -/

/-! ## The reduction of (10.9) to the shared-label bound (D1b) and the minor-arc bound (D1c) -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: good positions and their measure ([21] §3.2, Lemma 3.2)

For lists `ℓ` of `M` primes in each group, the omission products `D` (omit one label per group),
the two good-state tests on a ratio `r ∈ ℝ/ℤ` (realized on `(0, 1]`), and Lemma 3.2: the set of
`r` failing goodness has measure at most `exp(-c L^{0.1})`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Distance to the nearest integer and its level sets -/

lemma circNorm_eq_norm (t : ℝ) : circNorm t = ‖(t : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]; rfl

/-- For a nonzero integer `n`, `{r ∈ (0,1] : ‖n r‖ ≤ ε}` has measure at most `2ε`
(multiplication by `n` preserves Haar measure on `ℝ/ℤ`). -/
lemma volume_circNorm_le (n : ℤ) (hn : n ≠ 0) (ε : ℝ) :
    volume ({r : ℝ | circNorm (n * r) ≤ ε} ∩ Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * ε) := by
  set f : ℝ → UnitAddCircle := fun r => n • (r : UnitAddCircle)
  have hf : MeasurePreserving f (volume.restrict (Set.Ioc (0 : ℝ) 1)) volume := by
    have := (Measure.measurePreserving_zsmul (volume : Measure UnitAddCircle) hn).comp
      (AddCircle.measurePreserving_mk (1 : ℝ) 0)
    simpa [f, Function.comp_def] using this
  have hset : {r : ℝ | circNorm (n * r) ≤ ε} = f ⁻¹' Metric.closedBall 0 ε := by
    ext r
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, f]
    rw [circNorm_eq_norm, ← AddCircle.coe_zsmul]
    simp
  have hmeas : MeasurableSet (f ⁻¹' Metric.closedBall 0 ε) :=
    hf.measurable measurableSet_closedBall
  rw [hset, ← Measure.restrict_apply hmeas, hf.measure_preimage
    measurableSet_closedBall.nullMeasurableSet, AddCircle.volume_closedBall]
  exact ENNReal.ofReal_le_ofReal (min_le_right _ _)

/-! ## Test (i): the union bound -/

/-! ## Markov's inequality for a finite weighted family of bad sets -/

/-! ## Test (ii): one fresh draw, then Markov over the fresh draws -/

/-! ## Counting and asymptotics -/

/-- `L^b ≤ ε L^c` eventually, for `b < c` and `ε > 0`. -/
lemma eventually_rpow_le_rpow {b c : ℝ} (hbc : b < c) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ b ≤ ε * L ^ c := by
  have h := (tendsto_rpow_neg_atTop (sub_pos.2 hbc)).eventually (ge_mem_nhds hε)
  filter_upwards [h, Filter.eventually_gt_atTop 0] with L hL hL0
  have : L ^ b = L ^ (-(c - b)) * L ^ c := by
    rw [← Real.rpow_add hL0]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hL (by positivity)

/-! ## Lemma 3.2 -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the divisor input (3.9) of [21] §3.1

`∑_{h ≤ Z} τ(1 + l h)² ≤ 4 (Z + T)(1 + log T)³` whenever every `m` with `m⁴ ≤ (1 + lZ)³` is
`≤ T`. The proof replaces `τ(n)² = #{(d₁, d₂) : d₁, d₂ ∣ n}` by four times the number of divisor
pairs with `lcm⁴ ≤ n³` (one of `(d₁,d₂)`, `(n/d₁,n/d₂)`, `(d₁,n/d₂)`, `(n/d₁,d₂)` qualifies), and
then counts `h` in one residue class modulo the `lcm`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the shared-label parts are negligible ([21] §3.1 (3.9), §4.9 (4.61), (4.63))

Bounds for the inner sums `rawInner`, `majInner` at one pair of label products, for the measure of
the major arcs, and for the normalized mass of label pairs with a common prime. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-! ## Elementary facts about the cutoffs and coefficients -/

/-! ## The measure of the major arcs -/

/-- `vol 𝔐 ≤ 4 L^{3A₀}/Y` (`L = log x ≥ 1`, `A₀ ≥ 0`, `Y > 0`). -/
lemma volume_majorArcs_le (x A₀ Y : ℝ) (hL : 1 ≤ log x) (hA₀ : 0 ≤ A₀) (hY : 0 < Y) :
    volume (majorArcs x A₀ Y) ≤ ENNReal.ofReal (4 * log x ^ (3 * A₀) / Y) := by
  set Q := log x ^ A₀
  set K₀ := ⌊Q⌋₊
  set ρ := 2 * Q / Y
  have hQ1 : 1 ≤ Q := Real.one_le_rpow hL hA₀
  have hsub : majorArcs x A₀ Y ⊆ {0} ∪ ⋃ k ∈ Icc 1 K₀,
      ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩ Set.Ioc 0 1) := by
    rintro θ ⟨h0, h1, k, hk1, hkQ, c, -, hc⟩
    rcases h0.lt_or_eq with h0 | h0
    · right
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_Icc]
      refine ⟨k, ⟨hk1, Nat.le_floor hkQ⟩, ?_, h0, h1.le⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      calc circNorm (((k : ℤ) : ℝ) * θ) ≤ |((k : ℤ) : ℝ) * θ - c| := round_le _ c
        _ = k * |θ - c / k| := by
            have e : ((k : ℤ) : ℝ) * θ - c = k * (θ - c / k) := by
              push_cast; field_simp
            rw [e, abs_mul, abs_of_pos hk0]
        _ ≤ k * ρ := by gcongr
    · left; exact h0.symm
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  rw [Real.volume_singleton, zero_add]
  refine (measure_biUnion_finset_le _ _).trans ?_
  have hterm : ∀ k ∈ Icc 1 K₀, volume ({θ : ℝ | circNorm (((k : ℤ) : ℝ) * θ) ≤ k * ρ} ∩
      Set.Ioc 0 1) ≤ ENNReal.ofReal (2 * (k * ρ)) := fun k hk =>
    volume_circNorm_le k (by have := (mem_Icc.1 hk).1; omega) _
  refine (sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hK₀ : (K₀ : ℝ) ≤ Q := Nat.floor_le (by positivity)
  have hsum : ∑ k ∈ Icc 1 K₀, 2 * ((k : ℝ) * ρ) ≤ ∑ _k ∈ Icc 1 K₀, 2 * (Q * ρ) := by
    refine sum_le_sum fun k hk => ?_
    have : (k : ℝ) ≤ Q := (Nat.cast_le.2 (mem_Icc.1 hk).2).trans hK₀
    gcongr
  refine hsum.trans ?_
  rw [sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
  have h3 : log x ^ (3 * A₀) = Q * Q * Q := by
    rw [show 3 * A₀ = A₀ + A₀ + A₀ by ring, Real.rpow_add (by linarith),
      Real.rpow_add (by linarith)]
  rw [h3]
  have hρ : 0 ≤ ρ := by positivity
  calc (K₀ : ℝ) * (2 * (Q * ρ)) ≤ Q * (2 * (Q * ρ)) := by gcongr
    _ = 4 * (Q * Q * Q) / Y := by simp only [ρ]; ring

/-! ## The raw inner sum at one pair of label products -/

/-! ## The major inner sum at one pair of label products -/

/-! ## The mass of label pairs with a common prime -/

/-! ## Inputs about the groups for large `x` -/

lemma le_of_mem_primeGroup {x b : ℝ} {q : ℕ} (h : q ∈ primeGroup x b) :
    exp (log x ^ b) ≤ q ∧ (q : ℝ) ≤ exp (2 * log x ^ b) := by
  unfold primeGroup at h
  simp only [mem_filter, mem_range] at h
  refine ⟨h.2.2, ?_⟩
  have := Nat.lt_succ_iff.1 h.1
  exact (Nat.cast_le.2 this).trans (Nat.floor_le (exp_pos _).le)

/-! ## Numerics -/


/-! ## D1b: the shared-label bound -/

/-- Common setting: the hypotheses used by both halves of D1b, at one `x`. -/
structure SharedSetting (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (Y Hm Hn : ℝ) (α β : ℕ → ℂ) (C : ℝ) :
    Prop where
  hL1 : 1 ≤ log x
  hx : 0 < x
  hHm : 0 < Hm
  hHn : 0 < Hn
  hY : 1 ≤ Y
  hX1 : 1 ≤ Hm * Hn
  hα0 : α 0 = 0
  hβ0 : β 0 = 0
  hαb : ∀ m, ‖α m‖ ≤ log x ^ C
  hβb : ∀ n, ‖β n‖ ≤ log x ^ C
  hV : ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j)
  hab : ∀ i, (0.1 : ℝ) < a i
  hlog : 1 + log (17 * (Hm * Hn)) ≤ 2 * log x


end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: root coordinates of a primitive position (for D7p)

For a primitive `P₀ = (u, v)` with `u ≥ 1`: `c = (−v⁻¹ mod u)`, `d = (1 + vc)/u`, the completion
`g = (u c; v d) ∈ SL₂(ℤ)`, `g z = (u z₁ + c z₂, v z₁ + d z₂)` and its inverse. Box conditions,
divisibility, goodness and the damping count transfer between `P = g z` and `z`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

/-- `c = (−v⁻¹ mod u)`. -/
noncomputable def rc (u v : ℕ) : ℤ := ((-(v : ZMod u)⁻¹ : ZMod u).val : ℤ)

/-! ## Goodness is invariant under integer shifts of the ratio -/

/-! ## The ratio of `g z` -/

/-! ## The damping count -/

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D1c (`minor_square_bound`) and the reduction

Four statements about the operator model of `L102D_OpDefs` (draft bundle
`Def_ArtinMinorOperator`):

* `MomentBoundStmt` (D7, [21] (3.19)/(4.1)): the moment of `(AA*)^R` is `≤ UV L^{-E₀ N}`;
* `PairingFromMomentStmt` (D5, [21] (3.20)): the pairing `⟨f, A f⟩_σ` is controlled by the moment;
* `GoodnessRemovalStmt` (D8a, [21] (4.56)–(4.57)): removing `G` from the pairing costs `UV L^{-A}`;
* `PadLiftStmt` (D8bc, [21] (4.58)–(4.63)): `Q^min = ∑_{dyads} d₀⁻¹ ⟨f, S T S f⟩_σ + O(XY L^{-A})`.

`minor_square_bound_of_cuts` proves the D1c statement from the four. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the cuts of D7 (the moment (4.1)) and the reduction

Seven statements about the draft model `L102D_OpDefs` + `L102D_MemDefs`, in the order of the
proof of [21] Proposition 4.1:

* `PathExpansionStmt` (D7p, exact): the physical moment is the sum over primitive roots `P₀` of
  the path functional in root coordinates, [21] §3.5 (3.30)–(3.32).
* `RootReplacementStmt` (D7r, [21] Lemma 3.4): the sum over roots is `UV/ζ(2)` times the integral
  of the independent-line moment over `[1,16] × [1,2] × [0,1]`, up to `UV L^{-AN}`.
* `MemoryIdentityStmt` (D7a, exact, [21] (4.5)–(4.15)): the independent-line moment is the
  baseline times the memory moment with global birth distinctness (no truncation).
* `TruncationStmt` (D7b, [21] (4.16)): truncating the memory at `B = ⌈L²⌉` costs `L^{-AN}`.
* `GhostBoundStmt` (D7c, [21] (4.19)–(4.22)): `‖G_j‖ ≤ C_K` on `H_B`.
* `EdgeBoundStmt` (D7d, [21] (4.23)–(4.42)): `‖E_j‖ ≤ L^{-G}` on `H_B`, `A₀` and then `K` large.
* `DistinctnessStmt` (D7e, [21] (4.43)–(4.55)): given D7c and D7d, the truncated memory moment
  with global birth distinctness is `≤ L^{-(G-1)N}`.

`moment_bound_of_cuts` proves `MomentBoundStmt` (D7) from them. -/

-- `MemParams.RootIn` now lives in the bundle `Def_ArtinMemoryModel` (round 5).

namespace ArtinPrimitiveRoots.L102D

open Real Finset

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: crude edge rows ([21] (4.23)–(4.25)) with forced fresh labels (for D7e)

* `target_count`: at most `16` targets `z'` in the box with `det(z, z') = j₁` (`z' = h z + j₁ w`,
  `τ(z')/τ(z) ∈ [1/16, 16]`);
* `norm_edgeMult_le`: `‖edgeMult‖ ≤ 1[|t| < 5Y] (1[t = b − a] + vol 𝔐)`;
* `edge_row`: the weighted absolute row sum of an edge with any multiplier `κ` of that shape, with
  the fresh labels of the groups in `C` forced into a set `V`. Uses prover G's `coeffK`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

section Geo

variable (P : MemParams)

end Geo

/-! ## The kernel -/

/-! ## The crude edge row -/

section Row

variable (P : MemParams)

end Row

section RowMain

variable (P : MemParams)

end RowMain

section RowThm

variable (P : MemParams)

end RowThm

section RowSum

variable (P : MemParams)

end RowSum

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the weighted Schur test for choice-indexed operators

An operator in the row convention, `(O f)(s) = ∑_{c ∈ Ch} coeff(s, c) f(out(s, c))` (outputs
outside the state set `St` dropped), on `ℓ²(St, μ)`. With a positive Schur weight `w`, a weighted
row bound `R` and a weighted column bound `C` give `‖O f‖² ≤ R C ‖f‖²` ([21] §4.4). -/

namespace ArtinPrimitiveRoots.L102D

open Finset

variable {α γ : Type*} [DecidableEq α]

/-- The choice-indexed operator. -/
def choiceOp (St : Finset α) (Ch : Finset γ) (coeff : α → γ → ℂ) (out : α → γ → α)
    (f : α → ℂ) (s : α) : ℂ :=
  ∑ c ∈ Ch, coeff s c * (if out s c ∈ St then f (out s c) else 0)

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the crude norm of a modified edge ([21] (4.23)–(4.25)) (for D7e)

An edge whose coefficients are multiplied by anything of modulus `≤ 1` (phases, validity checks) has
norm `≤ √R · √(3^K R)` on `H_B`, `R = 2^K · 16 (1 + (10Y+1) vol 𝔐) · (2 + 2B)^K`: rows by `edge_row`,
columns by prover G's reversal (`L102G.col_via_rev`), and G's bilinear Cauchy–Schwarz
(`L102G.piece_bound`, `L102G.opBound_of_bilin`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The crude edge row bound `R`. -/
noncomputable def edgeR : ℝ :=
  2 ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
    (2 + 2 * P.B) ^ P.K

lemma edgeR_nonneg (hY : 0 ≤ P.Y) : 0 ≤ edgeR P := by
  unfold edgeR
  have : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  positivity

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: basic facts about the memory parameters (no stubs)

`etav_mem`, `bprime_mem` (`0 < b'_p ≤ 1` once `N < p`), `bprime_ge_half`, `abs_baseline_le`, and
the asymptotic fact that the group primes eventually exceed any fixed multiple of `R + 1`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

lemma etav_mem (P : MemParams) (j : ℕ) : 0 ≤ P.etav j ∧ P.etav j ≤ 1 := by
  unfold MemParams.etav MemParams.qv
  split_ifs <;> norm_num

lemma bprime_ge_half (P : MemParams) {p : ℕ} (hp : 2 * P.N + 1 ≤ p) : 1 / 2 ≤ P.bprime p := by
  have hs : ∑ j ∈ range (P.N + 1), P.etav j ≤ P.N + 1 := by
    calc ∑ j ∈ range (P.N + 1), P.etav j ≤ ∑ _j ∈ range (P.N + 1), (1 : ℝ) :=
          sum_le_sum fun j _ => (etav_mem P j).2
      _ = P.N + 1 := by simp
  have hp' : 2 * ((P.N : ℝ) + 1) ≤ p + 1 := by
    have : (2 * P.N + 1 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  unfold MemParams.bprime
  have : (∑ j ∈ range (P.N + 1), P.etav j) / ((p : ℝ) + 1) ≤ 1 / 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  linarith

/-- Eventually every group prime is at least `C (R + 1)`. -/
lemma eventually_groupPrimes_ge {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, (0.1 : ℝ) < a i) (C : ℝ) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ p ∈ groupPrimes x a, C * (momentPower x + 1) ≤ p := by
  have hL : Filter.Tendsto (fun x : ℝ => log x ^ (0.1 : ℝ)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp tendsto_log_atTop
  filter_upwards [hL.eventually_ge_atTop (720 * (|C| + 1) + 722),
    Filter.eventually_ge_atTop (exp 1)] with x hx hx1
  intro p hp
  have hlog : 1 ≤ log x := by
    rw [← log_exp 1]; exact log_le_log (exp_pos 1) hx1
  simp only [groupPrimes, mem_biUnion, mem_univ, true_and] at hp
  obtain ⟨i, hi⟩ := hp
  simp only [primeGroup, mem_filter] at hi
  have hpge : exp (log x ^ a i) ≤ p := hi.2.2
  have h1 : log x ^ (0.1 : ℝ) ≤ log x ^ a i := rpow_le_rpow_of_exponent_le hlog (ha i).le
  set y := log x ^ (0.1 : ℝ) with hy
  have hy0 : 0 ≤ y := by positivity
  have h5 : y ^ 5 = log x ^ (0.5 : ℝ) := by
    rw [hy, ← rpow_natCast, ← rpow_mul (by linarith)]; norm_num
  have hmp : (momentPower x : ℝ) + 1 ≤ y ^ 5 + 2 := by
    unfold momentPower
    have := Nat.ceil_lt_add_one (show 0 ≤ log x ^ (0.5 : ℝ) / 2 by positivity)
    have h2 : 0 ≤ log x ^ (0.5 : ℝ) := by positivity
    rw [h5]; linarith
  have h6 := Real.pow_div_factorial_le_exp y hy0 6
  have hf : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
  rw [hf] at h6
  have hy1 : 1 ≤ y := by linarith [abs_nonneg C]
  have hy5 : 1 ≤ y ^ 5 := one_le_pow₀ hy1
  have hkey : (|C| + 1) * (y ^ 5 + 2) ≤ y ^ 6 / 720 := by
    have e : y ^ 6 / 720 = y * y ^ 5 / 720 := by ring
    rw [e, le_div_iff₀ (by norm_num)]
    have h7 : (720 * (|C| + 1) + 722) * y ^ 5 ≤ y * y ^ 5 :=
      mul_le_mul_of_nonneg_right hx (by positivity)
    have h8 : y ≤ y ^ 5 := le_self_pow₀ hy1 (by norm_num)
    have h9 : 720 * (|C| + 1) ≤ y ^ 5 := by linarith [abs_nonneg C]
    have hc0 : 0 ≤ |C| + 1 := by positivity
    nlinarith
  have hCabs : C * ((momentPower x : ℝ) + 1) ≤ (|C| + 1) * (y ^ 5 + 2) := by
    have h0 : 0 ≤ (momentPower x : ℝ) + 1 := by positivity
    calc C * ((momentPower x : ℝ) + 1) ≤ |C| * ((momentPower x : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) h0
      _ ≤ (|C| + 1) * (y ^ 5 + 2) := by
          apply mul_le_mul (by linarith) hmp h0 (by positivity)
  calc C * ((momentPower x : ℝ) + 1) ≤ (|C| + 1) * (y ^ 5 + 2) := hCabs
    _ ≤ y ^ 6 / 720 := hkey
    _ ≤ exp y := h6
    _ ≤ exp (log x ^ a i) := exp_le_exp.2 h1
    _ ≤ p := hpge

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7c, the ghost bound ([21] (4.19)–(4.22))

Weighted Schur test with the weight `w = v₀^{memory size}`, `v₀ = 12`. The ghost coefficient is a
product over particle types (`gAbs`), so the weighted row and column sums factor:
* row, per hit type: `∑_{u ≤ n} C(n,u) (η'/ρ)^u (q/ρ²)^{n−u} v₀^{n−u} · ∑_v (v₀ η'Vλ/ρ)^v/v!
  ≤ v₀^n (η'/(ρv₀) + q/ρ²)^n exp(v₀η'Vλ/ρ)`;
* column, per hit type (input count `n' − v + u` for output count `n'`):
  `λ^{n'} v₀^{n'}/n'! · (q/ρ² + η'V/(ρ v₀))^{n'} · exp(v₀ η' λ/ρ)`.
With `ρ = 3/4`, `q_j ∈ {1/2, 1/4}`, `Vᵢ ≤ 3/2` (Mertens, through the stub) the parentheses are
`≤ 1`, and `∑_{hits} λ ≤ ∑ᵢ ∑_p νᵢ(p) ≤ 2K` once `b'_p ≥ 1/2`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

section GhostAlg

variable (P : MemParams)

/-- The absolute ghost factor of one particle type: input count `n`, deleted `u`, born `v`. -/
noncomputable def gAbs (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n u v : ℕ) : ℝ :=
  if P.IsHit z y then
    (if u ≤ n then (n.choose u : ℝ) * (P.etav j / memRho) ^ u * (P.qv j / memRho ^ 2) ^ (n - u) *
      (P.etav j * P.Vg y.1.1 / memRho * P.lam y) ^ v / (v.factorial : ℝ) else 0)
  else (if u = 0 ∧ v = 0 then 1 else 0)

lemma memRho_pos : (0 : ℝ) < memRho := by unfold memRho; norm_num

lemma qv_nonneg (j : ℕ) : 0 ≤ P.qv j := by unfold MemParams.qv; split_ifs <;> norm_num

lemma gAbs_nonneg (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n u v : ℕ) (hV : 0 ≤ P.Vg y.1.1)
    (hl : 0 ≤ P.lam y) : 0 ≤ gAbs P j z y n u v := by
  have := (etav_mem P j).1
  have := qv_nonneg P j
  have := memRho_pos
  unfold gAbs
  split_ifs <;> positivity

lemma norm_ghostCoeff_le (j : ℕ) (s : P.MState) (c : P.Mem × P.Mem)
    (hV : ∀ i, 0 ≤ P.Vg i) (hl : ∀ y, 0 ≤ P.lam y) :
    ‖P.ghostCoeff j s c‖ ≤ ∏ y, gAbs P j s.1 y (s.2.2 y) (c.1 y) (c.2 y) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold MemParams.ghostCoeff
  split_ifs with h
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_prod]
    refine prod_le_prod (fun y _ => abs_nonneg _) fun y _ => ?_
    unfold gAbs
    by_cases hy : P.IsHit s.1 y
    · rw [if_pos hy, if_pos hy, if_pos (h.1 y)]
      have e : ((s.2.2 y).choose (c.1 y) : ℝ) * (-P.etav j / memRho) ^ c.1 y *
          (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
          (-P.etav j * P.Vg y.1.1 / memRho) ^ c.2 y * P.lam y ^ c.2 y /
            ((c.2 y).factorial : ℝ) =
          (-1) ^ (c.1 y + c.2 y) * (((s.2.2 y).choose (c.1 y) : ℝ) *
            (P.etav j / memRho) ^ c.1 y * (P.qv j / memRho ^ 2) ^ (s.2.2 y - c.1 y) *
            (P.etav j * P.Vg y.1.1 / memRho * P.lam y) ^ c.2 y / ((c.2 y).factorial : ℝ)) := by
        rw [pow_add, mul_pow (P.etav j * P.Vg y.1.1 / memRho), neg_div, neg_pow,
          neg_mul, neg_div, neg_pow]
        ring
      rw [e, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by have := hV y.1.1; have := hl y; positivity)]
    · rw [if_neg hy, if_neg hy, abs_one, if_pos ⟨(h.2 y hy).1, (h.2 y hy).2⟩]
  · rw [norm_zero]
    exact prod_nonneg fun y _ => gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)

end GhostAlg

section GhostAssembly

variable (P : MemParams)

/-- The product formula for sums over pairs of memories. -/
lemma sum_ghostChoices_prod_le (F : P.PT → ℕ → ℕ → ℝ) (hF : ∀ y u v, 0 ≤ F y u v) :
    ∑ c ∈ P.ghostChoices, ∏ y, F y (c.1 y) (c.2 y) ≤
      ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), F y u v := by
  set T := Fintype.piFinset fun _ : P.PT => range (P.B + 1) with hT
  have hsub : P.ghostChoices ⊆ T ×ˢ T := by
    intro c hc
    simp only [MemParams.ghostChoices, mem_product, MemParams.memSet, mem_filter] at hc
    exact mem_product.2 ⟨hc.1.1, hc.2.1⟩
  calc ∑ c ∈ P.ghostChoices, ∏ y, F y (c.1 y) (c.2 y) ≤
      ∑ c ∈ T ×ˢ T, ∏ y, F y (c.1 y) (c.2 y) :=
        sum_le_sum_of_subset_of_nonneg hsub fun c _ _ => prod_nonneg fun y _ => hF _ _ _
    _ = ∑ e ∈ T, ∑ b ∈ T, ∏ y, F y (e y) (b y) := sum_product _ _ _
    _ = ∑ e ∈ T, ∏ y, ∑ v ∈ range (P.B + 1), F y (e y) v := by
        refine sum_congr rfl fun e _ => ?_
        rw [hT, prod_univ_sum]
    _ = ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), F y u v := by
        rw [hT, prod_univ_sum]

lemma memSize_pow (v₀ : ℝ) (m : P.Mem) : v₀ ^ P.memSize m = ∏ y, v₀ ^ m y := by
  unfold MemParams.memSize; rw [prod_pow_eq_pow_sum]

end GhostAssembly

section GhostFinal

lemma mem_grp_of_part (P : MemParams) (y : P.PT) : y.1.2.1 ∈ P.grp y.1.1 := by
  have h := y.2
  simp only [MemParams.partSet, mem_biUnion, mem_univ, true_and, mem_image, mem_range] at h
  obtain ⟨i, p, hp, l, _, he⟩ := h
  rw [← he]; exact hp

lemma sum_hit_lam_le (P : MemParams) (z : ℤ × ℤ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) :
    ∑ y : P.PT, (if P.IsHit z y then P.lam y else 0) ≤ ∑ i, ∑ p ∈ P.grp i, P.nu i p := by
  rw [← sum_filter]
  set H := (univ : Finset P.PT).filter fun y => P.IsHit z y
  set g : P.PT → Fin P.K × ℕ := fun y => (y.1.1, y.1.2.1)
  set S := (univ ×ˢ P.gPrimes).filter fun q : Fin P.K × ℕ => q.2 ∈ P.grp q.1
  have hinj : Set.InjOn g H := by
    intro y hy y' hy' he
    simp only [H, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    simp only [g, Prod.mk.injEq] at he
    apply Subtype.ext
    have h3 : y.1.2.2 = y'.1.2.2 := by
      unfold MemParams.IsHit at hy hy'; rw [hy, hy', he.2]
    exact Prod.ext he.1 (Prod.ext he.2 h3)
  have himg : H.image g ⊆ S := by
    intro q hq
    simp only [mem_image] at hq
    obtain ⟨y, _, rfl⟩ := hq
    simp only [S, g, mem_filter, mem_product, mem_univ, true_and]
    have := mem_grp_of_part P y
    refine ⟨?_, this⟩
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨y.1.1, this⟩
  calc ∑ y ∈ H, P.lam y = ∑ y ∈ H, (fun q : Fin P.K × ℕ => P.nu q.1 q.2) (g y) := rfl
    _ = ∑ q ∈ H.image g, P.nu q.1 q.2 :=
        (sum_image (f := fun q : Fin P.K × ℕ => P.nu q.1 q.2) hinj).symm
    _ ≤ ∑ q ∈ S, P.nu q.1 q.2 := sum_le_sum_of_subset_of_nonneg himg fun q hq _ => by
        simp only [S, mem_filter] at hq; exact hnu _ _ hq.2
    _ = ∑ i, ∑ p ∈ P.grp i, P.nu i p := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_filter]
        congr 1
        ext p
        simp only [mem_filter, and_iff_right_iff_imp]
        intro hp
        simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
        exact ⟨i, hp⟩

/-- `Vᵢ ≥ 1/2` eventually (Mertens). -/
lemma eventually_Vg_ge_half {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ j, (1 : ℝ) / 2 ≤ groupReciprocalSum x (a j) := by
  refine Filter.eventually_all.2 fun j => ?_
  have hm := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hlog : (1 : ℝ) / 2 < log (2 / 1) := by
    rw [div_one]; have := Real.log_two_gt_d9; linarith
  have hev := hm.eventually (lt_mem_nhds hlog)
  have hy : Filter.Tendsto (fun x : ℝ => exp (log x ^ a j)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop)
  filter_upwards [hy.eventually hev] with x hx
  refine hx.le.trans ?_
  unfold groupReciprocalSum primeGroup
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  have e2 : exp (log x ^ a j) ^ (2 : ℝ) = exp (2 * log x ^ a j) := by
    rw [← Real.exp_mul]; ring_nf
  rw [e2, Real.rpow_one] at hp
  exact ⟨hp.1, hp.2.1, hp.2.2.le⟩

/-- `Vᵢ ≤ 3/2` eventually (Mertens with exponents `1/2, 2`: `Vᵢ ≤ ∑_{X^{1/2} < p ≤ X²} 1/p → log 4`). -/
lemma eventually_Vg_le {K : ℕ} (a : Fin K → ℝ) (ha : ∀ i, 0 < a i) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ j, groupReciprocalSum x (a j) ≤ 3 / 2 := by
  refine Filter.eventually_all.2 fun j => ?_
  have hm := mertens_prime_reciprocals (1 / 2) 2 (by norm_num) (by norm_num)
  have hlog : log (2 / (1 / 2)) < 3 / 2 := by
    have e : (2 : ℝ) / (1 / 2) = 2 * 2 := by norm_num
    rw [e, Real.log_mul (by norm_num) (by norm_num)]
    have := Real.log_two_lt_d9; linarith
  have hev := hm.eventually (gt_mem_nhds hlog)
  have hy : Filter.Tendsto (fun x : ℝ => exp (log x ^ a j)) Filter.atTop Filter.atTop :=
    tendsto_exp_atTop.comp ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop)
  have hpos : ∀ᶠ x : ℝ in Filter.atTop, 0 < log x ^ a j :=
    ((tendsto_rpow_atTop (ha j)).comp tendsto_log_atTop).eventually_gt_atTop 0
  filter_upwards [hy.eventually hev, hpos] with x hx hx0
  refine le_trans ?_ hx.le
  unfold groupReciprocalSum primeGroup
  refine sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) (fun p _ _ => by positivity)
  simp only [mem_filter, mem_range] at hp ⊢
  have e2 : exp (log x ^ a j) ^ (2 : ℝ) = exp (2 * log x ^ a j) := by
    rw [← Real.exp_mul]; ring_nf
  have e3 : exp (log x ^ a j) ^ ((1 : ℝ) / 2) = exp (log x ^ a j / 2) := by
    rw [← Real.exp_mul]; ring_nf
  rw [e2, e3]
  refine ⟨hp.1, hp.2.1, lt_of_lt_of_le ?_ hp.2.2⟩
  exact exp_lt_exp.2 (by linarith)

lemma ghost_params_ok (P : MemParams) (j : ℕ) (hV : ∀ i, P.Vg i ≤ 3 / 2) :
    P.etav j / memRho / 12 + P.qv j / memRho ^ 2 ≤ 1 ∧
      ∀ i, P.qv j / memRho ^ 2 + P.etav j * P.Vg i / memRho / 12 ≤ 1 := by
  unfold MemParams.etav MemParams.qv memRho
  constructor
  · split_ifs <;> norm_num
  · intro i
    have := hV i
    split_ifs
    · have h : (1 - 1 / 2 : ℝ) * P.Vg i / (3 / 4) / 12 ≤ 1 / 12 := by
        rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
      have h2 : (1 / 2 : ℝ) / (3 / 4) ^ 2 = 8 / 9 := by norm_num
      linarith
    · have h : (1 - 1 / 4 : ℝ) * P.Vg i / (3 / 4) / 12 ≤ 1 / 8 := by
        rw [div_le_iff₀ (by norm_num), div_le_iff₀ (by norm_num)]; nlinarith
      have h2 : (1 / 4 : ℝ) / (3 / 4) ^ 2 = 4 / 9 := by norm_num
      linarith


end GhostFinal

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: ghost rows with forced births (for D7e, large ranks)

A ghost birth slot `(i, k)` holds the `k`-th smallest prime born in group `i`. If the slots in `Cs` are
all forced to take values in a set `V`, at least `|Cs|` births lie in `V`; exponential tilting
`1[n ≥ c] ≤ τ^{n − c}` (`τ = 1/D ≥ 1`) multiplies the birth weight of the particles over `V` by `τ`,
so the weighted row sum `≤ e^{36K} · e^{18 τ ∑_{p ∈ V} ν(p)} · τ^{−|Cs|} ≤ e^{36K+1} D^{|Cs|}`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-! ## Counting forced slots -/

lemma card_forced_le {Sl : Type} [Fintype Sl] [DecidableEq Sl] (v : Sl → Option ℕ)
    (V : Finset ℕ) (Cs : Finset Sl) (h : ∀ q ∈ Cs, v q ≠ none ∧ (v q).getD 0 ∈ V) :
    Cs.card ≤ ∑ p ∈ V, Multiset.count p (slotMs v) := by
  have hsub : Cs ⊆ V.biUnion fun p => univ.filter fun q => v q = some p := by
    intro q hq
    obtain ⟨h1, h2⟩ := h q hq
    obtain ⟨p, hp⟩ := Option.ne_none_iff_exists'.1 h1
    rw [mem_biUnion]
    refine ⟨p, by rw [hp] at h2; simpa using h2, mem_filter.2 ⟨mem_univ _, hp⟩⟩
  refine (card_le_card hsub).trans (card_biUnion_le.trans (le_of_eq ?_))
  refine sum_congr rfl fun p _ => ?_
  rw [count_slotMs]

/-- The number of births over `V`. -/
noncomputable def nV (V : Finset ℕ) (b : P.Mem) : ℕ := ∑ y, if y.1.2.1 ∈ V then b y else 0

lemma sum_count_bornPrimes (V : Finset ℕ) (b : P.Mem) :
    ∑ p ∈ V, Multiset.count p (MemParams.bornPrimes P b) = nV P V b := by
  unfold MemParams.bornPrimes nV
  simp only [Multiset.count_sum', Multiset.count_nsmul, Multiset.count_singleton]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← mul_sum, sum_ite_eq']
  split_ifs <;> simp

lemma forced_ghost_le (b : P.Mem) (hb : P.memSize b ≤ P.B) (V : Finset ℕ)
    (Cs : Finset (DSlot P)) {τ : ℝ} (hτ : 1 ≤ τ) :
    (∏ q ∈ Cs, (if ghostBirth P b q ≠ none ∧ (ghostBirth P b q).getD 0 ∈ V then (1 : ℝ)
      else 0)) * τ ^ Cs.card ≤ τ ^ nV P V b := by
  by_cases h : ∀ q ∈ Cs, ghostBirth P b q ≠ none ∧ (ghostBirth P b q).getD 0 ∈ V
  · rw [prod_eq_one fun q hq => if_pos (h q hq), one_mul]
    refine pow_le_pow_right₀ hτ ?_
    have := card_forced_le (ghostBirth P b) V Cs h
    rwa [slotMs_ghostBirth P b hb, sum_count_bornPrimes] at this
  · push_neg at h
    obtain ⟨q, hq, hq'⟩ := h
    rw [prod_eq_zero hq (if_neg fun h' => hq' h'.1 h'.2), zero_mul]
    positivity

/-! ## The tilted row -/

lemma row_type_tilt (j : ℕ) (z : ℤ × ℤ) (y : P.PT) (n : ℕ) {v₀ τ : ℝ} (hv₀ : 0 < v₀)
    (hτ : 0 ≤ τ) (hV : 0 ≤ P.Vg y.1.1) (hl : 0 ≤ P.lam y)
    (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) :
    ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1), gAbs P j z y n u v * v₀ ^ (n - u + v) * τ ^ v ≤
      v₀ ^ n * (if P.IsHit z y then
        exp (v₀ * τ * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) := by
  have hη := (etav_mem P j).1
  have hq := qv_nonneg P j
  have hρ := memRho_pos
  unfold gAbs
  by_cases hy : P.IsHit z y
  · simp only [if_pos hy]
    set X := P.etav j / memRho
    set Q := P.qv j / memRho ^ 2
    set W := P.etav j * P.Vg y.1.1 / memRho * P.lam y
    have hX0 : 0 ≤ X := by positivity
    have hQ0 : 0 ≤ Q := by positivity
    have hW0 : 0 ≤ W := by positivity
    have hsplit : ∀ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * Q ^ (n - u) * W ^ v / (v.factorial : ℝ)
          else 0) * v₀ ^ (n - u + v) * τ ^ v =
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) *
          ∑ v ∈ range (P.B + 1), (v₀ * τ * W) ^ v / (v.factorial : ℝ) := by
      intro u _
      rw [mul_sum]
      refine sum_congr rfl fun v _ => ?_
      split_ifs
      · rw [pow_add, mul_pow, mul_pow, mul_pow]; ring
      · simp
    rw [sum_congr rfl hsplit, ← sum_mul]
    have hexp : ∑ v ∈ range (P.B + 1), (v₀ * τ * W) ^ v / (v.factorial : ℝ) ≤ exp (v₀ * τ * W) :=
      Real.sum_le_exp_of_nonneg (by positivity) _
    have hbin : ∑ u ∈ range (P.B + 1),
        (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) ≤ v₀ ^ n := by
      have h1 : ∑ u ∈ range (P.B + 1),
          (if u ≤ n then (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) else 0) ≤
          ∑ u ∈ range (n + 1), (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) := by
        rw [← sum_filter]
        refine sum_le_sum_of_subset_of_nonneg (fun u hu => ?_) (fun u _ _ => by positivity)
        simp only [mem_filter, mem_range] at hu ⊢; omega
      have h2 : ∑ u ∈ range (n + 1), (n.choose u : ℝ) * X ^ u * (Q * v₀) ^ (n - u) =
          (X + Q * v₀) ^ n := by
        rw [add_pow]; refine sum_congr rfl fun u _ => by ring
      have h3 : X + Q * v₀ = v₀ * (X / v₀ + Q) := by field_simp
      have h4 : (X + Q * v₀) ^ n ≤ v₀ ^ n := by
        rw [h3, mul_pow]
        have : (X / v₀ + Q) ^ n ≤ 1 := pow_le_one₀ (by positivity) hX
        calc v₀ ^ n * (X / v₀ + Q) ^ n ≤ v₀ ^ n * 1 :=
              mul_le_mul_of_nonneg_left this (by positivity)
          _ = v₀ ^ n := mul_one _
      linarith
    exact mul_le_mul hbin hexp (sum_nonneg fun v _ => by positivity) (by positivity)
  · simp only [if_neg hy, mul_one]
    rw [sum_eq_single 0]
    · rw [sum_eq_single 0]
      · simp
      · intro v _ hv; simp [hv]
      · intro h; simp at h
    · intro u _ hu
      refine sum_eq_zero fun v _ => ?_
      simp [hu]
    · intro h; simp at h

/-- The tilt of particle `y`. -/
noncomputable def tiltOf (V : Finset ℕ) (τ : ℝ) (y : P.PT) : ℝ := if y.1.2.1 ∈ V then τ else 1

lemma pow_nV (V : Finset ℕ) (τ : ℝ) (b : P.Mem) :
    τ ^ nV P V b = ∏ y, tiltOf P V τ y ^ b y := by
  unfold nV tiltOf
  rw [← prod_pow_eq_pow_sum]
  refine prod_congr rfl fun y _ => ?_
  split_ifs <;> simp

/-- **The tilted weighted ghost row.** -/
theorem ghost_row_tilt (j : ℕ) (s : P.MState) {v₀ τ : ℝ} (hv₀ : 0 < v₀) (hτ : 0 ≤ τ)
    (hV : ∀ i, 0 ≤ P.Vg i) (hl : ∀ y, 0 ≤ P.lam y)
    (hX : P.etav j / memRho / v₀ + P.qv j / memRho ^ 2 ≤ 1) (V : Finset ℕ) :
    ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
      (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) *
        τ ^ nV P V c.2 ≤
    (∏ y, if P.IsHit s.1 y then
      exp (v₀ * tiltOf P V τ y * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) *
      v₀ ^ P.memSize s.2.2 := by
  have htl : ∀ y, 0 ≤ tiltOf P V τ y := fun y => by unfold tiltOf; split_ifs <;> linarith
  calc ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
        (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) *
          τ ^ nV P V c.2 ≤
      ∑ c ∈ P.ghostChoices, ∏ y, (gAbs P j s.1 y (s.2.2 y) (c.1 y) (c.2 y) *
        v₀ ^ (s.2.2 y - c.1 y + c.2 y) * tiltOf P V τ y ^ c.2 y) := by
        refine sum_le_sum fun c _ => ?_
        have h1 := norm_ghostCoeff_le P j s c hV hl
        have h2 : (if P.ghostOut s c ∈ P.stSet then v₀ ^ P.memSize (P.ghostOut s c).2.2 else 0) ≤
            ∏ y, v₀ ^ (s.2.2 y - c.1 y + c.2 y) := by
          rw [← memSize_pow]
          split_ifs
          · rfl
          · positivity
        rw [prod_mul_distrib, prod_mul_distrib, ← pow_nV]
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact mul_le_mul h1 h2 (by split_ifs <;> positivity)
          (prod_nonneg fun y _ => gAbs_nonneg P j _ y _ _ _ (hV _) (hl y))
    _ ≤ ∏ y, ∑ u ∈ range (P.B + 1), ∑ v ∈ range (P.B + 1),
          gAbs P j s.1 y (s.2.2 y) u v * v₀ ^ (s.2.2 y - u + v) * tiltOf P V τ y ^ v :=
        sum_ghostChoices_prod_le P (fun y u v => gAbs P j s.1 y (s.2.2 y) u v *
          v₀ ^ (s.2.2 y - u + v) * tiltOf P V τ y ^ v) fun y u v =>
            mul_nonneg (mul_nonneg (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)) (by positivity))
              (pow_nonneg (htl y) _)
    _ ≤ ∏ y, (v₀ ^ s.2.2 y * (if P.IsHit s.1 y then
          exp (v₀ * tiltOf P V τ y * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1)) :=
        prod_le_prod (fun y _ => sum_nonneg fun u _ => sum_nonneg fun v _ =>
          mul_nonneg (mul_nonneg (gAbs_nonneg P j _ y _ _ _ (hV _) (hl y)) (by positivity))
            (pow_nonneg (htl y) _))
          fun y _ => row_type_tilt P j s.1 y (s.2.2 y) hv₀ (htl y) (hV _) (hl y) hX
    _ = _ := by rw [prod_mul_distrib, memSize_pow, mul_comm]

/-! ## The forced ghost row -/

lemma sum_hit_lam_filter_le (z : ℤ × ℤ) (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p)
    (V : Finset ℕ) :
    ∑ y : P.PT, (if P.IsHit z y ∧ y.1.2.1 ∈ V then P.lam y else 0) ≤
      ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p := by
  rw [← sum_filter]
  set H := (univ : Finset P.PT).filter fun y => P.IsHit z y ∧ y.1.2.1 ∈ V
  set g : P.PT → Fin P.K × ℕ := fun y => (y.1.1, y.1.2.1)
  set S := (univ ×ˢ P.gPrimes).filter fun q : Fin P.K × ℕ => q.2 ∈ (P.grp q.1).filter (· ∈ V)
  have hinj : Set.InjOn g H := by
    intro y hy y' hy' he
    simp only [H, coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hy hy'
    simp only [g, Prod.mk.injEq] at he
    apply Subtype.ext
    have h3 : y.1.2.2 = y'.1.2.2 := by
      have a := hy.1; have b := hy'.1
      unfold MemParams.IsHit at a b; rw [a, b, he.2]
    exact Prod.ext he.1 (Prod.ext he.2 h3)
  have himg : H.image g ⊆ S := by
    intro q hq
    simp only [mem_image] at hq
    obtain ⟨y, hy, rfl⟩ := hq
    simp only [H, mem_filter, mem_univ, true_and] at hy
    simp only [S, g, mem_filter, mem_product, mem_univ, true_and]
    have := mem_grp_of_part P y
    refine ⟨?_, this, hy.2⟩
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨y.1.1, this⟩
  calc ∑ y ∈ H, P.lam y = ∑ y ∈ H, (fun q : Fin P.K × ℕ => P.nu q.1 q.2) (g y) := rfl
    _ = ∑ q ∈ H.image g, P.nu q.1 q.2 :=
        (sum_image (f := fun q : Fin P.K × ℕ => P.nu q.1 q.2) hinj).symm
    _ ≤ ∑ q ∈ S, P.nu q.1 q.2 := sum_le_sum_of_subset_of_nonneg himg fun q hq _ => by
        simp only [S, mem_filter] at hq; exact hnu _ _ hq.2.1
    _ = ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p := by
        rw [sum_filter, sum_product]
        refine sum_congr rfl fun i _ => ?_
        rw [← sum_filter]
        congr 1
        ext p
        simp only [mem_filter, and_iff_right_iff_imp]
        intro hp
        simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
        exact ⟨i, hp.1⟩

lemma nu_nonneg_of (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i) (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p) :
    ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p := by
  intro i p hp
  have hp' : p ∈ P.gPrimes := by
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]; exact ⟨i, hp⟩
  have := hb p hp'
  have : 0 < P.Vg i := by linarith [hVge i]
  unfold MemParams.nu; positivity

lemma sum_nu_le_two (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
    (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p) (i : Fin P.K) :
    ∑ p ∈ P.grp i, P.nu i p ≤ 2 := by
  have hVi : 0 < P.Vg i := by linarith [hVge i]
  have hgrp : ∀ p ∈ P.grp i, p ∈ P.gPrimes := by
    intro p hp
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨i, hp⟩
  calc ∑ p ∈ P.grp i, P.nu i p ≤ ∑ p ∈ P.grp i, 2 / P.Vg i * (1 / (p : ℝ)) := by
        refine sum_le_sum fun p hp => ?_
        have hbp := hb p (hgrp p hp)
        have hp0 : (0 : ℝ) < p := by
          have := hp; simp only [MemParams.grp, primeGroup, mem_filter] at this
          exact_mod_cast this.2.1.pos
        unfold MemParams.nu
        rw [div_le_iff₀ (by positivity)]
        rw [show 2 / P.Vg i * (1 / (p : ℝ)) * (P.Vg i * ((p : ℝ) + 1) * P.bprime p) =
          2 * P.bprime p * (((p : ℝ) + 1) / p) by field_simp]
        have : (1 : ℝ) ≤ ((p : ℝ) + 1) / p := by rw [le_div_iff₀ hp0]; linarith
        nlinarith
    _ = 2 / P.Vg i * P.Vg i := by
        rw [← mul_sum]; rfl
    _ = 2 := by field_simp

set_option maxHeartbeats 1000000 in
/-- **The forced ghost row**: the slots `Cs` forced into `V`. -/
theorem ghost_forced_row (j : ℕ) (s : P.MState) (hVle' : ∀ i, P.Vg i ≤ 3 / 2)
    (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i) (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)
    (V : Finset ℕ) (Cs : Finset (DSlot P)) {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hDV : 18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D) :
    ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ * (if P.ghostOut s c ∈ P.stSet then 1 else 0) *
      (∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧ (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ)
        else 0)) * (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 ≤
    exp (36 * P.K + 1) * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by
  have hVpos : ∀ i, 0 < P.Vg i := fun i => by linarith [hVge i]
  have hV : ∀ i, 0 ≤ P.Vg i := fun i => (hVpos i).le
  have hnu := nu_nonneg_of P hVge hb
  have hl : ∀ y : P.PT, 0 ≤ P.lam y := fun y => hnu _ _ (mem_grp_of_part P y)
  have hhit : ∀ z, ∑ y : P.PT, (if P.IsHit z y then P.lam y else 0) ≤ 2 * P.K := by
    intro z
    refine (sum_hit_lam_le P z hnu).trans ?_
    calc ∑ i, ∑ p ∈ P.grp i, P.nu i p ≤ ∑ _i : Fin P.K, (2 : ℝ) :=
          sum_le_sum fun i _ => sum_nu_le_two P hVge hb i
      _ = 2 * P.K := by simp [mul_comm]
  obtain ⟨hX, -⟩ := ghost_params_ok P j hVle'
  have hη := etav_mem P j
  set τ := D⁻¹ with hτdef
  have hτ1 : 1 ≤ τ := by rw [hτdef]; exact one_le_inv₀ hD0 |>.2 hD1
  have hτ0 : 0 ≤ τ := by linarith
  -- forced slots ≤ tilt
  have hforce : ∀ c ∈ P.ghostChoices,
      (∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧ (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ)
        else 0)) ≤ D ^ Cs.card * τ ^ nV P V c.2 := by
    intro c hc
    have hb2 : P.memSize c.2 ≤ P.B := memSize_le_of_mem P ((mem_ghostChoices_iff' P c).1 hc).2
    have h := forced_ghost_le P c.2 hb2 V Cs hτ1
    have hDτ : D ^ Cs.card * τ ^ Cs.card = 1 := by
      rw [← mul_pow, hτdef, mul_inv_cancel₀ hD0.ne', one_pow]
    calc (∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧ (ghostBirth P c.2 q).getD 0 ∈ V then
          (1 : ℝ) else 0)) =
        D ^ Cs.card * ((∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧
          (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ) else 0)) * τ ^ Cs.card) := by
          rw [mul_comm _ (τ ^ Cs.card), ← mul_assoc, hDτ, one_mul]
      _ ≤ D ^ Cs.card * τ ^ nV P V c.2 := mul_le_mul_of_nonneg_left h (by positivity)
  have hprod0 : ∀ c : P.Mem × P.Mem, 0 ≤ ∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧
      (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ) else 0) :=
    fun c => prod_nonneg fun q _ => by split_ifs <;> norm_num
  calc ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ * (if P.ghostOut s c ∈ P.stSet then 1 else 0) *
        (∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧ (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ)
          else 0)) * (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 ≤
      ∑ c ∈ P.ghostChoices, D ^ Cs.card * (‖P.ghostCoeff j s c‖ *
        (if P.ghostOut s c ∈ P.stSet then (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 else 0) *
          τ ^ nV P V c.2) := by
        refine sum_le_sum fun c hc => ?_
        have h := hforce c hc
        have hn := norm_nonneg (P.ghostCoeff j s c)
        split_ifs with hout
        · calc ‖P.ghostCoeff j s c‖ * 1 * (∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧
                (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ) else 0)) *
                (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 ≤
              ‖P.ghostCoeff j s c‖ * 1 * (D ^ Cs.card * τ ^ nV P V c.2) *
                (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 := by
                gcongr
            _ = _ := by ring
        · simp only [mul_zero, zero_mul]
          positivity
    _ = D ^ Cs.card * ∑ c ∈ P.ghostChoices, ‖P.ghostCoeff j s c‖ *
        (if P.ghostOut s c ∈ P.stSet then (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 else 0) *
          τ ^ nV P V c.2 := by rw [mul_sum]
    _ ≤ D ^ Cs.card * ((∏ y, if P.IsHit s.1 y then
          exp (12 * tiltOf P V τ y * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) *
          12 ^ P.memSize s.2.2) :=
        mul_le_mul_of_nonneg_left (ghost_row_tilt P j s (by norm_num) hτ0 hV hl hX V)
          (by positivity)
    _ ≤ D ^ Cs.card * (exp (36 * P.K + 1) * 12 ^ P.memSize s.2.2) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity))
          (by positivity)
        have e : ∏ y : P.PT, (if P.IsHit s.1 y then
            exp (12 * tiltOf P V τ y * (P.etav j * P.Vg y.1.1 / memRho * P.lam y)) else 1) =
            exp (∑ y : P.PT, if P.IsHit s.1 y then
              12 * tiltOf P V τ y * (P.etav j * P.Vg y.1.1 / memRho * P.lam y) else 0) := by
          rw [Real.exp_sum]; refine prod_congr rfl fun y _ => ?_
          split_ifs <;> simp
        rw [e]
        refine exp_le_exp.2 ?_
        have hW : ∀ y : P.PT, P.etav j * P.Vg y.1.1 / memRho * P.lam y ≤ 3 / 2 * P.lam y := by
          intro y
          have hly := hl y
          have h1 : P.etav j * P.Vg y.1.1 / memRho ≤ 3 / 2 := by
            unfold memRho
            rw [div_le_iff₀ (by norm_num)]
            have : P.etav j ≤ 3 / 4 := by
              unfold MemParams.etav MemParams.qv; split_ifs <;> norm_num
            nlinarith [hVle' y.1.1, hV y.1.1, hη.1]
          nlinarith
        have hW0 : ∀ y : P.PT, 0 ≤ P.etav j * P.Vg y.1.1 / memRho * P.lam y := by
          intro y; have := hl y; have := hV y.1.1; have := hη.1; have := memRho_pos
          positivity
        calc ∑ y : P.PT, (if P.IsHit s.1 y then
              12 * tiltOf P V τ y * (P.etav j * P.Vg y.1.1 / memRho * P.lam y) else 0) ≤
            ∑ y : P.PT, (18 * (if P.IsHit s.1 y then P.lam y else 0) +
              18 * τ * (if P.IsHit s.1 y ∧ y.1.2.1 ∈ V then P.lam y else 0)) := by
              refine sum_le_sum fun y _ => ?_
              have hWy := hW y
              have hW0y := hW0 y
              have hly := hl y
              unfold tiltOf
              by_cases hh : P.IsHit s.1 y
              · by_cases hv : y.1.2.1 ∈ V
                · simp only [hh, hv, and_self, if_true]
                  nlinarith
                · simp only [hh, hv, and_false, if_true, if_false]
                  nlinarith
              · simp only [hh, false_and, if_false]; nlinarith
          _ = 18 * ∑ y : P.PT, (if P.IsHit s.1 y then P.lam y else 0) +
              18 * τ * ∑ y : P.PT, (if P.IsHit s.1 y ∧ y.1.2.1 ∈ V then P.lam y else 0) := by
              rw [sum_add_distrib, mul_sum, mul_sum]
          _ ≤ 18 * (2 * P.K) + τ * D := by
              have h1 := hhit s.1
              have h2 := sum_hit_lam_filter_le P s.1 hnu V
              nlinarith
          _ = 36 * P.K + 1 := by rw [hτdef, inv_mul_cancel₀ hD0.ne']; ring
    _ = exp (36 * P.K + 1) * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by ring

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: statement forms proposed for publication (round 4b)

`DistinctnessStmtNG`: D7e without the ghost hypothesis of `DistinctnessStmt` (its proof does not use
it). With it, D7 needs no ghost cut (`moment_bound_of_pub_cuts`, `L102D_PubMain`). -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

/-- The cut `opBound_ghost_of_norm_le_ghostCoeff` as a proposition. -/
def GhostDomStmt : Prop :=
  ∀ (P : MemParams) (j : ℕ), (∀ i, P.Vg i ≤ 3 / 2) → (∀ i, (1 : ℝ) / 2 ≤ P.Vg i) →
    (∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p) →
    ∀ (cf : P.MState → P.Mem × P.Mem → ℂ), (∀ s c, ‖cf s c‖ ≤ ‖P.ghostCoeff j s c‖) →
    P.OpBound (fun f s => ∑ c ∈ P.ghostChoices,
      cf s c * (if P.ghostOut s c ∈ P.stSet then f (P.ghostOut s c) else 0))
      (Real.exp (30 * P.K))

/-- The cut `opBound_edge_of_norm_le_edgeCoeff` as a proposition. -/
def EdgeDomStmt : Prop :=
  ∀ (P : MemParams) (ω : ℝ × ℝ × ℝ), P.RootIn ω → 0 < P.U → 0 < P.Y → ∀ (j : ℕ),
    (∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) → (∀ i, 1 / 2 ≤ P.Vg i) → (∀ i, P.Vg i ≤ 3 / 2) →
    (∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2) →
    ∀ (cf : P.MState → Finset (Fin P.K) × (ℤ × ℤ) × (Fin P.K → ℕ × Bool) → ℂ),
    (∀ s c, ‖cf s c‖ ≤ ‖P.edgeCoeff ω j s c‖) →
    P.OpBound (fun f s => ∑ c ∈ P.edgeChoices,
      cf s c * (if P.edgeOut s c ∈ P.stSet then f (P.edgeOut s c) else 0))
      (√(2 ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
          (2 + 2 * P.B) ^ P.K) *
        √(3 ^ P.K * (2 ^ P.K * (16 * (1 + (10 * P.Y + 1) *
          (volume (majorArcs P.x P.A₀ P.Y)).toReal)) * (2 + 2 * P.B) ^ P.K)))

set_option maxRecDepth 100000 in
/-- The cut `sum_norm_edgeCoeff_mul_pow_le` as a proposition. -/
def EdgeRowStmt : Prop :=
  ∀ (P : MemParams) (ω : ℝ × ℝ × ℝ), P.RootIn ω → 0 < P.U → 0 < P.Y → ∀ (j : ℕ),
    (∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) → (∀ i, 1 / 2 ≤ P.Vg i) →
    ∀ (C : Finset (Fin P.K)) (Vs : Finset ℕ) {v₀ : ℝ}, 1 ≤ v₀ → ∀ (s : P.MState), s ∈ P.stSet →
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
      (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ Vs then 1 else 0) *
        v₀ ^ P.memSize (P.edgeOutMem s c) ≤
    (1 + v₀) ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
      (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ Vs), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * v₀ ^ P.memSize s.2.2

/-- D7e without the ghost hypothesis (which the proof does not use): the form proposed for
publication. -/
def DistinctnessStmtNG (δ c₁ c₂ : ℝ) : Prop :=
  ∀ G : ℝ, 0 < G → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
    ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
    (∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G))) →
    ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
      c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
        let P := dyadParams x a A₀ Y Hm Hn k
        ∀ ω, P.RootIn ω → ‖P.memMomentD ω‖ ≤ log x ^ (-((G - 1) * P.N))

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the distinctness chain, small ranks (for D7e)

* `memMomentD_eq_forests`: `memMomentD = ∑_F TF F` (born-set chain → record chain → forest
  expansion of the validity check).
* `TF_phase`: each forest term through phases is a plain chain of ops with multipliers of modulus
  `≤ 1` (`rchain_push`, `rchain_drop`).
* `norm_mchain_le`: such a chain is `≤ ‖b‖² e^{30K(N+1)} ∏_j β_j`, the edge blocks `S E_j S` having
  norm `β_j`: the hypothesis bound when the forest does not touch `E_j` (the multiplier is then `1`
  on all fresh labels, by disjointness of the groups), the crude bound otherwise. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory
open scoped ComplexConjugate

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The empty record. -/
def rec0 : Rec (DSlot P) := fun _ _ => none

/-- A dummy start state. -/
def dummyS : P.MState := ((1, 0), fun _ _ => 0, fun _ => 0)

/-- Forests of the chain. -/
abbrev FT := Fin (4 * P.N + 2) × DSlot P → Option (Fin (4 * P.N + 2) × DSlot P)

open Classical in
/-- The forest term. -/
noncomputable def TF (ω : ℝ × ℝ × ℝ) (F : FT P) : ℂ :=
  rchain (fun _ _ _ => (1 : ℂ)) 0 (fullL P ω)
    (fun s rc => P.bVec s * ((if WithinOK (qBound P) rc (4 * P.N + 2) then 1 else 0) *
      ∏ b, gF rc b (F b))) (dummyS P) (rec0 P)

open Classical in
/-- **The forest expansion of the distinct moment.** -/
theorem memMomentD_eq_forests (ω : ℝ × ℝ × ℝ) :
    P.memMomentD ω = ∑ F ∈ (forests (4 * P.N + 2) : Finset (FT P)), TF P ω F := by
  rw [memMomentD_eq_bschain P ω (dummyS P)]
  have h0 := bschain_eq_rchain (R := ℂ) (qBound P) (fullL P ω) 0 P.bVec (dummyS P) (rec0 P)
  have hv : ValidBelow (qBound P) (rec0 P) 0 :=
    ⟨fun k hk => absurd hk (Nat.not_lt_zero _), fun k hk => absurd hk (Nat.not_lt_zero _),
      fun k k' _ hk' => absurd hk' (Nat.not_lt_zero _)⟩
  have hvb : valsBelow (rec0 P) 0 = ∅ := by unfold valsBelow; simp
  rw [if_pos hv, one_mul, hvb, zero_add, length_fullL] at h0
  rw [h0]
  unfold TF
  rw [← rchain_sum]
  refine rchain_congr _ 0 _ _ _ _ (fun s rc _ => ?_) _
  rw [validBelow_ind, prod_forest, mul_sum, mul_sum]

/-! ## Phases -/

/-- The per-op multiplier of the phase expansion. -/
noncomputable def mF (F : FT P) (t : Fin (4 * P.N + 2) × DSlot P → ℕ) (k : ℕ)
    (v : DSlot P → Option ℕ) : ℂ :=
  wk (qBound P) v * phM (qBound P) (4 * P.N + 2) F t k v

lemma norm_mF_le (F : FT P) (t : Fin (4 * P.N + 2) × DSlot P → ℕ) (k : ℕ)
    (v : DSlot P → Option ℕ) : ‖mF P F t k v‖ ≤ 1 := by
  unfold mF; rw [norm_mul]
  exact mul_le_one₀ (norm_wk_le _ _) (norm_nonneg _) (norm_phM_le _ _ _ _ _ _)

lemma qBound_pos : 0 < qBound P := by unfold qBound; omega

/-- **A forest term through phases.** -/
lemma TF_phase (ω : ℝ × ℝ × ℝ) (F : FT P) :
    TF P ω F = (-(qBound P : ℂ)⁻¹) ^ frank F * ∑ t ∈ phRange (qBound P) F,
      mchain (fun k v => 1 * mF P F t k v) 0 (fullL P ω) P.bVec (dummyS P) := by
  classical
  unfold TF
  have e : ∀ s (rc : Rec (DSlot P)), P.bVec s * ((if WithinOK (qBound P) rc (4 * P.N + 2) then
      (1 : ℂ) else 0) * ∏ b, gF rc b (F b)) = (-(qBound P : ℂ)⁻¹) ^ frank F *
      ∑ t ∈ phRange (qBound P) F, P.bVec s * ∏ k ∈ range (4 * P.N + 2), mF P F t k (rc k) := by
    intro s rc
    rw [forest_term_chain (qBound P) (qBound_pos P) F rc]
    simp only [mul_sum]
    refine sum_congr rfl fun t _ => ?_
    unfold mF; ring
  rw [rchain_congr _ 0 _ _ (fun s rc => (-(qBound P : ℂ)⁻¹) ^ frank F *
    ∑ t ∈ phRange (qBound P) F, P.bVec s * ∏ k ∈ range (4 * P.N + 2), mF P F t k (rc k)) _
    (fun s rc _ => e s rc) _]
  rw [rchain_smul, rchain_sum]
  congr 1
  refine sum_congr rfl fun t _ => ?_
  have hp := rchain_push (fun _ _ _ => (1 : ℂ)) (fun k _ v => mF P F t k v)
    (fun _ _ _ _ _ => rfl) (fullL P ω) 0 (fun s _ => P.bVec s) (dummyS P) (rec0 P)
  simp only [zero_add, length_fullL] at hp
  rw [hp]
  exact rchain_drop (fun k v => 1 * mF P F t k v) (fullL P ω) 0 P.bVec (dummyS P) (rec0 P)

/-! ## Ops as operators -/

/-- One op as an operator, with a multiplier on its births. -/
noncomputable def opB (o : BOp ℂ P.MState (DSlot P)) (μ : (DSlot P → Option ℕ) → ℂ)
    (g : P.MState → ℂ) : P.MState → ℂ :=
  fun s => ∑ c ∈ o.ch, o.coeff s c * μ (o.birth s c) * g (o.out s c)

lemma mchain_cons' (m : ℕ → (DSlot P → Option ℕ) → ℂ) (k : ℕ) (o : BOp ℂ P.MState (DSlot P))
    (os : List (BOp ℂ P.MState (DSlot P))) (f : P.MState → ℂ) :
    mchain m k (o :: os) f = opB P o (m k) (mchain m (k + 1) os f) := rfl

lemma wNorm_smul (c : ℂ) (f : P.MState → ℂ) :
    P.wNorm (fun s => c * f s) = ‖c‖ * P.wNorm f := by
  unfold MemParams.wNorm
  rw [show (∑ s ∈ P.stSet, P.stWeight s * ‖c * f s‖ ^ 2) =
      ‖c‖ ^ 2 * ∑ s ∈ P.stSet, P.stWeight s * ‖f s‖ ^ 2 by
    rw [mul_sum]; refine sum_congr rfl fun s _ => by rw [norm_mul]; ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]

lemma opB_sym (μ : (DSlot P → Option ℕ) → ℂ) (g : P.MState → ℂ) :
    opB P (symBOp P) μ g = fun s => μ (fun _ => none) * P.symM g s := by
  funext s
  unfold opB MemParams.symM MemParams.listSym
  simp only [symBOp]
  simp only [mul_sum]
  refine sum_congr rfl fun pr _ => by ring

lemma opB_ghost (j : ℕ) (μ : (DSlot P → Option ℕ) → ℂ) (g : P.MState → ℂ) :
    opB P (ghostBOp P j) μ g = choiceOp P.stSet P.ghostChoices
      (fun s c => P.ghostCoeff j s c * μ (ghostBirth P c.2)) P.ghostOut g := by
  funext s
  unfold opB choiceOp
  refine sum_congr rfl fun c _ => ?_
  show P.ghostCoeff j s c * (if P.ghostOut s c ∈ P.stSet then 1 else 0) *
    μ (ghostBirth P c.2) * g (P.ghostOut s c) = _
  split_ifs <;> ring

lemma opB_edge (ω : ℝ × ℝ × ℝ) (j : ℕ) (μ : (DSlot P → Option ℕ) → ℂ) (g : P.MState → ℂ) :
    opB P (edgeBOp P ω j) μ g = choiceOp P.stSet P.edgeChoices
      (fun s c => P.edgeCoeff ω j s c * μ (edgeBirth P c.2.2)) P.edgeOut g := by
  funext s
  unfold opB choiceOp
  refine sum_congr rfl fun c _ => ?_
  show P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then 1 else 0) *
    μ (edgeBirth P c.2.2) * g (P.edgeOut s c) = _
  split_ifs <;> ring

lemma edgeOrd_smul (ω : ℝ × ℝ × ℝ) (j : ℕ) (c : ℂ) (f : P.MState → ℂ) :
    P.edgeOrd ω j (fun s => c * f s) = fun s => c * P.edgeOrd ω j f s := by
  funext s
  unfold MemParams.edgeOrd
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

lemma symM_smul (c : ℂ) (f : P.MState → ℂ) :
    P.symM (fun s => c * f s) = fun s => c * P.symM f s := by
  funext s
  unfold MemParams.symM MemParams.listSym
  simp only [mul_sum]
  refine sum_congr rfl fun pr _ => by ring

/-- An untouched edge block is the edge itself (up to the constant multipliers of the `S`). -/
lemma block_eq (ω : ℝ × ℝ × ℝ) (j : ℕ) (μ1 μE μ3 : (DSlot P → Option ℕ) → ℂ)
    (hE : ∀ c ∈ P.edgeChoices, μE (edgeBirth P c.2.2) = 1) (g : P.MState → ℂ) :
    opB P (symBOp P) μ1 (opB P (edgeBOp P ω j) μE (opB P (symBOp P) μ3 g)) =
      fun s => (μ1 (fun _ => none) * μ3 (fun _ => none)) * P.edgeOp ω j g s := by
  have h1 : opB P (edgeBOp P ω j) μE = P.edgeOrd ω j := by
    funext h s
    unfold opB MemParams.edgeOrd
    refine sum_congr rfl fun c hc => ?_
    show P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then 1 else 0) *
      μE (edgeBirth P c.2.2) * h (P.edgeOut s c) = _
    rw [hE c hc]; split_ifs <;> ring
  rw [h1, opB_sym, opB_sym, edgeOrd_smul, symM_smul]
  funext s
  unfold MemParams.edgeOp
  ring

section Bounds

variable (hVle : ∀ i, P.Vg i ≤ 3 / 2) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)

include hVle hVge hb

omit hVle in
lemma stWeight_nonneg' : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s :=
  fun s hs => L102G.stWeight_nonneg P (nu_nonneg_of P hVge hb) s hs

lemma opB_ghost_bound (hGd : GhostDomStmt) (j : ℕ) (μ : (DSlot P → Option ℕ) → ℂ)
    (hμ : ∀ v, ‖μ v‖ ≤ 1) (g : P.MState → ℂ) :
    P.wNorm (opB P (ghostBOp P j) μ g) ≤ exp (30 * P.K) * P.wNorm g := by
  rw [opB_ghost]
  refine hGd P j hVle hVge hb _ (fun s c => ?_) g
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (hμ _)

lemma block_bound_touched (hEd : EdgeDomStmt) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (hY : 0 < P.Y)
    (j : ℕ) (μ1 μE μ3 : (DSlot P → Option ℕ) → ℂ) (h1 : ‖μ1 (fun _ => none)‖ ≤ 1)
    (hE : ∀ v, ‖μE v‖ ≤ 1) (h3 : ‖μ3 (fun _ => none)‖ ≤ 1) (g : P.MState → ℂ) :
    P.wNorm (opB P (symBOp P) μ1 (opB P (edgeBOp P ω j) μE (opB P (symBOp P) μ3 g))) ≤
      (√(edgeR P) * √(3 ^ P.K * edgeR P)) * P.wNorm g := by
  have hμ := stWeight_nonneg' P hVge hb
  have hnu := nu_nonneg_of P hVge hb
  have hME : 0 ≤ √(edgeR P) * √(3 ^ P.K * edgeR P) := by positivity
  rw [opB_sym]
  rw [wNorm_smul]
  refine (mul_le_of_le_one_left (by unfold MemParams.wNorm; positivity) h1).trans ?_
  refine (L102G.wNorm_symM_le P hμ _).trans ?_
  rw [opB_edge]
  refine (hEd P ω hω hU hY j hnu hVge hVle (sum_nu_le_two P hVge hb) _
    (fun s c => ?_) _).trans ?_
  · rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (hE _)
  · refine mul_le_mul_of_nonneg_left ?_ hME
    rw [opB_sym, wNorm_smul]
    refine (mul_le_of_le_one_left (by unfold MemParams.wNorm; positivity) h3).trans ?_
    exact L102G.wNorm_symM_le P hμ _

omit hVle hVge hb in
lemma block_bound_untouched (ω : ℝ × ℝ × ℝ) (j : ℕ) {e : ℝ}
    (hEB : P.OpBound (P.edgeOp ω j) e) (μ1 μE μ3 : (DSlot P → Option ℕ) → ℂ)
    (h1 : ‖μ1 (fun _ => none)‖ ≤ 1) (h3 : ‖μ3 (fun _ => none)‖ ≤ 1)
    (hE : ∀ c ∈ P.edgeChoices, μE (edgeBirth P c.2.2) = 1) (g : P.MState → ℂ) :
    P.wNorm (opB P (symBOp P) μ1 (opB P (edgeBOp P ω j) μE (opB P (symBOp P) μ3 g))) ≤
      e * P.wNorm g := by
  rw [block_eq P ω j μ1 μE μ3 hE g, wNorm_smul, norm_mul]
  have hw : 0 ≤ P.wNorm (P.edgeOp ω j g) := by unfold MemParams.wNorm; positivity
  calc ‖μ1 (fun _ => none)‖ * ‖μ3 (fun _ => none)‖ * P.wNorm (P.edgeOp ω j g) ≤
      1 * P.wNorm (P.edgeOp ω j g) :=
        mul_le_mul_of_nonneg_right (mul_le_one₀ h1 (norm_nonneg _) h3) hw
    _ ≤ e * P.wNorm g := by rw [one_mul]; exact hEB g

omit hVle hVge hb in
lemma tailL_succ (ω : ℝ × ℝ × ℝ) (i : ℕ) :
    tailL P ω (i + 1) = ghostBOp P (P.N - (i + 1)) :: symBOp P :: edgeBOp P ω (P.N - (i + 1)) ::
      symBOp P :: tailL P ω i := rfl

/-- **The tail of a chain with multipliers of modulus `≤ 1`**, block by block. -/
theorem wNorm_tail (hGd : GhostDomStmt) (ω : ℝ × ℝ × ℝ) (m : ℕ → (DSlot P → Option ℕ) → ℂ)
    (hm : ∀ k v, ‖m k v‖ ≤ 1) (β : ℕ → ℝ) (hβ : ∀ j, 0 ≤ β j)
    (hblock : ∀ j < P.N, ∀ g, P.wNorm (opB P (symBOp P) (m (4 * j + 2))
      (opB P (edgeBOp P ω j) (m (4 * j + 3)) (opB P (symBOp P) (m (4 * j + 4)) g))) ≤
        β j * P.wNorm g) :
    ∀ i, i ≤ P.N → ∀ f, P.wNorm (mchain m (4 * (P.N - i) + 1) (tailL P ω i) f) ≤
      exp (30 * P.K) ^ (i + 1) * (∏ j ∈ Ico (P.N - i) P.N, β j) * P.wNorm f := by
  intro i
  induction i with
  | zero =>
    intro _ f
    simp only [Nat.sub_zero, Ico_self, prod_empty, mul_one, zero_add, pow_one]
    show P.wNorm (opB P (ghostBOp P P.N) (m (4 * P.N + 1)) f) ≤ _
    exact opB_ghost_bound P hVle hVge hb hGd _ _ (hm _) f
  | succ i ih =>
    intro hi f
    set j := P.N - (i + 1) with hj
    have hk : 4 * (P.N - (i + 1)) + 1 + 1 + 1 + 1 + 1 = 4 * (P.N - i) + 1 := by omega
    rw [tailL_succ, mchain_cons', mchain_cons', mchain_cons', mchain_cons', hk]
    have h2 : 4 * j + 1 + 1 = 4 * j + 2 := by ring
    have h3 : 4 * j + 1 + 1 + 1 = 4 * j + 3 := by ring
    have h4 : 4 * j + 1 + 1 + 1 + 1 = 4 * j + 4 := by ring
    rw [h2, h3, h4]
    have hjN : j < P.N := by omega
    have hrest := ih (by omega) f
    have hIco : Ico (P.N - (i + 1)) P.N = insert j (Ico (P.N - i) P.N) := by
      rw [hj]
      ext x; simp only [mem_Ico, mem_insert]; omega
    have hnot : j ∉ Ico (P.N - i) P.N := by simp only [mem_Ico]; omega
    rw [hIco, prod_insert hnot]
    have hP : 0 ≤ ∏ j ∈ Ico (P.N - i) P.N, β j := prod_nonneg fun _ _ => hβ _
    calc P.wNorm (opB P (ghostBOp P j) (m (4 * j + 1)) (opB P (symBOp P) (m (4 * j + 2))
          (opB P (edgeBOp P ω j) (m (4 * j + 3)) (opB P (symBOp P) (m (4 * j + 4))
            (mchain m (4 * (P.N - i) + 1) (tailL P ω i) f))))) ≤
        exp (30 * P.K) * P.wNorm (opB P (symBOp P) (m (4 * j + 2))
          (opB P (edgeBOp P ω j) (m (4 * j + 3)) (opB P (symBOp P) (m (4 * j + 4))
            (mchain m (4 * (P.N - i) + 1) (tailL P ω i) f)))) :=
          opB_ghost_bound P hVle hVge hb hGd _ _ (hm _) _
      _ ≤ exp (30 * P.K) * (β j * P.wNorm (mchain m (4 * (P.N - i) + 1) (tailL P ω i) f)) :=
          mul_le_mul_of_nonneg_left (hblock j hjN _) (exp_pos _).le
      _ ≤ exp (30 * P.K) * (β j * (exp (30 * P.K) ^ (i + 1) *
          (∏ j ∈ Ico (P.N - i) P.N, β j) * P.wNorm f)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrest (hβ j)) (exp_pos _).le
      _ = exp (30 * P.K) ^ (i + 1 + 1) * (β j * ∏ j ∈ Ico (P.N - i) P.N, β j) * P.wNorm f := by
          ring

end Bounds

/-! ## The first op and the small-rank bound -/

lemma norm_mchain_full (ω : ℝ × ℝ × ℝ) (m : ℕ → (DSlot P → Option ℕ) → ℂ)
    (hm : ∀ v, ‖m 0 v‖ ≤ 1) (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s) (f : P.MState → ℂ) :
    ‖mchain m 0 (fullL P ω) f (dummyS P)‖ ≤
      P.wNorm P.bVec * P.wNorm (mchain m 1 (tailL P ω P.N) f) := by
  set T := mchain m 1 (tailL P ω P.N) f
  show ‖∑ s ∈ P.stSet, ((P.stWeight s : ℂ) * P.bVec s) * m 0 (initBirth P s.2.1) * T s‖ ≤ _
  refine (norm_sum_le _ _).trans ?_
  calc ∑ s ∈ P.stSet, ‖((P.stWeight s : ℂ) * P.bVec s) * m 0 (initBirth P s.2.1) * T s‖ ≤
      ∑ s ∈ P.stSet, (√(P.stWeight s) * ‖P.bVec s‖) * (√(P.stWeight s) * ‖T s‖) := by
        refine sum_le_sum fun s hs => ?_
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ s hs)]
        have h1 := hm (initBirth P s.2.1)
        have e : √(P.stWeight s) * ‖P.bVec s‖ * (√(P.stWeight s) * ‖T s‖) =
            P.stWeight s * ‖P.bVec s‖ * ‖T s‖ := by
          rw [show √(P.stWeight s) * ‖P.bVec s‖ * (√(P.stWeight s) * ‖T s‖) =
            (√(P.stWeight s) * √(P.stWeight s)) * ‖P.bVec s‖ * ‖T s‖ by ring,
            Real.mul_self_sqrt (hμ s hs)]
        rw [e]
        have h0 : 0 ≤ P.stWeight s * ‖P.bVec s‖ := mul_nonneg (hμ s hs) (norm_nonneg _)
        calc P.stWeight s * ‖P.bVec s‖ * ‖m 0 (initBirth P s.2.1)‖ * ‖T s‖ ≤
            P.stWeight s * ‖P.bVec s‖ * 1 * ‖T s‖ := by gcongr
          _ = _ := by ring
    _ ≤ √(∑ s ∈ P.stSet, (√(P.stWeight s) * ‖P.bVec s‖) ^ 2) *
        √(∑ s ∈ P.stSet, (√(P.stWeight s) * ‖T s‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = P.wNorm P.bVec * P.wNorm T := by
        unfold MemParams.wNorm
        congr 2
        · refine sum_congr rfl fun s hs => ?_
          rw [mul_pow, Real.sq_sqrt (hμ s hs)]
        · refine sum_congr rfl fun s hs => ?_
          rw [mul_pow, Real.sq_sqrt (hμ s hs)]

lemma wk_edgeBirth (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i'))
    (tg : Fin P.K → ℕ × Bool) (htg : tg ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ) :
    wk (qBound P) (edgeBirth P tg) = 1 := by
  have hmem : ∀ i, (tg i).1 ∈ P.grp i := fun i =>
    (mem_product.1 (Fintype.mem_piFinset.1 htg i)).1
  unfold wk
  rw [if_pos]
  constructor
  · intro q q' hq hqq'
    unfold edgeBirth at hq hqq'
    by_cases h1 : q.2.val = 0 ∧ (tg q.1).2 = false
    · rw [if_pos h1] at hqq'
      by_cases h2 : q'.2.val = 0 ∧ (tg q'.1).2 = false
      · rw [if_pos h2, Option.some.injEq] at hqq'
        have hi : q.1 = q'.1 := by
          by_contra hne
          have hd := hdisj _ _ hne
          exact Finset.disjoint_left.1 hd (hmem q.1) (hqq' ▸ hmem q'.1)
        exact Prod.ext hi (Fin.ext (by rw [h1.1, h2.1]))
      · rw [if_neg h2] at hqq'; exact absurd hqq' (by simp)
    · rw [if_neg h1] at hq; exact absurd rfl hq
  · intro q p hq
    unfold edgeBirth at hq
    split_ifs at hq with h
    rw [Option.some.injEq] at hq
    rw [← hq]
    refine lt_qBound P ?_
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨q.1, hmem q.1⟩

/-- An op index touched by the forest. -/
def Touched {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ) : Prop :=
  ∃ b ∈ fdom F, (b.1 : ℕ) = k ∨ ((ftgt F b).1 : ℕ) = k

open Classical in
lemma card_touched_le {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (N : ℕ) :
    ((range N).filter fun j => Touched P F (4 * j + 3)).card ≤ 2 * frank F := by
  have hsub : (range N).filter (fun j => Touched P F (4 * j + 3)) ⊆
      (fdom F).image (fun b => ((b.1 : ℕ) - 3) / 4) ∪
        (fdom F).image (fun b => (((ftgt F b).1 : ℕ) - 3) / 4) := by
    intro j hj
    obtain ⟨b, hb, h⟩ := (mem_filter.1 hj).2
    rcases h with h | h
    · exact mem_union_left _ (mem_image.2 ⟨b, hb, by rw [h]; omega⟩)
    · exact mem_union_right _ (mem_image.2 ⟨b, hb, by rw [h]; omega⟩)
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 := card_image_le (s := fdom F) (f := fun b => ((b.1 : ℕ) - 3) / 4)
  have h2 := card_image_le (s := fdom F) (f := fun b => (((ftgt F b).1 : ℕ) - 3) / 4)
  have h3 : (fdom F).card = frank F := rfl
  omega

open Classical in
lemma prod_beta_le (N r : ℕ) (T : ℕ → Prop) (hT : ((range N).filter T).card ≤ r) {e ME : ℝ}
    (he : 0 < e) (heME : e ≤ ME) :
    ∏ j ∈ range N, (if T j then ME else e) ≤ e ^ N * (ME / e) ^ r := by
  have h1 : 1 ≤ ME / e := by rw [le_div_iff₀ he]; linarith
  have e1 : ∏ j ∈ range N, (if T j then ME else e) =
      e ^ N * ∏ j ∈ range N, (if T j then ME / e else 1) := by
    rw [show e ^ N = ∏ _j ∈ range N, e by rw [prod_const, card_range], ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    split_ifs
    · field_simp
    · ring
  rw [e1, prod_ite, prod_const_one, mul_one, prod_const]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 hT) (by positivity)

section Small

variable (hVle : ∀ i, P.Vg i ≤ 3 / 2) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)

include hVle hVge hb

open Classical in
/-- **The small-rank bound** for one forest term. -/
theorem TF_small (hGd : GhostDomStmt) (hEd : EdgeDomStmt) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {e : ℝ} (he : 0 < e)
    (heME : e ≤ √(edgeR P) * √(3 ^ P.K * edgeR P))
    (hEB : ∀ j < P.N, P.OpBound (P.edgeOp ω j) e) (F : FT P) :
    ‖TF P ω F‖ ≤ P.wNorm P.bVec ^ 2 * exp (30 * P.K) ^ (P.N + 1) * e ^ P.N *
      ((√(edgeR P) * √(3 ^ P.K * edgeR P)) / e) ^ (2 * frank F) := by
  set ME := √(edgeR P) * √(3 ^ P.K * edgeR P)
  have hμ := stWeight_nonneg' P hVge hb
  set β : ℕ → ℝ := fun j => if Touched P F (4 * j + 3) then ME else e with hβdef
  have hβ0 : ∀ j, 0 ≤ β j := fun j => by
    simp only [hβdef]; split_ifs
    · exact he.le.trans heME
    · exact he.le
  set Bnd := P.wNorm P.bVec ^ 2 * exp (30 * P.K) ^ (P.N + 1) * e ^ P.N *
    (ME / e) ^ (2 * frank F) with hBnd
  -- one phase
  have hone : ∀ t, ‖mchain (fun k v => 1 * mF P F t k v) 0 (fullL P ω) P.bVec (dummyS P)‖ ≤
      Bnd := by
    intro t
    set m : ℕ → (DSlot P → Option ℕ) → ℂ := fun k v => 1 * mF P F t k v with hmdef
    have hm : ∀ k v, ‖m k v‖ ≤ 1 := fun k v => by
      simp only [hmdef, one_mul]; exact norm_mF_le P F t k v
    have hblock : ∀ j < P.N, ∀ g, P.wNorm (opB P (symBOp P) (m (4 * j + 2))
        (opB P (edgeBOp P ω j) (m (4 * j + 3)) (opB P (symBOp P) (m (4 * j + 4)) g))) ≤
          β j * P.wNorm g := by
      intro j hj g
      by_cases hT : Touched P F (4 * j + 3)
      · simp only [hβdef, if_pos hT]
        exact block_bound_touched P hVle hVge hb hEd ω hω hU hY j _ _ _ (hm _ _) (hm _) (hm _ _) g
      · simp only [hβdef, if_neg hT]
        refine block_bound_untouched P ω j (hEB j hj) _ _ _ (hm _ _) (hm _ _) (fun c hc => ?_) g
        have htg : c.2.2 ∈ Fintype.piFinset fun i => P.grp i ×ˢ univ :=
          tg_mem_of_mem_edgeChoices P hc
        simp only [hmdef, mF, one_mul]
        rw [wk_edgeBirth P hdisj _ htg, one_mul]
        refine phM_untouched _ _ F t _ (fun b hb => ?_) _
        exact ⟨fun h => hT ⟨b, hb, Or.inl h⟩, fun h => hT ⟨b, hb, Or.inr h⟩⟩
    have htail := wNorm_tail P hVle hVge hb hGd ω m hm β hβ0 hblock P.N le_rfl P.bVec
    simp only [Nat.sub_self, mul_zero, zero_add] at htail
    have hfull := norm_mchain_full P ω m (hm 0) hμ P.bVec
    have hprod : ∏ j ∈ Ico 0 P.N, β j ≤ e ^ P.N * (ME / e) ^ (2 * frank F) := by
      rw [← range_eq_Ico]
      exact prod_beta_le P.N _ _ (card_touched_le P F P.N) he heME
    have hwb : 0 ≤ P.wNorm P.bVec := by unfold MemParams.wNorm; positivity
    calc ‖mchain m 0 (fullL P ω) P.bVec (dummyS P)‖ ≤
        P.wNorm P.bVec * P.wNorm (mchain m 1 (tailL P ω P.N) P.bVec) := hfull
      _ ≤ P.wNorm P.bVec * (exp (30 * P.K) ^ (P.N + 1) * (∏ j ∈ Ico 0 P.N, β j) *
          P.wNorm P.bVec) := mul_le_mul_of_nonneg_left htail hwb
      _ ≤ P.wNorm P.bVec * (exp (30 * P.K) ^ (P.N + 1) * (e ^ P.N * (ME / e) ^ (2 * frank F)) *
          P.wNorm P.bVec) := by gcongr
      _ = Bnd := by rw [hBnd]; ring
  rw [TF_phase, norm_mul, norm_pow, norm_neg, norm_inv, Complex.norm_natCast]
  have hQ : (0 : ℝ) < qBound P := by exact_mod_cast qBound_pos P
  calc ((qBound P : ℝ)⁻¹) ^ frank F * ‖∑ t ∈ phRange (qBound P) F,
        mchain (fun k v => 1 * mF P F t k v) 0 (fullL P ω) P.bVec (dummyS P)‖ ≤
      ((qBound P : ℝ)⁻¹) ^ frank F * ∑ t ∈ phRange (qBound P) F, Bnd :=
        mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (sum_le_sum fun t _ => hone t))
          (by positivity)
    _ = Bnd := by
        rw [sum_const, nsmul_eq_mul, card_phRange, ← mul_assoc, ← mul_pow,
          inv_mul_cancel₀ hQ.ne', one_pow, one_mul]

end Small

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: the distinctness chain, large ranks (for D7e)

Absolute values: a constrained birth `b` of the forest only has to take a value already born at an
earlier op (`norm_forest_term_le`); this indicator is pushed into the op of `b` and the chain is
bounded by weighted row iteration with the weight `12^{memory}`. Every op has rows
`≤ Bmax · D^{#constrained slots}`: ghosts by tilting (`ghost_forced_row`), edges by the crude row with
forced fresh labels (`edge_row`), symmetrizations trivially. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The crude edge row with weight `12^{memory}`. -/
noncomputable def edgeR12 : ℝ :=
  13 ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
    (2 + 2 * P.B) ^ P.K

/-- The uniform row bound. -/
noncomputable def Bmax : ℝ := exp (36 * P.K + 1) * edgeR12 P

lemma one_le_edgeR12 (hY : 0 ≤ P.Y) : 1 ≤ edgeR12 P := by
  unfold edgeR12
  have hε : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  have h1 : (1 : ℝ) ≤ 13 ^ P.K := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    have : 0 ≤ (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ (2 + 2 * P.B) ^ P.K := one_le_pow₀ (by linarith [(Nat.cast_nonneg P.B : (0:ℝ) ≤ P.B)])
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

lemma one_le_Bmax (hY : 0 ≤ P.Y) : 1 ≤ Bmax P := by
  unfold Bmax
  have := one_le_edgeR12 P hY
  have h : (1 : ℝ) ≤ exp (36 * P.K + 1) := one_le_exp (by positivity)
  nlinarith

/-! ## Forced rows of the ops -/

lemma mem_tailL (ω : ℝ × ℝ × ℝ) (i : ℕ) (o : BOp ℂ P.MState (DSlot P)) (ho : o ∈ tailL P ω i) :
    (∃ j, o = ghostBOp P j) ∨ o = symBOp P ∨ (∃ j, o = edgeBOp P ω j) := by
  induction i with
  | zero =>
    simp only [tailL, List.mem_singleton] at ho
    exact Or.inl ⟨_, ho⟩
  | succ i ih =>
    rw [tailL_succ] at ho
    simp only [List.mem_cons] at ho
    rcases ho with h | h | h | h | h
    · exact Or.inl ⟨_, h⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨_, h⟩)
    · exact Or.inr (Or.inl h)
    · exact ih h

lemma norm_mul_ind (a : ℂ) (p : Prop) [Decidable p] :
    ‖a * (if p then (1 : ℂ) else 0)‖ = ‖a‖ * (if p then (1 : ℝ) else 0) := by
  split_ifs <;> simp

set_option maxHeartbeats 1000000 in
/-- The forced edge row. -/
lemma edge_forced_row (hRd : EdgeRowStmt) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) (j : ℕ)
    (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
    (hsum : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2) (s : P.MState) (hs : s ∈ P.stSet)
    (Cs : Finset (DSlot P)) (V : Finset ℕ) {D : ℝ} (hD0 : 0 ≤ D)
    (hDi : ∀ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D) :
    ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then 1 else 0)‖ *
      (∏ q ∈ Cs, (if edgeBirth P c.2.2 q ≠ none ∧ (edgeBirth P c.2.2 q).getD 0 ∈ V then (1 : ℝ)
        else 0)) * (12 : ℝ) ^ P.memSize (P.edgeOut s c).2.2 ≤
    edgeR12 P * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by
  classical
  have hε : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  have hR0 : 0 ≤ edgeR12 P := (zero_le_one).trans (one_le_edgeR12 P hY.le)
  have hm : P.memSize s.2.2 ≤ P.B := by
    have h1 := ((mem_stSet_iff' P s).1 hs).2.2
    unfold MemParams.memSet at h1
    exact (mem_filter.1 h1).2
  by_cases hC : ∀ q ∈ Cs, q.2.val = 0
  · set C := Cs.image Prod.fst with hCdef
    have hcard : C.card = Cs.card := card_image_of_injOn fun q hq q' hq' h =>
      Prod.ext h (Fin.ext (by rw [hC q hq, hC q' hq']))
    have hind : ∀ c : L102G.EC P, (∏ q ∈ Cs, (if edgeBirth P c.2.2 q ≠ none ∧
        (edgeBirth P c.2.2 q).getD 0 ∈ V then (1 : ℝ) else 0)) ≤
        (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ V then 1 else 0) := by
      intro c
      split_ifs with h
      · exact prod_le_one (fun q _ => by split_ifs <;> norm_num) fun q _ => by
          split_ifs <;> norm_num
      · push_neg at h
        obtain ⟨i, hi, hi'⟩ := h
        obtain ⟨q, hq, rfl⟩ := mem_image.1 hi
        refine le_of_eq (prod_eq_zero hq (if_neg fun h' => ?_))
        unfold edgeBirth at h'
        by_cases hf : (c.2.2 q.1).2 = false
        · rw [if_pos ⟨hC q hq, hf⟩] at h'
          exact hi' hf (by simpa using h'.2)
        · rw [if_neg fun h'' => hf h''.2] at h'
          exact h'.1 rfl
    have hrow := hRd P ω hω hU hY j hnu hVge C V (by norm_num : (1 : ℝ) ≤ 12) s hs
    have hprod : ∏ i : Fin P.K, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p
        else ∑ p ∈ P.grp i, P.nu i p + 2 * (P.memSize s.2.2 : ℝ)) ≤
        (2 + 2 * P.B) ^ P.K * D ^ Cs.card := by
      have hX : (1 : ℝ) ≤ 2 + 2 * P.B := by
        have : (0 : ℝ) ≤ P.B := Nat.cast_nonneg _
        linarith
      calc ∏ i : Fin P.K, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p
            else ∑ p ∈ P.grp i, P.nu i p + 2 * (P.memSize s.2.2 : ℝ)) ≤
          ∏ i : Fin P.K, ((2 + 2 * P.B) * (if i ∈ C then D else 1)) := by
            refine prod_le_prod (fun i _ => ?_) fun i _ => ?_
            · split_ifs
              · exact sum_nonneg fun p hp => hnu i p (mem_filter.1 hp).1
              · exact add_nonneg (sum_nonneg fun p hp => hnu i p hp) (by positivity)
            · split_ifs
              · calc ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D := hDi i
                  _ ≤ (2 + 2 * P.B) * D := le_mul_of_one_le_left hD0 hX
              · have : (P.memSize s.2.2 : ℝ) ≤ P.B := by exact_mod_cast hm
                linarith [hsum i]
        _ = (2 + 2 * P.B) ^ P.K * D ^ Cs.card := by
            rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin, prod_ite_mem,
              univ_inter, prod_const, hcard]
    calc ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c * (if P.edgeOut s c ∈ P.stSet then 1 else 0)‖ *
          (∏ q ∈ Cs, (if edgeBirth P c.2.2 q ≠ none ∧ (edgeBirth P c.2.2 q).getD 0 ∈ V then
            (1 : ℝ) else 0)) * (12 : ℝ) ^ P.memSize (P.edgeOut s c).2.2 ≤
        ∑ c ∈ P.edgeChoices, ‖P.edgeCoeff ω j s c‖ *
          (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ V then 1 else 0) *
            (12 : ℝ) ^ P.memSize (P.edgeOutMem s c) := by
          refine sum_le_sum fun c _ => ?_
          rw [norm_mul_ind]
          have h1 : ‖P.edgeCoeff ω j s c‖ * (if P.edgeOut s c ∈ P.stSet then (1 : ℝ) else 0) ≤
              ‖P.edgeCoeff ω j s c‖ := by
            split_ifs <;> simp
          have h2 := hind c
          have h0 : 0 ≤ ∏ q ∈ Cs, (if edgeBirth P c.2.2 q ≠ none ∧
              (edgeBirth P c.2.2 q).getD 0 ∈ V then (1 : ℝ) else 0) :=
            prod_nonneg fun q _ => by split_ifs <;> norm_num
          have h12 : (0 : ℝ) ≤ 12 ^ P.memSize (P.edgeOut s c).2.2 := by positivity
          calc ‖P.edgeCoeff ω j s c‖ * (if P.edgeOut s c ∈ P.stSet then (1 : ℝ) else 0) *
                (∏ q ∈ Cs, (if edgeBirth P c.2.2 q ≠ none ∧ (edgeBirth P c.2.2 q).getD 0 ∈ V then
                  (1 : ℝ) else 0)) * (12 : ℝ) ^ P.memSize (P.edgeOut s c).2.2 ≤
              ‖P.edgeCoeff ω j s c‖ *
                (if ∀ i ∈ C, (c.2.2 i).2 = false ∧ (c.2.2 i).1 ∈ V then 1 else 0) *
                  (12 : ℝ) ^ P.memSize (P.edgeOut s c).2.2 := by
                gcongr
            _ = _ := rfl
      _ ≤ (1 + 12) ^ P.K * (16 * (1 + (10 * P.Y + 1) *
            (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
          (∏ i, (if i ∈ C then ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p
            else ∑ p ∈ P.grp i, P.nu i p + 2 * P.memSize s.2.2)) * 12 ^ P.memSize s.2.2 := hrow
      _ ≤ (1 + 12) ^ P.K * (16 * (1 + (10 * P.Y + 1) *
            (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
          ((2 + 2 * P.B) ^ P.K * D ^ Cs.card) * 12 ^ P.memSize s.2.2 := by
          have : 0 ≤ (1 + 12 : ℝ) ^ P.K * (16 * (1 + (10 * P.Y + 1) *
              (volume (majorArcs P.x P.A₀ P.Y)).toReal)) := by
            have : 0 ≤ 10 * P.Y + 1 := by linarith
            positivity
          gcongr
      _ = edgeR12 P * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by
          unfold edgeR12; norm_num; ring
  · push_neg at hC
    obtain ⟨q, hq, hq0⟩ := hC
    have hz : ∀ c : L102G.EC P, (∏ q ∈ Cs, (if edgeBirth P c.2.2 q ≠ none ∧
        (edgeBirth P c.2.2 q).getD 0 ∈ V then (1 : ℝ) else 0)) = 0 := by
      intro c
      refine prod_eq_zero hq (if_neg fun h => h.1 ?_)
      unfold edgeBirth
      rw [if_neg fun h => hq0 h.1]
    rw [sum_eq_zero fun c _ => by rw [hz c]; ring]
    positivity

/-- The forced row of a symmetrization. -/
lemma sym_forced_row (s : P.MState) (Cs : Finset (DSlot P)) (V : Finset ℕ) {D : ℝ}
    (hD0 : 0 ≤ D) :
    ∑ c ∈ (symBOp P).ch, ‖(symBOp P).coeff s c‖ *
      (∏ q ∈ Cs, (if (symBOp P).birth s c q ≠ none ∧ ((symBOp P).birth s c q).getD 0 ∈ V then
        (1 : ℝ) else 0)) * (12 : ℝ) ^ P.memSize ((symBOp P).out s c).2.2 ≤
    D ^ Cs.card * 12 ^ P.memSize s.2.2 := by
  by_cases hC : Cs = ∅
  · subst hC
    simp only [prod_empty, mul_one, card_empty, pow_zero, one_mul]
    simp only [symBOp]
    rw [sum_const, card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (Fin P.K → Equiv.Perm (Fin (P.J + 1))) : ℝ) =
        (((P.J + 1).factorial ^ P.K : ℕ) : ℝ) := by
      rw [← L102G.card_slotPerm P]
    rw [hcard, norm_inv, Complex.norm_natCast, ← mul_assoc, mul_inv_cancel₀ (by positivity),
      one_mul]
  · obtain ⟨q, hq⟩ := nonempty_iff_ne_empty.2 hC
    rw [sum_eq_zero fun c _ => ?_]
    · positivity
    · rw [prod_eq_zero hq (if_neg fun h => h.1 rfl)]; ring

section Rows

variable (hVle : ∀ i, P.Vg i ≤ 3 / 2) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)

include hVle hVge hb

/-- **Every op of the tail has forced rows `≤ Bmax D^{#forced}`.** -/
lemma tail_forced_row (hRd : EdgeRowStmt) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y)
    (i : ℕ) (o : BOp ℂ P.MState (DSlot P)) (ho : o ∈ tailL P ω i) (s : P.MState)
    (hs : s ∈ P.stSet) (Cs : Finset (DSlot P)) (V : Finset ℕ) {D : ℝ} (hD0 : 0 < D)
    (hD1 : D ≤ 1) (hDV : 18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D) :
    ∑ c ∈ o.ch, ‖o.coeff s c‖ *
      (∏ q ∈ Cs, (if o.birth s c q ≠ none ∧ (o.birth s c q).getD 0 ∈ V then (1 : ℝ) else 0)) *
        (12 : ℝ) ^ P.memSize (o.out s c).2.2 ≤
    Bmax P * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by
  have hnu := nu_nonneg_of P hVge hb
  have hB1 := one_le_Bmax P hY.le
  have hDi : ∀ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D := by
    intro i
    have h1 : ∀ i, 0 ≤ ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p :=
      fun i => sum_nonneg fun p hp => hnu i p (mem_filter.1 hp).1
    have h2 : ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤
        ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p :=
      single_le_sum (fun i _ => h1 i) (mem_univ i)
    linarith
  have hw : (0 : ℝ) ≤ 12 ^ P.memSize s.2.2 := by positivity
  rcases mem_tailL P ω i o ho with ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩
  · -- ghost
    have h := ghost_forced_row P j s hVle hVge hb V Cs hD0 hD1 hDV
    have e : ∀ c ∈ (ghostBOp P j).ch, ‖(ghostBOp P j).coeff s c‖ *
        (∏ q ∈ Cs, (if (ghostBOp P j).birth s c q ≠ none ∧
          ((ghostBOp P j).birth s c q).getD 0 ∈ V then (1 : ℝ) else 0)) *
        (12 : ℝ) ^ P.memSize ((ghostBOp P j).out s c).2.2 =
        ‖P.ghostCoeff j s c‖ * (if P.ghostOut s c ∈ P.stSet then 1 else 0) *
        (∏ q ∈ Cs, (if ghostBirth P c.2 q ≠ none ∧ (ghostBirth P c.2 q).getD 0 ∈ V then (1 : ℝ)
          else 0)) * (12 : ℝ) ^ P.memSize (P.ghostOut s c).2.2 := by
      intro c _
      show ‖P.ghostCoeff j s c * (if P.ghostOut s c ∈ P.stSet then 1 else 0)‖ * _ * _ = _
      rw [norm_mul_ind]
      rfl
    rw [sum_congr rfl e]
    refine h.trans ?_
    have : exp (36 * P.K + 1) ≤ Bmax P := by
      unfold Bmax
      exact le_mul_of_one_le_right (exp_pos _).le (one_le_edgeR12 P hY.le)
    gcongr
  · -- symmetrization
    refine (sym_forced_row P s Cs V hD0.le).trans ?_
    calc D ^ Cs.card * 12 ^ P.memSize s.2.2 = 1 * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by ring
      _ ≤ Bmax P * D ^ Cs.card * 12 ^ P.memSize s.2.2 := by gcongr
  · -- edge
    have h := edge_forced_row P hRd ω hω hU hY j hnu hVge (sum_nu_le_two P hVge hb) s hs Cs V hD0.le hDi
    refine h.trans ?_
    have : edgeR12 P ≤ Bmax P := by
      unfold Bmax
      exact le_mul_of_one_le_left ((zero_le_one).trans (one_le_edgeR12 P hY.le))
        (one_le_exp (by positivity))
    gcongr

end Rows

/-! ## The large-rank bound -/

lemma forests_lt {n : ℕ} {F : Fin n × DSlot P → Option (Fin n × DSlot P)}
    (hF : F ∈ forests n) : ∀ b a, F b = some a → a.1 < b.1 := by
  intro b a h
  have := Fintype.mem_piFinset.1 hF b
  rw [h, mem_insert] at this
  rcases this with h1 | h1
  · exact absurd h1 (by simp)
  · obtain ⟨a', ha', he⟩ := mem_image.1 h1
    rw [Option.some.injEq] at he
    rw [← he]; exact (mem_filter.1 ha').2

/-- The number of forest addresses at op `k`. -/
noncomputable def cnt {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ) : ℕ :=
  ((fdom F).filter fun b => (b.1 : ℕ) = k).card

open Classical in
/-- The forced-birth indicator of op `k`. -/
noncomputable def chi {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ)
    (rc : Rec (DSlot P)) (v : DSlot P → Option ℕ) : ℝ :=
  ∏ b ∈ (fdom F).filter (fun b => (b.1 : ℕ) = k),
    (if v b.2 ≠ none ∧ (v b.2).getD 0 ∈ valsBelow rc k then 1 else 0)

lemma chi_nonneg {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ)
    (rc : Rec (DSlot P)) (v : DSlot P → Option ℕ) : 0 ≤ chi P F k rc v :=
  prod_nonneg fun _ _ => by split_ifs <;> norm_num

lemma chi_le_one {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ)
    (rc : Rec (DSlot P)) (v : DSlot P → Option ℕ) : chi P F k rc v ≤ 1 :=
  prod_le_one (fun _ _ => by split_ifs <;> norm_num) fun _ _ => by split_ifs <;> norm_num

lemma valsBelow_congr (rc rc' : Rec (DSlot P)) (k : ℕ) (h : ∀ k' < k, rc k' = rc' k') :
    valsBelow rc k = valsBelow rc' k := by
  unfold valsBelow
  exact biUnion_congr rfl fun k' hk' => by rw [h k' (mem_range.1 hk')]

lemma chi_local {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) :
    Local (fun k rc v => chi P F k rc v) := by
  intro k rc rc' v h
  show chi P F k rc v = chi P F k rc' v
  unfold chi
  rw [valsBelow_congr P rc rc' k h]

lemma chi_eq_image {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ)
    (rc : Rec (DSlot P)) (v : DSlot P → Option ℕ) :
    chi P F k rc v = ∏ q ∈ ((fdom F).filter (fun b => (b.1 : ℕ) = k)).image Prod.snd,
      (if v q ≠ none ∧ (v q).getD 0 ∈ valsBelow rc k then (1 : ℝ) else 0) := by
  unfold chi
  rw [prod_image]
  intro b hb b' hb' h
  have e1 := (mem_filter.1 hb).2
  have e2 := (mem_filter.1 hb').2
  exact Prod.ext (Fin.ext (by rw [e1, e2])) h

lemma card_image_cnt {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (k : ℕ) :
    (((fdom F).filter (fun b => (b.1 : ℕ) = k)).image Prod.snd).card = cnt P F k := by
  unfold cnt
  refine card_image_of_injOn fun b hb b' hb' h => ?_
  have e1 := (mem_filter.1 hb).2
  have e2 := (mem_filter.1 hb').2
  exact Prod.ext (Fin.ext (by rw [e1, e2])) h

lemma card_valsBelow_le (rc : Rec (DSlot P)) (k : ℕ) :
    (valsBelow rc k).card ≤ k * Fintype.card (DSlot P) := by
  unfold valsBelow
  refine card_biUnion_le.trans ?_
  calc ∑ k' ∈ range k, (bvals (rc k')).card ≤ ∑ _k' ∈ range k, Fintype.card (DSlot P) := by
        refine sum_le_sum fun k' _ => ?_
        unfold bvals
        exact card_image_le.trans (card_le_univ _)
    _ = k * Fintype.card (DSlot P) := by rw [sum_const, card_range, smul_eq_mul]

open Classical in
lemma prod_chi {n : ℕ} (F : Fin n × DSlot P → Option (Fin n × DSlot P)) (rc : Rec (DSlot P)) :
    ∏ b ∈ fdom F, (if rc b.1 b.2 ≠ none ∧ (rc b.1 b.2).getD 0 ∈ valsBelow rc b.1 then (1 : ℝ)
      else 0) = ∏ k ∈ range n, chi P F k rc (rc k) := by
  rw [← prod_fiberwise_of_maps_to (g := fun b : Fin n × DSlot P => (b.1 : ℕ)) (t := range n)
    (fun b _ => mem_range.2 b.1.isLt)]
  refine prod_congr rfl fun k _ => ?_
  unfold chi
  refine prod_congr rfl fun b hb => ?_
  have e := (mem_filter.1 hb).2
  rw [e]

lemma sum_cnt {n : ℕ} {F : Fin (n + 1) × DSlot P → Option (Fin (n + 1) × DSlot P)}
    (hF : F ∈ forests (n + 1)) : ∑ i ∈ range n, cnt P F (1 + i) = frank F := by
  have h0 : cnt P F 0 = 0 := by
    unfold cnt
    rw [card_eq_zero, filter_eq_empty_iff]
    intro b hb h
    have hb' : F b ≠ none := (mem_filter.1 hb).2
    obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hb'
    have := forests_lt P hF b a ha
    rw [Fin.lt_def, h] at this
    exact Nat.not_lt_zero _ this
  have h1 : frank F = ∑ k ∈ range (n + 1), cnt P F k := by
    unfold cnt
    have := card_eq_sum_card_fiberwise (f := fun b : Fin (n + 1) × DSlot P => (b.1 : ℕ))
      (s := fdom F) (t := range (n + 1)) (fun b _ => mem_range.2 b.1.isLt)
    exact this
  rw [h1, sum_range_succ', h0, add_zero]
  exact sum_congr rfl fun i _ => by rw [Nat.add_comm 1 i]

lemma bVec_w (s : P.MState) :
    ‖P.bVec s‖ * (12 : ℝ) ^ P.memSize s.2.2 = ‖P.bVec s‖ := by
  unfold MemParams.bVec
  split_ifs with h
  · have : P.memSize s.2.2 = 0 := by unfold MemParams.memSize; rw [h.2]; simp
    rw [this]; simp
  · simp

lemma norm_bVec_le (s : P.MState) : ‖P.bVec s‖ ≤ (12 : ℝ) ^ P.memSize s.2.2 := by
  unfold MemParams.bVec
  have : (1 : ℝ) ≤ 12 ^ P.memSize s.2.2 := one_le_pow₀ (by norm_num)
  split_ifs <;> simp <;> linarith

section Large

variable (hVle : ∀ i, P.Vg i ≤ 3 / 2) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)

include hVle hVge hb

open Classical in
/-- **The large-rank bound** for one forest term. -/
theorem TF_large (hRd : EdgeRowStmt) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U) (hY : 0 < P.Y) (F : FT P)
    (hF : F ∈ forests (4 * P.N + 2)) {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hDV : ∀ V : Finset ℕ, V.card ≤ (4 * P.N + 2) * Fintype.card (DSlot P) →
      18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D) :
    ‖TF P ω F‖ ≤ (∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖) * Bmax P ^ (4 * P.N + 1) *
      D ^ frank F := by
  have hFlt := forests_lt P hF
  have hμ := stWeight_nonneg' P hVge hb
  set osA := (fullL P ω).map BOp.abs with hosA
  set tailA := (tailL P ω P.N).map BOp.abs with htailA
  have hosA' : osA = (initOp P).abs :: tailA := by rw [hosA, htailA]; rfl
  have hlen : osA.length = 4 * P.N + 2 := by rw [hosA, List.length_map, length_fullL]
  have htlen : tailA.length = 4 * P.N + 1 := by rw [htailA, List.length_map, length_tailL]
  have hcoef : ∀ o ∈ osA, ∀ s c, 0 ≤ o.coeff s c := by
    intro o ho s c
    obtain ⟨o', _, rfl⟩ := List.mem_map.1 ho
    exact norm_nonneg _
  have hcoefT : ∀ o ∈ tailA, ∀ s c, 0 ≤ o.coeff s c := by
    intro o ho s c
    obtain ⟨o', _, rfl⟩ := List.mem_map.1 ho
    exact norm_nonneg _
  -- absolute values and the forced-birth indicators
  have h1 : ‖TF P ω F‖ ≤ rchain (fun _ _ _ => (1 : ℝ)) 0 osA
      (fun s rc => ‖P.bVec s‖ * ∏ i ∈ range osA.length, chi P F (0 + i) rc (rc (0 + i)))
      (dummyS P) (rec0 P) := by
    unfold TF
    refine (norm_rchain_le _ _ _ _ _ _).trans ?_
    refine rchain_mono _ _ (fun _ _ _ => norm_nonneg _) (fun _ _ _ => by simp) osA hcoef 0 _ _
      (fun _ _ => norm_nonneg _) (fun s rc => ?_) _ _
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    refine (norm_forest_term_le (qBound P) F hFlt rc).trans ?_
    simp only [hlen, zero_add]
    rw [← prod_chi P F rc]
    refine mul_le_of_le_one_left (prod_nonneg fun _ _ => by split_ifs <;> norm_num) ?_
    split_ifs <;> norm_num
  have hp := rchain_push (R := ℝ) (fun _ _ _ => (1 : ℝ)) (fun k rc v => chi P F k rc v)
    (chi_local P F) osA 0 (fun s _ => ‖P.bVec s‖) (dummyS P) (rec0 P)
  rw [hp] at h1
  -- the rows of the tail
  set Rk : ℕ → ℝ := fun k => Bmax P * D ^ cnt P F k with hRk
  have hRk0 : ∀ k, 0 ≤ Rk k := fun k => by
    have := one_le_Bmax P hY.le
    simp only [hRk]; positivity
  have hinv : ∀ o ∈ tailA, ∀ s ∈ ({s | s ∈ P.stSet} : Set P.MState), ∀ c ∈ o.ch,
      o.coeff s c ≠ 0 → o.out s c ∈ ({s | s ∈ P.stSet} : Set P.MState) := by
    intro o ho s hs c _ hc
    obtain ⟨o', ho', rfl⟩ := List.mem_map.1 ho
    simp only [Set.mem_setOf_eq] at hs ⊢
    have hc' : o'.coeff s c ≠ 0 := fun h => hc (by simp [BOp.abs, h])
    rcases mem_tailL P ω P.N o' ho' with ⟨j, rfl⟩ | rfl | ⟨j, rfl⟩
    · by_contra hout
      have hout' : P.ghostOut s c ∉ P.stSet := hout
      exact hc' (by show P.ghostCoeff j s c * _ = 0; rw [if_neg hout', mul_zero])
    · exact (L102G.mem_stSet_permS P c s).2 hs
    · by_contra hout
      have hout' : P.edgeOut s c ∉ P.stSet := hout
      exact hc' (by show P.edgeCoeff ω j s c * _ = 0; rw [if_neg hout', mul_zero])
  have hrow : ∀ i (hi : i < tailA.length), ∀ s ∈ ({s | s ∈ P.stSet} : Set P.MState), ∀ rc,
      ∑ c ∈ (tailA.get ⟨i, hi⟩).ch, (tailA.get ⟨i, hi⟩).coeff s c *
        (1 * chi P F (1 + i) rc ((tailA.get ⟨i, hi⟩).birth s c)) *
          (12 : ℝ) ^ P.memSize ((tailA.get ⟨i, hi⟩).out s c).2.2 ≤
        Rk (1 + i) * 12 ^ P.memSize s.2.2 := by
    intro i hi s hs rc
    have hi' : i < (tailL P ω P.N).length := by rw [← List.length_map (f := BOp.abs)]; exact hi
    have hget : tailA.get ⟨i, hi⟩ = ((tailL P ω P.N).get ⟨i, hi'⟩).abs := by
      simp only [htailA, List.get_eq_getElem, List.getElem_map]
    rw [hget]
    set o := (tailL P ω P.N).get ⟨i, hi'⟩
    have ho : o ∈ tailL P ω P.N := List.get_mem _ _
    set Cs := ((fdom F).filter (fun b => (b.1 : ℕ) = 1 + i)).image Prod.snd
    set V := valsBelow rc (1 + i)
    have hV : V.card ≤ (4 * P.N + 2) * Fintype.card (DSlot P) := by
      refine (card_valsBelow_le P rc (1 + i)).trans ?_
      have : 1 + i ≤ 4 * P.N + 2 := by rw [htlen] at hi; omega
      exact Nat.mul_le_mul_right _ this
    have h := tail_forced_row P hVle hVge hb hRd ω hω hU hY P.N o ho s hs Cs V hD0 hD1 (hDV V hV)
    rw [card_image_cnt] at h
    simp only [hRk]
    refine le_trans (le_of_eq ?_) h
    refine sum_congr rfl fun c _ => ?_
    rw [one_mul, chi_eq_image]
    rfl
  have htail : ∀ s ∈ P.stSet, ∀ rc, rchain (fun k rc v => 1 * chi P F k rc v) 1 tailA
      (fun s _ => ‖P.bVec s‖) s rc ≤
      (∏ i ∈ range tailA.length, Rk (1 + i)) * 12 ^ P.memSize s.2.2 := by
    intro s hs rc
    exact rchain_row_on (fun k rc v => 1 * chi P F k rc v)
      (fun k rc v => by rw [one_mul]; exact chi_nonneg P F k rc v)
      {s | s ∈ P.stSet} (fun s => (12 : ℝ) ^ P.memSize s.2.2) Rk hRk0 tailA 1 hcoefT hinv hrow
      (fun s _ => ‖P.bVec s‖) (fun _ _ => norm_nonneg _) (fun s _ _ => norm_bVec_le P s) s hs rc
  have hprod : ∏ i ∈ range tailA.length, Rk (1 + i) = Bmax P ^ (4 * P.N + 1) * D ^ frank F := by
    rw [htlen]
    simp only [hRk]
    rw [prod_mul_distrib, prod_const, card_range, prod_pow_eq_pow_sum]
    congr 2
    exact sum_cnt P (n := 4 * P.N + 1) hF
  rw [hprod] at htail
  -- the first op
  refine h1.trans ?_
  rw [hosA']
  show ∑ s ∈ P.stSet, ‖(P.stWeight s : ℂ) * P.bVec s‖ * (1 * chi P F 0 (rec0 P) (initBirth P s.2.1)) *
      rchain (fun k rc v => 1 * chi P F k rc v) (0 + 1) tailA (fun s _ => ‖P.bVec s‖) s
        (recUpd (rec0 P) 0 (initBirth P s.2.1)) ≤ _
  rw [sum_mul, sum_mul]
  refine sum_le_sum fun s hs => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ s hs), one_mul, zero_add]
  have hc := chi_le_one P F 0 (rec0 P) (initBirth P s.2.1)
  have hc0 := chi_nonneg P F 0 (rec0 P) (initBirth P s.2.1)
  have ht := htail s hs (recUpd (rec0 P) 0 (initBirth P s.2.1))
  have ht0 : 0 ≤ rchain (fun k rc v => 1 * chi P F k rc v) 1 tailA (fun s _ => ‖P.bVec s‖) s
      (recUpd (rec0 P) 0 (initBirth P s.2.1)) :=
    rchain_nonneg _ (fun k rc v => by rw [one_mul]; exact chi_nonneg P F k rc v) tailA hcoefT 1 _
      (fun _ _ => norm_nonneg _) _ _
  have hw := bVec_w P s
  have hB : 0 ≤ Bmax P ^ (4 * P.N + 1) * D ^ frank F := by
    have := one_le_Bmax P hY.le; positivity
  have hsb : 0 ≤ P.stWeight s * ‖P.bVec s‖ := mul_nonneg (hμ s hs) (norm_nonneg _)
  calc P.stWeight s * ‖P.bVec s‖ * chi P F 0 (rec0 P) (initBirth P s.2.1) *
        rchain (fun k rc v => 1 * chi P F k rc v) 1 tailA (fun s _ => ‖P.bVec s‖) s
          (recUpd (rec0 P) 0 (initBirth P s.2.1)) ≤
      P.stWeight s * ‖P.bVec s‖ * 1 *
        (Bmax P ^ (4 * P.N + 1) * D ^ frank F * 12 ^ P.memSize s.2.2) := by
        gcongr
    _ = P.stWeight s * (‖P.bVec s‖ * 12 ^ P.memSize s.2.2) * Bmax P ^ (4 * P.N + 1) *
        D ^ frank F := by ring
    _ = P.stWeight s * ‖P.bVec s‖ * Bmax P ^ (4 * P.N + 1) * D ^ frank F := by rw [hw]

end Large

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7e, the distinct moment ([21] (4.43)–(4.55))

`dist_bound_P`: for one set of parameters, splitting the forests at rank `r₀`,
`‖memMomentD‖ ≤ e (‖b‖² e^{30K(N+1)} ε^N (A² Z)^{r₀} + ‖b‖₁ Bmax^{4N+1} (A² D)^{r₀+1})`, with `ε` the edge
bound, `Z = (M_E/ε)²`, `A` the number of birth addresses and `D` the cost of a forced birth. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-- The number of birth addresses. -/
noncomputable def nAddr : ℕ := Fintype.card (Fin (4 * P.N + 2) × DSlot P)

lemma nAddr_eq : nAddr P = (4 * P.N + 2) * (P.K * (P.J + 1 + P.B)) := by
  unfold nAddr DSlot
  simp only [Fintype.card_prod, Fintype.card_fin]

lemma nAddr_pos (hK : 0 < P.K) : 0 < nAddr P := by
  rw [nAddr_eq]; positivity

section Combine

variable (hVle : ∀ i, P.Vg i ≤ 3 / 2) (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i)
  (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)

include hVle hVge hb

open Classical in
/-- **The distinct moment for one set of parameters.** -/
theorem dist_bound_P (hGd : GhostDomStmt) (hEd : EdgeDomStmt) (hRd : EdgeRowStmt)
    (hK : 0 < P.K) (ω : ℝ × ℝ × ℝ) (hω : P.RootIn ω) (hU : 0 < P.U)
    (hY : 0 < P.Y) (hdisj : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i')) {e : ℝ} (he : 0 < e)
    (heME : e ≤ √(edgeR P) * √(3 ^ P.K * edgeR P))
    (hEB : ∀ j < P.N, P.OpBound (P.edgeOp ω j) e) {D : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1)
    (hDV : ∀ V : Finset ℕ, V.card ≤ (4 * P.N + 2) * Fintype.card (DSlot P) →
      18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D)
    (hAD : (nAddr P : ℝ) ^ 2 * D ≤ 1) (r₀ : ℕ) :
    ‖P.memMomentD ω‖ ≤
      exp 1 * (P.wNorm P.bVec ^ 2 * exp (30 * P.K) ^ (P.N + 1) * e ^ P.N *
        ((nAddr P : ℝ) ^ 2 * ((√(edgeR P) * √(3 ^ P.K * edgeR P)) / e) ^ 2) ^ r₀) +
      exp 1 * ((∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖) * Bmax P ^ (4 * P.N + 1) *
        ((nAddr P : ℝ) ^ 2 * D) ^ (r₀ + 1)) := by
  set ME := √(edgeR P) * √(3 ^ P.K * edgeR P)
  set Z := (ME / e) ^ 2 with hZ
  set A := (nAddr P : ℝ)
  set Cs := P.wNorm P.bVec ^ 2 * exp (30 * P.K) ^ (P.N + 1) * e ^ P.N
  set Cl := (∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖) * Bmax P ^ (4 * P.N + 1)
  have hμ := stWeight_nonneg' P hVge hb
  have hA1 : (1 : ℝ) ≤ A := by
    have := nAddr_pos P hK
    simp only [A]; exact_mod_cast this
  have hZ1 : 1 ≤ Z := by
    have : 1 ≤ ME / e := by rw [le_div_iff₀ he]; linarith
    simp only [hZ]; nlinarith
  have hCs : 0 ≤ Cs := by
    have : 0 ≤ P.wNorm P.bVec := by unfold MemParams.wNorm; positivity
    positivity
  have hCl : 0 ≤ Cl := by
    have h1 : 0 ≤ ∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖ :=
      sum_nonneg fun s hs => mul_nonneg (hμ s hs) (norm_nonneg _)
    have := one_le_Bmax P hY.le
    positivity
  have hAcard : Fintype.card (Fin (4 * P.N + 2) × DSlot P) = nAddr P := rfl
  have hApos : 0 < Fintype.card (Fin (4 * P.N + 2) × DSlot P) := nAddr_pos P hK
  rw [memMomentD_eq_forests]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ F ∈ (forests (4 * P.N + 2) : Finset (FT P)), ‖TF P ω F‖ ≤
      Cs * (if frank F ≤ r₀ then Z ^ frank F else 0) +
        Cl * (if r₀ < frank F then D ^ frank F else 0) := by
    intro F hF
    by_cases hr : frank F ≤ r₀
    · rw [if_pos hr, if_neg (not_lt.2 hr), mul_zero, add_zero]
      have h := TF_small P hVle hVge hb hGd hEd ω hω hU hY hdisj he heME hEB F
      rw [pow_mul] at h
      exact h
    · rw [if_neg hr, if_pos (not_le.1 hr), mul_zero, zero_add]
      exact TF_large P hVle hVge hb hRd ω hω hU hY F hF hD0 hD1 hDV
  refine (sum_le_sum hterm).trans ?_
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hs := forest_sum_le (Sl := DSlot P) (4 * P.N + 2) hApos (Y := Z) (M := (A ^ 2 * Z) ^ r₀)
    (by positivity) (by positivity) (fun f => f ≤ r₀) (fun f hf => by
      rw [hAcard]
      exact pow_le_pow_right₀ (by nlinarith) hf)
  have hl := forest_sum_le (Sl := DSlot P) (4 * P.N + 2) hApos (Y := D)
    (M := (A ^ 2 * D) ^ (r₀ + 1)) hD0.le (by positivity) (fun f => r₀ < f) (fun f hf => by
      rw [hAcard]
      exact pow_le_pow_of_le_one (by positivity) hAD hf)
  have e1 : Cs * ∑ F ∈ (forests (4 * P.N + 2) : Finset (FT P)),
      (if frank F ≤ r₀ then Z ^ frank F else 0) ≤ Cs * (exp 1 * (A ^ 2 * Z) ^ r₀) :=
    mul_le_mul_of_nonneg_left hs hCs
  have e2 : Cl * ∑ F ∈ (forests (4 * P.N + 2) : Finset (FT P)),
      (if r₀ < frank F then D ^ frank F else 0) ≤ Cl * (exp 1 * (A ^ 2 * D) ^ (r₀ + 1)) :=
    mul_le_mul_of_nonneg_left hl hCl
  calc _ ≤ Cs * (exp 1 * (A ^ 2 * Z) ^ r₀) + Cl * (exp 1 * (A ^ 2 * D) ^ (r₀ + 1)) :=
        add_le_add e1 e2
    _ = _ := by ring

end Combine

end ArtinPrimitiveRoots.L102D
end

section
/-! # L102D: D7e, `DistinctnessStmt` ([21] (4.43)–(4.55))

From `dist_bound_P` with `ε = L^{−G}`, `D = 72 K A e^{−L^{0.1}}`, `r₀ = ⌊N/(2α')⌋`: with `ℓ = log L`,
* the small ranks cost `exp(1 + K(J+1) + 30K(N+1) − GNℓ + Nℓ/2) ≤ ½ L^{−(G−1)N}` once `ℓ ≥ 128K`;
* the large ranks cost `exp(1 + K(J+1) + (4N+1)(β₀ + β₁ℓ) − N L^{0.1}/(4α')) ≤ ½ L^{−(G−1)N}`, as the
  group primes exceed `e^{L^{0.1}}`, so a forced birth costs `D ≈ L^{O(1)} e^{−L^{0.1}}`. -/

namespace ArtinPrimitiveRoots.L102D

open Real Finset MeasureTheory

set_option maxRecDepth 100000

attribute [local irreducible] MemParams.stSet MemParams.memSet MemParams.zSet MemParams.partSet
  listCands

variable (P : MemParams)

/-! ## Sizes for one set of parameters -/

lemma nAddr_le {L : ℝ} (hL : 1 ≤ L) (hN : (P.N : ℝ) ≤ 3 * L) (hJ : (P.J : ℝ) ≤ L)
    (hB : (P.B : ℝ) ≤ L ^ 2 + 1) : (nAddr P : ℝ) ≤ 56 * P.K * L ^ 3 := by
  rw [nAddr_eq]
  push_cast
  have hK : (0 : ℝ) ≤ P.K := Nat.cast_nonneg _
  have h1 : (4 * (P.N : ℝ) + 2) ≤ 14 * L := by linarith
  have h2 : ((P.J : ℝ) + 1 + P.B) ≤ 4 * L ^ 2 := by nlinarith
  have h3 : (0 : ℝ) ≤ 4 * (P.N : ℝ) + 2 := by positivity
  have h4 : (0 : ℝ) ≤ (P.J : ℝ) + 1 + P.B := by positivity
  calc (4 * (P.N : ℝ) + 2) * (P.K * ((P.J : ℝ) + 1 + P.B)) ≤ (14 * L) * (P.K * (4 * L ^ 2)) := by
        gcongr
    _ = 56 * P.K * L ^ 3 := by ring

lemma eps_le (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 1 ≤ P.Y) :
    (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal ≤ 44 * log P.x ^ (3 * P.A₀) := by
  have hY0 : 0 < P.Y := by linarith
  have hv := volume_majorArcs_le P.x P.A₀ P.Y hL hA₀ hY0
  have hv' : (volume (majorArcs P.x P.A₀ P.Y)).toReal ≤ 4 * log P.x ^ (3 * P.A₀) / P.Y :=
    ENNReal.toReal_le_of_le_ofReal (by positivity) hv
  have hε : 0 ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  calc (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal ≤
      (11 * P.Y) * (4 * log P.x ^ (3 * P.A₀) / P.Y) := by
        gcongr
        linarith
    _ = 44 * log P.x ^ (3 * P.A₀) := by field_simp; ring

lemma one_le_rpow_log (hL : 1 ≤ log P.x) {c : ℝ} (hc : 0 ≤ c) : 1 ≤ log P.x ^ c :=
  one_le_rpow hL hc

lemma edgeR_le (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 1 ≤ P.Y)
    (hB : (P.B : ℝ) ≤ log P.x ^ 2 + 1) :
    edgeR P ≤ 720 * 12 ^ P.K * (log P.x ^ (3 * P.A₀) * (log P.x) ^ (2 * P.K)) := by
  unfold edgeR
  have h1 := eps_le P hL hA₀ hY
  have h2 := one_le_rpow_log P hL (c := 3 * P.A₀) (by positivity)
  have h3 : (2 + 2 * (P.B : ℝ)) ≤ 6 * log P.x ^ 2 := by nlinarith
  have h4 : (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) ≤
      720 * log P.x ^ (3 * P.A₀) := by linarith
  have h5 : (0 : ℝ) ≤ 16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    have : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ 10 * P.Y + 1 := by linarith
    positivity
  calc (2 : ℝ) ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
        (2 + 2 * P.B) ^ P.K ≤ 2 ^ P.K * (720 * log P.x ^ (3 * P.A₀)) * (6 * log P.x ^ 2) ^ P.K := by
        gcongr
    _ = 720 * 12 ^ P.K * (log P.x ^ (3 * P.A₀) * (log P.x) ^ (2 * P.K)) := by
        rw [mul_pow, ← pow_mul, show (12 : ℝ) ^ P.K = 2 ^ P.K * 6 ^ P.K by
          rw [← mul_pow]; norm_num]
        ring

lemma edgeR12_le (hL : 1 ≤ log P.x) (hA₀ : 0 ≤ P.A₀) (hY : 1 ≤ P.Y)
    (hB : (P.B : ℝ) ≤ log P.x ^ 2 + 1) :
    edgeR12 P ≤ 720 * 78 ^ P.K * (log P.x ^ (3 * P.A₀) * (log P.x) ^ (2 * P.K)) := by
  unfold edgeR12
  have h1 := eps_le P hL hA₀ hY
  have h3 : (2 + 2 * (P.B : ℝ)) ≤ 6 * log P.x ^ 2 := by nlinarith
  have h4 : (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) ≤
      720 * log P.x ^ (3 * P.A₀) := by
    have h2 := one_le_rpow_log P hL (c := 3 * P.A₀) (by positivity)
    linarith
  have h5 : (0 : ℝ) ≤ 16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    have : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
    have : 0 ≤ 10 * P.Y + 1 := by linarith
    positivity
  calc (13 : ℝ) ^ P.K * (16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal)) *
        (2 + 2 * P.B) ^ P.K ≤ 13 ^ P.K * (720 * log P.x ^ (3 * P.A₀)) * (6 * log P.x ^ 2) ^ P.K := by
        gcongr
    _ = 720 * 78 ^ P.K * (log P.x ^ (3 * P.A₀) * (log P.x) ^ (2 * P.K)) := by
        rw [mul_pow, ← pow_mul, show (78 : ℝ) ^ P.K = 13 ^ P.K * 6 ^ P.K by
          rw [← mul_pow]; norm_num]
        ring

lemma one_le_edgeR (hY : 0 ≤ P.Y) : 1 ≤ edgeR P := by
  unfold edgeR
  have hε : (0 : ℝ) ≤ (volume (majorArcs P.x P.A₀ P.Y)).toReal := ENNReal.toReal_nonneg
  have h1 : (1 : ℝ) ≤ 2 ^ P.K := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ 16 * (1 + (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal) := by
    have : 0 ≤ (10 * P.Y + 1) * (volume (majorArcs P.x P.A₀ P.Y)).toReal := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ (2 + 2 * P.B) ^ P.K :=
    one_le_pow₀ (by linarith [(Nat.cast_nonneg P.B : (0:ℝ) ≤ P.B)])
  calc (1 : ℝ) = 1 * 1 * 1 := by ring
    _ ≤ _ := by gcongr

lemma ME_eq (hY : 0 ≤ P.Y) :
    √(edgeR P) * √(3 ^ P.K * edgeR P) = √(3 ^ P.K) * edgeR P := by
  have h0 : 0 ≤ edgeR P := edgeR_nonneg P hY
  rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 ^ P.K)]
  rw [show √(edgeR P) * (√(3 ^ P.K) * √(edgeR P)) = √(3 ^ P.K) * (√(edgeR P) * √(edgeR P)) by
    ring, Real.mul_self_sqrt h0]

lemma ME_bounds (hY : 0 ≤ P.Y) :
    edgeR P ≤ √(edgeR P) * √(3 ^ P.K * edgeR P) ∧
      √(edgeR P) * √(3 ^ P.K * edgeR P) ≤ 3 ^ P.K * edgeR P := by
  rw [ME_eq P hY]
  have h0 : 0 ≤ edgeR P := edgeR_nonneg P hY
  have h3 : (1 : ℝ) ≤ 3 ^ P.K := one_le_pow₀ (by norm_num)
  have hs1 : 1 ≤ √(3 ^ P.K : ℝ) := by rw [Real.one_le_sqrt]; exact h3
  have hs2 : √(3 ^ P.K : ℝ) ≤ 3 ^ P.K := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- The cost of a forced birth. -/
lemma forced_cost (hVge : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i) (hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p)
    {T : ℝ} (hT : ∀ i, ∀ p ∈ P.grp i, exp T ≤ p) (V : Finset ℕ) {M : ℕ} (hV : V.card ≤ M) :
    18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ 72 * P.K * M * exp (-T) := by
  have hgrp : ∀ i, ∀ p ∈ P.grp i, p ∈ P.gPrimes := by
    intro i p hp
    simp only [MemParams.gPrimes, groupPrimes, mem_biUnion, mem_univ, true_and]
    exact ⟨i, hp⟩
  have hnu : ∀ i, ∀ p ∈ P.grp i, P.nu i p ≤ 4 * exp (-T) := by
    intro i p hp
    have hVi := hVge i
    have hbp := hb p (hgrp i p hp)
    have hpT := hT i p hp
    have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (exp_pos T) hpT
    unfold MemParams.nu
    rw [div_le_iff₀ (by
      have : 0 < P.Vg i := by linarith
      have : 0 < P.bprime p := by linarith
      positivity)]
    have e1 : 4 * exp (-T) * (P.Vg i * ((p : ℝ) + 1) * P.bprime p) ≥
        4 * exp (-T) * ((1 / 2) * ((p : ℝ) + 1) * (1 / 2)) := by
      have : 0 ≤ 4 * exp (-T) := by positivity
      apply mul_le_mul_of_nonneg_left _ this
      have : 0 ≤ (p : ℝ) + 1 := by positivity
      have h1 : (1 / 2) * ((p : ℝ) + 1) ≤ P.Vg i * ((p : ℝ) + 1) :=
        mul_le_mul_of_nonneg_right hVi this
      calc (1 / 2) * ((p : ℝ) + 1) * (1 / 2) ≤ P.Vg i * ((p : ℝ) + 1) * (1 / 2) := by gcongr
        _ ≤ P.Vg i * ((p : ℝ) + 1) * P.bprime p := by
            gcongr
    have e2 : 4 * exp (-T) * ((1 / 2) * ((p : ℝ) + 1) * (1 / 2)) ≥ exp (-T) * p := by
      nlinarith [exp_pos (-T)]
    have e3 : exp (-T) * p ≥ 1 := by
      calc (1 : ℝ) = exp (-T) * exp T := by rw [← exp_add]; simp
        _ ≤ exp (-T) * p := mul_le_mul_of_nonneg_left hpT (exp_pos _).le
    linarith
  have hK : ∀ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ M * (4 * exp (-T)) := by
    intro i
    calc ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤
        ∑ _p ∈ (P.grp i).filter (· ∈ V), 4 * exp (-T) :=
          sum_le_sum fun p hp => hnu i p (mem_filter.1 hp).1
      _ = ((P.grp i).filter (· ∈ V)).card * (4 * exp (-T)) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ M * (4 * exp (-T)) := by
          gcongr
          have : ((P.grp i).filter (· ∈ V)).card ≤ V.card :=
            card_le_card fun p hp => (mem_filter.1 hp).2
          exact_mod_cast this.trans hV
  calc 18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤
      18 * ∑ _i : Fin P.K, (M : ℝ) * (4 * exp (-T)) := by gcongr with i; exact hK i
    _ = 72 * P.K * M * exp (-T) := by rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `‖b‖₁ = ∑ μ |b| ≤ 2^{K(J+1)}`. -/
lemma bsum_le (hnu : ∀ i, ∀ p ∈ P.grp i, 0 ≤ P.nu i p) (hsum : ∀ i, ∑ p ∈ P.grp i, P.nu i p ≤ 2) :
    ∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖ ≤ 2 ^ (P.K * (P.J + 1)) := by
  classical
  have hlw : ∀ ℓ ∈ listCands P.x P.a P.J, 0 ≤ P.listWeight ℓ := by
    intro ℓ hℓ
    unfold MemParams.listWeight
    refine prod_nonneg fun i _ => prod_nonneg fun k _ => hnu i _ ?_
    simp only [listCands, Fintype.mem_piFinset] at hℓ
    exact hℓ i k
  have hmw0 : P.memWeight 0 = 1 := by
    unfold MemParams.memWeight; simp
  -- the support maps injectively to the lists
  have h1 : ∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖ =
      ∑ s ∈ P.stSet.filter (fun s => s.1 = (1, 0) ∧ s.2.2 = 0), P.listWeight s.2.1 := by
    rw [sum_filter]
    refine sum_congr rfl fun s _ => ?_
    unfold MemParams.bVec MemParams.stWeight
    split_ifs with h
    · rw [h.2, hmw0]; simp
    · simp
  have h2 : ∑ s ∈ P.stSet.filter (fun s => s.1 = (1, 0) ∧ s.2.2 = 0), P.listWeight s.2.1 ≤
      ∑ ℓ ∈ listCands P.x P.a P.J, P.listWeight ℓ := by
    rw [← sum_image (f := fun ℓ => P.listWeight ℓ) (g := fun s : P.MState => s.2.1)]
    · refine sum_le_sum_of_subset_of_nonneg (fun ℓ hℓ => ?_) (fun ℓ hℓ _ => hlw ℓ hℓ)
      obtain ⟨s, hs, rfl⟩ := mem_image.1 hℓ
      have := (mem_filter.1 hs).1
      exact ((mem_stSet_iff' P _).1 this).2.1
    · intro s hs s' hs' he
      have a := (mem_filter.1 hs).2
      have b := (mem_filter.1 hs').2
      exact Prod.ext (a.1.trans b.1.symm) (Prod.ext he (a.2.trans b.2.symm))
  have h3 : ∑ ℓ ∈ listCands P.x P.a P.J, P.listWeight ℓ =
      ∏ i : Fin P.K, ∏ _k : Fin (P.J + 1), ∑ p ∈ P.grp i, P.nu i p := by
    unfold listCands MemParams.listWeight
    rw [← prod_univ_sum (t := fun i => Fintype.piFinset fun _ : Fin (P.J + 1) =>
      primeGroup P.x (P.a i)) (f := fun i ℓi => ∏ k, P.nu i (ℓi k))]
    refine prod_congr rfl fun i _ => ?_
    rw [← prod_univ_sum (t := fun _ : Fin (P.J + 1) => primeGroup P.x (P.a i))
      (f := fun _ p => P.nu i p)]
    rfl
  have h4 : ∏ i : Fin P.K, ∏ _k : Fin (P.J + 1), ∑ p ∈ P.grp i, P.nu i p ≤
      ∏ _i : Fin P.K, ∏ _k : Fin (P.J + 1), (2 : ℝ) :=
    prod_le_prod (fun i _ => prod_nonneg fun k _ => sum_nonneg fun p hp => hnu i p hp)
      fun i _ => prod_le_prod (fun k _ => sum_nonneg fun p hp => hnu i p hp) fun k _ => hsum i
  rw [h1]
  refine h2.trans (h3 ▸ h4.trans (le_of_eq ?_))
  simp only [prod_const, card_univ, Fintype.card_fin]
  rw [← pow_mul, mul_comm]

lemma wNorm_bVec_sq (hμ : ∀ s ∈ P.stSet, 0 ≤ P.stWeight s) :
    P.wNorm P.bVec ^ 2 = ∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖ := by
  unfold MemParams.wNorm
  rw [Real.sq_sqrt (sum_nonneg fun s hs => mul_nonneg (hμ s hs) (sq_nonneg _))]
  refine sum_congr rfl fun s _ => ?_
  unfold MemParams.bVec
  split_ifs <;> simp

/-! ## The numerics -/

lemma two_pow_le_exp (n : ℕ) : (2 : ℝ) ^ n ≤ exp n := by
  rw [← Real.exp_one_pow]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) n

lemma pow_exp (n : ℕ) (y : ℝ) : exp y ^ n = exp (n * y) := by
  rw [← Real.exp_nat_mul]

/-- The cost `A² D` of a forced birth. -/
lemma AD_bound {K : ℕ} {ℓ A : ℝ} (hK : 1 ≤ K) (hA1 : 1 ≤ A) (hA : A ≤ 56 * K * exp (3 * ℓ))
    (hc4 : 2 * (log (72 * K * (56 * K) ^ 3) + 9 * ℓ) ≤ exp (0.1 * ℓ)) :
    A ^ 2 * (72 * K * A * exp (-exp (0.1 * ℓ))) ≤ exp (-(exp (0.1 * ℓ) / 2)) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hA0 : 0 ≤ A := by linarith
  calc A ^ 2 * (72 * K * A * exp (-exp (0.1 * ℓ))) = 72 * K * A ^ 3 * exp (-exp (0.1 * ℓ)) := by
        ring
    _ ≤ 72 * K * (56 * K * exp (3 * ℓ)) ^ 3 * exp (-exp (0.1 * ℓ)) := by gcongr
    _ = exp (log (72 * K * (56 * K) ^ 3) + 9 * ℓ - exp (0.1 * ℓ)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add, Real.exp_log (by positivity),
          mul_pow, ← Real.exp_nat_mul]
        push_cast; ring_nf
    _ ≤ exp (-(exp (0.1 * ℓ) / 2)) := by rw [exp_le_exp]; linarith

/-- **The final numerics.** -/
lemma dist_numeric {K N J r₀ α' : ℕ} {G A₀ ℓ bw bs A ME Bm : ℝ} (hK : 1 ≤ K) (hG : 0 < G)
    (hA₀ : 0 < A₀) (hN1 : 1 ≤ N) (hJN : J ≤ N)
    (hα' : 6 + 6 * A₀ + 4 * K + 2 * G + 1 ≤ α') (hr₀ : 2 * α' * r₀ ≤ N)
    (hr₀' : N < 2 * α' * (r₀ + 1)) (hℓ1 : 1 ≤ ℓ) (hℓK : 128 * K ≤ ℓ)
    (hℓZ : log ((56 * K * 720 * 36 ^ K) ^ 2) ≤ ℓ)
    (hc4 : 2 * (log (72 * K * (56 * K) ^ 3) + 9 * ℓ) ≤ exp (0.1 * ℓ))
    (hc5 : 4 * α' * (2 + 2 * K + 5 * (36 * K + 1 + log (720 * 78 ^ K)) +
      (5 * (3 * A₀ + 2 * K) + G) * ℓ) ≤ exp (0.1 * ℓ))
    (hbw : bw ≤ 2 ^ (K * (J + 1))) (hbs : bs ≤ 2 ^ (K * (J + 1)))
    (hA1 : 1 ≤ A) (hA : A ≤ 56 * K * exp (3 * ℓ))
    (hME0 : 0 ≤ ME) (hME : ME ≤ 720 * 36 ^ K * exp ((3 * A₀ + 2 * K) * ℓ))
    (hBm0 : 0 ≤ Bm) (hBm : Bm ≤ exp (36 * K + 1) * (720 * 78 ^ K) * exp ((3 * A₀ + 2 * K) * ℓ)) :
    exp 1 * (bw * exp (30 * K) ^ (N + 1) * exp (-G * ℓ) ^ N *
        (A ^ 2 * (ME / exp (-G * ℓ)) ^ 2) ^ r₀) +
      exp 1 * (bs * Bm ^ (4 * N + 1) * (A ^ 2 * (72 * K * A * exp (-exp (0.1 * ℓ)))) ^ (r₀ + 1)) ≤
    exp (-((G - 1) * N) * ℓ) := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hJr : (J : ℝ) ≤ N := by exact_mod_cast hJN
  have hℓ0 : 0 ≤ ℓ := by linarith
  have h2b : (2 : ℝ) ^ (K * (J + 1)) ≤ exp (K * (J + 1)) := by
    have := two_pow_le_exp (K * (J + 1)); push_cast at this; exact this
  -- the small ranks
  set c₀ : ℝ := 56 * K * 720 * 36 ^ K with hc₀
  have hc₀pos : 0 < c₀ := by positivity
  have hX : A * (ME / exp (-G * ℓ)) ≤ c₀ * exp ((3 + 3 * A₀ + 2 * K + G) * ℓ) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_mul, neg_neg]
    have hA0 : 0 ≤ A := by linarith
    calc A * (ME * exp (G * ℓ)) ≤ (56 * K * exp (3 * ℓ)) *
          ((720 * 36 ^ K * exp ((3 * A₀ + 2 * K) * ℓ)) * exp (G * ℓ)) := by gcongr
      _ = c₀ * (exp (3 * ℓ) * exp ((3 * A₀ + 2 * K) * ℓ) * exp (G * ℓ)) := by rw [hc₀]; ring
      _ = c₀ * exp ((3 + 3 * A₀ + 2 * K + G) * ℓ) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hX0 : 0 ≤ A * (ME / exp (-G * ℓ)) := by
    have : 0 ≤ A := by linarith
    positivity
  have hZ : A ^ 2 * (ME / exp (-G * ℓ)) ^ 2 ≤ exp (α' * ℓ) := by
    rw [← mul_pow]
    calc (A * (ME / exp (-G * ℓ))) ^ 2 ≤ (c₀ * exp ((3 + 3 * A₀ + 2 * K + G) * ℓ)) ^ 2 :=
          pow_le_pow_left₀ hX0 hX 2
      _ = exp (log (c₀ ^ 2) + 2 * (3 + 3 * A₀ + 2 * K + G) * ℓ) := by
          rw [Real.exp_add, Real.exp_log (by positivity), mul_pow, ← Real.exp_nat_mul]
          push_cast; ring_nf
      _ ≤ exp (α' * ℓ) := by
          rw [exp_le_exp]
          have hlc : log (c₀ ^ 2) ≤ ℓ := by rw [hc₀]; exact hℓZ
          have h1 : (6 + 6 * A₀ + 4 * K + 2 * G + 1) * ℓ ≤ α' * ℓ :=
            mul_le_mul_of_nonneg_right hα' hℓ0
          have e : 2 * (3 + 3 * A₀ + 2 * K + G) * ℓ = (6 + 6 * A₀ + 4 * K + 2 * G + 1) * ℓ - ℓ := by
            ring
          linarith
  have hT1 : exp 1 * (bw * exp (30 * K) ^ (N + 1) * exp (-G * ℓ) ^ N *
      (A ^ 2 * (ME / exp (-G * ℓ)) ^ 2) ^ r₀) ≤
      exp (1 + K * (J + 1) + 30 * K * (N + 1) - G * N * ℓ + α' * r₀ * ℓ) := by
    have hZ0 : 0 ≤ A ^ 2 * (ME / exp (-G * ℓ)) ^ 2 := by positivity
    calc exp 1 * (bw * exp (30 * K) ^ (N + 1) * exp (-G * ℓ) ^ N *
          (A ^ 2 * (ME / exp (-G * ℓ)) ^ 2) ^ r₀) ≤
        exp 1 * (exp (K * (J + 1)) * exp (30 * K) ^ (N + 1) * exp (-G * ℓ) ^ N *
          exp (α' * ℓ) ^ r₀) := by
          gcongr
          exact hbw.trans h2b
      _ = exp (1 + K * (J + 1) + 30 * K * (N + 1) - G * N * ℓ + α' * r₀ * ℓ) := by
          rw [pow_exp, pow_exp, pow_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add]
          push_cast; ring_nf
  have key2 : ∀ X : ℝ, exp X * 2 = exp (X + log 2) := fun X => by
    rw [Real.exp_add, Real.exp_log (by norm_num)]
  have hlog2 : log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hKN : (K : ℝ) ≤ K * N := le_mul_of_one_le_right (by positivity) hNr
  have hKN1 : (1 : ℝ) ≤ K * N := one_le_mul_of_one_le_of_one_le hKr hNr
  have hJ1 : (K : ℝ) * (J + 1) ≤ 2 * K * N := by
    have : (J : ℝ) + 1 ≤ 2 * N := by linarith
    calc (K : ℝ) * (J + 1) ≤ K * (2 * N) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * K * N := by ring
  have hNl : 0 ≤ (N : ℝ) * ℓ := by positivity
  have hT1' : exp (1 + K * (J + 1) + 30 * K * (N + 1) - G * N * ℓ + α' * r₀ * ℓ) ≤
      exp (-((G - 1) * N) * ℓ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), key2, exp_le_exp]
    have hr : (2 * α' * r₀ : ℝ) ≤ N := by exact_mod_cast hr₀
    have h2 : (α' : ℝ) * r₀ * ℓ ≤ N * ℓ / 2 := by
      have : (α' : ℝ) * r₀ ≤ N / 2 := by linarith
      calc (α' : ℝ) * r₀ * ℓ ≤ (N / 2) * ℓ := mul_le_mul_of_nonneg_right this hℓ0
        _ = N * ℓ / 2 := by ring
    have h3 : 64 * ((K : ℝ) * N) ≤ N * ℓ / 2 := by
      have : (N : ℝ) * (128 * K) ≤ N * ℓ := mul_le_mul_of_nonneg_left hℓK (by positivity)
      linarith only [this]
    have e1 : (30 : ℝ) * K * (N + 1) = 30 * (K * N) + 30 * K := by ring
    have e2 : (2 : ℝ) * K * N = 2 * (K * N) := by ring
    have eR : -((G - 1) * N) * ℓ = -(G * N * ℓ) + N * ℓ := by ring
    linarith only [hJ1, e1, e2, eR, h2, h3, hKN, hKN1, hlog2]
  -- the large ranks
  set β₀ : ℝ := 36 * K + 1 + log (720 * 78 ^ K) with hβ₀
  set β₁ : ℝ := 3 * A₀ + 2 * K with hβ₁
  have hβ₀0 : 0 ≤ β₀ := by
    have : 0 ≤ log (720 * 78 ^ K : ℝ) := Real.log_nonneg
      (one_le_mul_of_one_le_of_one_le (by norm_num) (one_le_pow₀ (by norm_num)))
    rw [hβ₀]; positivity
  have hβ₁0 : 0 ≤ β₁ := by rw [hβ₁]; positivity
  have hBm' : Bm ≤ exp (β₀ + β₁ * ℓ) := by
    rw [hβ₀, hβ₁, Real.exp_add, Real.exp_add, Real.exp_log (by positivity)]
    exact hBm
  have hA0 : 0 ≤ A := by linarith
  have hAD := AD_bound hK hA1 hA hc4
  have hAD0 : 0 ≤ A ^ 2 * (72 * K * A * exp (-exp (0.1 * ℓ))) := by positivity
  have hT2 : exp 1 * (bs * Bm ^ (4 * N + 1) * (A ^ 2 * (72 * K * A * exp (-exp (0.1 * ℓ)))) ^
      (r₀ + 1)) ≤ exp (1 + K * (J + 1) + (4 * N + 1) * (β₀ + β₁ * ℓ) -
        (r₀ + 1) * (exp (0.1 * ℓ) / 2)) := by
    calc exp 1 * (bs * Bm ^ (4 * N + 1) * (A ^ 2 * (72 * K * A * exp (-exp (0.1 * ℓ)))) ^
          (r₀ + 1)) ≤ exp 1 * (exp (K * (J + 1)) * exp (β₀ + β₁ * ℓ) ^ (4 * N + 1) *
            exp (-(exp (0.1 * ℓ) / 2)) ^ (r₀ + 1)) := by
          gcongr
          exact hbs.trans h2b
      _ = _ := by
          rw [pow_exp, pow_exp, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          push_cast; ring_nf
  have hT2' : exp (1 + K * (J + 1) + (4 * N + 1) * (β₀ + β₁ * ℓ) -
      (r₀ + 1) * (exp (0.1 * ℓ) / 2)) ≤ exp (-((G - 1) * N) * ℓ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2), key2, exp_le_exp]
    set W := 2 + 2 * (K : ℝ) + 5 * β₀ + (5 * β₁ + G) * ℓ with hW
    have hc5' : 4 * (α' : ℝ) * W ≤ exp (0.1 * ℓ) := by rw [hW, hβ₀, hβ₁]; exact hc5
    have hr' : (N : ℝ) < 2 * α' * (r₀ + 1) := by exact_mod_cast hr₀'
    have hW0 : 0 ≤ W := by rw [hW]; positivity
    have hkey : (N : ℝ) * W ≤ (r₀ + 1) * (exp (0.1 * ℓ) / 2) := by
      have a1 : (N : ℝ) * W ≤ (2 * α' * (r₀ + 1)) * W := mul_le_mul_of_nonneg_right hr'.le hW0
      have a2 : (2 * (α' : ℝ) * (r₀ + 1)) * W = ((r₀ + 1) / 2) * (4 * α' * W) := by ring
      have a3 : ((r₀ : ℝ) + 1) / 2 * (4 * α' * W) ≤ ((r₀ + 1) / 2) * exp (0.1 * ℓ) :=
        mul_le_mul_of_nonneg_left hc5' (by positivity)
      have a4 : ((r₀ : ℝ) + 1) / 2 * exp (0.1 * ℓ) = (r₀ + 1) * (exp (0.1 * ℓ) / 2) := by ring
      linarith only [a1, a2, a3, a4]
    have h2 : (4 * (N : ℝ) + 1) * (β₀ + β₁ * ℓ) ≤ 5 * N * (β₀ + β₁ * ℓ) := by
      have h0 : 0 ≤ β₀ + β₁ * ℓ := by positivity
      have : 4 * (N : ℝ) + 1 ≤ 5 * N := by linarith
      exact mul_le_mul_of_nonneg_right this h0
    have h4 : (N : ℝ) * W = 2 * N + 2 * K * N + 5 * N * (β₀ + β₁ * ℓ) + G * N * ℓ := by
      rw [hW]; ring
    have eR : -((G - 1) * N) * ℓ = -(G * N * ℓ) + N * ℓ := by ring
    linarith only [hkey, h2, h4, eR, hNl, hJ1, hNr, hlog2]
  calc _ ≤ exp (-((G - 1) * N) * ℓ) / 2 + exp (-((G - 1) * N) * ℓ) / 2 :=
        add_le_add (hT1.trans hT1') (hT2.trans hT2')
    _ = exp (-((G - 1) * N) * ℓ) := by ring

/-! ## D7e -/

lemma eventually_lin_le_exp (a b : ℝ) : ∀ᶠ ℓ : ℝ in Filter.atTop, a + b * ℓ ≤ exp (0.1 * ℓ) := by
  filter_upwards [Filter.eventually_ge_atTop (200 * (|a| + |b|) + 1)] with ℓ hℓ
  have hab : 0 ≤ |a| + |b| := by positivity
  have hℓ1 : 1 ≤ ℓ := by linarith
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 0.1 * ℓ by linarith)
  have h1 : a + b * ℓ ≤ |a| + |b| * ℓ := by
    have := le_abs_self a
    have : b * ℓ ≤ |b| * ℓ := mul_le_mul_of_nonneg_right (le_abs_self b) (by linarith)
    linarith
  have h2 : |a| + |b| * ℓ ≤ (|a| + |b|) * ℓ := by
    have : |a| ≤ |a| * ℓ := le_mul_of_one_le_right (abs_nonneg a) hℓ1
    linarith
  have h3 : (|a| + |b|) * ℓ ≤ (0.1 * ℓ) ^ 2 / 2 := by
    have : (200 * (|a| + |b|)) * ℓ ≤ ℓ * ℓ := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    nlinarith
  have h4 : 0 ≤ 1 + 0.1 * ℓ := by linarith
  linarith

lemma rpow_eq_exp_log {L : ℝ} (hL : 0 < L) (c : ℝ) : L ^ c = exp (c * log L) := by
  rw [Real.rpow_def_of_pos hL, mul_comm]

/-- For large `x` the prime groups are pairwise disjoint (as `L102D_Pairing`'s lemma). -/
lemma eventually_disjoint_groups_D {K : ℕ} (a : Fin K → ℝ) (ha : StrictMono a) :
    ∀ᶠ x : ℝ in Filter.atTop, ∀ i j, i ≠ j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
  have hL : ∀ᶠ L : ℝ in Filter.atTop, ∀ i j : Fin K, a i < a j → 2 * L ^ a i < L ^ a j := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases hij : a i < a j
    · filter_upwards [eventually_rpow_le_rpow hij (ε := 1 / 3) (by norm_num),
        Filter.eventually_gt_atTop 0] with L h1 h2 _
      have : 0 < L ^ a j := by positivity
      linarith
    · exact Filter.Eventually.of_forall fun L h => absurd h hij
  filter_upwards [Real.tendsto_log_atTop.eventually hL] with x hx
  intro i j hij
  have key : ∀ i j : Fin K, a i < a j → Disjoint (primeGroup x (a i)) (primeGroup x (a j)) := by
    intro i j h
    refine Finset.disjoint_left.2 fun p hp hp' => ?_
    have h1 := (le_of_mem_primeGroup hp).2
    have h2 := (le_of_mem_primeGroup hp').1
    have := exp_lt_exp.2 (hx i j h)
    linarith
  rcases lt_or_gt_of_ne (ha.injective.ne hij) with h | h
  · exact key i j h
  · exact (key j i h).symm

/-- **D7e** (no ghost hypothesis). -/
theorem distinctness_bound_ng_of_cuts (δ c₁ c₂ : ℝ) (hGd : GhostDomStmt) (hEd : EdgeDomStmt)
    (hRd : EdgeRowStmt) : DistinctnessStmtNG δ c₁ c₂ := by
  intro G hG A₀ hA₀ K hK a ha hband hEdge
  obtain ⟨xE, hxE⟩ := hEdge
  have hpos : ∀ i, 0 < a i := fun i => by linarith [(hband i).1]
  set α' : ℕ := ⌈6 + 6 * A₀ + 4 * K + 2 * G + 1⌉₊ with hα'def
  have hα' : 6 + 6 * A₀ + 4 * K + 2 * G + 1 ≤ (α' : ℝ) := Nat.le_ceil _
  have hα'pos : 0 < α' := by
    have : (0 : ℝ) < α' := lt_of_lt_of_le (by positivity) hα'
    exact_mod_cast this
  have hnum : ∀ᶠ ℓ : ℝ in Filter.atTop, 1 ≤ ℓ ∧ 128 * (K : ℝ) ≤ ℓ ∧
      log ((56 * K * 720 * 36 ^ K) ^ 2) ≤ ℓ ∧
      2 * (log (72 * K * (56 * K) ^ 3) + 9 * ℓ) ≤ exp (0.1 * ℓ) ∧
      4 * α' * (2 + 2 * K + 5 * (36 * K + 1 + log (720 * 78 ^ K)) +
        (5 * (3 * A₀ + 2 * K) + G) * ℓ) ≤ exp (0.1 * ℓ) := by
    filter_upwards [Filter.eventually_ge_atTop 1, Filter.eventually_ge_atTop (128 * (K : ℝ)),
      Filter.eventually_ge_atTop (log ((56 * K * 720 * 36 ^ K) ^ 2)),
      eventually_lin_le_exp (2 * log (72 * K * (56 * K) ^ 3)) 18,
      eventually_lin_le_exp (4 * α' * (2 + 2 * K + 5 * (36 * K + 1 + log (720 * 78 ^ K))))
        (4 * α' * (5 * (3 * A₀ + 2 * K) + G))] with ℓ h1 h2 h3 h4 h5
    refine ⟨h1, h2, h3, by linarith, by linarith⟩
  have hℓx : Filter.Tendsto (fun x : ℝ => log (log x)) Filter.atTop Filter.atTop :=
    tendsto_log_atTop.comp tendsto_log_atTop
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.1 ((hℓx.eventually hnum).and
    ((tendsto_log_atTop.eventually_ge_atTop 1).and ((eventually_Vg_le a hpos).and
      ((eventually_Vg_ge_half a hpos).and
        ((eventually_groupPrimes_ge a (fun i => (hband i).1) 4).and
          ((eventually_disjoint_groups_D a ha).and
            ((Filter.eventually_ge_atTop xE).and (Filter.eventually_gt_atTop 0))))))))
  refine ⟨x₀, fun x Hm Hn hx hHm hHn hc1 hc2 Y hY k => ?_⟩
  obtain ⟨⟨hℓ1, hℓK, hℓZ, hc4, hc5⟩, hL1, hVle, hVge, hgp, hdisj, hxE', hx0⟩ := hx₀ x hx
  intro P ω hω
  set L := log x with hLdef
  set ℓ := log L with hℓdef
  have hL0 : 0 < L := by linarith
  have hLexp : L = exp ℓ := (Real.exp_log hL0).symm
  -- the parameters
  have hPK : P.K = K := rfl
  have hPN : P.N = 2 * momentPower x := rfl
  have hPJ : P.J = padCount x := rfl
  have hPB : P.B = ⌈L ^ 2⌉₊ := rfl
  have hPx : P.x = x := rfl
  have hPY : P.Y = Y := rfl
  have hPA : P.A₀ = A₀ := rfl
  have hK0 : 0 < P.K := by rw [hPK]; omega
  have hVle' : ∀ i, P.Vg i ≤ 3 / 2 := hVle
  have hVge' : ∀ i, (1 : ℝ) / 2 ≤ P.Vg i := hVge
  have hb : ∀ p ∈ P.gPrimes, 1 / 2 ≤ P.bprime p := by
    intro p hp
    apply bprime_ge_half
    have h4 := hgp p hp
    have : (2 * (2 * momentPower x : ℕ) + 1 : ℝ) ≤ 4 * (momentPower x + 1) := by
      push_cast; linarith
    exact_mod_cast this.trans h4
  have hnu := nu_nonneg_of P hVge' hb
  have hμ := stWeight_nonneg' P hVge' hb
  have hU : 0 < P.U := by
    show 0 < 2 ^ k * Y * Hm
    have : 0 < Hm := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) hHm
    have : 0 < Y := by linarith
    positivity
  have hY0 : 0 < P.Y := by rw [hPY]; linarith
  have hY1 : 1 ≤ P.Y := by rw [hPY]; exact hY
  have hdisj' : ∀ i i', i ≠ i' → Disjoint (P.grp i) (P.grp i') := hdisj
  -- sizes
  have hsq : 1 ≤ L ^ (0.5 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hN1 : 1 ≤ P.N := by
    rw [hPN]
    have : 0 < momentPower x := by
      unfold momentPower
      exact Nat.ceil_pos.2 (by positivity)
    omega
  have hNge : L ^ (0.5 : ℝ) ≤ P.N := by
    rw [hPN]; push_cast
    have := Nat.le_ceil (L ^ (0.5 : ℝ) / 2)
    unfold momentPower; linarith
  have hN3 : (P.N : ℝ) ≤ 3 * L := by
    rw [hPN]; push_cast
    unfold momentPower
    have h1 := Nat.ceil_lt_add_one (show 0 ≤ L ^ (0.5 : ℝ) / 2 by positivity)
    have h2 : L ^ (0.5 : ℝ) ≤ L := by
      calc L ^ (0.5 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
        _ = L := Real.rpow_one L
    linarith
  have hJle : (P.J : ℝ) ≤ L ^ (0.01 : ℝ) := by
    rw [hPJ]; unfold padCount
    exact Nat.floor_le (by positivity)
  have hJL : (P.J : ℝ) ≤ L := by
    refine hJle.trans ?_
    calc L ^ (0.01 : ℝ) ≤ L ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
      _ = L := Real.rpow_one L
  have hJN : P.J ≤ P.N := by
    have : (P.J : ℝ) ≤ P.N := by
      refine hJle.trans (le_trans ?_ hNge)
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    exact_mod_cast this
  have hBL : (P.B : ℝ) ≤ L ^ 2 + 1 := by
    rw [hPB]
    exact (Nat.ceil_lt_add_one (by positivity)).le
  have hBL' : (P.B : ℝ) ≤ log P.x ^ 2 + 1 := hBL
  have hLx : 1 ≤ log P.x := hL1
  -- the edge bound
  set e : ℝ := exp (-G * ℓ) with he_def
  have he : 0 < e := exp_pos _
  have heq : log x ^ (-G) = e := by rw [rpow_eq_exp_log hL0, he_def]
  have hEB : ∀ j < P.N, P.OpBound (P.edgeOp ω j) e := by
    intro j hj
    have := hxE x Hm Hn hxE' hHm hHn hc1 hc2 Y hY k ω hω j hj
    rw [heq] at this
    exact this
  have hME := ME_bounds P hY0.le
  have hER1 := one_le_edgeR P hY0.le
  have heME : e ≤ √(edgeR P) * √(3 ^ P.K * edgeR P) := by
    have : e ≤ 1 := by
      rw [he_def]; rw [exp_le_one_iff]
      have h0 : 0 ≤ G * ℓ := mul_nonneg hG.le (by linarith)
      rw [neg_mul]; exact neg_nonpos.2 h0
    linarith [hME.1]
  -- the forced-birth cost
  set A : ℝ := (nAddr P : ℝ) with hAdef
  have hA1 : 1 ≤ A := by
    have := nAddr_pos P hK0
    rw [hAdef]; exact_mod_cast this
  have hA : A ≤ 56 * K * exp (3 * ℓ) := by
    have := nAddr_le P hL1 hN3 hJL hBL
    rw [hPK] at this
    rw [hAdef]
    refine this.trans (le_of_eq ?_)
    rw [hLexp, ← Real.exp_nat_mul]; push_cast; ring_nf
  set D : ℝ := 72 * K * A * exp (-exp (0.1 * ℓ)) with hDdef
  have hD0 : 0 < D := by
    rw [hDdef]
    have h1 : (0 : ℝ) < K := by exact_mod_cast hK
    have h2 : (0 : ℝ) < A := by linarith
    exact mul_pos (mul_pos (mul_pos (by norm_num) h1) h2) (exp_pos _)
  have hAD := AD_bound hK hA1 hA hc4
  have hAD1 : A ^ 2 * D ≤ 1 := by
    rw [hDdef]; refine hAD.trans ?_
    rw [exp_le_one_iff]; have := exp_pos (0.1 * ℓ); linarith
  have hD1 : D ≤ 1 := by
    have : D ≤ A ^ 2 * D := le_mul_of_one_le_left hD0.le (one_le_pow₀ hA1)
    linarith
  have hT : ∀ i, ∀ p ∈ P.grp i, exp (exp (0.1 * ℓ)) ≤ p := by
    intro i p hp
    have hp' := hp
    simp only [MemParams.grp, primeGroup, mem_filter] at hp'
    refine le_trans ?_ hp'.2.2
    rw [exp_le_exp]
    have h1 : L ^ (0.1 : ℝ) ≤ L ^ P.a i :=
      Real.rpow_le_rpow_of_exponent_le hL1 (hband i).1.le
    have h2 : L ^ (0.1 : ℝ) = exp (0.1 * ℓ) := by rw [rpow_eq_exp_log hL0]
    rw [← h2]; exact h1
  have hDV : ∀ V : Finset ℕ, V.card ≤ (4 * P.N + 2) * Fintype.card (DSlot P) →
      18 * ∑ i, ∑ p ∈ (P.grp i).filter (· ∈ V), P.nu i p ≤ D := by
    intro V hV
    have hV' : V.card ≤ nAddr P := by
      unfold nAddr; rw [Fintype.card_prod, Fintype.card_fin]; exact hV
    have := forced_cost P hVge' hb hT V hV'
    rw [hDdef, hAdef, hPK.symm]
    exact this
  -- the rank cut
  set r₀ := P.N / (2 * α') with hr₀def
  have hr₀ : 2 * α' * r₀ ≤ P.N := Nat.mul_div_le _ _
  have hr₀' : P.N < 2 * α' * (r₀ + 1) := by
    rw [hr₀def]; exact Nat.lt_mul_div_succ _ (by omega)
  have hmain := dist_bound_P P hVle' hVge' hb hGd hEd hRd hK0 ω hω hU hY0 hdisj' he heME hEB hD0 hD1 hDV
    hAD1 r₀
  -- the numerics
  have hbsum := bsum_le P hnu (sum_nu_le_two P hVge' hb)
  have hbw := wNorm_bVec_sq P hμ
  have hMEle : √(edgeR P) * √(3 ^ P.K * edgeR P) ≤ 720 * 36 ^ K * exp ((3 * A₀ + 2 * K) * ℓ) := by
    refine hME.2.trans ?_
    have h1 := edgeR_le P hLx (by rw [hPA]; exact hA₀.le) hY1 hBL'
    rw [hPK, hPA, hPx] at h1
    rw [hPK]
    have e1 : log x ^ (3 * A₀) * log x ^ (2 * K) = exp ((3 * A₀ + 2 * K) * ℓ) := by
      rw [rpow_eq_exp_log hL0, ← hℓdef, show log x ^ (2 * K) = L ^ (2 * K) from rfl,
        hLexp, ← Real.exp_nat_mul, ← Real.exp_add]
      push_cast; ring_nf
    rw [e1] at h1
    calc (3 : ℝ) ^ K * edgeR P ≤ 3 ^ K * (720 * 12 ^ K * exp ((3 * A₀ + 2 * K) * ℓ)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 720 * 36 ^ K * exp ((3 * A₀ + 2 * K) * ℓ) := by
          rw [show (36 : ℝ) ^ K = 3 ^ K * 12 ^ K by rw [← mul_pow]; norm_num]; ring
  have hBm : Bmax P ≤ exp (36 * K + 1) * (720 * 78 ^ K) * exp ((3 * A₀ + 2 * K) * ℓ) := by
    have h1 := edgeR12_le P hLx (by rw [hPA]; exact hA₀.le) hY1 hBL'
    rw [hPK, hPA, hPx] at h1
    have e1 : log x ^ (3 * A₀) * log x ^ (2 * K) = exp ((3 * A₀ + 2 * K) * ℓ) := by
      rw [rpow_eq_exp_log hL0, ← hℓdef, show log x ^ (2 * K) = L ^ (2 * K) from rfl,
        hLexp, ← Real.exp_nat_mul, ← Real.exp_add]
      push_cast; ring_nf
    rw [e1] at h1
    unfold Bmax
    rw [hPK]
    calc exp (36 * (K : ℝ) + 1) * edgeR12 P ≤
        exp (36 * K + 1) * (720 * 78 ^ K * exp ((3 * A₀ + 2 * K) * ℓ)) :=
          mul_le_mul_of_nonneg_left h1 (exp_pos _).le
      _ = _ := by ring
  have hnumeric := dist_numeric (K := K) (N := P.N) (J := P.J) (r₀ := r₀) (α' := α') (G := G)
    (A₀ := A₀) (ℓ := ℓ) (bw := P.wNorm P.bVec ^ 2)
    (bs := ∑ s ∈ P.stSet, P.stWeight s * ‖P.bVec s‖) (A := A)
    (ME := √(edgeR P) * √(3 ^ P.K * edgeR P)) (Bm := Bmax P) hK hG hA₀ hN1 hJN hα' hr₀ hr₀'
    hℓ1 hℓK hℓZ hc4 hc5 (by rw [hbw]; rw [hPK] at hbsum; exact hbsum)
    (by rw [hPK] at hbsum; exact hbsum) hA1 hA (by positivity) hMEle
    ((zero_le_one).trans (one_le_Bmax P hY0.le)) hBm
  have hfinal : log x ^ (-((G - 1) * P.N)) = exp (-((G - 1) * P.N) * ℓ) := by
    rw [rpow_eq_exp_log hL0]
  rw [hfinal]
  refine hmain.trans (le_trans (le_of_eq ?_) hnumeric)
  rw [hPK]

end ArtinPrimitiveRoots.L102D
end

section
/-! Check module: `chk_norm_memMomentD_le_of_opBound_edgeOp`, the published statement `norm_memMomentD_le_of_opBound_edgeOp` verbatim, proved from the
development and the cuts `opBound_ghost_of_norm_le_ghostCoeff`, `opBound_edge_of_norm_le_edgeCoeff`, `sum_norm_edgeCoeff_mul_pow_le`. -/

namespace ArtinPrimitiveRoots

open Real

end ArtinPrimitiveRoots
end

section
open ArtinPrimitiveRoots
open Real
theorem solution (δ c₁ c₂ : ℝ) :
    ∀ G : ℝ, 0 < G → ∀ A₀ : ℝ, 0 < A₀ → ∀ K : ℕ, 1 ≤ K →
      ∀ a : Fin K → ℝ, StrictMono a → (∀ i, (0.1 : ℝ) < a i ∧ a i < 0.2) →
      (∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω → ∀ j < P.N, P.OpBound (P.edgeOp ω j) (log x ^ (-G))) →
      ∃ x₀ : ℝ, ∀ x Hm Hn : ℝ, x₀ ≤ x → x ^ δ ≤ Hm → x ^ δ ≤ Hn →
        c₁ * x ≤ Hm * Hn → Hm * Hn ≤ c₂ * x → ∀ Y : ℝ, 1 ≤ Y → ∀ k : ℕ,
          let P := dyadParams x a A₀ Y Hm Hn k
          ∀ ω, P.RootIn ω → ‖P.memMomentD ω‖ ≤ log x ^ (-((G - 1) * P.N)) :=
  L102D.distinctness_bound_ng_of_cuts δ c₁ c₂ opBound_ghost_of_norm_le_ghostCoeff
    opBound_edge_of_norm_le_edgeCoeff sum_norm_edgeCoeff_mul_pow_le
end
