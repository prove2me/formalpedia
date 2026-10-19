-- Prove2me | Definitions.Def_OAIQWSQN000
-- name    : OAIQWSQN000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:49:42.140972+00:00
-- url     : https://prove2.me/theorems/c938e1a5-655d-4c29-a2d7-f2f628dd276b
-- title:
--   OpenAI separable quotient split: definitions bundle OAIQWSQN000
-- statement:
--   One of the definitions bundles of the split of OpenAI's proof of `OAI.SeparableQuotient.negative_main`. Under the continuum hypothesis, neither the real nor the complex separable quotient assertion holds. The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/SeparableQuotients` (OpenAI, *Relative independence of the separable quotient problem*, OpenAI Math Release, September 23, 2026, result family 323, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them. Each module section starts by removing the instances `SubfieldClass.toSubringClass` and `SubringClass.toSubsemiringClass` locally, which speeds up instance search and changes nothing that is proved.
--
--   It also contains `ite_eq_left`, a lemma that newer Lean versions provide (it is `if_pos`), in the namespace `OAI.SeparableQuotient`, so that it cannot clash with another bundle.
--
--   The definitions of the published statement (`CH`, `HasSeparableQuotient`, `SQ`) come from the published bundle `Def_SeparableQuotientNegative`. It imports no other bundle of this split.
--
--   Modules: `BoundedCompleteness`, `BranchPaths`, `BranchReduction`, `CoherentClosures`, `ColorDecomposition`, `CoordinateDual`, `CoordinatePredual`, `ExactPairs`, `FiniteLp`, `LpDuality`, `MarkedEstimates`, `NormCompletion`, `NormingFamilies`, `NormingOperations`, `NormingTrees`, `Parameters`, `PartitionBlocks`, `PathCoding`, `PathConvergence`, `PathLimits`, `PathOperators`, `PathRigidity`, `PathStabilization`, `PrefixNormers`, `RealCoefficients`, `TailBlocks`, `WindowEstimates`, `WindowThinning`.
-- source:
--   OpenAI, Relative independence of the separable quotient problem, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 323; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Relative-independence-of-the-separable-quotient-problem-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/SeparableQuotients at commit adc7f12

import Mathlib

section
-- module Solutions.OAIQW_SeparableQuotient.Compat
namespace OAI.SeparableQuotient
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434


end OAI.SeparableQuotient
end

section
-- module Solutions.OAIQW_SeparableQuotient.PrefixNormers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient
open Set Metric
open scoped BigOperators Topology
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X]

@[reducible] noncomputable local instance prefixDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance prefixDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance

namespace PrefixNormers

variable {f : ℕ → StrongDual 𝕜 X}

/-- The closed linear span of the sequence. -/
def closedSpan (f : ℕ → StrongDual 𝕜 X) : Submodule 𝕜 (StrongDual 𝕜 X) :=
  (Submodule.span 𝕜 (Set.range f)).topologicalClosure

@[reducible] noncomputable local instance closedDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 (closedSpan f)) := inferInstance
@[reducible] noncomputable local instance closedDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (closedSpan f)) := inferInstance

/-- Evaluation on the closed span `G`. -/
noncomputable def evaluation (f : ℕ → StrongDual 𝕜 X) :
    X →L[𝕜] StrongDual 𝕜 (closedSpan f) :=
  (ContinuousLinearMap.precomp 𝕜 (closedSpan f).subtypeL).comp
    (NormedSpace.inclusionInDoubleDual 𝕜 X)

@[simp] lemma evaluation_apply (x : X) (v : closedSpan f) :
    evaluation f x v = (v : StrongDual 𝕜 X) x := rfl

end PrefixNormers
end SeparableQuotient

namespace SeparableQuotient
namespace PrefixNormers
universe u
variable {𝕜 : Type} [RCLike 𝕜]
variable {X : Type u} [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
variable {f : ℕ → StrongDual 𝕜 X}
@[reducible] noncomputable local instance outcomeDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance outcomeDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 X) := inferInstance
@[reducible] noncomputable local instance outcomeClosedDualNormedGroup :
    NormedAddCommGroup (StrongDual 𝕜 (closedSpan f)) := inferInstance
@[reducible] noncomputable local instance outcomeClosedDualNormedSpace :
    NormedSpace 𝕜 (StrongDual 𝕜 (closedSpan f)) := inferInstance

end PrefixNormers
end SeparableQuotient

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoherentClosures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient.CoherentClosures

open Set
universe u
variable {Γ : Type u} [LinearOrder Γ]

/-- Finite closures on the strict initial segment at β. -/
abbrev PreSystem (β : Γ) := Set.Iio β → ℕ → Finset Γ

/-- Coherence conditions below β. -/
structure PreGood (β : Γ) (G : PreSystem β) : Prop where
  lower : ∀ (a : Set.Iio β) n, ∀ x ∈ G a n, x ≤ a.val
  self : ∀ (a : Set.Iio β) n, a.val ∈ G a n
  mono : ∀ a : Set.Iio β, Monotone (G a)
  exhaust : ∀ (a : Set.Iio β) x, x ≤ a.val → ∃ n, x ∈ G a n
  coherent : ∀ (a b : Set.Iio β) n, b.val ∈ G a n →
    G b n = (G a n).filter (fun x => x ≤ b.val)

/-- The closure conditions at a new endpoint, relative to earlier closures. -/
structure ExtensionGood (β : Γ) (G : PreSystem β) (H : ℕ → Finset Γ) : Prop where
  lower : ∀ n, ∀ x ∈ H n, x ≤ β
  self : ∀ n, β ∈ H n
  mono : Monotone H
  exhaust : ∀ x, x ≤ β → ∃ n, x ∈ H n
  coherent : ∀ (a : Set.Iio β) n, a.val ∈ H n →
    G a n = (H n).filter (fun x => x ≤ a.val)

/-- A threshold beyond which two specified earlier coordinates are recorded. -/
lemma exists_next_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (a b : Set.Iio β) (p : ℕ) :
    ∃ q > p, a.val ∈ G (max a b) q ∧ b.val ∈ G (max a b) q := by
  obtain ⟨i, hi⟩ := hg.exhaust (max a b) a.val (le_max_left _ _)
  obtain ⟨j, hj⟩ := hg.exhaust (max a b) b.val (le_max_right _ _)
  refine ⟨max (max i j) (p + 1), ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le (Nat.lt_succ_self p) (le_max_right _ _)
  · exact hg.mono (max a b) (le_trans (le_max_left _ _) (le_max_left _ _)) hi
  · exact hg.mono (max a b) (le_trans (le_max_right _ _) (le_max_left _ _)) hj

/-- Each stage of the endpoint construction keeps one earlier endpoint and an
activation threshold. The next endpoint is the maximum of the old endpoint
and the next enumerated predecessor. -/
noncomputable def stage {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : ℕ → Set.Iio β × ℕ
  | 0 => (e 0, 0)
  | n+1 => let v := stage hg e n
    (max v.1 (e (n+1)), (exists_next_threshold hg v.1 (e (n+1)) v.2).choose)

lemma stage_zero {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : stage hg e 0 = (e 0, 0) := rfl

lemma stage_succ_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) :
    (stage hg e n).2 < (stage hg e (n+1)).2 ∧
    (stage hg e n).1.val ∈ G (stage hg e (n+1)).1 (stage hg e (n+1)).2 ∧
    (e (n+1)).val ∈ G (stage hg e (n+1)).1 (stage hg e (n+1)).2 := by
  exact (exists_next_threshold hg (stage hg e n).1 (e (n+1))
    (stage hg e n).2).choose_spec

lemma stage_threshold_strictMono {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : StrictMono (fun n => (stage hg e n).2) :=
  strictMono_nat_of_lt_succ fun n => (stage_succ_threshold hg e n).1

lemma stage_threshold_ge {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) : n ≤ (stage hg e n).2 :=
  (stage_threshold_strictMono hg e).id_le n

/-- The last activated stage at parameter p. -/
noncomputable def active {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : ℕ :=
  Nat.findGreatest (fun n => (stage hg e n).2 ≤ p) p

lemma active_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : (stage hg e (active hg e p)).2 ≤ p := by
  exact Nat.findGreatest_spec (P := fun n => (stage hg e n).2 ≤ p)
    (Nat.zero_le p) (show (stage hg e 0).2 ≤ p from Nat.zero_le p)

lemma stage_le_active {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) {n p : ℕ} (h : (stage hg e n).2 ≤ p) :
    n ≤ active hg e p :=
  Nat.le_findGreatest (le_trans (stage_threshold_ge hg e n) h) h

lemma active_mono {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) : Monotone (active hg e) := by
  intro p q hpq
  exact stage_le_active hg e (le_trans (active_threshold hg e p) hpq)

lemma active_at_threshold {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n : ℕ) : active hg e (stage hg e n).2 = n := by
  apply le_antisymm
  · exact (stage_threshold_strictMono hg e).le_iff_le.mp (active_threshold hg e _)
  · exact stage_le_active hg e le_rfl

/-- Earlier stage closures embed in later ones once the later stage is active. -/
lemma stage_subset_succ {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (n p : ℕ) (hp : (stage hg e (n+1)).2 ≤ p) :
    G (stage hg e n).1 p ⊆ G (stage hg e (n+1)).1 p := by
  have hm := hg.mono (stage hg e (n+1)).1 hp (stage_succ_threshold hg e n).2.1
  rw [hg.coherent (stage hg e (n+1)).1 (stage hg e n).1 p hm]
  exact Finset.filter_subset _ _

lemma stage_subset {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) {n m p : ℕ} (hnm : n ≤ m)
    (hp : (stage hg e m).2 ≤ p) : G (stage hg e n).1 p ⊆ G (stage hg e m).1 p := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m hnm ih =>
    apply Finset.Subset.trans (ih ((stage_threshold_strictMono hg e).monotone
      (Nat.le_succ m) |>.trans hp))
    exact stage_subset_succ hg e m p hp

/-- The new closure: keep the activated earlier closure and append β. -/
noncomputable def extended {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (p : ℕ) : Finset Γ :=
  insert β (G (stage hg e (active hg e p)).1 p)

lemma extended_good {β : Γ} {G : PreSystem β} (hg : PreGood β G)
    (e : ℕ → Set.Iio β) (he : Function.Surjective e) :
    ExtensionGood β G (extended hg e) := by
  classical
  constructor
  · intro n x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact (hg.lower _ _ _ hx).trans (stage hg e (active hg e n)).1.property.le
  · intro n
    exact Finset.mem_insert_self _ _
  · intro p q hpq
    apply Finset.insert_subset_insert
    exact (hg.mono _ hpq).trans
      (stage_subset hg e (active_mono hg e hpq) (active_threshold hg e q))
  · intro x hx
    rcases lt_or_eq_of_le hx with hx | rfl
    · obtain ⟨i, hi⟩ := he ⟨x, hx⟩
      refine ⟨(stage hg e i).2, Finset.mem_insert_of_mem ?_⟩
      rw [active_at_threshold]
      cases i with
      | zero => simpa [stage_zero, hi] using hg.self (e 0) 0
      | succ i => simpa only [hi] using (stage_succ_threshold hg e i).2.2
    · exact ⟨0, Finset.mem_insert_self _ _⟩
  · intro a n ha
    have hab : a.val ≠ β := ne_of_lt a.property
    have ha' := (Finset.mem_insert.mp ha).resolve_left hab
    rw [hg.coherent _ a n ha']
    apply Finset.ext
    intro x
    simp only [extended, Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hxa⟩; exact ⟨Or.inr hx, hxa⟩
    · rintro ⟨rfl | hx, hxa⟩
      · exact (not_le_of_gt a.property hxa).elim
      · exact ⟨hx, hxa⟩

/-- Empty strict segments require no recursive information. -/
lemma singleton_good {β : Γ} {G : PreSystem β} (h : IsEmpty (Set.Iio β)) :
    ExtensionGood β G (fun _ => {β}) := by
  classical
  constructor
  · intro n x hx; exact (Finset.mem_singleton.mp hx).le
  · intro n; simp
  · intro p q hpq; exact le_rfl
  · intro x hx
    have he : x = β := (lt_or_eq_of_le hx).resolve_left fun hlt => h.false ⟨x, hlt⟩
    subst x; exact ⟨0, by simp⟩
  · intro a; exact h.false a |>.elim

/-- Countability of the strict segment suffices to extend the coherent system. -/
lemma exists_extension {β : Γ} [Countable (Set.Iio β)]
    {G : PreSystem β} (hg : PreGood β G) :
    ∃ H : ℕ → Finset Γ, ExtensionGood β G H := by
  classical
  cases isEmpty_or_nonempty (Set.Iio β) with
  | inl h => exact ⟨fun _ => {β}, singleton_good h⟩
  | inr h =>
    let := h
    obtain ⟨e, he⟩ := exists_surjective_nat (Set.Iio β)
    exact ⟨extended hg e, extended_good hg e he⟩

/-- Full endpoint property for a total system. -/
structure GoodAt (F : Γ → ℕ → Finset Γ) (β : Γ) : Prop where
  lower : ∀ n, ∀ x ∈ F β n, x ≤ β
  self : ∀ n, β ∈ F β n
  mono : Monotone (F β)
  exhaust : ∀ x, x ≤ β → ∃ n, x ∈ F β n
  coherent : ∀ α n, α ∈ F β n → F α n = (F β n).filter (fun x => x ≤ α)

variable [WellFoundedLT Γ] [∀ β : Γ, Countable (Set.Iio β)]

/-- The recursion step is defined even on bad predecessor data; the bad branch
is never used in the well-founded construction. -/
noncomputable def next (β : Γ) (G : PreSystem β) : ℕ → Finset Γ := by
  classical
  exact if h : PreGood β G then (exists_extension h).choose else fun _ => {β}

omit [WellFoundedLT Γ] in
lemma next_good (β : Γ) (G : PreSystem β) (h : PreGood β G) :
    ExtensionGood β G (next β G) := by
  classical
  rw [next, dite_eq_left h]
  exact (exists_extension h).choose_spec

/-- The actual coherently nested finite closures on the well-order. -/
noncomputable def system : Γ → ℕ → Finset Γ :=
  WellFounded.fix wellFounded_lt fun β rec => next β (fun a => rec a.val a.property)

lemma system_eq (β : Γ) : system β = next β (fun a => system a.val) := by
  rw [system, WellFounded.fix_eq]

/-- Transfinite induction establishes the coherent closure properties. -/
theorem system_goodAt (β : Γ) : GoodAt system β := by
  classical
  refine (wellFounded_lt : WellFounded ((· < ·) : Γ → Γ → Prop)).induction β ?_
  intro β ih
  have hg : PreGood β (fun a => system a.val) := by
    constructor
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).lower
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).self
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).mono
    · intro a; exact (ih a.val (Set.mem_Iio.mp a.property)).exhaust
    · intro a b n hb; exact (ih a.val (Set.mem_Iio.mp a.property)).coherent b.val n hb
  have he := next_good β (fun a => system a.val) hg
  rw [← system_eq] at he
  refine ⟨he.lower, he.self, he.mono, he.exhaust, ?_⟩
  intro α n hα
  rcases lt_or_eq_of_le (he.lower n α hα) with hlt | rfl
  · exact he.coherent ⟨α, hlt⟩ n hα
  · exact (Finset.filter_eq_self.mpr fun x hx => he.lower n x hx).symm

end SeparableQuotient.CoherentClosures

namespace SeparableQuotient.CoherentClosures

open Set

/-- The coordinate set of the negative construction is really ω₁. -/
abbrev OmegaOne := (Cardinal.aleph 1).ord.ToType

instance omegaOne_initialSegment_countable (β : OmegaOne) : Countable (Set.Iio β) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  apply Cardinal.lt_aleph_one_iff.mp
  have h := Cardinal.mk_Iio_lt β (by simp [OmegaOne])
  simpa [OmegaOne] using h

/-- Positive-indexed finite closures. -/
noncomputable def F (β : OmegaOne) (p : ℕ) : Finset OmegaOne :=
  system β (p - 1)

lemma F_mono (β : OmegaOne) : Monotone (F β) := by
  intro p q hpq
  exact (system_goodAt β).mono (Nat.sub_le_sub_right hpq 1)

lemma F_coherent (β α : OmegaOne) (p : ℕ) (h : α ∈ F β p) :
    F α p = (F β p).filter (fun x => x ≤ α) :=
  (system_goodAt β).coherent α (p - 1) h

/-- Two closures containing α have the same ordered initial segment through α. -/
lemma shared_initial_segment (β γ α : OmegaOne) (p : ℕ)
    (hβ : α ∈ F β p) (hγ : α ∈ F γ p) :
    (F β p).filter (fun x => x ≤ α) = (F γ p).filter (fun x => x ≤ α) := by
  rw [← F_coherent β α p hβ, ← F_coherent γ α p hγ]

/-- The first positive parameter at which α enters the closure of β. The
irrelevant case α > β is set to zero. -/
noncomputable def rho (α β : OmegaOne) : ℕ := by
  classical
  exact if h : α ≤ β then Nat.find ((system_goodAt β).exhaust α h) + 1 else 0

lemma mem_F_rho (α β : OmegaOne) (h : α ≤ β) : α ∈ F β (rho α β) := by
  classical
  simp only [rho, dite_eq_left h, F, Nat.add_sub_cancel]
  exact Nat.find_spec ((system_goodAt β).exhaust α h)

lemma rho_le_iff (α β : OmegaOne) (h : α ≤ β) (p : ℕ) (hp : 1 ≤ p) :
    rho α β ≤ p ↔ α ∈ F β p := by
  classical
  constructor
  · intro hr
    exact F_mono β hr (mem_F_rho α β h)
  · intro ha
    have hn := Nat.find_min' ((system_goodAt β).exhaust α h) ha
    simp only [rho, dite_eq_left h]
    omega

end SeparableQuotient.CoherentClosures

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathCoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

namespace SeparableQuotient.PathCoding

open CoherentClosures

section OrderedArray
variable {Γ : Type*} [LinearOrder Γ]

/-- Position of a coordinate in an ordered finite closure; no ordinal label is
stored in the code. -/
def position (s : Finset Γ) (x : Γ) : ℕ := (s.filter (· < x)).card

lemma position_strictMonoOn (s : Finset Γ) : StrictMonoOn (position s) s := by
  intro x hx y _ hxy
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, hz.2.trans hxy⟩
  · intro heq
    have h : x ∈ s.filter (· < y) := Finset.mem_filter.mpr ⟨hx, hxy⟩
    rw [← heq] at h
    exact (lt_irrefl x) (Finset.mem_filter.mp h).2

lemma position_inj {s : Finset Γ} {x y : Γ} (hx : x ∈ s) (hy : y ∈ s)
    (h : position s x = position s y) : x = y :=
  (position_strictMonoOn s).injOn hx hy h

lemma position_align {s t : Finset Γ} {a x : Γ}
    (h : s.filter (· ≤ a) = t.filter (· ≤ a)) (hx : x ≤ a) :
    position s x = position t x := by
  unfold position
  congr 1
  ext z
  constructor <;> intro hz
  · obtain ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
    have hz' : z ∈ s.filter (· ≤ a) :=
      Finset.mem_filter.mpr ⟨hz, hzx.le.trans hx⟩
    rw [h] at hz'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz').1, hzx⟩
  · obtain ⟨hz, hzx⟩ := Finset.mem_filter.mp hz
    have hz' : z ∈ t.filter (· ≤ a) :=
      Finset.mem_filter.mpr ⟨hz, hzx.le.trans hx⟩
    rw [← h] at hz'
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz').1, hzx⟩

/-- A zero-filled rational array recorded by order positions, including zero values. -/
def arrayCode (s : Finset Γ) (f : Γ →₀ ℚ) : Finset (ℕ × ℚ) :=
  s.image (fun x => (position s x, f x))

lemma arrayCode_match {s t : Finset Γ} {f g : Γ →₀ ℚ}
    (h : arrayCode s f = arrayCode t g) {x : Γ} (hx : x ∈ s) :
    ∃ y ∈ t, position s x = position t y ∧ f x = g y := by
  have hm : (position s x, f x) ∈ arrayCode s f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
  rw [h] at hm
  obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp hm
  exact ⟨y, hy, (congrArg Prod.fst heq).symm, (congrArg Prod.snd heq).symm⟩

/-- Position alignment from equal compressed arrays and a shared initial segment. -/
lemma position_alignment {s t : Finset Γ} {a : Γ} {f g : Γ →₀ ℚ}
    (hst : s.filter (· ≤ a) = t.filter (· ≤ a))
    (hf : f.support ⊆ s) (hg : g.support ⊆ t)
    (hfa : ∀ x ∈ f.support, x < a)
    (hcode : arrayCode s f = arrayCode t g) : f = g := by
  have align : ∀ x ∈ s, x ≤ a → x ∈ t ∧ position s x = position t x := by
    intro x hx hxa
    have hm : x ∈ s.filter (· ≤ a) := Finset.mem_filter.mpr ⟨hx, hxa⟩
    rw [hst] at hm
    exact ⟨(Finset.mem_filter.mp hm).1, position_align hst hxa⟩
  have nonzero_align : ∀ x, f x ≠ 0 → f x = g x := by
    intro x hx
    have hfx : x ∈ f.support := Finsupp.mem_support_iff.mpr hx
    obtain ⟨y, hy, hpos, hval⟩ := arrayCode_match hcode (hf hfx)
    obtain ⟨hxt, hpxt⟩ := align x (hf hfx) (hfa x hfx).le
    have heq : x = y := position_inj hxt hy (hpxt.symm.trans hpos)
    simpa [heq] using hval
  ext x
  by_cases hfx : f x = 0
  · by_cases hgx : g x = 0
    · simp [hfx, hgx]
    obtain ⟨y, hy, hpos, hval⟩ := arrayCode_match hcode.symm
      (hg (Finsupp.mem_support_iff.mpr hgx))
    have hfy : f y ≠ 0 := by simpa [← hval] using hgx
    have hys : y ∈ f.support := Finsupp.mem_support_iff.mpr hfy
    obtain ⟨hyt, hpyt⟩ := align y hy (hfa y hys).le
    have heq : x = y := position_inj (hg (Finsupp.mem_support_iff.mpr hgx)) hyt
      (hpos.trans hpyt)
    exact (hfy (heq ▸ hfx)).elim
  · exact nonzero_align x hfx

end OrderedArray
end SeparableQuotient.PathCoding

namespace SeparableQuotient.PathCoding

open CoherentClosures

abbrev Code := List (ℕ × ℕ × Finset (ℕ × ℚ))

def codeBound : Code → ℕ
  | [] => 0
  | x :: xs => max x.2.1 (codeBound xs)

lemma metadata_le_codeBound {c : Code} {x : ℕ × ℕ × Finset (ℕ × ℚ)}
    (hx : x ∈ c) : x.2.1 ≤ codeBound c := by
  induction c with
  | nil => simp at hx
  | cons y ys ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst x
      exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- An injective code greater than every entry of its final metadata. -/
noncomputable def sigma (c : Code) : ℕ := Nat.pair (Encodable.encode c) (codeBound c + 1)

lemma sigma_injective : Function.Injective sigma := by
  intro c d h
  exact Encodable.encode_injective (Nat.pair_eq_pair.mp h).1

lemma codeBound_lt_sigma (c : Code) : codeBound c < sigma c :=
  (Nat.lt_succ_self _).trans_le (Nat.right_le_pair _ _)

/-- Raw infinite path data, retaining the actual rational pieces, declared
weights and metadata. Nonzero pieces are included here to define the prefix
endpoint without arbitrary defaults. Type-I membership is not needed for the
combinatorial rigidity theorem. -/
@[ext] structure RawPath where
  piece : ℕ → OmegaOne →₀ ℚ
  weight : ℕ → ℕ
  metadata : ℕ → ℕ
  nonzero : ∀ i, piece i ≠ 0

namespace RawPath

noncomputable def support (P : RawPath) (n : ℕ) : Finset OmegaOne :=
  (Finset.range (n+1)).biUnion (fun i => (P.piece i).support)

lemma mem_support_iff (P : RawPath) (n : ℕ) (a : OmegaOne) :
    a ∈ P.support n ↔ ∃ i ≤ n, a ∈ (P.piece i).support := by
  classical
  simp only [support, Finset.mem_biUnion, Finset.mem_range, Nat.lt_succ_iff]

lemma piece_support_subset (P : RawPath) {i n : ℕ} (hi : i ≤ n) :
    (P.piece i).support ⊆ P.support n := by
  intro a ha
  exact (P.mem_support_iff n a).mpr ⟨i, hi, ha⟩

lemma support_nonempty (P : RawPath) (n : ℕ) : (P.support n).Nonempty := by
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (P.nonzero n)
  exact ⟨a, P.piece_support_subset le_rfl ha⟩

noncomputable def endpoint (P : RawPath) (n : ℕ) : OmegaOne :=
  (P.support n).max' (P.support_nonempty n)

lemma endpoint_mem (P : RawPath) (n : ℕ) : P.endpoint n ∈ P.support n :=
  Finset.max'_mem _ _

lemma le_endpoint (P : RawPath) {n : ℕ} {a : OmegaOne} (ha : a ∈ P.support n) :
    a ≤ P.endpoint n := Finset.le_max' _ _ ha

noncomputable def closure (P : RawPath) (n : ℕ) : Finset OmegaOne :=
  F (P.endpoint n) (P.metadata n)

noncomputable def code (P : RawPath) (n : ℕ) : Code :=
  List.ofFn (fun i : Fin (n+1) =>
    (P.weight i, P.metadata i, arrayCode (P.closure n) (P.piece i)))

lemma code_length (P : RawPath) (n : ℕ) : (P.code n).length = n+1 :=
  List.length_ofFn

lemma code_eq_length {P Q : RawPath} {n m : ℕ} (h : P.code n = Q.code m) : n = m := by
  have h' := congrArg List.length h
  simpa only [code_length, Nat.add_right_cancel_iff] using h'

lemma code_eq_at {P Q : RawPath} {n : ℕ} (h : P.code n = Q.code n)
    (i : ℕ) (hi : i ≤ n) :
    P.weight i = Q.weight i ∧ P.metadata i = Q.metadata i ∧
      arrayCode (P.closure n) (P.piece i) = arrayCode (Q.closure n) (Q.piece i) := by
  have heq := congrFun (List.ofFn_injective h) ⟨i, Nat.lt_succ_iff.mpr hi⟩
  exact ⟨congrArg Prod.fst heq, congrArg (fun x => x.2.1) heq,
    congrArg (fun x => x.2.2) heq⟩

lemma metadata_le_codeBound (P : RawPath) (n : ℕ) : P.metadata n ≤ codeBound (P.code n) := by
  apply PathCoding.metadata_le_codeBound (x :=
    (P.weight n, P.metadata n, arrayCode (P.closure n) (P.piece n)))
  exact List.mem_ofFn.mpr ⟨⟨n, by omega⟩, rfl⟩

/-- Exact support, succession, weight and metadata conditions of a path. The
Type-I construction contributes only additional restrictions, not needed below. -/
structure Admissible (P : RawPath) : Prop where
  successive : ∀ i j, i < j → ∀ a ∈ (P.piece i).support,
    ∀ b ∈ (P.piece j).support, a < b
  metadata_strict : StrictMono P.metadata
  metadata_pos : ∀ i, 1 ≤ P.metadata i
  weight_pos : ∀ i, 1 ≤ P.weight i
  weight_le_metadata : ∀ i, P.weight i ≤ P.metadata i
  rho_bound : ∀ n a b, a ∈ P.support n → b ∈ P.support n → a ≤ b →
    rho a b ≤ P.metadata n
  rule : ∀ n, P.weight (n+1) = sigma (P.code n)

lemma Admissible.support_subset_closure {P : RawPath} (hP : P.Admissible) (n : ℕ) :
    P.support n ⊆ P.closure n := by
  intro a ha
  exact (rho_le_iff a (P.endpoint n) (P.le_endpoint ha) _ (hP.metadata_pos n)).mp
    (hP.rho_bound n a (P.endpoint n) ha (P.endpoint_mem n) (P.le_endpoint ha))

lemma Admissible.piece_support_subset_closure {P : RawPath} (hP : P.Admissible)
    {i n : ℕ} (hi : i ≤ n) : (P.piece i).support ⊆ P.closure n :=
  (P.piece_support_subset hi).trans (hP.support_subset_closure n)

lemma Admissible.weight_strict {P : RawPath} (hP : P.Admissible) : StrictMono P.weight := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [hP.rule n]
  exact (hP.weight_le_metadata n).trans_lt
    ((P.metadata_le_codeBound n).trans_lt (codeBound_lt_sigma _))

end RawPath
end SeparableQuotient.PathCoding

namespace SeparableQuotient.PathCoding.RawPath

open CoherentClosures

lemma Admissible.large_matching_prefix {P Q : RawPath} (hP : P.Admissible) (hQ : Q.Admissible)
    (hinf : (Set.range P.weight ∩ Set.range Q.weight).Infinite) (N : ℕ) :
    ∃ n ≥ N, P.code n = Q.code n := by
  obtain ⟨w, ⟨⟨k, hk⟩, ⟨l, hl⟩⟩, hw⟩ :=
    hinf.exists_gt (max (P.weight (N+1)) (Q.weight 0))
  have hk' : N+1 < k := hP.weight_strict.lt_iff_lt.mp
    (by rw [hk]; exact (le_max_left _ _).trans_lt hw)
  have hl' : 0 < l := hQ.weight_strict.lt_iff_lt.mp
    (by rw [hl]; exact (le_max_right _ _).trans_lt hw)
  have hcode : P.code (k-1) = Q.code (l-1) := by
    apply sigma_injective
    rw [← hP.rule, ← hQ.rule]
    have hk'' : k-1+1 = k := by omega
    have hl'' : l-1+1 = l := by omega
    rw [hk'', hl'', hk, hl]
  have heq := code_eq_length hcode
  refine ⟨k-1, by omega, ?_⟩
  simpa only [← heq] using hcode

/-- The support of P is order-cofinal below that of Q. -/
def SupportBelow (P Q : RawPath) : Prop :=
  ∀ i a, a ∈ (P.piece i).support →
    ∃ j b, b ∈ (Q.piece j).support ∧ a ≤ b

lemma supportBelow_total (P Q : RawPath) : P.SupportBelow Q ∨ Q.SupportBelow P := by
  classical
  by_cases h : P.SupportBelow Q
  · exact Or.inl h
  · right
    simp only [SupportBelow, not_forall, not_exists, not_and, not_le] at h
    obtain ⟨i, a, ha, h⟩ := h
    intro j b hb
    exact ⟨i, a, ha, (h j b hb).le⟩

lemma Admissible.eq_of_infinite_shared_weights_of_supportBelow {P Q : RawPath}
    (hP : P.Admissible) (hQ : Q.Admissible)
    (hinf : (Set.range P.weight ∩ Set.range Q.weight).Infinite)
    (hPQ : P.SupportBelow Q) : P = Q := by
  apply RawPath.ext
  · funext i
    obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (P.nonzero (i+1))
    obtain ⟨k, b, hb, hab⟩ := hPQ (i+1) a ha
    obtain ⟨n, hn, hcode⟩ := hP.large_matching_prefix hQ hinf (max (i+1) (max k (rho a b)))
    have hin : i ≤ n := by omega
    have hin' : i+1 ≤ n := (le_max_left _ _).trans hn
    have hkn : k ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
    have hrn : rho a b ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
    have hmeta := (code_eq_at hcode n le_rfl).2.1
    have haP : a ∈ P.closure n := hP.piece_support_subset_closure hin' ha
    have hbQ : b ∈ Q.closure n := hQ.piece_support_subset_closure hkn hb
    have haB : a ∈ F b (Q.metadata n) :=
      (rho_le_iff a b hab _ (hQ.metadata_pos n)).mp
        (hrn.trans (hQ.metadata_strict.id_le n))
    have haQ : a ∈ Q.closure n := by
      rw [F_coherent (Q.endpoint n) b (Q.metadata n) hbQ] at haB
      exact (Finset.mem_filter.mp haB).1
    apply position_alignment (a := a)
      (show (P.closure n).filter (· ≤ a) = (Q.closure n).filter (· ≤ a) from ?_)
      (hP.piece_support_subset_closure hin) (hQ.piece_support_subset_closure hin)
      (fun x hx => hP.successive i (i+1) (by omega) x hx a ha)
      (code_eq_at hcode i hin).2.2
    unfold closure at haP ⊢
    rw [hmeta] at haP ⊢
    exact shared_initial_segment (P.endpoint n) (Q.endpoint n) a (Q.metadata n) haP haQ
  · funext i
    obtain ⟨n, hin, hcode⟩ := hP.large_matching_prefix hQ hinf i
    exact (code_eq_at hcode i hin).1
  · funext i
    obtain ⟨n, hin, hcode⟩ := hP.large_matching_prefix hQ hinf i
    exact (code_eq_at hcode i hin).2.1

/-- Distinct admissible paths have only finitely many shared weights. -/
lemma Admissible.eq_of_infinite_shared_weights {P Q : RawPath}
    (hP : P.Admissible) (hQ : Q.Admissible)
    (hinf : (Set.range P.weight ∩ Set.range Q.weight).Infinite) : P = Q := by
  rcases supportBelow_total P Q with h | h
  · exact hP.eq_of_infinite_shared_weights_of_supportBelow hQ hinf h
  · exact (hQ.eq_of_infinite_shared_weights_of_supportBelow hP
      (by simpa only [Set.inter_comm] using hinf) h).symm

lemma Admissible.shared_weights_finite {P Q : RawPath}
    (hP : P.Admissible) (hQ : Q.Admissible) (hne : P ≠ Q) :
    (Set.range P.weight ∩ Set.range Q.weight).Finite := by
  by_contra hinf
  exact hne (hP.eq_of_infinite_shared_weights hQ hinf)

end SeparableQuotient.PathCoding.RawPath

namespace SeparableQuotient.PathCoding.RawPath

/-- A common finite deletion makes the weights of a finite collection of
pairwise distinct paths disjoint. This is the combinatorial input to the
Type-II tail estimate and the quotient-space path map. -/
lemma Admissible.disjoint_weight_tails {ι : Type*} [Fintype ι] (P : ι → RawPath)
    (hP : ∀ i, (P i).Admissible) (hinj : Function.Injective P) :
    ∃ N : ℕ, Pairwise (fun i j => Disjoint
      (Set.range (fun n => (P i).weight (n+N)))
      (Set.range (fun n => (P j).weight (n+N)))) := by
  classical
  have hbound : ∀ i j : ι, ∃ B : ℕ,
      i ≠ j → ∀ n m, (P i).weight n = (P j).weight m → n ≤ B := by
    intro i j
    by_cases hij : i = j
    · exact ⟨0, fun h => (h hij).elim⟩
    · have hfin := (hP i).shared_weights_finite (hP j) (hinj.ne hij)
      obtain ⟨B, hB⟩ := hfin.bddAbove
      refine ⟨B, fun _ n m heq => ?_⟩
      exact ((hP i).weight_strict.id_le n).trans
        (hB ⟨⟨n, rfl⟩, ⟨m, heq.symm⟩⟩)
  choose B hB using hbound
  let N := (Finset.univ : Finset (ι × ι)).sup (fun ij => B ij.1 ij.2) + 1
  refine ⟨N, ?_⟩
  intro i j hij
  apply Set.disjoint_left.mpr
  rintro w ⟨n, hn⟩ ⟨m, hm⟩
  have hnB := hB i j hij (n+N) (m+N) (hn.trans hm.symm)
  have hBN : B i j < N := Nat.lt_succ_of_le
    (Finset.le_sup (f := fun ij : ι × ι => B ij.1 ij.2) (Finset.mem_univ (i,j)))
  omega

end SeparableQuotient.PathCoding.RawPath

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- Admissible parameters for the pure s = k + 2 families and mixed s = 2 family, with q = (s + 1) / s. Integer powers avoid rounding noninteger powers. -/
namespace SeparableQuotient.Parameters

open Filter Topology

def d (n : ℕ) : ℕ := n+11

/-- State stores the exponent scale and twice the sum of all earlier lengths. -/
def state (s : ℕ) : ℕ → ℕ × ℕ
  | 0 => ((d 0 + 1) + 1 + d 0 + (d 0)^2, 0)
  | n+1 =>
    let old := state s n
    let B := old.2 + 2 * 2^(s*(s+1)*old.1)
    (old.1 + (B+1)*(d (n+1)+1) + 1 + d (n+1) + (d (n+1))^2, B)

def t (s n : ℕ) : ℕ := (state s n).1
def B (s n : ℕ) : ℕ := (state s n).2
def L (s n : ℕ) : ℕ := 2^(s*(s+1)*t s n)
def m (s n : ℕ) : ℕ := 2^((s-1)*(s+1)*t s n+d n)
def r (s : ℕ) : ℝ := (s:ℝ)/((s:ℝ)-1)
def q (s : ℕ) : ℝ := ((s:ℝ)+1)/(s:ℝ)
def theta (s n : ℕ) : ℝ := (L s n : ℝ) ^ (1/r s) / (m s n : ℝ)

lemma m_pos (s n : ℕ) : 0 < m s n := pow_pos (by omega) _

lemma theta_numerator {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    (L s n : ℝ) ^ (1/r s) = (2:ℝ)^((s-1)*(s+1)*t s n) := by
  have hs0 : (s:ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have hs1 : 1 ≤ s := by omega
  simp only [L, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  simp only [r, one_div_div, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    Nat.cast_sub hs1]
  field_simp

lemma theta_eq {s : ℕ} (hs : 2 ≤ s) (n : ℕ) : theta s n = (1/2:ℝ)^(d n) := by
  rw [theta, theta_numerator hs]
  simp only [m]
  push_cast
  rw [pow_add, div_mul_eq_div_div, div_self (by positivity : (2:ℝ)^((s-1)*(s+1)*t s n) ≠ 0)]
  exact (one_div_pow _ _).symm

lemma hasSum_theta {s : ℕ} (hs : 2 ≤ s) :
    HasSum (theta s) (1/1024:ℝ) := by
  have hgeom : HasSum (fun n : ℕ => (1/2:ℝ)^n) 2 := by
    convert hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) < 1) using 1; norm_num
  have h := hgeom.mul_left ((1/2:ℝ)^11)
  have h' : HasSum (theta s) ((1/2:ℝ)^11*2) := h.congr_fun (by
    intro n
    rw [theta_eq hs, d, pow_add, mul_comm])
  norm_num at h' ⊢
  exact h'

lemma theta_sum_small {s : ℕ} (hs : 2 ≤ s) : ∑' n, theta s n < (1/8:ℝ) := by
  rw [(hasSum_theta hs).tsum_eq]
  norm_num

lemma reciprocal_le_theta {s : ℕ} (hs : 2 ≤ s) (n : ℕ) :
    1/(m s n:ℝ) ≤ theta s n := by
  rw [theta, theta_numerator hs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact one_le_pow₀ (by norm_num)

lemma reciprocal_sum_small {s : ℕ} (hs : 2 ≤ s) :
    ∑' n, 1/(m s n:ℝ) < (1/8:ℝ) := by
  have hsum := (hasSum_theta hs).summable
  have hrecip : Summable (fun n => 1/(m s n:ℝ)) :=
    Summable.of_nonneg_of_le (fun n => by positivity) (reciprocal_le_theta hs) hsum
  exact (Summable.tsum_le_tsum (reciprocal_le_theta hs) hrecip hsum).trans_lt
    (theta_sum_small hs)

lemma s_r_conjugate {s : ℕ} (hs : 2 ≤ s) : Real.HolderConjugate (s:ℝ) (r s) :=
  Real.HolderConjugate.conjExponent (by exact_mod_cast (by omega : 1 < s))

lemma sNext_q_conjugate {s : ℕ} (hs : 2 ≤ s) : Real.HolderConjugate ((s:ℝ)+1) (q s) := by
  have hs0 : (0:ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have h := Real.HolderConjugate.conjExponent (p := (s:ℝ)+1) (by linarith)
  simpa only [Real.conjExponent, add_sub_cancel_right, q] using h

lemma q_bounds {s : ℕ} (hs : 2 ≤ s) :
    1 < q s ∧ q s < r s ∧ r s < (s:ℝ)+1 ∧ 1/((s:ℝ)+1) < 1/(s:ℝ) := by
  have hsR : (2:ℝ) ≤ s := by exact_mod_cast hs
  have hs0 : (0:ℝ) < s := by linarith
  have hs1 : (0:ℝ) < (s:ℝ)-1 := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [q, lt_div_iff₀ hs0]; linarith
  · rw [q, r, div_lt_div_iff₀ hs0 hs1]; nlinarith
  · rw [r, div_lt_iff₀ hs1]; nlinarith
  · exact one_div_lt_one_div_of_lt hs0 (by linarith)

end SeparableQuotient.Parameters

namespace SeparableQuotient.Colors
open CoherentClosures

/-- A partition of ω₁ into countably many unbounded fibers. -/
def partitionEquiv : OmegaOne.{0} ≃ ℕ × OmegaOne.{0} :=
  Classical.choice (Cardinal.eq.mp (by
    simp only [OmegaOne, Cardinal.mk_prod, Cardinal.lift_id, Cardinal.mk_nat,
      Cardinal.mk_ord_toType, Cardinal.aleph0_mul_aleph]))

def color (a : OmegaOne.{0}) : ℕ := (partitionEquiv a).1

def inColor (k : ℕ) (a : OmegaOne.{0}) : OmegaOne.{0} := partitionEquiv.symm (k, a)

@[simp] lemma color_inColor (k : ℕ) (a : OmegaOne.{0}) : color (inColor k a) = k := by
  simp [color, inColor]

lemma inColor_injective (k : ℕ) : Function.Injective (inColor k) := by
  intro a b h
  have := partitionEquiv.symm.injective h
  exact (Prod.mk.inj this).2

end SeparableQuotient.Colors

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open CoherentClosures PathCoding
open scoped ENNReal Classical
abbrev Γ := OmegaOne.{0}
abbrev Array := Γ →₀ ℚ

inductive Family where
  | pure : ℕ → Family
  | mixed : Family
  deriving DecidableEq

def Family.s : Family → ℕ
  | .pure k => k+2
  | .mixed => 2

lemma Family.s_ge_two (f : Family) : 2 ≤ f.s := by cases f <;> simp [Family.s]

def Family.q (f : Family) : ℝ := Parameters.q f.s

def Family.L (f : Family) (j : ℕ) : ℕ := Parameters.L f.s (j-1)
def Family.m (f : Family) (j : ℕ) : ℕ := Parameters.m f.s (j-1)

lemma Family.m_pos (f : Family) (j : ℕ) : 0 < f.m j := Parameters.m_pos _ _

/-- Succession refers to the full supports, in both orders in mixed mode. -/
def Successive (f : Family) (x y : Array) : Prop :=
  ∀ a ∈ x.support, ∀ b ∈ y.support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)

lemma Successive.disjoint {f : Family} {x y : Array} (h : Successive f x y) :
    Disjoint x.support y.support := by
  apply Finset.disjoint_left.mpr
  intro a hx hy
  exact (lt_irrefl a) (h a hx a hy).1

structure Crop where
  ordinal : Set Γ
  ordinal_convex : Set.OrdConnected ordinal
  colors : Set ℕ
  colors_convex : Set.OrdConnected colors

def Crop.set (A : Crop) : Family → Set Γ
  | .pure _ => A.ordinal
  | .mixed => A.ordinal ∩ Colors.color ⁻¹' A.colors

def restrict (A : Set Γ) (x : Array) : Array := x.filter (· ∈ A)

@[simp] lemma restrict_apply (A : Set Γ) (x : Array) (a : Γ) :
    restrict A x a = if a ∈ A then x a else 0 := Finsupp.filter_apply _ _ _

/-- A specified Type I expression. Child norming membership is imposed at its
construction stage, outside this data structure. -/
structure TypeI (f : Family) where
  weight : ℕ
  weight_pos : 1 ≤ weight
  length : ℕ
  length_pos : 1 ≤ length
  length_le : length ≤ f.L weight
  child : Fin length → Array
  child_nonzero : ∀ h, child h ≠ 0
  successive : ∀ h i, h < i → Successive f (child h) (child i)

def TypeI.value {f : Family} (e : TypeI f) : Array :=
  (1 / (f.m e.weight : ℚ)) • ∑ h, e.child h

/-- Exactly the finite prefix conditions, with unused raw entries ignored.
Padding raw data beyond length imposes no mathematical restriction. -/
structure PrefixValid (P : RawPath) (length : ℕ) : Prop where
  successive : ∀ i j, i < j → j < length → ∀ a ∈ (P.piece i).support,
    ∀ b ∈ (P.piece j).support, a < b
  metadata_strict : ∀ i j, i < j → j < length → P.metadata i < P.metadata j
  metadata_pos : ∀ i, i < length → 1 ≤ P.metadata i
  weight_pos : ∀ i, i < length → 1 ≤ P.weight i
  weight_le_metadata : ∀ i, i < length → P.weight i ≤ P.metadata i
  rho_bound : ∀ n, n < length → ∀ a b, a ∈ P.support n → b ∈ P.support n → a ≤ b →
    rho a b ≤ P.metadata n
  rule : ∀ n, n+1 < length → P.weight (n+1) = sigma (P.code n)

lemma PrefixValid.weight_strict {P : RawPath} {len : ℕ} (h : PrefixValid P len) :
    StrictMono (fun i : Fin len => P.weight i) := by
  cases len with
  | zero => intro i; exact i.elim0
  | succ len =>
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    change P.weight i < P.weight ((i : ℕ)+1)
    rw [h.rule i (by omega)]
    exact (h.weight_le_metadata i (by omega)).trans_lt
      ((P.metadata_le_codeBound i).trans_lt (codeBound_lt_sigma _))

structure FinitePath (f : Family) where
  raw : RawPath
  length : ℕ
  length_pos : 1 ≤ length
  valid : PrefixValid raw length
  piece : Fin length → TypeI f
  value_eq : ∀ i, (piece i).value = raw.piece i
  weight_eq : ∀ i, (piece i).weight = raw.weight i
  mixed_successive : ∀ (i j : Fin length), i < j →
    Successive f (raw.piece i) (raw.piece j)

def FinitePath.value {f : Family} (P : FinitePath f) : Array := ∑ i : Fin P.length, P.raw.piece i

def FinitePath.active {f : Family} (P : FinitePath f) (A : Crop) : Finset ℕ :=
  (Finset.univ.filter (fun i : Fin P.length => restrict (A.set f) (P.raw.piece i) ≠ 0)).image
    (fun i : Fin P.length => P.raw.weight i)

structure TypeII (f : Family) where
  length : ℕ
  path : Fin length → FinitePath f
  crop : Fin length → Crop
  coefficient : Fin length → ℚ
  bound : ∑ b, |(coefficient b : ℝ)| ^ f.q ≤ 1
  disjoint_active : Pairwise (fun b c =>
    Disjoint ((path b).active (crop b)) ((path c).active (crop c)))

def TypeII.value {f : Family} (e : TypeII f) : Array :=
  ∑ b, e.coefficient b • restrict ((e.crop b).set f) (e.path b).value

/-- Each stage retains previous stages and adjoins expressions whose Type I children belong to previous stages, with uncropped path data. -/
def stage (base : Set Array) (f : Family) : ℕ → Set Array
  | 0 => base
  | n+1 => stage base f n ∪
      {x | ∃ e : TypeI f, e.value = x ∧ ∀ h, e.child h ∈ stage base f n} ∪
      {x | ∃ e : TypeII f, e.value = x ∧
        ∀ b i h, ((e.path b).piece i).child h ∈ stage base f n}

def pureBase (k : ℕ) : Set Array :=
  {x | x = 0 ∨ ∃ a, Colors.color a = k ∧
    (x = Finsupp.single a 1 ∨ x = Finsupp.single a (-1))}

def Pure (k : ℕ) : Set Array := ⋃ n, stage (pureBase k) (.pure k) n

def Full : Set Array := ⋃ n, stage (⋃ k, Pure k) .mixed n

lemma stage_mono (base : Set Array) (f : Family) : Monotone (stage base f) := by
  apply monotone_nat_of_le_succ
  intro n x hx
  exact Or.inl (Or.inl hx)

lemma pure_subset_full (k : ℕ) : Pure k ⊆ Full := by
  intro x hx
  exact Set.mem_iUnion.mpr ⟨0, Set.mem_iUnion.mpr ⟨k, hx⟩⟩

lemma coordinate_mem (a : Γ) : Finsupp.single a 1 ∈ Full := by
  apply pure_subset_full (Colors.color a)
  exact Set.mem_iUnion.mpr ⟨0, Or.inr ⟨a, rfl, Or.inl rfl⟩⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open CoherentClosures PathCoding
open scoped Classical

lemma successive_coefficient_unique {f : Family} {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive f (v i) (v j)) {a : Γ} {i j : Fin n}
    (hi : v i a ≠ 0) (hj : v j a ≠ 0) : i = j := by
  by_contra hij
  rcases lt_or_gt_of_ne hij with hij | hij
  · exact Finset.disjoint_left.mp (h i j hij).disjoint
      (Finsupp.mem_support_iff.mpr hi) (Finsupp.mem_support_iff.mpr hj)
  · exact Finset.disjoint_left.mp (h j i hij).disjoint
      (Finsupp.mem_support_iff.mpr hj) (Finsupp.mem_support_iff.mpr hi)

lemma TypeI.coefficient_bound {f : Family} (e : TypeI f)
    (h : ∀ i a, |(e.child i a : ℝ)| ≤ 1) (a : Γ) :
    |(e.value a : ℝ)| ≤ 1 / (f.m e.weight : ℝ) := by
  classical
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos _
  have hsum : |∑ i, (e.child i a : ℝ)| ≤ 1 := by
    by_cases hex : ∃ i, e.child i a ≠ 0
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i]
      · exact h i a
      · intro j _ hji
        have hz : e.child j a = 0 := by
          by_contra hj
          exact hji (successive_coefficient_unique e.child e.successive hj hi)
        simp [hz]
      · simp
    · push Not at hex
      simp [hex]
  have heq : (e.value a : ℝ) = (1 / (f.m e.weight : ℝ)) * ∑ i, (e.child i a : ℝ) := by
    simp [TypeI.value, Finsupp.smul_apply, smul_eq_mul]
  rw [heq, abs_mul, abs_of_pos (one_div_pos.mpr hm)]
  simpa using mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hm))

/-- A coordinate meets at most one original path piece. -/
def FinitePath.hitIndex {f : Family} (P : FinitePath f) (a : Γ) : Fin P.length :=
  if h : ∃ i : Fin P.length, P.raw.piece i a ≠ 0 then h.choose
  else ⟨0, P.length_pos⟩

lemma FinitePath.value_at_hit {f : Family} (P : FinitePath f) (a : Γ) :
    P.value a = P.raw.piece (P.hitIndex a) a := by
  classical
  by_cases hex : ∃ i : Fin P.length, P.raw.piece i a ≠ 0
  · have hi : P.raw.piece (P.hitIndex a) a ≠ 0 := by
      simpa only [FinitePath.hitIndex, dite_eq_left hex] using hex.choose_spec
    change (∑ i : Fin P.length, P.raw.piece i) a = _
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (P.hitIndex a)]
    · intro j _ hj
      by_contra hne
      exact hj (successive_coefficient_unique (fun i : Fin P.length => P.raw.piece i)
        P.mixed_successive hne hi)
    · simp
  · push Not at hex
    simp [FinitePath.value, hex]

lemma FinitePath.hit_weight_active {f : Family} (P : FinitePath f) (A : Crop) (a : Γ)
    (ha : restrict (A.set f) P.value a ≠ 0) :
    P.raw.weight (P.hitIndex a) ∈ P.active A := by
  classical
  have hAc : a ∈ A.set f := by
    by_contra hn
    simp [hn] at ha
  have hv : P.raw.piece (P.hitIndex a) a ≠ 0 := by
    simpa [hAc, P.value_at_hit] using ha
  apply Finset.mem_image.mpr
  refine ⟨P.hitIndex a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro hz
  have hz' := congrArg (fun x : Array => x a) hz
  exact hv (by simpa [hAc] using hz')

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingOperations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

lemma Family.reciprocal_summable (f : Family) :
    Summable (fun n => 1 / (Parameters.m f.s n : ℝ)) :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    (Parameters.reciprocal_le_theta f.s_ge_two) (Parameters.hasSum_theta f.s_ge_two).summable

lemma TypeII.coefficient_le_one {f : Family} (e : TypeII f) (b : Fin e.length) :
    |(e.coefficient b : ℝ)| ≤ 1 := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  have hb : |(e.coefficient b : ℝ)| ^ f.q ≤ 1 :=
    (Finset.single_le_sum (fun i _ => Real.rpow_nonneg (abs_nonneg (e.coefficient i : ℝ)) f.q)
      (Finset.mem_univ b)).trans e.bound
  by_contra h
  have ht := Real.one_lt_rpow (lt_of_not_ge h) hq
  exact (not_lt_of_ge hb) ht

lemma TypeII.hit_weight_injective {f : Family} (e : TypeII f) (a : Γ) :
    Set.InjOn (fun b : Fin e.length => (e.path b).raw.weight ((e.path b).hitIndex a))
      {b | restrict ((e.crop b).set f) (e.path b).value a ≠ 0} := by
  intro b hb c hc heq
  by_contra hbc
  have hb' := (e.path b).hit_weight_active (e.crop b) a hb
  have hc' := (e.path c).hit_weight_active (e.crop c) a hc
  dsimp only at heq
  rw [heq] at hb'
  exact Finset.disjoint_left.mp (e.disjoint_active hbc) hb' hc'

lemma TypeII.coefficient_bound {f : Family} (e : TypeII f)
    (h : ∀ b i j a, |(((e.path b).piece i).child j a : ℝ)| ≤ 1) (a : Γ) :
    |(e.value a : ℝ)| < 1/8 := by
  classical
  let active : Finset (Fin e.length) := Finset.univ.filter
    (fun b => restrict ((e.crop b).set f) (e.path b).value a ≠ 0)
  let j : Fin e.length → ℕ := fun b =>
    (e.path b).raw.weight ((e.path b).hitIndex a)
  have jpos : ∀ b, 1 ≤ j b := fun b => (e.path b).valid.weight_pos _
    ((e.path b).hitIndex a).isLt
  have jinj : Set.InjOn (fun b => j b - 1) active := by
    intro b hb c hc heq
    apply e.hit_weight_injective a (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
    change j b = j c
    dsimp only at heq
    have := jpos b
    have := jpos c
    omega
  have hterm : ∀ b ∈ active,
      |(e.coefficient b : ℝ) * (restrict ((e.crop b).set f) (e.path b).value a : ℝ)|
        ≤ 1 / (Parameters.m f.s (j b - 1) : ℝ) := by
    intro b hb
    have hAc : a ∈ (e.crop b).set f := by
      by_contra hn
      have := (Finset.mem_filter.mp hb).2
      simp [hn] at this
    have hv : |((e.path b).raw.piece ((e.path b).hitIndex a) a : ℝ)| ≤
        1 / (f.m (j b) : ℝ) := by
      rw [← (e.path b).value_eq]
      have hh := ((e.path b).piece ((e.path b).hitIndex a)).coefficient_bound
        (h b ((e.path b).hitIndex a)) a
      simpa only [(e.path b).weight_eq] using hh
    rw [restrict_apply, ite_eq_left hAc, (e.path b).value_at_hit, abs_mul]
    exact (mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (abs_nonneg _)).trans
      (by simpa only [one_mul, Family.m] using hv)
  have hsum : (e.value a : ℝ) = ∑ b ∈ active,
      (e.coefficient b : ℝ) * (restrict ((e.crop b).set f) (e.path b).value a : ℝ) := by
    simp only [TypeII.value, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul, Rat.cast_sum,
      Rat.cast_mul]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro b _ hb
    have hz : restrict ((e.crop b).set f) (e.path b).value a = 0 := by
      simpa [active] using hb
    simp [hz]
  rw [hsum]
  calc
    |∑ b ∈ active, (e.coefficient b : ℝ) *
        (restrict ((e.crop b).set f) (e.path b).value a : ℝ)|
      ≤ ∑ b ∈ active, |(e.coefficient b : ℝ) *
        (restrict ((e.crop b).set f) (e.path b).value a : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b ∈ active, 1 / (Parameters.m f.s (j b - 1) : ℝ) := Finset.sum_le_sum hterm
    _ = ∑ n ∈ active.image (fun b => j b-1), 1 / (Parameters.m f.s n : ℝ) := by
      rw [Finset.sum_image]
      exact fun b hb c hc hbc => jinj hb hc hbc
    _ ≤ ∑' n, 1 / (Parameters.m f.s n : ℝ) :=
      f.reciprocal_summable.sum_le_tsum _ (fun _ _ => by positivity)
    _ < 1/8 := Parameters.reciprocal_sum_small f.s_ge_two

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma stage_coefficient_bound {base : Set Array} (f : Family)
    (hbase : ∀ x ∈ base, ∀ a, |(x a : ℝ)| ≤ 1) :
    ∀ n x, x ∈ stage base f n → ∀ a, |(x a : ℝ)| ≤ 1 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx a
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx a
    · exact (e.coefficient_bound (fun i => ih _ (he i)) a).trans (by
        have hm : (1 : ℝ) ≤ f.m e.weight := by exact_mod_cast f.m_pos e.weight
        exact (div_le_one (lt_of_lt_of_le (by norm_num) hm)).mpr hm)
    · exact le_trans (le_of_lt (e.coefficient_bound
        (fun b i j => ih _ (he b i j)) a)) (by norm_num)

lemma pureBase_coefficient_bound (k : ℕ) (x : Array) (hx : x ∈ pureBase k) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  rcases hx with rfl | ⟨b, _, rfl | rfl⟩
  · simp
  all_goals by_cases hab : a = b <;> simp [hab]

lemma pure_coefficient_bound (k : ℕ) (x : Array) (hx : x ∈ Pure k) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact stage_coefficient_bound (.pure k) (pureBase_coefficient_bound k) n x hn a

lemma full_coefficient_bound (x : Array) (hx : x ∈ Full) (a : Γ) :
    |(x a : ℝ)| ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_coefficient_bound .mixed ?_ n x hn a
  intro y hy
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
  exact pure_coefficient_bound k y hk

lemma restrict_support_subset (A : Set Γ) (x : Array) :
    (restrict A x).support ⊆ x.support := Finset.filter_subset _ _

lemma restrict_zero (A : Set Γ) : restrict A 0 = 0 := by ext a; simp

lemma restrict_smul (A : Set Γ) (c : ℚ) (x : Array) :
    restrict A (c • x) = c • restrict A x := by
  ext a
  by_cases h : a ∈ A <;> simp [h]

lemma restrict_sum {ι : Type*} (A : Set Γ) (s : Finset ι) (x : ι → Array) :
    restrict A (∑ i ∈ s, x i) = ∑ i ∈ s, restrict A (x i) := Finsupp.filter_sum _ _

lemma restrict_restrict (A B : Set Γ) (x : Array) :
    restrict A (restrict B x) = restrict (A ∩ B) x := by
  ext a
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp [hA, hB]

def Crop.inter (A B : Crop) : Crop :=
  ⟨A.ordinal ∩ B.ordinal, A.ordinal_convex.inter B.ordinal_convex,
    A.colors ∩ B.colors, A.colors_convex.inter B.colors_convex⟩

@[simp] lemma Crop.inter_set (A B : Crop) (f : Family) :
    (A.inter B).set f = A.set f ∩ B.set f := by
  cases f <;> ext a <;> simp [Crop.set, Crop.inter, and_assoc, and_left_comm, and_comm]

lemma Successive.restrict {f : Family} {x y : Array} (h : Successive f x y) (A : Set Γ) :
    Successive f (restrict A x) (restrict A y) := by
  intro a ha b hb
  exact h a (restrict_support_subset A x ha) b (restrict_support_subset A y hb)

lemma TypeII.active_crop_subset {f : Family} (P : FinitePath f) (A B : Crop) :
    P.active (A.inter B) ⊆ P.active B := by
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
  intro hz
  have hn := (Finset.mem_filter.mp hi).2
  apply hn
  rw [Crop.inter_set, ← restrict_restrict, hz, restrict_zero]

/-- Crops of Type II expressions retain the original paths and coding. -/
def TypeII.cropped {f : Family} (e : TypeII f) (A : Crop) : TypeII f where
  length := e.length
  path := e.path
  crop b := A.inter (e.crop b)
  coefficient := e.coefficient
  bound := e.bound
  disjoint_active := fun _b _c hbc => (e.disjoint_active hbc).mono
    (TypeII.active_crop_subset _ _ _) (TypeII.active_crop_subset _ _ _)

lemma TypeII.cropped_value {f : Family} (e : TypeII f) (A : Crop) :
    (e.cropped A).value = restrict (A.set f) e.value := by
  simp only [TypeII.value, TypeII.cropped, restrict_sum, restrict_smul,
    Crop.inter_set, restrict_restrict]
  rfl

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

/-- The crop operation discards zero children in order. -/
lemma TypeI.crop_cases {f : Family} (e : TypeI f) (A : Set Γ) :
    restrict A e.value = 0 ∨ ∃ d : TypeI f,
      d.weight = e.weight ∧ d.value = restrict A e.value ∧
      ∀ i, ∃ j, d.child i = restrict A (e.child j) := by
  let S : Finset (Fin e.length) := Finset.univ.filter (fun i => restrict A (e.child i) ≠ 0)
  have hsum : ∑ i ∈ S, restrict A (e.child i) = ∑ i, restrict A (e.child i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hi
  by_cases hS : S.Nonempty
  · right
    let idx : Fin S.card → Fin e.length := fun i => (S.orderIsoOfFin rfl i).val
    have hidx : StrictMono idx := (S.orderEmbOfFin rfl).strictMono
    have hiS : ∀ i, idx i ∈ S := fun i => (S.orderIsoOfFin rfl i).property
    let d : TypeI f :=
      { weight := e.weight
        weight_pos := e.weight_pos
        length := S.card
        length_pos := Finset.card_pos.mpr hS
        length_le := (Finset.card_le_card (Finset.filter_subset _ _)).trans (by simpa using e.length_le)
        child := fun i => restrict A (e.child (idx i))
        child_nonzero := fun i => (Finset.mem_filter.mp (hiS i)).2
        successive := fun i j hij => (e.successive _ _ (hidx hij)).restrict A }
    refine ⟨d, rfl, ?_, fun i => ⟨idx i, rfl⟩⟩
    have hsum' : ∑ i : Fin S.card, restrict A (e.child (idx i)) =
        ∑ i ∈ S, restrict A (e.child i) := by
      calc
        _ = ∑ i : S, restrict A (e.child i) :=
          (S.orderIsoOfFin rfl).toEquiv.sum_comp _
        _ = _ := (Finset.sum_subtype S (fun _ => Iff.rfl) (fun i => restrict A (e.child i))).symm
    simp only [d, TypeI.value, restrict_smul, restrict_sum, hsum', hsum]
  · left
    have hz : ∀ i, restrict A (e.child i) = 0 := by
      intro i
      by_contra hi
      exact hS ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    simp only [TypeI.value, restrict_smul, restrict_sum, hz, Finset.sum_const_zero, smul_zero]

lemma stage_zero {base : Set Array} (f : Family) (h0 : (0 : Array) ∈ base) (n : ℕ) :
    (0 : Array) ∈ stage base f n := stage_mono base f (Nat.zero_le n) h0

lemma stage_crop {base : Set Array} (f : Family) (h0 : (0 : Array) ∈ base)
    (hbase : ∀ (A : Crop) x, x ∈ base → restrict (A.set f) x ∈ base) :
    ∀ n (A : Crop) x, x ∈ stage base f n → restrict (A.set f) x ∈ stage base f n := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro A x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact Or.inl (Or.inl (ih A x hx))
    · rcases e.crop_cases (A.set f) with hz | ⟨d, _, hd, hchild⟩
      · rw [hz]
        exact stage_zero f h0 (n+1)
      · apply Or.inl ∘ Or.inr
        refine ⟨d, hd, ?_⟩
        intro i
        obtain ⟨j, hj⟩ := hchild i
        rw [hj]
        exact ih A _ (he j)
    · right
      exact ⟨e.cropped A, e.cropped_value A, he⟩

lemma pureBase_zero (k : ℕ) : (0 : Array) ∈ pureBase k := Or.inl rfl

lemma pureBase_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ pureBase k) :
    restrict (A.set (.pure k)) x ∈ pureBase k := by
  rcases hx with rfl | ⟨a, ha, rfl | rfl⟩
  · exact Or.inl (restrict_zero _)
  all_goals
    by_cases hA : a ∈ A.set (.pure k)
    · rw [restrict, Finsupp.filter_single_of_pos _ hA]
      exact Or.inr ⟨a, ha, by first | exact Or.inl rfl | exact Or.inr rfl⟩
    · rw [restrict, Finsupp.filter_single_of_neg _ hA]
      exact pureBase_zero k

lemma pure_zero (k : ℕ) : (0 : Array) ∈ Pure k := Set.mem_iUnion.mpr ⟨0, pureBase_zero k⟩

lemma pure_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ Pure k) :
    restrict (A.set (.pure k)) x ∈ Pure k := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n,
    stage_crop (.pure k) (pureBase_zero k) (pureBase_crop k) n A x hn⟩

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma TypeI.zero_at {f : Family} (e : TypeI f) (a : Γ)
    (h : ∀ i, e.child i a = 0) : e.value a = 0 := by
  simp [TypeI.value, h]

lemma FinitePath.zero_at {f : Family} (P : FinitePath f) (a : Γ)
    (h : ∀ i j, (P.piece i).child j a = 0) : P.value a = 0 := by
  rw [FinitePath.value, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [← P.value_eq]
  exact (P.piece i).zero_at a (h i)

lemma TypeII.zero_at {f : Family} (e : TypeII f) (a : Γ)
    (h : ∀ b i j, ((e.path b).piece i).child j a = 0) : e.value a = 0 := by
  simp only [TypeII.value, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul,
    restrict_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [(e.path b).zero_at a (h b)]
  simp

lemma stage_vanish {base : Set Array} (f : Family) (a : Γ)
    (hbase : ∀ x ∈ base, x a = 0) :
    ∀ n x, x ∈ stage base f n → x a = 0 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · exact e.zero_at a (fun i => ih _ (he i))
    · exact e.zero_at a (fun b i j => ih _ (he b i j))

lemma pure_vanish (k : ℕ) (x : Array) (hx : x ∈ Pure k) (a : Γ)
    (ha : Colors.color a ≠ k) : x a = 0 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_vanish (.pure k) a ?_ n x hn
  intro y hy
  rcases hy with rfl | ⟨b, hb, rfl | rfl⟩
  · rfl
  all_goals
    have hab : a ≠ b := by intro h; subst b; exact ha hb
    simp [hab]

lemma pure_mixed_crop (k : ℕ) (A : Crop) (x : Array) (hx : x ∈ Pure k) :
    restrict (A.set .mixed) x =
      if k ∈ A.colors then restrict (A.set (.pure k)) x else 0 := by
  ext a
  by_cases hcol : Colors.color a = k
  · by_cases hk : k ∈ A.colors <;> simp [Crop.set, hcol, hk]
  · have hz := pure_vanish k x hx a hcol
    by_cases hk : k ∈ A.colors <;> simp [Crop.set, hk, hz]

lemma full_crop (A : Crop) (x : Array) (hx : x ∈ Full) :
    restrict (A.set .mixed) x ∈ Full := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨n, stage_crop .mixed ?_ ?_ n A x hn⟩
  · exact Set.mem_iUnion.mpr ⟨0, pure_zero 0⟩
  · intro B y hy
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hy
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [pure_mixed_crop k B y hk]
    split_ifs
    · exact pure_crop k B y hk
    · exact pure_zero k

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma Successive.neg {f : Family} {x y : Array} (h : Successive f x y) :
    Successive f (-x) (-y) := by
  intro a ha b hb
  exact h a (by simpa using ha) b (by simpa using hb)

def TypeI.neg {f : Family} (e : TypeI f) : TypeI f where
  weight := e.weight
  weight_pos := e.weight_pos
  length := e.length
  length_pos := e.length_pos
  length_le := e.length_le
  child i := -e.child i
  child_nonzero i := neg_ne_zero.mpr (e.child_nonzero i)
  successive i j hij := (e.successive i j hij).neg

@[simp] lemma TypeI.neg_value {f : Family} (e : TypeI f) : e.neg.value = -e.value := by
  simp [TypeI.value, TypeI.neg, Finset.sum_neg_distrib]
  rfl

def TypeII.neg {f : Family} (e : TypeII f) : TypeII f where
  length := e.length
  path := e.path
  crop := e.crop
  coefficient b := -e.coefficient b
  bound := by simpa using e.bound
  disjoint_active := e.disjoint_active

@[simp] lemma TypeII.neg_value {f : Family} (e : TypeII f) : e.neg.value = -e.value := by
  simp [TypeII.value, TypeII.neg, Finset.sum_neg_distrib]
  rfl

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.FiniteLp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.LpFinite
universe u
open scoped ENNReal NNReal Classical
variable {Γ : Type u}

/-- A rational array, as an ℓᵖ vector. -/
def array (p : ℝ≥0∞) (f : Γ →₀ ℚ) : lp (fun _ : Γ => ℝ) p :=
  ⟨fun a => (f a : ℝ), by
    apply Memℓp.of_exponent_ge (q := 0) ?_ (zero_le : (0 : ℝ≥0∞) ≤ p)
    apply memℓp_zero_iff.mpr
    exact f.support.finite_toSet.subset (fun a ha => by simpa using ha)⟩

@[simp] lemma array_apply (p : ℝ≥0∞) (f : Γ →₀ ℚ) (a : Γ) : array p f a = (f a : ℝ) := rfl

@[simp] lemma array_zero (p : ℝ≥0∞) : array p (0 : Γ →₀ ℚ) = 0 := by
  apply lp.ext
  funext a
  simp

@[simp] lemma array_add (p : ℝ≥0∞) (f g : Γ →₀ ℚ) : array p (f+g) = array p f + array p g := by
  apply lp.ext
  funext a
  simp

@[simp] lemma array_smul (p : ℝ≥0∞) (c : ℚ) (f : Γ →₀ ℚ) :
    array p (c • f) = (c : ℝ) • array p f := by
  apply lp.ext
  funext a
  simp

@[simp] lemma array_sum {ι : Type*} (p : ℝ≥0∞) (s : Finset ι) (f : ι → Γ →₀ ℚ) :
    array p (∑ i ∈ s, f i) = ∑ i ∈ s, array p (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, array_add, ih]

lemma norm_array_filter_le (p : ℝ≥0∞) (hp : p ≠ 0) (f : Γ →₀ ℚ) (A : Set Γ) :
    ‖array p (f.filter (· ∈ A))‖ ≤ ‖array p f‖ := by
  apply lp.norm_mono hp
  intro a
  by_cases ha : a ∈ A <;> simp [ha]

lemma norm_array_single {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (a : Γ) (c : ℚ) :
    ‖array p (Finsupp.single a c)‖ = |(c : ℝ)| := by
  have h : array p (Finsupp.single a c) = lp.single p a (c : ℝ) := by
    apply lp.ext
    funext b
    by_cases hba : b = a <;> simp [hba, lp.single_apply]
  rw [h]
  exact (lp.norm_single (E := fun _ : Γ => ℝ) (pos_iff_ne_zero.mpr hp) a (c : ℝ)).trans
    (Real.norm_eq_abs _)

end SeparableQuotient.LpFinite

namespace SeparableQuotient.LpFinite
open scoped ENNReal NNReal Classical
universe u v
variable {Γ : Type u} {ι : Type v} {p : ℝ≥0∞}

/-- Exact disjoint-support identity, including arbitrary finite index sets. -/
lemma norm_sum_rpow (hp : 0 < p.toReal) (s : Finset ι)
    (v : ι → lp (fun _ : Γ => ℝ) p)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, v i a = 0 ∨ v j a = 0) :
    ‖∑ i ∈ s, v i‖ ^ p.toReal = ∑ i ∈ s, ‖v i‖ ^ p.toReal := by
  have hpoint : ∀ a, ‖∑ i ∈ s, v i a‖ ^ p.toReal = ∑ i ∈ s, ‖v i a‖ ^ p.toReal := by
    intro a
    by_cases hex : ∃ i ∈ s, v i a ≠ 0
    · obtain ⟨i, hi, hv⟩ := hex
      have hz : ∀ j ∈ s, j ≠ i → v j a = 0 := by
        intro j hj hji
        exact (hdis j hj i hi hji a).resolve_right hv
      rw [Finset.sum_eq_single i (fun j hj hji => hz j hj hji) (fun hn => (hn hi).elim)]
      rw [Finset.sum_eq_single i (fun j hj hji => by rw [hz j hj hji]; simp [hp.ne'])
        (fun hn => (hn hi).elim)]
    · push Not at hex
      simp only [Finset.sum_eq_zero (fun i hi => hex i hi), norm_zero,
        Real.zero_rpow hp.ne']
      symm
      exact Finset.sum_eq_zero fun i hi => by rw [hex i hi]; simp [hp.ne']
  rw [lp.norm_rpow_eq_tsum hp]
  simp only [lp.coeFn_sum, Finset.sum_apply, hpoint]
  rw [Summable.tsum_finsetSum (fun i _ => (lp.memℓp (v i)).summable hp)]
  simp only [lp.norm_rpow_eq_tsum hp]

lemma norm_sum_le_card_rpow [Fact (1 ≤ p)] (hp : 0 < p.toReal) (s : Finset ι)
    (v : ι → lp (fun _ : Γ => ℝ) p)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ a, v i a = 0 ∨ v j a = 0)
    (hbound : ∀ i ∈ s, ‖v i‖ ≤ 1) :
    ‖∑ i ∈ s, v i‖ ≤ (s.card : ℝ) ^ (1 / p.toReal) := by
  apply (Real.rpow_le_rpow_iff (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _) hp).mp
  rw [norm_sum_rpow hp s v hdis, ← Real.rpow_mul (Nat.cast_nonneg _),
    one_div_mul_cancel hp.ne', Real.rpow_one]
  calc
    _ ≤ ∑ i ∈ s, (1 : ℝ) := Finset.sum_le_sum fun i hi => by
      simpa using Real.rpow_le_rpow (norm_nonneg (v i)) (hbound i hi) hp.le
    _ = _ := by simp

end SeparableQuotient.LpFinite

namespace SeparableQuotient.Norming
open scoped ENNReal NNReal Classical
open LpFinite

def Family.r (f : Family) : ℝ := Parameters.r f.s
lemma Family.r_gt_one (f : Family) : 1 < f.r :=
  (Parameters.q_bounds f.s_ge_two).1.trans (Parameters.q_bounds f.s_ge_two).2.1
lemma Family.r_pos (f : Family) : 0 < f.r := zero_lt_one.trans f.r_gt_one

def Family.exponent (f : Family) : ℝ≥0∞ := ENNReal.ofReal f.r
instance Family.exponent_fact (f : Family) : Fact (1 ≤ f.exponent) :=
  ⟨by simpa [Family.exponent] using ENNReal.ofReal_le_ofReal f.r_gt_one.le⟩
@[simp] lemma Family.exponent_toReal (f : Family) : f.exponent.toReal = f.r :=
  ENNReal.toReal_ofReal f.r_pos.le
lemma Family.exponent_ne_zero (f : Family) : f.exponent ≠ 0 := by
  exact ne_of_gt ((zero_lt_one : (0 : ℝ≥0∞) < 1).trans_le (Fact.out : 1 ≤ f.exponent))

def Family.theta (f : Family) (j : ℕ) : ℝ := Parameters.theta f.s (j-1)
lemma Family.theta_formula (f : Family) (j : ℕ) :
    f.theta j = (f.L j : ℝ)^(1/f.r) / (f.m j : ℝ) := rfl

lemma TypeI.lp_bound {f : Family} (e : TypeI f)
    (h : ∀ i, ‖array f.exponent (e.child i)‖ ≤ 1) :
    ‖array f.exponent e.value‖ ≤ f.theta e.weight := by
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin e.length)), ∀ j ∈ Finset.univ,
      i ≠ j → ∀ a, array f.exponent (e.child i) a = 0 ∨
        array f.exponent (e.child j) a = 0 := by
    intro i _ j _ hij a
    by_cases hi : e.child i a = 0
    · exact Or.inl (by simp [hi])
    · right
      have hz : e.child j a = 0 := by
        by_contra hj
        exact hij (successive_coefficient_unique e.child e.successive hi hj)
      simp [hz]
  have hsum : ‖∑ i, array f.exponent (e.child i)‖ ≤ (e.length : ℝ)^(1/f.r) := by
    simpa using norm_sum_le_card_rpow (by simpa using f.r_pos) Finset.univ
      (fun i => array f.exponent (e.child i)) hd (fun i _ => h i)
  have hm : 0 < (f.m e.weight : ℝ) := by exact_mod_cast f.m_pos _
  rw [TypeI.value, array_smul, array_sum, norm_smul, Family.theta_formula]
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hm)]
  calc
    (1/(f.m e.weight:ℝ)) * ‖∑ i, array f.exponent (e.child i)‖
      ≤ (1/(f.m e.weight:ℝ)) * (e.length:ℝ)^(1/f.r) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (1/(f.m e.weight:ℝ)) * (f.L e.weight:ℝ)^(1/f.r) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast e.length_le)
        (one_div_nonneg.mpr f.r_pos.le)
    _ = _ := by ring

lemma FinitePath.crop_lp_bound {f : Family} (P : FinitePath f) (A : Crop)
    (h : ∀ i j, ‖array f.exponent ((P.piece i).child j)‖ ≤ 1) :
    ‖array f.exponent (restrict (A.set f) P.value)‖ ≤ ∑ j ∈ P.active A, f.theta j := by
  let s : Finset (Fin P.length) := Finset.univ.filter
    (fun i => restrict (A.set f) (P.raw.piece i) ≠ 0)
  have heq : restrict (A.set f) P.value = ∑ i ∈ s, restrict (A.set f) (P.raw.piece i) := by
    rw [FinitePath.value, restrict, Finsupp.filter_sum]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [s] using hi
  rw [heq, array_sum]
  calc
    ‖∑ i ∈ s, array f.exponent (restrict (A.set f) (P.raw.piece i))‖
      ≤ ∑ i ∈ s, ‖array f.exponent (restrict (A.set f) (P.raw.piece i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, f.theta (P.raw.weight i) := by
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ‖array f.exponent (P.raw.piece i)‖ :=
          norm_array_filter_le f.exponent f.exponent_ne_zero _ _
        _ ≤ f.theta (P.raw.weight i) := by
          rw [← P.value_eq, ← P.weight_eq]
          exact (P.piece i).lp_bound (h i)
    _ = _ := by
      change _ = ∑ j ∈ s.image (fun i : Fin P.length => P.raw.weight i), f.theta j
      rw [Finset.sum_image]
      exact fun _ _ _ _ hij => P.valid.weight_strict.injective hij

lemma TypeII.lp_bound {f : Family} (e : TypeII f)
    (h : ∀ b i j, ‖array f.exponent (((e.path b).piece i).child j)‖ ≤ 1) :
    ‖array f.exponent e.value‖ < 1/8 := by
  let s := Finset.univ.biUnion (fun b => (e.path b).active (e.crop b))
  have hpos : ∀ j ∈ s, 1 ≤ j := by
    intro j hj
    obtain ⟨b, _, hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hj
    exact (e.path b).valid.weight_pos _ i.isLt
  have hinj : Set.InjOn (fun j : ℕ => j-1) s := by
    intro j hj k hk heq
    have := hpos j hj
    have := hpos k hk
    change j-1 = k-1 at heq
    omega
  rw [TypeII.value, array_sum]
  calc
    ‖∑ b, array f.exponent (e.coefficient b • restrict ((e.crop b).set f) (e.path b).value)‖
      ≤ ∑ b, ‖array f.exponent (e.coefficient b • restrict ((e.crop b).set f) (e.path b).value)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ b, ∑ j ∈ (e.path b).active (e.crop b), f.theta j := by
      apply Finset.sum_le_sum
      intro b _
      rw [array_smul, norm_smul, Real.norm_eq_abs]
      calc
        _ ≤ 1 * ‖array f.exponent (restrict ((e.crop b).set f) (e.path b).value)‖ :=
          mul_le_mul_of_nonneg_right (e.coefficient_le_one b) (norm_nonneg _)
        _ ≤ _ := by simpa using (e.path b).crop_lp_bound (e.crop b) (h b)
    _ = ∑ j ∈ s, f.theta j := by
      symm
      apply Finset.sum_biUnion
      intro b _ c _ hbc
      exact e.disjoint_active hbc
    _ = ∑ n ∈ s.image (fun j => j-1), Parameters.theta f.s n := by
      rw [Finset.sum_image]
      · rfl
      · exact fun _ hj _ hk heq => hinj hj hk heq
    _ ≤ ∑' n, Parameters.theta f.s n :=
      (Parameters.hasSum_theta f.s_ge_two).summable.sum_le_tsum _
        (fun n _ => by rw [Parameters.theta_eq f.s_ge_two]; positivity)
    _ < 1/8 := Parameters.theta_sum_small f.s_ge_two

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped ENNReal NNReal Classical
open LpFinite

lemma Family.theta_le_one (f : Family) (j : ℕ) : f.theta j ≤ 1 := by
  rw [Family.theta, Parameters.theta_eq f.s_ge_two]
  exact pow_le_one₀ (by norm_num) (by norm_num)

lemma stage_lp_bound {base : Set Array} (f : Family)
    (hbase : ∀ x ∈ base, ‖array f.exponent x‖ ≤ 1) :
    ∀ n x, x ∈ stage base f n → ‖array f.exponent x‖ ≤ 1 := by
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · exact (e.lp_bound (fun i => ih _ (he i))).trans (f.theta_le_one _)
    · exact (e.lp_bound (fun b i j => ih _ (he b i j))).le.trans (by norm_num)

/-- The pure coefficient ℓr estimate. -/
lemma pure_lp_bound (k : ℕ) (x : Array) (hx : x ∈ Pure k) :
    ‖array (Family.pure k).exponent x‖ ≤ 1 := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  apply stage_lp_bound (.pure k) ?_ n x hn
  intro y hy
  rcases hy with rfl | ⟨a, _, rfl | rfl⟩
  · simp
  · rw [norm_array_single (Family.exponent_ne_zero _)]; norm_num
  · rw [norm_array_single (Family.exponent_ne_zero _)]; norm_num

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ColorDecomposition
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped Classical

lemma convex_sum_le_one {E : Type*} [AddCommGroup E] [Module ℚ E]
    {S : Set E} (hS : Convex ℚ S) (h0 : (0 : E) ∈ S)
    {ι : Type*} [Fintype ι] (a : ι → ℚ) (x : ι → E)
    (ha : ∀ i, 0 ≤ a i) (hs : ∑ i, a i ≤ 1) (hx : ∀ i, x i ∈ S) :
    (∑ i, a i • x i) ∈ S := by
  let w : Option ι → ℚ := fun i => i.elim (1 - ∑ j, a j) a
  let z : Option ι → E := fun i => i.elim 0 x
  have hw : ∀ i ∈ (Finset.univ : Finset (Option ι)), 0 ≤ w i := by
    rintro (_ | i) _
    · exact sub_nonneg.mpr hs
    · exact ha i
  have hs' : ∑ i, w i = 1 := by simp [w, Fintype.sum_option]
  have hz : ∀ i ∈ (Finset.univ : Finset (Option ι)), z i ∈ S := by
    rintro (_ | i) _
    · exact h0
    · exact hx i
  simpa [w, z, Fintype.sum_option] using hS.sum_mem hw hs' hz

lemma absConvex_sum_le_one {E : Type*} [AddCommGroup E] [Module ℚ E]
    {S : Set E} (hS : AbsConvex ℚ S) (h0 : (0 : E) ∈ S)
    {ι : Type*} [Fintype ι] (a : ι → ℚ) (x : ι → E)
    (hs : ∑ i, |a i| ≤ 1) (hx : ∀ i, x i ∈ S) :
    (∑ i, a i • x i) ∈ S := by
  let z : ι → E := fun i => if 0 ≤ a i then x i else -x i
  have hz : ∀ i, z i ∈ S := by
    intro i
    dsimp [z]
    split_ifs
    · exact hx i
    · exact hS.1.neg_mem_iff.mpr (hx i)
  have heq : ∀ i, |a i| • z i = a i • x i := by
    intro i
    by_cases hi : 0 ≤ a i
    · simp [z, hi, abs_of_nonneg hi]
    · simp [z, hi, abs_of_neg (lt_of_not_ge hi)]
  simpa only [heq] using convex_sum_le_one hS.2 h0 (fun i => |a i|) z
    (fun i => abs_nonneg _) hs hz

def colorSet (k : ℕ) : Set Γ := {a | Colors.color a = k}

def colorRestrict (k : ℕ) (A : Crop) (x : Array) : Array :=
  restrict (colorSet k) (restrict (A.set .mixed) x)

lemma mixed_color_unique {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive .mixed (v i) (v j))
    (k : ℕ) (A : Crop) {i j : Fin n}
    (hi : colorRestrict k A (v i) ≠ 0) (hj : colorRestrict k A (v j) ≠ 0) : i = j := by
  have hex : ∀ x : Array, x ≠ 0 → ∃ a, x a ≠ 0 := by
    intro x hx
    by_contra hh
    push Not at hh
    exact hx (Finsupp.ext hh)
  obtain ⟨a, ha⟩ := hex _ hi
  obtain ⟨b, hb⟩ := hex _ hj
  have ha' : a ∈ (v i).support ∧ Colors.color a = k := by
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_⟩
    · intro hz
      simp [colorRestrict, hz] at ha
    · by_contra hh
      simp [colorRestrict, colorSet, hh] at ha
  have hb' : b ∈ (v j).support ∧ Colors.color b = k := by
    refine ⟨Finsupp.mem_support_iff.mpr ?_, ?_⟩
    · intro hz
      simp [colorRestrict, hz] at hb
    · by_contra hh
      simp [colorRestrict, colorSet, hh] at hb
  rcases lt_trichotomy i j with hij | hij | hij
  · have hh := (h i j hij a ha'.1 b hb'.1).2 rfl
    omega
  · exact hij
  · have hh := (h j i hij b hb'.1 a ha'.1).2 rfl
    omega

lemma colorRestrict_sum {n : ℕ} (v : Fin n → Array)
    (h : ∀ i j, i < j → Successive .mixed (v i) (v j))
    (k : ℕ) (A : Crop) (i : Fin n) (hi : colorRestrict k A (v i) ≠ 0) :
    colorRestrict k A (∑ j, v j) = colorRestrict k A (v i) := by
  simp only [colorRestrict, restrict_sum]
  apply Finset.sum_eq_single i
  · intro j _ hji
    by_contra hj
    exact hji (mixed_color_unique v h k A hj hi)
  · simp

lemma colorRestrict_sum_zero {n : ℕ} (v : Fin n → Array)
    (k : ℕ) (A : Crop) (h : ∀ i, colorRestrict k A (v i) = 0) :
    colorRestrict k A (∑ j, v j) = 0 := by
  simp only [colorRestrict, restrict_sum] at h ⊢
  simp only [h, Finset.sum_const_zero]

lemma TypeI.color_decomposition (e : TypeI .mixed) (k : ℕ) (A : Crop)
    {S : Set Array} (h0 : (0 : Array) ∈ S)
    (h : ∀ i, colorRestrict k A (e.child i) ∈ S) :
    ∃ g ∈ S, colorRestrict k A e.value = (1 / (Family.mixed.m e.weight : ℚ)) • g := by
  by_cases hex : ∃ i, colorRestrict k A (e.child i) ≠ 0
  · obtain ⟨i, hi⟩ := hex
    refine ⟨colorRestrict k A (e.child i), h i, ?_⟩
    simp only [TypeI.value, colorRestrict, restrict_smul]
    congr 1
    exact colorRestrict_sum e.child e.successive k A i hi
  · push Not at hex
    refine ⟨0, h0, ?_⟩
    have hz := colorRestrict_sum_zero e.child k A hex
    simp only [TypeI.value, colorRestrict, restrict_smul] at hz ⊢
    rw [hz, smul_zero]

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

lemma FinitePath.color_decomposition (P : FinitePath .mixed) (k : ℕ) (A : Crop)
    {S : Set Array} (h0 : (0 : Array) ∈ S)
    (h : ∀ i j, colorRestrict k A ((P.piece i).child j) ∈ S) :
    ∃ (i : Fin P.length) (g : Array), g ∈ S ∧
      colorRestrict k A P.value = (1 / (Family.mixed.m (P.raw.weight i) : ℚ)) • g ∧
      (colorRestrict k A P.value ≠ 0 → P.raw.weight i ∈ P.active A) := by
  by_cases hex : ∃ i : Fin P.length, colorRestrict k A (P.raw.piece i) ≠ 0
  · obtain ⟨i, hi⟩ := hex
    obtain ⟨g, hg, heq⟩ := (P.piece i).color_decomposition k A h0 (h i)
    have hv : colorRestrict k A P.value = colorRestrict k A (P.raw.piece i) :=
      colorRestrict_sum (fun i : Fin P.length => P.raw.piece i) P.mixed_successive k A i hi
    refine ⟨i, g, hg, ?_, ?_⟩
    · rw [hv, ← P.value_eq, heq, P.weight_eq]
    · intro _
      apply Finset.mem_image.mpr
      refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      intro hz
      apply hi
      simp only [colorRestrict, hz, restrict_zero]
  · push Not at hex
    have hz : colorRestrict k A P.value = 0 := colorRestrict_sum_zero _ k A hex
    exact ⟨⟨0, P.length_pos⟩, 0, h0, by simp [hz], by simp [hz]⟩

lemma TypeII.color_mem (e : TypeII .mixed) (k : ℕ)
    {S : Set Array} (hS : AbsConvex ℚ S) (h0 : (0 : Array) ∈ S)
    (h : ∀ b i j, colorRestrict k (e.crop b) (((e.path b).piece i).child j) ∈ S) :
    restrict (colorSet k) e.value ∈ S := by
  choose i g hg heq hact using fun b =>
    (e.path b).color_decomposition k (e.crop b) h0 (h b)
  let active : Finset (Fin e.length) := Finset.univ.filter
    (fun b => colorRestrict k (e.crop b) (e.path b).value ≠ 0)
  let j (b : Fin e.length) : ℕ := (e.path b).raw.weight (i b)
  let c (b : Fin e.length) : ℚ :=
    if b ∈ active then e.coefficient b / (Family.mixed.m (j b) : ℚ) else 0
  have jpos : ∀ b, 1 ≤ j b := fun b => (e.path b).valid.weight_pos _ (i b).isLt
  have jinj : Set.InjOn (fun b => j b - 1) active := by
    intro b hb d hd hbd
    by_contra hne
    have hb' := hact b (Finset.mem_filter.mp hb).2
    have hd' := hact d (Finset.mem_filter.mp hd).2
    have hsame : j b = j d := by
      change j b - 1 = j d - 1 at hbd
      have := jpos b
      have := jpos d
      omega
    change j b ∈ _ at hb'
    rw [hsame] at hb'
    exact Finset.disjoint_left.mp (e.disjoint_active hne) hb' hd'
  have hcR : ∑ b, |(c b : ℝ)| ≤
      ∑ b ∈ active, 1 / (Parameters.m Family.mixed.s (j b-1) : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro b _
    by_cases hb : b ∈ active
    · have hm : 0 < (Family.mixed.m (j b) : ℝ) := by exact_mod_cast Family.mixed.m_pos _
      simp only [c, ite_eq_left hb, Rat.cast_div, Rat.cast_natCast, abs_div, abs_of_pos hm]
      have hb' : colorRestrict k (e.crop b) (e.path b).value ≠ 0 := (Finset.mem_filter.mp hb).2
      simp only [ite_eq_left hb']
      exact div_le_div_of_nonneg_right (e.coefficient_le_one b) hm.le
    · have hb' : ¬ colorRestrict k (e.crop b) (e.path b).value ≠ 0 := by
        simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and] using hb
      simp [c, hb, hb']
  have hcsR : ∑ b, |(c b : ℝ)| ≤ 1 := by
    calc
      _ ≤ ∑ b ∈ active, 1 / (Parameters.m Family.mixed.s (j b-1) : ℝ) := hcR
      _ = ∑ n ∈ active.image (fun b => j b-1), 1 / (Parameters.m Family.mixed.s n : ℝ) := by
        rw [Finset.sum_image]
        exact fun b hb d hd hbd => jinj hb hd hbd
      _ ≤ ∑' n, 1 / (Parameters.m Family.mixed.s n : ℝ) :=
        Family.mixed.reciprocal_summable.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ 1 := (Parameters.reciprocal_sum_small Family.mixed.s_ge_two).le.trans (by norm_num)
  have hcs : ∑ b, |c b| ≤ 1 := by exact_mod_cast hcsR
  have hv : restrict (colorSet k) e.value = ∑ b, c b • g b := by
    simp only [TypeII.value, restrict_sum, restrict_smul]
    apply Finset.sum_congr rfl
    intro b _
    change e.coefficient b • colorRestrict k (e.crop b) (e.path b).value = _
    by_cases hb : b ∈ active
    · rw [heq b, smul_smul]
      simp only [c, ite_eq_left hb, j, div_eq_mul_inv, one_mul]
    · have hz : colorRestrict k (e.crop b) (e.path b).value = 0 := by
        simpa only [active, Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hb
      simp [c, hb, hz]
  rw [hv]
  exact absConvex_sum_le_one hS h0 c g hcs hg

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.all : Crop := ⟨Set.univ, Set.ordConnected_univ, Set.univ, Set.ordConnected_univ⟩

@[simp] lemma Crop.all_set (f : Family) : Crop.all.set f = Set.univ := by
  cases f <;> simp [Crop.all, Crop.set]

@[simp] lemma restrict_univ (x : Array) : restrict Set.univ x = x := by
  ext a
  simp

@[simp] lemma colorRestrict_all (k : ℕ) (x : Array) :
    colorRestrict k Crop.all x = restrict (colorSet k) x := by
  simp [colorRestrict]

lemma pure_color_restrict (k l : ℕ) (x : Array) (hx : x ∈ Pure l) :
    restrict (colorSet k) x = if k = l then x else 0 := by
  ext a
  by_cases hkl : k = l
  · subst l
    by_cases ha : Colors.color a = k
    · simp [colorSet, ha]
    · simp [colorSet, ha, pure_vanish k x hx a ha]
  · by_cases ha : Colors.color a = k
    · have hl : Colors.color a ≠ l := by omega
      simp [colorSet, hkl, ha, pure_vanish l x hx a hl]
    · simp [colorSet, hkl, ha]

lemma mixedBase_crop (A : Crop) (x : Array) (hx : x ∈ ⋃ k, Pure k) :
    restrict (A.set .mixed) x ∈ ⋃ k, Pure k := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion.mpr
  refine ⟨k, ?_⟩
  rw [pure_mixed_crop k A x hk]
  split_ifs
  · exact pure_crop k A x hk
  · exact pure_zero k

lemma mixed_stage_crop (n : ℕ) (A : Crop) (x : Array)
    (hx : x ∈ stage (⋃ k, Pure k) .mixed n) :
    restrict (A.set .mixed) x ∈ stage (⋃ k, Pure k) .mixed n :=
  stage_crop .mixed (Set.mem_iUnion.mpr ⟨0, pure_zero 0⟩) mixedBase_crop n A x hx

lemma mixed_stage_color_hull (k : ℕ) :
    ∀ n x, x ∈ stage (⋃ l, Pure l) .mixed n →
      restrict (colorSet k) x ∈ absConvexHull ℚ (Pure k) := by
  have h0 : (0 : Array) ∈ absConvexHull ℚ (Pure k) := subset_absConvexHull (pure_zero k)
  intro n
  induction n with
  | zero =>
    intro x hx
    obtain ⟨l, hl⟩ := Set.mem_iUnion.mp hx
    rw [pure_color_restrict k l x hl]
    split_ifs with hkl
    · subst l
      exact subset_absConvexHull hl
    · exact h0
  | succ n ih =>
    intro x hx
    rcases hx with (hx | ⟨e, rfl, he⟩) | ⟨e, rfl, he⟩
    · exact ih x hx
    · obtain ⟨g, hg, hv⟩ := e.color_decomposition k Crop.all h0 (fun i => by
        simpa only [colorRestrict_all] using ih _ (he i))
      rw [colorRestrict_all] at hv
      rw [hv]
      apply (absConvex_absConvexHull (𝕜 := ℚ) (s := Pure k)).1.smul_mem ?_ hg
      rw [norm_div, norm_one]
      have hm : (1 : ℝ) ≤ Family.mixed.m e.weight := by exact_mod_cast Family.mixed.m_pos _
      simpa only [← Rat.norm_cast_real, Rat.cast_natCast, Real.norm_natCast, one_div, inv_one] using
        (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hm)
    · apply e.color_mem k absConvex_absConvexHull h0
      intro b i j
      exact ih _ (mixed_stage_crop n (e.crop b) _ (he b i j))

/-- Every mixed-stage normer restricts to the absolute convex hull of the pure norming set. -/
lemma full_color_hull (k : ℕ) (x : Array) (hx : x ∈ Full) :
    restrict (colorSet k) x ∈ absConvexHull ℚ (Pure k) := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact mixed_stage_color_hull k n x hn

end SeparableQuotient.Norming

namespace SeparableQuotient.LpFinite
open scoped Classical ENNReal
universe u
variable {Γ : Type u} {p : ℝ≥0∞} [Fact (1 ≤ p)]

lemma absConvex_norm_array : AbsConvex ℚ {f : Γ →₀ ℚ | ‖array p f‖ ≤ 1} := by
  constructor
  · intro a ha
    rintro _ ⟨x, hx, rfl⟩
    change ‖array p (a • x)‖ ≤ 1
    rw [array_smul, norm_smul, Rat.norm_cast_real]
    exact (mul_le_mul_of_nonneg_left hx (norm_nonneg a)).trans (by simpa using ha)
  · intro x hx y hy a b ha hb hab
    change ‖array p (a • x + b • y)‖ ≤ 1
    simp only [array_add, array_smul]
    have ha' : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have hb' : (0 : ℝ) ≤ b := by exact_mod_cast hb
    have hab' : (a : ℝ) + (b : ℝ) = 1 := by exact_mod_cast hab
    calc
      _ ≤ ‖(a : ℝ) • array p x‖ + ‖(b : ℝ) • array p y‖ := norm_add_le _ _
      _ = (a : ℝ) * ‖array p x‖ + (b : ℝ) * ‖array p y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha', Real.norm_of_nonneg hb']
      _ ≤ (a : ℝ) * 1 + (b : ℝ) * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hx ha') (mul_le_mul_of_nonneg_left hy hb')
      _ = 1 := by simpa using hab'

end SeparableQuotient.LpFinite

namespace SeparableQuotient.Norming
open scoped ENNReal Classical
open LpFinite

/-- Full mixed normers retain the exact pure ℓr bound on each color. -/
lemma full_color_lp_bound (k : ℕ) (f : Array) (hf : f ∈ Full) :
    ‖array (Family.pure k).exponent (restrict (colorSet k) f)‖ ≤ 1 :=
  absConvexHull_min (fun x hx => pure_lp_bound k x hx) absConvex_norm_array
    (full_color_hull k f hf)

end SeparableQuotient.Norming

namespace SeparableQuotient.LpFinite
open scoped Classical ENNReal
universe u
variable {Γ : Type u}

/-- Real finitely supported vectors in the usual ℓp space. -/
def realArray (p : ℝ≥0∞) (x : Γ →₀ ℝ) : lp (fun _ : Γ => ℝ) p :=
  ⟨fun a => x a, Memℓp.of_exponent_ge (memℓp_zero_iff.mpr x.hasFiniteSupport) (zero_le : 0 ≤ p)⟩

@[simp] lemma realArray_apply (p : ℝ≥0∞) (x : Γ →₀ ℝ) (a : Γ) :
    realArray p x a = x a := rfl

lemma pairing_le {p q : ℝ≥0∞} (hpq : p.toReal.HolderConjugate q.toReal)
    (x : Γ →₀ ℝ) (f : Γ →₀ ℚ) :
    |x.sum (fun a t => t * (f a : ℝ))| ≤ ‖realArray p x‖ * ‖array q f‖ := by
  have h := lp.tsum_mul_le_mul_norm hpq (realArray p x) (array q f)
  calc
    _ ≤ ∑ a ∈ x.support, |x a * (f a : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a ∈ x.support, ‖realArray p x a‖ * ‖array q f a‖ := by
      simp only [realArray_apply, array_apply, Real.norm_eq_abs, abs_mul]
    _ ≤ ∑' a, ‖realArray p x a‖ * ‖array q f a‖ :=
      h.1.sum_le_tsum _ (fun a _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ ≤ _ := h.2

end SeparableQuotient.LpFinite

namespace SeparableQuotient.Norming
open scoped ENNReal

def Family.primalExponent (f : Family) : ℝ≥0∞ := f.s
instance Family.primalExponent_fact (f : Family) : Fact (1 ≤ f.primalExponent) :=
  ⟨by change (1 : ℝ≥0∞) ≤ (f.s : ℝ≥0∞); exact_mod_cast (f.s_ge_two.trans' (by omega : 1 ≤ 2))⟩
@[simp] lemma Family.primalExponent_toReal (f : Family) : f.primalExponent.toReal = f.s := by
  simp [Family.primalExponent]
lemma Family.conjugate (f : Family) :
    f.primalExponent.toReal.HolderConjugate f.exponent.toReal := by
  simpa only [Family.primalExponent_toReal, Family.exponent_toReal, Family.r] using
    Parameters.s_r_conjugate f.s_ge_two
end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

/- The completion of c₀₀ under a bounded rational norming set. -/
namespace SeparableQuotient.NormConstruction
open scoped Topology ENNReal
open Filter
universe u
variable {Γ : Type u}

structure NormingSet (Γ : Type u) where
  carrier : Set (Γ →₀ ℚ)
  coordinate_mem : ∀ a, Finsupp.single a 1 ∈ carrier
  coefficient_bound : ∀ f ∈ carrier, ∀ a, |(f a : ℝ)| ≤ 1

namespace NormingSet
variable (K : NormingSet Γ)
abbrev BoundedSpace := lp (fun _ : K.carrier => ℝ) ⊤

def coordinateVector (a : Γ) : K.BoundedSpace :=
  ⟨fun f => (f.val a : ℝ), memℓp_infty ⟨1, by
    rintro _ ⟨f, rfl⟩
    exact K.coefficient_bound f.val f.property a⟩⟩

@[simp] lemma coordinateVector_apply (a : Γ) (f : K.carrier) :
    K.coordinateVector a f = (f.val a : ℝ) := rfl

/-- Algebraic inclusion of the prescribed finitely supported vectors. -/
def finiteMap : (Γ →₀ ℝ) →ₗ[ℝ] K.BoundedSpace :=
  Finsupp.linearCombination ℝ K.coordinateVector

@[simp] lemma finiteMap_single (a : Γ) (t : ℝ) :
    K.finiteMap (Finsupp.single a t) = t • K.coordinateVector a :=
  Finsupp.linearCombination_single _ _ _

lemma finiteMap_apply (x : Γ →₀ ℝ) (f : K.carrier) :
    K.finiteMap x f = x.sum (fun a t => t * (f.val a : ℝ)) := by
  change (lp.evalₗ (𝕜 := ℝ) (fun _ : K.carrier => ℝ) ⊤ f) (K.finiteMap x) = _
  simp only [finiteMap, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    map_smul, lp.evalₗ_apply, K.coordinateVector_apply, smul_eq_mul]

@[simp] lemma finiteMap_coordinate (x : Γ →₀ ℝ) (a : Γ) :
    K.finiteMap x ⟨Finsupp.single a 1, K.coordinate_mem a⟩ = x a := by
  classical
  rw [K.finiteMap_apply]
  simp [Finsupp.sum, Finsupp.single_apply, apply_ite, eq_comm]

/-- The concrete Banach completion. Its norm is literally the supremum of
absolute evaluations over K. -/
def closedSpan : Submodule ℝ K.BoundedSpace := K.finiteMap.range.topologicalClosure
abbrev Space := K.closedSpan

instance instCompleteSpaceSubtypePreLpElemFinsuppRatCarrierRealMemAddSubgroupBoundedSpaceSubmoduleSpace : CompleteSpace K.Space := by
  let : IsClosed (K.closedSpan : Set K.BoundedSpace) :=
    Submodule.isClosed_topologicalClosure _
  exact IsClosed.completeSpace_coe

def includeFinite : (Γ →₀ ℝ) →ₗ[ℝ] K.Space :=
  K.finiteMap.codRestrict K.closedSpan (fun x =>
    Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

@[simp] lemma includeFinite_val (x : Γ →₀ ℝ) :
    (K.includeFinite x).val = K.finiteMap x := rfl

lemma denseRange_includeFinite : DenseRange K.includeFinite := by
  have hd : DenseRange (Set.inclusion (show (K.finiteMap.range : Set K.BoundedSpace) ⊆
      K.closedSpan from Submodule.le_topologicalClosure _)) :=
    (denseRange_inclusion_iff _).mpr (by intro x hx; exact hx)
  exact hd.comp (show Function.Surjective K.finiteMap.rangeRestrict from fun ⟨y, x, hx⟩ =>
      ⟨x, Subtype.ext hx⟩).denseRange
    (continuous_inclusion _)

def functional (f : K.carrier) : K.Space →L[ℝ] ℝ :=
  (lp.evalCLM ℝ (fun _ : K.carrier => ℝ) ⊤ f).comp K.closedSpan.subtypeL

def coordinate (a : Γ) : K.Space →L[ℝ] ℝ :=
  K.functional ⟨Finsupp.single a 1, K.coordinate_mem a⟩

@[simp] lemma functional_includeFinite (f : K.carrier) (x : Γ →₀ ℝ) :
    K.functional f (K.includeFinite x) = x.sum (fun a t => t * (f.val a : ℝ)) :=
  K.finiteMap_apply x f

@[simp] lemma coordinate_includeFinite (a : Γ) (x : Γ →₀ ℝ) :
    K.coordinate a (K.includeFinite x) = x a := K.finiteMap_coordinate x a

def generator (a : Γ) : K.Space := K.includeFinite (Finsupp.single a 1)

lemma functional_bound (f : K.carrier) (x : K.Space) : |K.functional f x| ≤ ‖x‖ :=
  lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x.val f

lemma norm_functional_le (f : K.carrier) : ‖K.functional f‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  simpa [Real.norm_eq_abs] using K.functional_bound f x

/-- Every norming functional is its finite coordinate combination even after
completion; hence no nonzero completed vector can vanish at every coordinate. -/
lemma functional_eq_sum (f : K.carrier) :
    K.functional f = ∑ a ∈ f.val.support, (f.val a : ℝ) • K.coordinate a := by
  classical
  let g : K.Space →L[ℝ] ℝ := ∑ a ∈ f.val.support, (f.val a : ℝ) • K.coordinate a
  have hlin : (K.functional f).toLinearMap.comp K.includeFinite =
      g.toLinearMap.comp K.includeFinite := by
    apply Finsupp.lhom_ext
    intro a t
    simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe,
      K.functional_includeFinite, Finsupp.sum_single_index, zero_mul]
    change t * (f.val a : ℝ) = (∑ b ∈ f.val.support,
      (f.val b : ℝ) • K.coordinate b) (K.includeFinite (Finsupp.single a t))
    simp only [sum_apply, smul_apply,
      K.coordinate_includeFinite, Finsupp.single_apply, smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · simp [mul_comm]
    · intro b _ hab
      simp [Ne.symm hab]
    · intro ha
      have hz : f.val a = 0 := by simpa using (not_congr Finsupp.mem_support_iff).mp ha
      simp [hz]
  apply DFunLike.coe_injective
  apply K.denseRange_includeFinite.equalizer (K.functional f).continuous g.continuous
  funext x
  exact LinearMap.congr_fun hlin x

lemma coordinates_separate (x : K.Space) (h : ∀ a, K.coordinate a x = 0) : x = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext f
  change K.functional f x = 0
  rw [K.functional_eq_sum]
  simp [h]

lemma coordinate_ext {x y : K.Space} (h : ∀ a, K.coordinate a x = K.coordinate a y) : x = y := by
  apply sub_eq_zero.mp
  apply K.coordinates_separate
  intro a
  rw [(K.coordinate a).map_sub x y, h a, sub_self]

end NormingSet
end SeparableQuotient.NormConstruction

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology ENNReal Classical
open Filter
universe u
variable {Γ : Type u} (K : NormingSet Γ)

/-- Stability of a norming set under the specified coordinate crop. -/
def CropStable (A : Set Γ) : Prop := ∀ f ∈ K.carrier, f.filter (· ∈ A) ∈ K.carrier

variable (A : Set Γ) (hA : K.CropStable A)

def cropNormer (f : K.carrier) : K.carrier := ⟨f.val.filter (· ∈ A), hA _ f.property⟩

def cropAmbient : K.BoundedSpace →L[ℝ] K.BoundedSpace :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨fun f => x (K.cropNormer A hA f), memℓp_infty ⟨‖x‖, by
        rintro _ ⟨f, rfl⟩
        exact lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x _⟩⟩
      map_add' := fun x y => by apply lp.ext; rfl
      map_smul' := fun c x => by apply lp.ext; rfl }
    1 (fun x => by
      simpa only [one_mul] using lp.norm_le_of_forall_le (norm_nonneg x)
        (fun f => lp.norm_apply_le_norm (by simp : (⊤ : ℝ≥0∞) ≠ 0) x
          (K.cropNormer A hA f)))

@[simp] lemma cropAmbient_apply (x : K.BoundedSpace) (f : K.carrier) :
    K.cropAmbient A hA x f = x (K.cropNormer A hA f) := rfl

lemma cropAmbient_finiteMap (x : Γ →₀ ℝ) :
    K.cropAmbient A hA (K.finiteMap x) = K.finiteMap (x.filter (· ∈ A)) := by
  apply lp.ext
  funext f
  rw [K.cropAmbient_apply, K.finiteMap_apply, K.finiteMap_apply]
  simp only [cropNormer, Finsupp.filter_apply, apply_ite, Rat.cast_zero,
    mul_zero]
  rw [Finsupp.sum_filter_index]
  simp only [Finsupp.sum, Finsupp.support_filter, Finset.sum_filter]

lemma cropAmbient_mem (x : K.Space) : K.cropAmbient A hA x.val ∈ K.closedSpan := by
  have hi : K.finiteMap.range ∈ Module.End.invtSubmodule (K.cropAmbient A hA) := by
    rw [Module.End.mem_invtSubmodule_iff_map_le]
    rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨v.filter (· ∈ A), (K.cropAmbient_finiteMap A hA v).symm⟩
  have hc := Submodule.topologicalClosure_mem_invtSubmodule hi
  rw [Module.End.mem_invtSubmodule_iff_map_le] at hc
  exact hc ⟨x.val, x.property, rfl⟩

/-- Contractive interval/rectangle projection on the actual Banach completion. -/
def projection : K.Space →L[ℝ] K.Space :=
  ((K.cropAmbient A hA).comp K.closedSpan.subtypeL).codRestrict K.closedSpan
    (K.cropAmbient_mem A hA)

@[simp] lemma projection_includeFinite (x : Γ →₀ ℝ) :
    K.projection A hA (K.includeFinite x) = K.includeFinite (x.filter (· ∈ A)) :=
  Subtype.ext (K.cropAmbient_finiteMap A hA x)

lemma coordinate_projection (a : Γ) (x : K.Space) :
    K.coordinate a (K.projection A hA x) = if a ∈ A then K.coordinate a x else 0 := by
  have h : (K.coordinate a).comp (K.projection A hA) =
      if a ∈ A then K.coordinate a else 0 := by
    apply DFunLike.coe_injective
    apply K.denseRange_includeFinite.equalizer
      ((K.coordinate a).comp (K.projection A hA)).continuous
      (if a ∈ A then K.coordinate a else (0 : K.Space →L[ℝ] ℝ)).continuous
    funext v
    by_cases ha : a ∈ A <;> simp [ha]
  by_cases ha : a ∈ A <;> simpa [ha] using DFunLike.congr_fun h x

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinateDual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

@[reducible] local instance dualNormedGroup : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance

/-- The coordinate predual. -/
def predual : Submodule ℝ (StrongDual ℝ K.Space) :=
  (Submodule.span ℝ (Set.range K.coordinate)).topologicalClosure

instance predual_isClosed : IsClosed (K.predual : Set (StrongDual ℝ K.Space)) :=
  Submodule.isClosed_topologicalClosure _

lemma coordinate_mem_predual (a : Γ) : K.coordinate a ∈ K.predual :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a, rfl⟩)

@[reducible] local instance predualDualNormedGroup :
    NormedAddCommGroup (StrongDual ℝ K.predual) := inferInstance
@[reducible] local instance predualDualNormedSpace :
    NormedSpace ℝ (StrongDual ℝ K.predual) := inferInstance

/-- Canonical evaluation into the dual of the coordinate span. -/
def evaluation : K.Space →L[ℝ] StrongDual ℝ K.predual :=
  (ContinuousLinearMap.precomp ℝ K.predual.subtypeL).comp
    (NormedSpace.inclusionInDoubleDual ℝ K.Space)

@[simp] lemma evaluation_apply (x : K.Space) (g : K.predual) :
    K.evaluation x g = g.val x := rfl

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Topology Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)
@[reducible] local instance dualNormedGroup' : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace' : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance

/-- The coordinate functional regarded as an element of the actual predual. -/
def predualCoordinate (a : Γ) : K.predual := ⟨K.coordinate a, K.coordinate_mem_predual a⟩

def rationalPredual : (Γ →₀ ℚ) →ₗ[ℚ] K.predual :=
  Finsupp.linearCombination ℚ K.predualCoordinate

lemma rationalPredual_val (f : Γ →₀ ℚ) :
    (K.rationalPredual f).val = ∑ a ∈ f.support, (f a : ℝ) • K.coordinate a := by
  simp only [rationalPredual, Finsupp.linearCombination_apply, Finsupp.sum]
  rw [show (∑ a ∈ f.support, f a • K.predualCoordinate a).val =
      ∑ a ∈ f.support, (f a • K.predualCoordinate a).val from
    Submodule.coe_sum _ _ _]
  congr 1

lemma rationalPredual_eq_functional (f : K.carrier) :
    (K.rationalPredual f.val).val = K.functional f := by
  rw [K.rationalPredual_val, K.functional_eq_sum]

@[simp] lemma rationalPredual_single (a : Γ) (q : ℚ) :
    K.rationalPredual (Finsupp.single a q) = q • K.predualCoordinate a :=
  Finsupp.linearCombination_single _ _ _

lemma rationalPredual_apply (f : Γ →₀ ℚ) (x : K.Space) :
    (K.rationalPredual f).val x = ∑ a ∈ f.support, (f a : ℝ) * K.coordinate a x := by
  rw [K.rationalPredual_val]
  simp only [sum_apply, smul_apply, smul_eq_mul]

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)
@[reducible] local instance dualNormedGroup'' : NormedAddCommGroup (StrongDual ℝ K.Space) := inferInstance
@[reducible] local instance dualNormedSpace'' : NormedSpace ℝ (StrongDual ℝ K.Space) := inferInstance

/-- Evaluation of any rational array, not only chosen normers. -/
def evaluateArray (x : K.Space) : (Γ →₀ ℚ) →ₗ[ℚ] ℝ where
  toFun := fun f => (K.rationalPredual f).val x
  map_add' := by intro f g; simp
  map_smul' := by intro q f; simp

lemma evaluateArray_eq (x : K.Space) (f : Γ →₀ ℚ) :
    K.evaluateArray x f = ∑ a ∈ f.support, (f a : ℝ) * K.coordinate a x :=
  K.rationalPredual_apply f x

lemma evaluateArray_eq_functional (x : K.Space) (f : K.carrier) :
    K.evaluateArray x f.val = K.functional f x := by
  change (K.rationalPredual f).val x = _
  rw [K.rationalPredual_eq_functional f]

end SeparableQuotient.NormConstruction.NormingSet

namespace SeparableQuotient.NormConstruction.NormingSet
open scoped Classical
universe u
variable {Γ : Type u} (K : NormingSet Γ)

lemma evaluateArray_projection (x : K.Space) (A : Set Γ) (hA : K.CropStable A)
    (f : Γ →₀ ℚ) :
    K.evaluateArray (K.projection A hA x) f = K.evaluateArray x (f.filter (· ∈ A)) := by
  rw [K.evaluateArray_eq, K.evaluateArray_eq]
  simp only [Finsupp.support_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  rw [K.coordinate_projection]
  by_cases ha : a ∈ A <;> simp [ha]

end SeparableQuotient.NormConstruction.NormingSet

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.CoordinatePredual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

/-- The full norming set obtained from finite-stage pure and mixed operations. -/
def norming : NormingSet Γ where
  carrier := Full
  coordinate_mem := Norming.coordinate_mem
  coefficient_bound := full_coefficient_bound

/-- The actual real Banach space E of the CH construction. -/
abbrev E := norming.Space

@[reducible] instance EGroup : NormedAddCommGroup E := inferInstanceAs (NormedAddCommGroup norming.Space)
@[reducible] instance ESpace : NormedSpace ℝ E := inferInstanceAs (NormedSpace ℝ norming.Space)
instance ETopologicalAdd : IsTopologicalAddGroup E :=
  SeminormedAddCommGroup.toIsTopologicalAddGroup

instance instCompleteSpaceSubtypePreLpElemFinsuppΓRatCarrierNormingRealMemAddSubgroupBoundedSpaceSubmoduleE : CompleteSpace E := inferInstanceAs (CompleteSpace norming.Space)

instance instInfiniteΓ : Infinite Γ := Cardinal.infinite_iff.mpr (by
  simp [Γ, CoherentClosures.OmegaOne])

abbrev e (a : Γ) : E := norming.generator a
abbrev coordinate (a : Γ) : StrongDual ℝ E := norming.coordinate a

lemma cropStable (A : Crop) : norming.CropStable (A.set .mixed) :=
  full_crop A

/-- Every ordinal/color rectangle projection is defined on the full completion. -/
def projection (A : Crop) : E →L[ℝ] E := norming.projection (A.set .mixed) (cropStable A)

lemma coordinate_projection (A : Crop) (x : E) (a : Γ) :
    coordinate a (projection A x) = if a ∈ A.set .mixed then coordinate a x else 0 :=
  norming.coordinate_projection (A.set .mixed) (cropStable A) a x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction LpFinite
open scoped Classical ENNReal

/-- The ℓs-coordinate estimate on finite vectors. -/
lemma norm_includeFinite_on_color (k : ℕ) (x : Γ →₀ ℝ)
    (hx : ∀ a ∈ x.support, Colors.color a = k) :
    ‖norming.includeFinite x‖ ≤ ‖realArray (Family.pure k).primalExponent x‖ := by
  change ‖norming.finiteMap x‖ ≤ ‖realArray (Family.pure k).primalExponent x‖
  apply lp.norm_le_of_forall_le (norm_nonneg _)
  intro f
  rw [norming.finiteMap_apply]
  have heq : x.sum (fun a t => t * (f.val a : ℝ)) =
      x.sum (fun a t => t * (restrict (colorSet k) f.val a : ℝ)) := by
    apply Finset.sum_congr rfl
    intro a ha
    simp only [restrict_apply, colorSet, Set.mem_ofPred_eq, hx a ha, ↓reduceIte]
  rw [heq]
  calc
    _ ≤ ‖realArray (Family.pure k).primalExponent x‖ *
        ‖array (Family.pure k).exponent (restrict (colorSet k) f.val)‖ :=
      pairing_le (Family.conjugate (.pure k)) _ _
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (full_color_lp_bound k f.val f.property)
        (norm_nonneg (realArray (Family.pure k).primalExponent x))

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

abbrev X₀ := norming.predual

@[reducible] local instance dualEGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical

@[reducible] local instance dualEGroup2 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace2 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup2 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace2 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup2 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace2 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.ordinalSet (I : Set Γ) (hI : Set.OrdConnected I) : Crop :=
  ⟨I, hI, Set.univ, Set.ordConnected_univ⟩

def Crop.colorSet (D : Set ℕ) (hD : Set.OrdConnected D) : Crop :=
  ⟨Set.univ, Set.ordConnected_univ, D, hD⟩

def Crop.oneColor (k : ℕ) : Crop := Crop.colorSet {k} Set.ordConnected_singleton

def Crop.colorsBelow (n : ℕ) : Crop := Crop.colorSet (Set.Iio n) Set.ordConnected_Iio

@[simp] lemma Crop.oneColor_set (k : ℕ) : (Crop.oneColor k).set .mixed = Norming.colorSet k := by
  ext a
  simp [Crop.oneColor, Crop.colorSet, Crop.set, Norming.colorSet]

@[simp] lemma Crop.colorsBelow_set (n : ℕ) :
    (Crop.colorsBelow n).set .mixed = {a | Colors.color a < n} := by
  ext a
  simp [Crop.colorsBelow, Crop.colorSet, Crop.set]

@[simp] lemma Crop.ordinalSet_set (I : Set Γ) (hI : Set.OrdConnected I) :
    (Crop.ordinalSet I hI).set .mixed = I := by
  ext a
  simp [Crop.ordinalSet, Crop.set]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction
open scoped Classical

@[reducible] local instance dualEGroup3 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace3 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup3 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace3 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup3 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace3 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BoundedCompleteness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup4 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace4 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup4 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace4 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup4 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace4 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open scoped Classical

def Crop.colorWindow (lo hi : ℕ) : Crop := Crop.colorSet (Set.Ico lo hi) Set.ordConnected_Ico

@[simp] lemma Crop.colorWindow_set (lo hi : ℕ) :
    (Crop.colorWindow lo hi).set .mixed = {a | lo ≤ Colors.color a ∧ Colors.color a < hi} := by
  ext a
  simp [Crop.colorWindow, Crop.colorSet, Crop.set]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup5 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace5 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup5 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace5 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup5 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace5 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup6 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace6 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup6 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace6 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup6 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace6 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup7 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace7 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup7 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace7 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup7 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace7 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.PathLimits
open Filter
open scoped Topology
universe u
variable {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma unit_bound (f : StrongDual ℝ Z) (hf : ‖f‖ ≤ 1) (x : Z) : ‖f x‖ ≤ ‖x‖ :=
  (f.le_opNorm x).trans (by simpa only [one_mul] using
    mul_le_mul_of_nonneg_right hf (norm_nonneg x))

lemma cauchy_of_dense (f : ℕ → StrongDual ℝ Z) (hf : ∀ n, ‖f n‖ ≤ 1)
    (D : Set Z) (hD : Dense D) (h : ∀ x ∈ D, CauchySeq (fun n => f n x)) (x : Z) :
    CauchySeq (fun n => f n x) := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hD x) (ε/4) (by positivity)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (h y hy) (ε/4) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  have hmxy : dist (f m x) (f m y) ≤ dist x y := by
    simpa only [dist_eq_norm, ← map_sub] using unit_bound (f m) (hf m) (x-y)
  have hnxy : dist (f n y) (f n x) ≤ dist x y := by
    rw [dist_comm (f n y)]
    simpa only [dist_eq_norm, ← map_sub] using unit_bound (f n) (hf n) (x-y)
  have ht := calc
    dist (f m x) (f n x) ≤ dist (f m x) (f m y) + dist (f m y) (f n x) := dist_triangle _ _ _
    _ ≤ dist (f m x) (f m y) + (dist (f m y) (f n y) + dist (f n y) (f n x)) :=
      add_le_add le_rfl (dist_triangle _ _ _)
  have := hN m hm n hn
  have hd : dist x y < ε/4 := by simpa only [dist_comm] using hxy
  linarith

/-- Bounded pointwise convergence on a dense set determines an actual bounded
functional on the completed space; no weak-star sequential compactness is used. -/
lemma exists_limit_of_dense (f : ℕ → StrongDual ℝ Z) (hf : ∀ n, ‖f n‖ ≤ 1)
    (D : Set Z) (hD : Dense D) (h : ∀ x ∈ D, CauchySeq (fun n => f n x)) :
    ∃ P : StrongDual ℝ Z, ‖P‖ ≤ 1 ∧ ∀ x, Tendsto (fun n => f n x) atTop (𝓝 (P x)) := by
  choose g hg using (fun x => cauchySeq_tendsto_of_complete (cauchy_of_dense f hf D hD h x))
  have hb : Bornology.IsBounded (Set.range f) := isBounded_iff_forall_norm_le.mpr
    ⟨1, by rintro _ ⟨n, rfl⟩; exact hf n⟩
  let P : StrongDual ℝ Z := ContinuousLinearMap.ofTendstoOfBoundedRange g f
    (tendsto_pi_nhds.mpr hg) hb
  have hP : ‖P‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound P (by norm_num)
    intro x
    simpa only [P, ContinuousLinearMap.ofTendstoOfBoundedRange_apply, one_mul] using le_of_tendsto (hg x).norm
      (Filter.Eventually.of_forall (fun n => unit_bound (f n) (hf n) x))
  exact ⟨P, hP, hg⟩

end SeparableQuotient.PathLimits

namespace SeparableQuotient.Norming
open scoped Classical
open PathCoding

def Family.base : Family → Set Array
  | .pure k => pureBase k
  | .mixed => ⋃ k, Pure k

def Family.norming (f : Family) : Set Array := ⋃ n, stage f.base f n

lemma Family.norming_subset_full (f : Family) : f.norming ⊆ Full := by
  cases f with
  | pure k => exact pure_subset_full k
  | mixed => exact Set.Subset.rfl

lemma common_stage {f : Family} {ι : Type*} [Fintype ι] (x : ι → Array)
    (hx : ∀ i, x i ∈ f.norming) : ∃ n, ∀ i, x i ∈ stage f.base f n := by
  have hh : ∀ i, ∃ n, x i ∈ stage f.base f n := fun i => Set.mem_iUnion.mp (hx i)
  choose n hn using hh
  exact ⟨Finset.univ.sup n, fun i => stage_mono _ _ (Finset.le_sup (Finset.mem_univ i)) (hn i)⟩

lemma TypeII.mem_family {f : Family} (e : TypeII f)
    (h : ∀ b i j, ((e.path b).piece i).child j ∈ f.norming) : e.value ∈ f.norming := by
  let ι := Σ b : Fin e.length, Σ i : Fin (e.path b).length, Fin ((e.path b).piece i).length
  obtain ⟨n, hn⟩ := common_stage (fun a : ι => ((e.path a.1).piece a.2.1).child a.2.2)
    (fun a => h a.1 a.2.1 a.2.2)
  exact Set.mem_iUnion.mpr ⟨n+1, Or.inr ⟨e, rfl, fun b i j => hn ⟨b,i,j⟩⟩⟩

lemma admissible_prefix {P : RawPath} (h : P.Admissible) (n : ℕ) : PrefixValid P n where
  successive := fun i j hij _ => h.successive i j hij
  metadata_strict := fun _i _j hij _ => h.metadata_strict hij
  metadata_pos := fun i _ => h.metadata_pos i
  weight_pos := fun i _ => h.weight_pos i
  weight_le_metadata := fun i _ => h.weight_le_metadata i
  rho_bound := fun i _ => h.rho_bound i
  rule := fun i _ => h.rule i

/-- Actual infinite paths retain all original Type I expressions, weights, and
uncropped metadata. No completion of the coding tree is inserted as a path. -/
structure InfinitePath (f : Family) where
  raw : RawPath
  admissible : raw.Admissible
  piece : ℕ → TypeI f
  value_eq : ∀ i, (piece i).value = raw.piece i
  weight_eq : ∀ i, (piece i).weight = raw.weight i
  successive : ∀ i j, i < j → Successive f (raw.piece i) (raw.piece j)
  children_mem : ∀ i j, (piece i).child j ∈ f.norming

def InfinitePath.prefix {f : Family} (P : InfinitePath f) (n : ℕ) : FinitePath f where
  raw := P.raw
  length := n+1
  length_pos := by omega
  valid := admissible_prefix P.admissible (n+1)
  piece := fun i => P.piece i
  value_eq := fun i => P.value_eq i
  weight_eq := fun i => P.weight_eq i
  mixed_successive := fun i j hij => P.successive i j hij

def FinitePath.oneTerm {f : Family} (P : FinitePath f) (A : Crop) : TypeII f where
  length := 1
  path := fun _ => P
  crop := fun _ => A
  coefficient := fun _ => 1
  bound := by simp
  disjoint_active := fun b c hbc => (hbc (Subsingleton.elim _ _)).elim

@[simp] lemma FinitePath.oneTerm_value {f : Family} (P : FinitePath f) (A : Crop) :
    (P.oneTerm A).value = restrict (A.set f) P.value := by
  change (∑ _b : Fin 1, (1 : ℚ) • restrict (A.set f) P.value) = _
  simp

lemma InfinitePath.prefix_crop_mem {f : Family} (P : InfinitePath f) (n : ℕ) (A : Crop) :
    restrict (A.set f) (P.prefix n).value ∈ f.norming := by
  rw [← FinitePath.oneTerm_value]
  exact TypeII.mem_family _ (fun _ i j => P.children_mem i j)

lemma InfinitePath.prefix_mem {f : Family} (P : InfinitePath f) (n : ℕ) :
    (P.prefix n).value ∈ Full := by
  apply f.norming_subset_full
  simpa only [Crop.all_set, restrict_univ] using P.prefix_crop_mem n Crop.all

lemma InfinitePath.piece_coefficient_unique {f : Family} (P : InfinitePath f)
    {i j : ℕ} {a : Γ} (hi : P.raw.piece i a ≠ 0) (hj : P.raw.piece j a ≠ 0) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with h | h
  · have := P.admissible.successive i j h a (Finsupp.mem_support_iff.mpr hi)
      a (Finsupp.mem_support_iff.mpr hj)
    exact (lt_irrefl a) this
  · have := P.admissible.successive j i h a (Finsupp.mem_support_iff.mpr hj)
      a (Finsupp.mem_support_iff.mpr hi)
    exact (lt_irrefl a) this

lemma InfinitePath.prefix_at_hit {f : Family} (P : InfinitePath f) (a : Γ) (i n : ℕ)
    (hi : P.raw.piece i a ≠ 0) (hin : i ≤ n) :
    (P.prefix n).value a = P.raw.piece i a := by
  change (∑ j : Fin (n+1), P.raw.piece j) a = _
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (⟨i, by omega⟩ : Fin (n+1))]
  · intro j _ hji
    by_contra hn
    exact hji (Fin.ext (P.piece_coefficient_unique hn hi))
  · simp

lemma InfinitePath.prefix_coordinate_eventually_constant {f : Family} (P : InfinitePath f)
    (a : Γ) : ∃ q : ℚ, ∀ᶠ n in Filter.atTop, (P.prefix n).value a = q := by
  by_cases h : ∃ i, P.raw.piece i a ≠ 0
  · obtain ⟨i, hi⟩ := h
    exact ⟨P.raw.piece i a, (Filter.eventually_ge_atTop i).mono (fun n hn => P.prefix_at_hit a i n hi hn)⟩
  · push Not at h
    refine ⟨0, Filter.Eventually.of_forall (fun n => ?_)⟩
    change (∑ j : Fin (n+1), P.raw.piece j) a = 0
    simp only [Finsupp.finsetSum_apply, h, Finset.sum_const_zero]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup8 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace8 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

def pathPartial {f : Family} (P : InfinitePath f) (n : ℕ) : StrongDual ℝ E :=
  norming.functional ⟨(P.prefix n).value, P.prefix_mem n⟩

lemma pathPartial_bound {f : Family} (P : InfinitePath f) (n : ℕ) : ‖pathPartial P n‖ ≤ 1 :=
  norming.norm_functional_le _

lemma pathPartial_finite_cauchy {f : Family} (P : InfinitePath f) (x : Γ →₀ ℝ) :
    CauchySeq (fun n => pathPartial P n (norming.includeFinite x)) := by
  choose q hq using P.prefix_coordinate_eventually_constant
  have he : ∀ᶠ n in atTop, pathPartial P n (norming.includeFinite x) =
      x.sum (fun a t => t * (q a : ℝ)) := by
    filter_upwards [(Filter.eventually_all_finset x.support).mpr (fun a _ => hq a)] with n hn
    rw [pathPartial, norming.functional_includeFinite]
    apply Finset.sum_congr rfl
    intro a ha
    change x a * ((P.prefix n).value a : ℝ) = x a * (q a : ℝ)
    rw [hn a ha]
  exact (tendsto_const_nhds.congr' (he.mono fun _ h => h.symm)).cauchySeq

lemma exists_pathFunctional {f : Family} (P : InfinitePath f) :
    ∃ F : StrongDual ℝ E, ‖F‖ ≤ 1 ∧ ∀ x, Tendsto (fun n => pathPartial P n x) atTop (𝓝 (F x)) := by
  apply PathLimits.exists_limit_of_dense _ (pathPartial_bound P) _ norming.denseRange_includeFinite
  rintro _ ⟨x, rfl⟩
  exact pathPartial_finite_cauchy P x

/-- Path partial sums are bounded and converge pointwise. -/
def pathFunctional {f : Family} (P : InfinitePath f) : StrongDual ℝ E :=
  (exists_pathFunctional P).choose

lemma pathPartial_tendsto {f : Family} (P : InfinitePath f) (x : E) :
    Tendsto (fun n => pathPartial P n x) atTop (𝓝 (pathFunctional P x)) :=
  (exists_pathFunctional P).choose_spec.2 x

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

def InfinitePath.tailCrop {f : Family} (P : InfinitePath f) (N : ℕ) : Crop where
  ordinal := Set.Ioi (P.raw.endpoint N)
  ordinal_convex := Set.ordConnected_Ioi
  colors := Set.univ
  colors_convex := Set.ordConnected_univ

@[simp] lemma InfinitePath.tailCrop_set {f g : Family} (P : InfinitePath f) (N : ℕ) :
    (P.tailCrop N).set g = Set.Ioi (P.raw.endpoint N) := by
  cases g <;> simp [Crop.set, InfinitePath.tailCrop]

lemma InfinitePath.before_endpoint {f : Family} (P : InfinitePath f)
    {N i : ℕ} (hi : i ≤ N) {a : Γ} (ha : a ∈ (P.raw.piece i).support) :
    a ≤ P.raw.endpoint N := P.raw.le_endpoint (P.raw.piece_support_subset hi ha)

lemma InfinitePath.after_endpoint {f : Family} (P : InfinitePath f)
    {N i : ℕ} (hi : N < i) {a : Γ} (ha : a ∈ (P.raw.piece i).support) :
    P.raw.endpoint N < a := by
  obtain ⟨j, hj, he⟩ := (P.raw.mem_support_iff N _).mp (P.raw.endpoint_mem N)
  exact P.admissible.successive j i (hj.trans_lt hi) _ he a ha

lemma InfinitePath.tail_piece {f : Family} (P : InfinitePath f) (N i : ℕ) :
    restrict ((P.tailCrop N).set f) (P.raw.piece i) = if N < i then P.raw.piece i else 0 := by
  ext a
  rw [restrict_apply, tailCrop_set]
  by_cases hai : P.raw.piece i a = 0
  · by_cases hi : N < i <;> simp [hi, hai]
  · have ha := Finsupp.mem_support_iff.mpr hai
    by_cases hi : N < i
    · simp [hi, P.after_endpoint hi ha]
    · have hnot : ¬ P.raw.endpoint N < a := not_lt_of_ge (P.before_endpoint (Nat.le_of_not_gt hi) ha)
      simp [hi, hnot]

lemma InfinitePath.tail_active_subset {f : Family} (P : InfinitePath f) (N n : ℕ) :
    ↑((P.prefix n).active (P.tailCrop N)) ⊆ Set.range (fun i => P.raw.weight (i+N+1)) := by
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
  have hi' := (Finset.mem_filter.mp hi).2
  change restrict ((P.tailCrop N).set f) (P.raw.piece i) ≠ 0 at hi'
  rw [P.tail_piece] at hi'
  have hNi : N < (i : ℕ) := by
    by_contra hn
    exact hi' (ite_eq_right hn)
  refine ⟨(i : ℕ)-N-1, ?_⟩
  change P.raw.weight (((i : ℕ)-N-1)+N+1) = P.raw.weight i
  congr 1
  omega

lemma InfinitePath.tail_prefix_coeff {f : Family} (P : InfinitePath f) (N n : ℕ)
    (hn : N ≤ n) :
    restrict ((P.tailCrop N).set f) (P.prefix n).value =
      (P.prefix n).value - (P.prefix N).value := by
  ext a
  rw [restrict_apply, tailCrop_set, Finsupp.sub_apply, Set.mem_Ioi]
  by_cases ha : P.raw.endpoint N < a
  · rw [ite_eq_left ha]
    have hz : (P.prefix N).value a = 0 := by
      change (∑ i : Fin (N+1), P.raw.piece i) a = 0
      rw [Finsupp.finsetSum_apply]
      apply Finset.sum_eq_zero
      intro i _
      by_contra h
      exact (not_le_of_gt ha) (P.before_endpoint (by omega) (Finsupp.mem_support_iff.mpr h))
    simp [hz]
  · rw [ite_eq_right ha]
    by_cases hz : (P.prefix n).value a = 0
    · have hzN : (P.prefix N).value a = 0 := by
        by_contra hzN
        have hit := (P.prefix N).value_at_hit a
        change (P.prefix N).value a = P.raw.piece ((P.prefix N).hitIndex a) a at hit
        have hh : P.raw.piece ((P.prefix N).hitIndex a) a ≠ 0 := by rwa [← hit]
        have he := P.prefix_at_hit a ((P.prefix N).hitIndex a) n hh
          (by have := ((P.prefix N).hitIndex a).isLt; change _ < N+1 at this; omega)
        exact hh (he.symm.trans hz)
      simp [hz, hzN]
    · have hit := (P.prefix n).value_at_hit a
      change (P.prefix n).value a = P.raw.piece ((P.prefix n).hitIndex a) a at hit
      have hh : P.raw.piece ((P.prefix n).hitIndex a) a ≠ 0 := by rwa [← hit]
      have hi : ((P.prefix n).hitIndex a : ℕ) ≤ N := by
        by_contra hi
        exact ha (P.after_endpoint (Nat.lt_of_not_ge hi) (Finsupp.mem_support_iff.mpr hh))
      rw [P.prefix_at_hit a _ N hh hi, hit, sub_self]

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup9 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace9 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

lemma pathPartial_crop_apply {f : Family} (P : InfinitePath f) (N n : ℕ) (x : E) :
    pathPartial P n (projection (P.tailCrop N) x) =
      norming.evaluateArray x (restrict ((P.tailCrop N).set f) (P.prefix n).value) := by
  rw [pathPartial, ← norming.evaluateArray_eq_functional]
  change norming.evaluateArray (norming.projection _ _ x) _ = _
  rw [norming.evaluateArray_projection]
  simp only [InfinitePath.tailCrop_set, restrict]

def pathTail {f : Family} (P : InfinitePath f) (N : ℕ) : StrongDual ℝ E :=
  (pathFunctional P).comp (projection (P.tailCrop N))

lemma pathTail_complement {f : Family} (P : InfinitePath f) (N : ℕ) :
    pathFunctional P - pathTail P N = (norming.rationalPredual (P.prefix N).value).val := by
  ext x
  have ht := (pathPartial_tendsto P x).sub
    (pathPartial_tendsto P (projection (P.tailCrop N) x))
  apply tendsto_nhds_unique ht
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  rw [pathPartial_crop_apply, P.tail_prefix_coeff N n hn, map_sub]
  rw [norming.evaluateArray_eq_functional x ⟨(P.prefix n).value, P.prefix_mem n⟩]
  change norming.evaluateArray x (P.prefix N).value = _
  simp only [pathPartial]
  ring

lemma pathTail_complement_mem {f : Family} (P : InfinitePath f) (N : ℕ) :
    pathFunctional P - pathTail P N ∈ X₀ := by
  rw [pathTail_complement]
  exact (norming.rationalPredual (P.prefix N).value).property

/-- The exact original coding is retained in all finite tails. -/
lemma rational_tail_bound {f : Family} {h : ℕ} (P : Fin h → InfinitePath f) (N : ℕ)
    (hdis : Pairwise (fun i j => Disjoint
      (Set.range (fun n => (P i).raw.weight (n+N+1)))
      (Set.range (fun n => (P j).raw.weight (n+N+1)))))
    (c : Fin h → ℚ) (hc : ∑ i, |(c i : ℝ)| ^ f.q ≤ 1) :
    ‖∑ i, (c i : ℝ) • pathTail (P i) N‖ ≤ 1 := by
  let e : ℕ → TypeII f := fun n => {
    length := h
    path := fun i => (P i).prefix n
    crop := fun i => (P i).tailCrop N
    coefficient := c
    bound := hc
    disjoint_active := fun i j hij => Finset.disjoint_left.mpr (fun w hw hw' =>
      Set.disjoint_left.mp (hdis hij) ((P i).tail_active_subset N n hw)
        ((P j).tail_active_subset N n hw')) }
  have he : ∀ n, (e n).value ∈ Full := fun n => f.norming_subset_full
    ((e n).mem_family (fun i j k => (P i).children_mem j k))
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  have ht : Tendsto (fun n => ∑ i, (c i : ℝ) * pathPartial (P i) n
      (projection ((P i).tailCrop N) x)) atTop
      (𝓝 (∑ i, (c i : ℝ) * pathTail (P i) N x)) := by
    apply tendsto_finsetSum _
    intro i _
    exact tendsto_const_nhds.mul (pathPartial_tendsto (P i) _)
  have hb : ∀ n, ‖∑ i, (c i : ℝ) * pathPartial (P i) n
      (projection ((P i).tailCrop N) x)‖ ≤ ‖x‖ := by
    intro n
    have heq : norming.evaluateArray x (e n).value = ∑ i, (c i : ℝ) *
        pathPartial (P i) n (projection ((P i).tailCrop N) x) := by
      simp only [e, TypeII.value, map_sum, map_rat_smul, Rat.smul_def,
        pathPartial_crop_apply]
    rw [← heq, norming.evaluateArray_eq_functional x ⟨(e n).value, he n⟩]
    exact PathLimits.unit_bound _ (norming.norm_functional_le _) x
  simpa only [sum_apply, smul_apply,
    smul_eq_mul, one_mul] using le_of_tendsto ht.norm (Eventually.of_forall hb)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.RealCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.RealCoefficients
open Filter
open scoped Topology
universe u v
variable {ι : Type u} [Fintype ι]
variable {Z : Type v} [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Rational coefficients suffice for the closed finite-dimensional ℓq ball.
This uses actual density, not an assumed real Type II operation. -/
lemma rational_to_real (q : ℝ) (hq : 0 < q) (v : ι → Z)
    (h : ∀ c : ι → ℚ, (∑ i, |(c i : ℝ)| ^ q) ≤ 1 → ‖∑ i, (c i : ℝ) • v i‖ ≤ 1)
    (c : ι → ℝ) (hc : (∑ i, |c i| ^ q) ≤ 1) : ‖∑ i, c i • v i‖ ≤ 1 := by
  let Q : (ι → ℝ) → ℝ := fun c => ∑ i, |c i| ^ q
  let F : (ι → ℝ) → Z := fun c => ∑ i, c i • v i
  have hQ : Continuous Q := by
    apply continuous_finsetSum
    intro i _
    exact (Real.continuous_rpow_const hq.le).comp (continuous_apply i).abs
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro i _
    exact (continuous_apply i).smul continuous_const
  have hD : DenseRange (fun a : ι → ℚ => fun i => (a i : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  have hstrict : ∀ a : ι → ℝ, Q a < 1 → ‖F a‖ ≤ 1 := by
    intro a ha
    have hclosed : IsClosed {a : ι → ℝ | ‖F a‖ ≤ 1} := isClosed_le hF.norm continuous_const
    apply closure_minimal (s := {a : ι → ℝ | Q a < 1} ∩
        Set.range (fun a : ι → ℚ => fun i => (a i : ℝ))) (t := {a | ‖F a‖ ≤ 1})
        (by rintro _ ⟨hb, b, rfl⟩; exact h b hb.le) hclosed
    exact hD.open_subset_closure_inter (isOpen_lt hQ continuous_const) ha
  let t : ℕ → ℝ := fun n => 1 - 1/((n+2 : ℕ) : ℝ)
  have ht0 (n : ℕ) : 0 ≤ t n := by
    dsimp [t]
    have hd : (1 : ℝ) ≤ ((n+2 : ℕ) : ℝ) := by norm_cast; omega
    have : 1/((n+2 : ℕ) : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr hd
    linarith
  have ht1 (n : ℕ) : t n < 1 := by
    dsimp [t]
    have : 0 < 1/((n+2 : ℕ) : ℝ) := by positivity
    linarith
  have ht : Tendsto t atTop (𝓝 1) := by
    have hz : Tendsto (fun n : ℕ => 1/((n+2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 2).mpr tendsto_one_div_atTop_nhds_zero_nat
    simpa only [sub_zero] using tendsto_const_nhds.sub hz
  have hb (n : ℕ) : ‖F (t n • c)‖ ≤ 1 := by
    apply hstrict
    have he : Q (t n • c) = (t n)^q * Q c := by
      dsimp only [Q]
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (ht0 n),
        Real.mul_rpow (ht0 n) (abs_nonneg _), Finset.mul_sum]
    rw [he]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (Real.rpow_nonneg (ht0 n) _) hc)
      (Real.rpow_lt_one (ht0 n) (ht1 n) hq)
  have htF : Tendsto (fun n => F (t n • c)) atTop (𝓝 (F c)) := by
    have hcT : Tendsto (fun n => t n • c) atTop (𝓝 c) := by
      simpa only [one_smul] using ht.smul (tendsto_const_nhds (x := c))
    exact (hF.tendsto c).comp hcT
  exact le_of_tendsto htF.norm (Eventually.of_forall hb)

end SeparableQuotient.RealCoefficients

namespace SeparableQuotient.RealCoefficients
open scoped Classical
universe u v
variable {ι : Type u} [Fintype ι]
variable {Z : Type v} [SeminormedAddCommGroup Z] [NormedSpace ℝ Z]

lemma bound_from_unit (q : ℝ) (hq : 0 < q) (v : ι → Z)
    (h : ∀ c : ι → ℝ, (∑ i, |c i| ^ q) ≤ 1 → ‖∑ i, c i • v i‖ ≤ 1)
    (c : ι → ℝ) : ‖∑ i, c i • v i‖ ≤ (∑ i, |c i| ^ q) ^ (1/q) := by
  let z : ℝ := ∑ i, |c i| ^ q
  have hz : 0 ≤ z := Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (abs_nonneg _) _)
  by_cases hz0 : z = 0
  · have hc0 (i : ι) : c i = 0 := by
      have hi : |c i| ^ q ≤ z := Finset.single_le_sum
        (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
      rw [hz0] at hi
      have he : |c i| ^ q = 0 := le_antisymm hi (Real.rpow_nonneg (abs_nonneg _) _)
      exact abs_eq_zero.mp ((Real.rpow_eq_zero (abs_nonneg _) hq.ne').mp he)
    rw [show (∑ i, c i • v i) = 0 by simp [hc0], norm_zero]
    exact Real.rpow_nonneg hz _
  · let A : ℝ := z ^ (1/q)
    have hA : 0 < A := Real.rpow_pos_of_pos (lt_of_le_of_ne hz (Ne.symm hz0)) _
    have hAq : A^q = z := by
      rw [← Real.rpow_mul hz, one_div_mul_cancel hq.ne', Real.rpow_one]
    have hd : (∑ i, |c i/A| ^ q) = 1 := by
      simp only [abs_div, abs_of_pos hA, Real.div_rpow (abs_nonneg _) hA.le,
        ← Finset.sum_div, hAq]
      exact div_self hz0
    have hb := h (fun i => c i/A) hd.le
    have he : (∑ i, c i • v i) = A • (∑ i, (c i/A) • v i) := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [smul_smul, mul_div_cancel₀ _ hA.ne']
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos hA]
    exact mul_le_of_le_one_right hA.le hb

end SeparableQuotient.RealCoefficients

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathConvergence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding
open scoped Classical

/-- Paths are indexed by their full raw data, not by an arbitrary chosen
expression witnessing membership. The witness is retained when used. -/
def PathIndex (f : Family) := {r : RawPath // ∃ P : InfinitePath f, P.raw = r}

def PathIndex.repr {f : Family} (a : PathIndex f) : InfinitePath f := a.property.choose

@[simp] lemma PathIndex.repr_raw {f : Family} (a : PathIndex f) : a.repr.raw = a.val :=
  a.property.choose_spec

lemma PathIndex.repr_injective {f : Family} : Function.Injective
    (fun a : PathIndex f => a.repr.raw) := by
  intro a b hab
  apply Subtype.ext
  simpa only [PathIndex.repr_raw] using hab

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup10 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace10 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

lemma real_tail_bound {f : Family} {h : ℕ} (P : Fin h → InfinitePath f) (N : ℕ)
    (hdis : Pairwise (fun i j => Disjoint
      (Set.range (fun n => (P i).raw.weight (n+N+1)))
      (Set.range (fun n => (P j).raw.weight (n+N+1)))))
    (c : Fin h → ℝ) :
    ‖∑ i, c i • pathTail (P i) N‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q) := by
  have hq : 0 < f.q := lt_trans zero_lt_one (Parameters.q_bounds f.s_ge_two).1
  apply RealCoefficients.bound_from_unit f.q hq (fun i => pathTail (P i) N)
  intro a ha
  exact RealCoefficients.rational_to_real f.q hq (fun i => pathTail (P i) N)
    (rational_tail_bound P N hdis) a ha

lemma exists_tail_estimate {f : Family} {h : ℕ} (P : Fin h → InfinitePath f)
    (hinj : Function.Injective (fun i => (P i).raw)) :
    ∃ N, ∀ c : Fin h → ℝ,
      ‖∑ i, c i • pathTail (P i) N‖ ≤ (∑ i, |c i| ^ f.q) ^ (1/f.q) := by
  obtain ⟨N, hN⟩ := RawPath.Admissible.disjoint_weight_tails
    (fun i => (P i).raw) (fun i => (P i).admissible) hinj
  refine ⟨N, real_tail_bound P N ?_⟩
  intro i j hij
  apply (hN hij).mono
  · rintro w ⟨n, rfl⟩
    exact ⟨n+1, by change (P i).raw.weight ((n+1)+N) = (P i).raw.weight (n+N+1); congr 1; omega⟩
  · rintro w ⟨n, rfl⟩
    exact ⟨n+1, by change (P j).raw.weight ((n+1)+N) = (P j).raw.weight (n+N+1); congr 1; omega⟩

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

@[reducible] local instance dualEGroup11 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace11 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
@[reducible] local instance predualGroup11 : NormedAddCommGroup X₀ := inferInstance
@[reducible] local instance predualSpace11 : NormedSpace ℝ X₀ := inferInstance
@[reducible] local instance dualPredualGroup11 : NormedAddCommGroup (StrongDual ℝ X₀) := inferInstance
@[reducible] local instance dualPredualSpace11 : NormedSpace ℝ (StrongDual ℝ X₀) := inferInstance

/-- Admissible block sequences with real coefficients. Pure mode requires one color, mixed mode both orders. -/
structure BlockSequence (f : Family) where
  vector : ℕ → Γ →₀ ℝ
  nonzero : ∀ n, vector n ≠ 0
  successive : ∀ i j, i < j → ∀ a ∈ (vector i).support, ∀ b ∈ (vector j).support,
    a < b ∧ (f = .mixed → Colors.color a < Colors.color b)
  pure_color : ∀ k, f = .pure k → ∀ n a, a ∈ (vector n).support → Colors.color a = k

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathStabilization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology
@[reducible] local instance dualEGroup12 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace12 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathRigidity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology
@[reducible] local instance dualEGroup13 : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance dualESpace13 : NormedSpace ℝ (StrongDual ℝ E) := inferInstance

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.SeriesTails
open Filter
open scoped Topology Classical

noncomputable def tail (a : ℕ → ℝ) (N : ℕ) : ℝ := ∑' k, a (k+N)

end SeparableQuotient.SeriesTails

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def vectorL1 (x : Γ →₀ ℝ) : ℝ := ∑ a ∈ x.support, |x a|

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PartitionBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

noncomputable def ordinalHull (s : Finset Γ) (hs : s.Nonempty) : Set Γ :=
  Set.Icc (s.min' hs) (s.max' hs)

lemma ordinalHull_connected (s : Finset Γ) (hs : s.Nonempty) :
    Set.OrdConnected (ordinalHull s hs) := Set.ordConnected_Icc

noncomputable def intervalProjection (I : Set Γ) (hI : Set.OrdConnected I) : E →L[ℝ] E :=
  projection (Crop.ordinalSet I hI)

/-- An interval-partition inequality and its constant-16 difference-vector version. Intervals may be unbounded or singletons. -/
def PartitionBound (x : E) (N : ℕ) (A r : ℝ) : Prop :=
  ∀ d : ℕ, 1 ≤ d → d ≤ N → ∀ (I : Fin d → Set Γ) (hI : ∀ i, Set.OrdConnected (I i)),
    (∀ i j, i < j → ∀ a ∈ I i, ∀ b ∈ I j, a < b) →
    ∑ i : Fin d, ‖intervalProjection (I i) (hI i) x‖ ≤ A * (d : ℝ)^(1/r)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

/-- Algebraic finite blocks in the specified tail, with no completion added. -/
noncomputable def BlockSequence.tailSpan {f : Family} (z : BlockSequence f) (a : ℕ) :
    Submodule ℝ (Γ →₀ ℝ) := Submodule.span ℝ (Set.range (fun n => z.vector (n+a)))

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

noncomputable def vectorCrop (x : Γ →₀ ℝ) (hx : x ≠ 0) : Crop where
  ordinal := ordinalHull x.support (Finsupp.support_nonempty_iff.mpr hx)
  ordinal_convex := ordinalHull_connected _ _
  colors := Set.Icc ((x.support.image Colors.color).min' ((Finsupp.support_nonempty_iff.mpr hx).image _))
    ((x.support.image Colors.color).max' ((Finsupp.support_nonempty_iff.mpr hx).image _))
  colors_convex := Set.ordConnected_Icc

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.TailBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction Filter
open scoped Classical Topology

noncomputable def BlockSequence.prefixSupport {f : Family} (z : BlockSequence f) (b : ℕ) : Finset Γ :=
  (Finset.range b).biUnion (fun n => (z.vector n).support)

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter SeriesTails
open scoped Classical Topology

noncomputable def BlockSequence.prefixRho {f : Family} (z : BlockSequence f) (a : ℕ) : ℕ :=
  (z.prefixSupport a ×ˢ z.prefixSupport a).sup (fun p => rho (min p.1 p.2) (max p.1 p.2))

/-- The recursively selected unit blocks, before pathwise-Cauchy differences.
No weak compactness hypothesis is smuggled into this structure. -/
structure PreliminaryData {f : Family} (z : BlockSequence f) (J : ℕ) (ε : ℝ) (n : ℕ) where
  vector : Γ →₀ ℝ
  start : ℕ
  finish : ℕ
  lower : ℕ
  upper : ℕ
  mem : vector ∈ z.tailSpan start
  support : vector.support ⊆ z.prefixSupport finish
  finish_ge : start ≤ finish
  unit : ‖norming.includeFinite vector‖ = 1
  prescribed : J < lower
  order : lower ≤ upper
  coherence : z.prefixRho start < lower
  partition : PartitionBound (norming.includeFinite vector) (f.L lower) 8 f.r
  tail_small : vectorL1 vector * tail (fun j => 1/(f.m j : ℝ)) (upper+1) ≤ ε/2
  tail_vanish : vectorL1 vector * tail (fun j => 1/(f.m j : ℝ)) (upper+1) ≤ 1/(n+1 : ℝ)

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.WindowThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.AdaptiveThinning
open scoped Classical

variable (R : ℕ → ℕ → Set ℕ → Prop)
variable (hR : ∀ n i (N : Set ℕ), N.Infinite → ∃ W ⊆ N, W.Infinite ∧ R n i W)

structure Step (n : ℕ) (N : Set ℕ) where
  index : ℕ
  mem : index ∈ N
  rest : Set ℕ
  infinite : rest.Infinite
  subset : rest ⊆ N
  later : ∀ i ∈ rest, index < i
  good : R n index rest

include hR in
lemma exists_step (n : ℕ) (N : Set ℕ) (hN : N.Infinite) : Nonempty (Step R n N) := by
  obtain ⟨i, hi⟩ := hN.nonempty
  have htail : (N \ Set.Iic i).Infinite := hN.sdiff (Set.finite_Iic i)
  obtain ⟨W, hW, hWi, hWR⟩ := hR n i _ htail
  refine ⟨⟨i, hi, W, hWi, fun j hj => (hW hj).1, ?_, hWR⟩⟩
  intro j hj
  have := (hW hj).2
  simpa using this

noncomputable def choice (n : ℕ) (N : Set ℕ) (hN : N.Infinite) : Step R n N :=
  Classical.choice (exists_step R hR n N hN)

end SeparableQuotient.AdaptiveThinning

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.MarkedEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.FiniteVectors
open scoped Classical ENNReal
universe u
variable {ι : Type u} [Fintype ι]

def vec (p : ℝ≥0∞) (v : ι → ℝ) : lp (fun _ : ι => ℝ) p := ⟨v, Memℓp.all v⟩

@[simp] lemma vec_apply (p : ℝ≥0∞) (v : ι → ℝ) (i : ι) : vec p v i = v i := rfl
@[simp] lemma vec_zero (p : ℝ≥0∞) : vec p (0 : ι → ℝ) = 0 := rfl
@[simp] lemma vec_add (p : ℝ≥0∞) (v w : ι → ℝ) : vec p (v+w) = vec p v+vec p w := rfl
@[simp] lemma vec_smul (p : ℝ≥0∞) (c : ℝ) (v : ι → ℝ) : vec p (c • v) = c • vec p v := rfl

lemma norm_rpow {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) :
    ‖vec p v‖^p.toReal = ∑ i, |v i|^p.toReal := by
  rw [lp.norm_rpow_eq_tsum hp, tsum_fintype]
  simp only [vec_apply, Real.norm_eq_abs]

lemma norm_le {p : ℝ≥0∞} (hp : 0 < p.toReal) (v : ι → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (h : ∑ i, |v i|^p.toReal ≤ K^p.toReal) : ‖vec p v‖ ≤ K := by
  apply (Real.rpow_le_rpow_iff (lp.norm_nonneg' (vec p v)) hK hp).mp
  rw [norm_rpow hp]
  exact h

end SeparableQuotient.FiniteVectors

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.NormingTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures
open scoped Classical

lemma TypeI.value_ne_zero {f : Family} (e : TypeI f) : e.value ≠ 0 := by
  let h : Fin e.length := ⟨0, e.length_pos⟩
  obtain ⟨a, ha⟩ := Finsupp.support_nonempty_iff.mpr (e.child_nonzero h)
  have hca := Finsupp.mem_support_iff.mp ha
  have hsum : (∑ i, e.child i) a = e.child h a := by
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single h]
    · intro i _ hih
      by_contra hi
      exact hih (successive_coefficient_unique e.child e.successive hi hca)
    · simp
  intro hz
  have hza := congrArg (fun x : Array => x a) hz
  have hm : (f.m e.weight : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (f.m_pos _).ne'
  exact (mul_ne_zero (inv_ne_zero hm) hca) (by
    simpa only [TypeI.value, Finsupp.smul_apply, hsum, smul_eq_mul,
      one_div, Finsupp.zero_apply] using hza)

noncomputable def TypeI.singletonMetadata {f : Family} (e : TypeI f) : ℕ :=
  max e.weight (1 + (e.value.support.product e.value.support).sup (fun p => rho p.1 p.2))

noncomputable def TypeI.singletonRaw {f : Family} (e : TypeI f) : RawPath where
  piece := fun _ => e.value
  weight := fun _ => e.weight
  metadata := fun _ => e.singletonMetadata
  nonzero := fun _ => e.value_ne_zero

lemma TypeI.singletonRaw_valid {f : Family} (e : TypeI f) : PrefixValid e.singletonRaw 1 where
  successive := fun i j hij hj => by omega
  metadata_strict := fun i j hij hj => by omega
  metadata_pos := fun _ _ => by
    exact (by omega : 1 ≤ 1 + (e.value.support.product e.value.support).sup (fun p => rho p.1 p.2)).trans (le_max_right _ _)
  weight_pos := fun _ _ => e.weight_pos
  weight_le_metadata := fun _ _ => le_max_left _ _
  rho_bound := by
    intro n hn a b ha hb _
    have hn0 : n = 0 := by omega
    subst n
    have ha' : a ∈ e.value.support := by simpa [RawPath.support,singletonRaw] using ha
    have hb' : b ∈ e.value.support := by simpa [RawPath.support,singletonRaw] using hb
    exact (Finset.le_sup (s := e.value.support.product e.value.support) (b := (a,b))
      (f := fun p : Γ × Γ => rho p.1 p.2) (Finset.mem_product.mpr ⟨ha',hb'⟩)).trans
      ((Nat.le_add_left _ _).trans (le_max_right _ _))
  rule := fun n hn => by omega

noncomputable def TypeI.singletonPath {f : Family} (e : TypeI f) : FinitePath f where
  raw := e.singletonRaw
  length := 1
  length_pos := le_rfl
  valid := e.singletonRaw_valid
  piece := fun _ => e
  value_eq := fun _ => rfl
  weight_eq := fun _ => rfl
  mixed_successive := fun _i _j hij => (not_lt_of_ge (le_of_eq (Subsingleton.elim _ _)) hij).elim

@[simp] lemma TypeI.singletonPath_value {f : Family} (e : TypeI f) : e.singletonPath.value = e.value := by
  change (∑ _ : Fin 1, e.value) = e.value
  simp

noncomputable def TypeI.toTypeII {f : Family} (e : TypeI f) : TypeII f := e.singletonPath.oneTerm Crop.all

@[simp] lemma TypeI.toTypeII_value {f : Family} (e : TypeI f) : e.toTypeII.value = e.value := by
  simp [toTypeII]

end SeparableQuotient.Norming

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.ExactPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter FiniteVectors
open scoped Classical Topology ENNReal BigOperators

/-- Exact pairs with uncropped child legality and support bounds in both orders. -/
structure ExactPair {f : Family} (z : BlockSequence f) (a J : ℕ) where
  vector : Γ →₀ ℝ
  nonzero : vector ≠ 0
  mem_tail : vector ∈ z.tailSpan a
  norm_le : ‖norming.includeFinite vector‖ ≤ 500
  pure_color : ∀ k, f = .pure k → ∀ α ∈ vector.support, Colors.color α = k
  piece : TypeI f
  weight_eq : piece.weight = J
  child_mem : ∀ h, piece.child h ∈ f.norming
  eval_ge : 1/2 ≤ norming.evaluateArray (norming.includeFinite vector) piece.value
  support : ∀ α ∈ piece.value.support, α ∈ (vectorCrop vector nonzero).set f

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding CoherentClosures Filter
open scoped Classical Topology

structure TreeNode {f : Family} (z : BlockSequence f) where
  start : ℕ
  weight : ℕ
  weight_pos : 1 ≤ weight
  pair : ExactPair z start weight
  finish : ℕ
  finish_ge : start ≤ finish
  support : pair.vector.support ⊆ z.prefixSupport finish
  metadata : ℕ
  metadata_pos : 1 ≤ metadata
  weight_le_metadata : weight ≤ metadata

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.BranchReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.ActualSpace
open Norming Set
open scoped Classical Topology

abbrev Cut := WithTop Γ

def initialSet (γ : Cut) : Set Γ := {a | (a : Cut) < γ}

lemma initialSet_connected (γ : Cut) : Set.OrdConnected (initialSet γ) :=
  Set.ordConnected_Iio.preimage_mono (WithTop.coe_mono)

def initialCrop (γ : Cut) := Crop.ordinalSet (initialSet γ) (initialSet_connected γ)

def initialP (γ : Cut) : E →L[ℝ] E := projection (initialCrop γ)

def colorP (k : ℕ) : E →L[ℝ] E := projection (Crop.oneColor k)

@[simp] lemma coordinate_initialP (γ : Cut) (x : E) (a : Γ) :
    coordinate a (initialP γ x) = if (a : Cut) < γ then coordinate a x else 0 := by
  simp only [initialP,coordinate_projection,initialCrop,Crop.ordinalSet_set,initialSet,Set.mem_ofPred_eq]

@[simp] lemma coordinate_colorP (k : ℕ) (x : E) (a : Γ) :
    coordinate a (colorP k x) = if Colors.color a = k then coordinate a x else 0 := by
  simp only [colorP,coordinate_projection,Crop.oneColor_set,Norming.colorSet,Set.mem_ofPred_eq]

@[simp] lemma initialP_top (x : E) : initialP ⊤ x = x := by
  apply norming.coordinate_ext
  intro a
  simp

end SeparableQuotient.ActualSpace

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.LpDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.LpCoding
open Filter
open scoped Classical Topology ENNReal
universe u v
variable {ι : Type u} {p q : ℝ≥0∞}

def finite (p : ℝ≥0∞) : (ι →₀ ℝ) →ₗ[ℝ] lp (fun _ : ι => ℝ) p where
  toFun c := ⟨fun i => c i, Memℓp.of_exponent_ge (memℓp_zero_iff.mpr c.hasFiniteSupport) (zero_le (a := p))⟩
  map_add' _ _ := by apply lp.ext; funext i; rfl
  map_smul' _ _ := by apply lp.ext; funext i; rfl

@[simp] lemma finite_apply (p : ℝ≥0∞) (c : ι →₀ ℝ) (i : ι) : finite p c i = c i := rfl

@[simp] lemma finite_single (p : ℝ≥0∞) (i : ι) (a : ℝ) :
    finite p (Finsupp.single i a) = lp.single p i a := by
  apply lp.ext
  funext j
  simp [lp.single_apply,Finsupp.single_apply,Pi.single_apply,eq_comm]

lemma norm_finite (hp : 0 < p.toReal) (c : ι →₀ ℝ) :
    ‖finite p c‖ = (∑ i ∈ c.support, |c i| ^ p.toReal) ^ (1/p.toReal) := by
  rw [lp.norm_eq_tsum_rpow hp]
  congr 1
  simp only [finite_apply,Real.norm_eq_abs]
  apply tsum_eq_sum
  intro i hi
  simp [Finsupp.notMem_support_iff.mp hi,hp.ne']

lemma finite_dense [Fact (1 ≤ p)] (hp : p ≠ ∞) : DenseRange (finite p : (ι →₀ ℝ) → _) := by
  intro x
  apply isClosed_closure.mem_of_tendsto (lp.hasSum_single hp x)
  apply Eventually.of_forall
  intro s
  apply subset_closure
  refine ⟨∑ i ∈ s, Finsupp.single i (x i),?_⟩
  simp

end SeparableQuotient.LpCoding

namespace SeparableQuotient.LpCoding
open Filter
open scoped Classical Topology ENNReal
universe u v
variable {ι : Type u} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

omit [Fact (1 ≤ p)] [Fact (1 ≤ q)] in
lemma single_eq_smul (p : ℝ≥0∞) (i : ι) (a : ℝ) :
    lp.single (E := fun _ : ι => ℝ) p i a = a • lp.single p i (1 : ℝ) := by
  simpa only [smul_eq_mul,mul_one] using (lp.single_smul (E := fun _ : ι => ℝ) (𝕜 := ℝ) p i a (1 : ℝ))

end SeparableQuotient.LpCoding

end

end OAI
end

section
-- module Solutions.OAIQW_SeparableQuotient.PathOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
attribute [-instance] SubfieldClass.toSubringClass SubringClass.toSubsemiringClass

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped ENNReal

def Family.pathExponent (f : Family) : ℝ≥0∞ := ENNReal.ofReal f.q
lemma Family.q_gt_one (f : Family) : 1 < f.q := (Parameters.q_bounds f.s_ge_two).1
lemma Family.q_pos (f : Family) : 0 < f.q := zero_lt_one.trans f.q_gt_one
instance Family.pathExponent_fact (f : Family) : Fact (1 ≤ f.pathExponent) :=
  ⟨by simpa [Family.pathExponent] using ENNReal.ofReal_le_ofReal f.q_gt_one.le⟩
@[simp] lemma Family.pathExponent_real (f : Family) : f.pathExponent.toReal = f.q :=
  ENNReal.toReal_ofReal f.q_pos.le
lemma Family.pathExponent_pos (f : Family) : 0 < f.pathExponent.toReal := by simpa using f.q_pos
lemma Family.pathExponent_ne_top (f : Family) : f.pathExponent ≠ ∞ := ENNReal.ofReal_ne_top
end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology
@[reducible] local instance pathDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance pathDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
abbrev W := (StrongDual ℝ E) ⧸ X₀
@[reducible] local instance wGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance wSpace : NormedSpace ℝ W := inferInstance
local instance wComplete : CompleteSpace W := inferInstance

def pathCoset {f : Family} (P : PathIndex f) : W := X₀.mkQL (pathFunctional P.repr)

lemma coset_sum_bound {f : Family} {h : ℕ} (P : Fin h → PathIndex f)
    (hinj : Function.Injective P) (c : Fin h → ℝ) :
    ‖∑ i, c i • pathCoset (P i)‖ ≤ (∑ i, |c i|^f.q)^(1/f.q) := by
  obtain ⟨N,hN⟩ := exists_tail_estimate (fun i => (P i).repr)
    (PathIndex.repr_injective.comp hinj)
  have he (i : Fin h) : pathCoset (P i) = X₀.mkQL (pathTail (P i).repr N) := by
    apply (Submodule.Quotient.eq X₀).mpr
    exact pathTail_complement_mem _ _
  simp_rw [he]
  simp_rw [← map_smul]
  rw [← map_sum]
  exact (Submodule.Quotient.norm_mk_le _ _).trans (hN c)

def finitePathMap (f : Family) : (PathIndex f →₀ ℝ) →ₗ[ℝ] W :=
  Finsupp.linearCombination ℝ pathCoset

lemma finitePathMap_bound (f : Family) (c : PathIndex f →₀ ℝ) :
    ‖finitePathMap f c‖ ≤ ‖LpCoding.finite f.pathExponent c‖ := by
  let e : Fin c.support.card ≃ c.support := c.support.equivFin.symm
  have h := coset_sum_bound (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective) (fun i => c (e i))
  have he : finitePathMap f c = ∑ i : Fin c.support.card, c (e i) • pathCoset (e i).val := by
    change (∑ a ∈ c.support, c a • pathCoset a) = _
    rw [← Finset.sum_attach]
    exact (e.sum_comp (fun a : c.support => c a • pathCoset a.val)).symm
  have hs : (∑ a ∈ c.support, |c a|^f.q) = ∑ i, |c (e i)|^f.q := by
    rw [← Finset.sum_attach]
    exact (e.sum_comp (fun a : c.support => |c a|^f.q)).symm
  rw [he,LpCoding.norm_finite f.pathExponent_pos,Family.pathExponent_real,hs]
  exact h

/-- A bounded path map constructed by completion of path cosets. -/
def pathMap (f : Family) : lp (fun _ : PathIndex f => ℝ) f.pathExponent →L[ℝ] W :=
  (finitePathMap f).extendOfNorm (LpCoding.finite f.pathExponent)

lemma pathMap_finite (f : Family) (c : PathIndex f →₀ ℝ) :
    pathMap f (LpCoding.finite f.pathExponent c) = finitePathMap f c := by
  exact LinearMap.extendOfNorm_eq (f := finitePathMap f)
    (e := LpCoding.finite f.pathExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.pathExponent) f.pathExponent_ne_top)
    ⟨1,fun c => by simpa only [one_mul] using finitePathMap_bound f c⟩ c

@[simp] lemma pathMap_single (f : Family) (P : PathIndex f) (a : ℝ) :
    pathMap f (lp.single f.pathExponent P a) = a • pathCoset P := by
  rw [← LpCoding.finite_single,pathMap_finite]
  simp [finitePathMap]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures Cardinal
open scoped Classical Cardinal

lemma rawPath_card_le (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) :
    Cardinal.mk RawPath ≤ Cardinal.mk Γ := by
  have hΓ : Cardinal.mk Γ = continuum := by
    rw [show Cardinal.mk Γ = Cardinal.aleph 1 by simp [Γ,OmegaOne],← hCH,Cardinal.mk_real]
  have hA : Cardinal.mk Array = continuum := by
    rw [Cardinal.mk_finsupp_of_infinite Γ ℚ,hΓ]
    simp [Cardinal.aleph0_le_continuum]
  let code : RawPath → (ℕ → Array × ℕ × ℕ) := fun P n => (P.piece n,P.weight n,P.metadata n)
  have hi : Function.Injective code := by
    intro P Q h
    apply RawPath.ext
    · funext n; exact congrArg Prod.fst (congrFun h n)
    · funext n; exact congrArg (fun x => x.2.1) (congrFun h n)
    · funext n; exact congrArg (fun x => x.2.2) (congrFun h n)
  calc
    Cardinal.mk RawPath ≤ Cardinal.mk (ℕ → Array × ℕ × ℕ) := Cardinal.mk_le_of_injective hi
    _ = continuum := by simp [Cardinal.mk_prod,hA]
    _ = Cardinal.mk Γ := hΓ.symm

lemma pathIndex_card_le (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) :
    Cardinal.mk (PathIndex f) ≤ Cardinal.mk Γ :=
  (Cardinal.mk_subtype_le _).trans (rawPath_card_le hCH)

def pathLabelBase (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) : PathIndex f ↪ Γ :=
  Classical.choice ((Cardinal.le_def _ _).mp (pathIndex_card_le hCH f))

def Family.index : Family → ℕ
  | .mixed => 0
  | .pure k => k+1

def Family.sourceColor : Family → ℕ
  | .mixed => 1
  | .pure k => k+1

/-- An inner color partitions the shared C₁ while retaining the outer color. -/
def pathLabel (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) (P : PathIndex f) : Γ :=
  Colors.inColor f.sourceColor (Colors.inColor f.index (pathLabelBase hCH f P))

@[simp] lemma pathLabel_color (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) (P : PathIndex f) :
    Colors.color (pathLabel hCH f P) = f.sourceColor := by
  simp [pathLabel]

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped ENNReal

def Family.sourceExponent (f : Family) : ℝ≥0∞ := (Family.pure f.sourceColor).primalExponent
instance Family.sourceExponent_fact (f : Family) : Fact (1 ≤ f.sourceExponent) :=
  (Family.pure f.sourceColor).primalExponent_fact
@[simp] lemma Family.sourceExponent_real (f : Family) : f.sourceExponent.toReal = (f.s : ℝ)+1 := by
  change ((Family.pure f.sourceColor).primalExponent).toReal = _
  rw [Family.primalExponent_toReal]
  cases f <;> simp [Family.sourceColor,Family.s] <;> ring
lemma Family.sourceExponent_ne_top (f : Family) : f.sourceExponent ≠ ∞ := ENNReal.natCast_ne_top _
lemma Family.pathConjugate (f : Family) : f.sourceExponent.toReal.HolderConjugate f.pathExponent.toReal := by
  simpa only [Family.sourceExponent_real,Family.pathExponent_real,Family.q] using
    Parameters.sNext_q_conjugate f.s_ge_two

def pathLabelEmb (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) : PathIndex f ↪ Γ where
  toFun := pathLabel hCH f
  inj' _ _ h := (pathLabelBase hCH f).injective
    (Colors.inColor_injective f.index (Colors.inColor_injective f.sourceColor h))

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

def finiteLabelMap (f : Family) : (PathIndex f →₀ ℝ) →ₗ[ℝ] E :=
  norming.includeFinite.comp (Finsupp.lmapDomain ℝ ℝ (pathLabel hCH f))

lemma finiteLabelMap_eq (f : Family) (c : PathIndex f →₀ ℝ) :
    finiteLabelMap hCH f c = norming.includeFinite (c.embDomain (pathLabelEmb hCH f)) := by
  rw [Finsupp.embDomain_eq_mapDomain]
  rfl

lemma finiteLabelMap_bound (f : Family) (c : PathIndex f →₀ ℝ) :
    ‖finiteLabelMap hCH f c‖ ≤ ‖LpCoding.finite f.sourceExponent c‖ := by
  rw [finiteLabelMap_eq]
  calc
    _ ≤ ‖LpFinite.realArray f.sourceExponent (c.embDomain (pathLabelEmb hCH f))‖ := by
      apply norm_includeFinite_on_color
      intro a ha
      rw [Finsupp.support_embDomain] at ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      exact pathLabel_color hCH f i
    _ = _ := by
      change ‖LpCoding.finite f.sourceExponent (c.embDomain (pathLabelEmb hCH f))‖ = _
      rw [LpCoding.norm_finite f.pathConjugate.pos,LpCoding.norm_finite f.pathConjugate.pos,
        Finsupp.support_embDomain,Finset.sum_map]
      simp only [Finsupp.embDomain_apply_self]

/-- The color synthesis operator. -/
def labelMap (f : Family) : lp (fun _ : PathIndex f => ℝ) f.sourceExponent →L[ℝ] E :=
  (finiteLabelMap hCH f).extendOfNorm (LpCoding.finite f.sourceExponent)

lemma labelMap_finite (f : Family) (c : PathIndex f →₀ ℝ) :
    labelMap hCH f (LpCoding.finite f.sourceExponent c) = finiteLabelMap hCH f c := by
  exact LinearMap.extendOfNorm_eq (f := finiteLabelMap hCH f)
    (e := LpCoding.finite f.sourceExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.sourceExponent) f.sourceExponent_ne_top)
    ⟨1,fun c => by simpa only [one_mul] using finiteLabelMap_bound hCH f c⟩ c

end SeparableQuotient.ActualSpace

end

end OAI
end


