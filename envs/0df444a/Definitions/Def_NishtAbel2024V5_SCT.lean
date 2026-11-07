-- Prove2me | Definitions.Def_NishtAbel2024V5_SCT
-- name    : NishtAbel2024V5_SCT
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T04:23:26.355088+00:00
-- url     : https://prove2.me/theorems/c7bc85be-c75a-441e-998e-47ae6e3fd2f7
-- title:
--   Chapter 5.2 (V5 Support): Infinite Ramsey Theorem and Size-Change Termination Graph Metatheory
-- statement:
--   Self-contained formalization of the size-change termination (SCT) metatheory (Section 5.2, Lemma 1 and Theorem 1, pp. 34–35 of Nisht and Abel 2024), including an ultrafilter proof of infinite Ramsey's theorem (`Mathlib.Order.Filter.Ultrafilter`), finiteness of the transitive closure of bounded invocation graphs, associativity and conformance compatibility of invocation graph composition $\mathcal{G}_1 \cdot \mathcal{G}_2$, and well-foundedness of the induced semantic call relation.
-- source:
--   Nisht & Abel 2024, Kind Inference and Termination Checking in a Language with Co-Patterns and Size-Change Termination, https://urn.kb.se/resolve?urn=urn:nbn:se:chalmers:diva-542843, Section 5.2, pp. 34-35, Lemma 1 & Theorem 1

import Definitions.Def_NishtAbel2024V2_Syntax
import Mathlib.Order.WellFounded
import Mathlib.Order.Filter.Ultrafilter.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finite.Prod
import Mathlib.Data.List.Basic

universe u

/-! ## Solutions/V3/SCT/NoChain.lean -/


/-- To establish well-foundedness it is enough to rule out descending sequences. -/
theorem NishtAbel2024V3.wellFounded_of_no_descending_sequence {α : Type u} (r : α → α → Prop)
    (h : ∀ f : ℕ → α, (∀ n, r (f (n + 1)) (f n)) → False) : WellFounded r :=
  wellFounded_iff_isEmpty_descending_chain.mpr ⟨fun ⟨f, hf⟩ => h f hf⟩

/-! ## Solutions/V3/SCT/Ramsey.lean -/

section
-- module Solutions.OAIQW_SeparableQuotient.RamseyThinning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace NishtAbel2024V3.RamseyPort

noncomputable section

namespace SeparableQuotient.InfiniteRamsey
open Filter
open scoped Classical

variable {χ : Type*} [Finite χ]

lemma eventually_constant (U : Ultrafilter ℕ) (f : ℕ → χ) :
    ∃ b, ∀ᶠ m in U, f m = b :=
  U.eventually_exists_iff.mp (Eventually.of_forall (fun m => ⟨f m, rfl⟩))

def limitColor (U : Ultrafilter ℕ) (c : Finset ℕ → χ) : ℕ → Finset ℕ → χ
  | 0, s => c s
  | k+1, s => (eventually_constant U (fun m => limitColor U c k (insert m s))).choose

lemma limitColor_eventually (U : Ultrafilter ℕ) (c : Finset ℕ → χ)
    (k : ℕ) (s : Finset ℕ) :
    ∀ᶠ m in U, limitColor U c k (insert m s) = limitColor U c (k+1) s :=
  (eventually_constant U (fun m => limitColor U c k (insert m s))).choose_spec

/-- The finite-set form of the infinite Ramsey theorem, proved by iterated
ultrafilter colors. Used only for the four-hit thinning in exact-pairs. -/
theorem homogeneous (n : ℕ) (c : Finset ℕ → χ) :
    ∃ (M : Set ℕ) (b : χ), M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let b := limitColor U c n ∅
  let Good : Finset ℕ → Prop := fun S => ∀ s ⊆ S, s.card ≤ n → limitColor U c (n-s.card) s = b
  have hempty : Good ∅ := by
    intro s hs _
    have he : s = ∅ := Finset.subset_empty.mp hs
    subst s
    rfl
  have hstep (S : Finset ℕ) (hS : Good S) : ∃ m > S.sup id, Good (insert m S) := by
    have hev (s : Finset ℕ) (hs : s ⊆ S) : ∀ᶠ m in U,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b := by
      by_cases hlt : s.card < n
      · have he : n-s.card-1+1 = n-s.card := by omega
        exact (limitColor_eventually U c (n-s.card-1) s).mono
          (fun _ h _ => h.trans (by rw [he]; exact hS s hs hlt.le))
      · exact Eventually.of_forall (fun _ h => (hlt h).elim)
    have hall : ∀ᶠ m in U, ∀ s ∈ S.powerset,
        s.card < n → limitColor U c (n-s.card-1) (insert m s) = b :=
      (eventually_all_finset S.powerset).mpr (fun s hs => hev s (Finset.mem_powerset.mp hs))
    have hlarge : ∀ᶠ m in U, S.sup id < m :=
      (eventually_gt_atTop (S.sup id)).filter_mono (Ultrafilter.of_le atTop)
    obtain ⟨m, hm, hall⟩ := (hlarge.and hall).exists
    have hmS : m ∉ S := by
      intro h
      exact (not_le_of_gt hm) (Finset.le_sup (f := id) h)
    refine ⟨m, hm, fun s hs hcard => ?_⟩
    by_cases hms : m ∈ s
    · let t := s.erase m
      have hts : t ⊆ S := by
        intro a ha
        have hh := Finset.mem_of_subset hs (Finset.mem_of_mem_erase ha)
        exact (Finset.mem_insert.mp hh).resolve_left (Finset.ne_of_mem_erase ha)
      have htc : t.card+1 = s.card := by
        exact Finset.card_erase_add_one hms
      have he : insert m t = s := Finset.insert_erase hms
      have hh := hall t (Finset.mem_powerset.mpr hts) (by omega)
      simpa only [he, show n-t.card-1 = n-s.card by omega] using hh
    · have hss : s ⊆ S := by
        intro a ha
        exact (Finset.mem_insert.mp (hs ha)).resolve_left (fun h => hms (h ▸ ha))
      exact hS s hss hcard
  let next (S : {S : Finset ℕ // Good S}) : ℕ := (hstep S.val S.property).choose
  have hn (S : {S : Finset ℕ // Good S}) : S.val.sup id < next S ∧ Good (insert (next S) S.val) :=
    (hstep S.val S.property).choose_spec
  let seq : ℕ → {S : Finset ℕ // Good S} := Nat.rec ⟨∅, hempty⟩
    (fun _ S => ⟨insert (next S) S.val, (hn S).2⟩)
  have hseq (i : ℕ) : (seq (i+1)).val = insert (next (seq i)) (seq i).val := rfl
  have hmono : Monotone (fun i => (seq i).val) := monotone_nat_of_le_succ
    (fun i => by rw [hseq]; exact Finset.subset_insert _ _)
  let v : ℕ → ℕ := fun i => next (seq i)
  have hvmem (i : ℕ) : v i ∈ (seq (i+1)).val := by rw [hseq]; exact Finset.mem_insert_self _ _
  have hv : StrictMono v := by
    apply strictMono_nat_of_lt_succ
    intro i
    exact (Finset.le_sup (f := id) (hvmem i)).trans_lt (hn (seq (i+1))).1
  let M : Set ℕ := ⋃ i, ↑(seq i).val
  have hM : M.Infinite := (Set.infinite_range_of_injective hv.injective).mono (by
    rintro _ ⟨i, rfl⟩
    exact Set.mem_iUnion.mpr ⟨i+1, hvmem i⟩)
  refine ⟨M, b, hM, fun s hs hcard => ?_⟩
  have hex : ∀ a : s, ∃ i, a.val ∈ (seq i).val :=
    fun a => Set.mem_iUnion.mp (hs a.property)
  choose k hk using hex
  let N := Finset.univ.sup k
  have hsub : s ⊆ (seq N).val := by
    intro a ha
    exact hmono (Finset.le_sup (f := k) (Finset.mem_univ ⟨a, ha⟩)) (hk ⟨a, ha⟩)
  have hh := (seq N).property s hsub hcard.le
  simpa only [hcard, Nat.sub_self, limitColor] using hh

/-- Relative version for any infinite subset of the natural numbers. -/
theorem homogeneous_subset_oai (n : ℕ) (c : Finset ℕ → χ) (A : Set ℕ) (hA : A.Infinite) :
    ∃ (M : Set ℕ) (b : χ), M ⊆ A ∧ M.Infinite ∧
      ∀ s : Finset ℕ, (↑s : Set ℕ) ⊆ M → s.card = n → c s = b := by
  let f : ℕ → ℕ := Nat.nth (· ∈ A)
  have hf : StrictMono f := Nat.nth_strictMono hA
  obtain ⟨B, b, hB, hb⟩ := homogeneous n (fun s => c (s.image f))
  refine ⟨f '' B, b, ?_, hB.image hf.injective.injOn, ?_⟩
  · rintro _ ⟨i, _, rfl⟩
    exact Nat.nth_mem_of_infinite hA i
  · intro s hs hcard
    let t := s.preimage f (hf.injective.injOn)
    have him : t.image f = s := by
      ext a
      constructor
      · intro ha
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
        exact Finset.mem_preimage.mp hi
      · intro ha
        obtain ⟨i, _, rfl⟩ := hs ha
        exact Finset.mem_image.mpr ⟨i, Finset.mem_preimage.mpr ha, rfl⟩
    have hts : (↑t : Set ℕ) ⊆ B := by
      intro i hi
      have hfi : f i ∈ s := (Finset.mem_preimage.mp hi)
      obtain ⟨j, hj, he⟩ := hs hfi
      exact hf.injective he ▸ hj
    have htcard : t.card = n := by rw [← hcard, ← him, Finset.card_image_of_injective _ hf.injective]
    simpa only [him] using hb t hts htcard

end SeparableQuotient.InfiniteRamsey

end

end NishtAbel2024V3.RamseyPort
end


/-! ## Solutions/V3/SCT/RamseyBridge.lean -/

namespace NishtAbel2024V2.SCTPort


theorem homogeneous_pair_subsequence {C : Type} [Finite C] (c : Nat → Nat → C)
    (ramsey : ∀ (color : Finset Nat → C), ∃ (M : Set Nat) (b : C), M.Infinite ∧
      ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) :
    ∃ (seq : Nat → Nat) (color : C), StrictMono seq ∧
      ∀ i j, i < j → c (seq i) (seq j) = color := by
  classical
  let pairColor (s : Finset Nat) : C :=
    if h : s.Nonempty then c (s.min' h) (s.max' h) else c 0 0
  obtain ⟨M, color, hinf, hcolor⟩ := ramsey pairColor
  refine ⟨Nat.nth (fun n => n ∈ M), color, Nat.nth_strictMono hinf, ?_⟩
  intro i j hij
  have hlt := (Nat.nth_strictMono (p := fun n => n ∈ M) hinf) hij
  have ha := Nat.nth_mem_of_infinite (p := fun n => n ∈ M) hinf i
  have hb := Nat.nth_mem_of_infinite (p := fun n => n ∈ M) hinf j
  have hsub : (↑({Nat.nth (fun n => n ∈ M) i, Nat.nth (fun n => n ∈ M) j} : Finset Nat) : Set Nat) ⊆ M := by
    simpa only [Finset.coe_insert, Finset.coe_singleton, Set.insert_subset_iff,
      Set.singleton_subset_iff] using And.intro ha hb
  have hcard : ({Nat.nth (fun n => n ∈ M) i, Nat.nth (fun n => n ∈ M) j} : Finset Nat).card = 2 :=
    Finset.card_pair (ne_of_lt hlt)
  have hc := hcolor _ hsub hcard
  simpa [pairColor, Finset.min'_pair, Finset.max'_pair, min_eq_left (le_of_lt hlt),
    max_eq_right (le_of_lt hlt)] using hc

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/IdempotentRamsey.lean -/

namespace NishtAbel2024V2.SCTPort


/-- Ramsey extraction of a homogeneous idempotent interval value. -/
theorem homogeneous_idempotent_intervals {Name Graph : Type} {Carrier : Type u} [Finite Name] [Finite Graph]
    (name : Nat → Name) (graph : Nat → Nat → Graph) (val : Graph → Carrier)
    (comp : Carrier → Carrier → Carrier)
    (hcomp : ∀ i j k, i < j → j < k → val (graph i k) = comp (val (graph j k)) (val (graph i j)))
    (ramsey : ∀ (color : Finset Nat → Name × Name × Graph),
      ∃ (M : Set Nat) (b : Name × Name × Graph), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) :
    ∃ (seq : Nat → Nat) (f : Name) (G : Graph), StrictMono seq ∧
      (∀ i, name (seq i) = f) ∧
      (∀ i j, i < j → graph (seq i) (seq j) = G) ∧ comp (val G) (val G) = val G := by
  obtain ⟨seq, v, hmono, hpair⟩ :=
    homogeneous_pair_subsequence (fun i j => (name i, name j, graph i j)) ramsey
  refine ⟨seq, v.1, v.2.2, hmono, ?_, ?_, ?_⟩
  · intro i
    exact congrArg (fun p : Name × Name × Graph => p.1) (hpair i (i + 1) (Nat.lt_succ_self i))
  · intro i j hij
    exact congrArg (fun p : Name × Name × Graph => p.2.2) (hpair i j hij)
  · have h01 : graph (seq 0) (seq 1) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 0 1 (by decide))
    have h12 : graph (seq 1) (seq 2) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 1 2 (by decide))
    have h02 : graph (seq 0) (seq 2) = v.2.2 :=
      congrArg (fun p : Name × Name × Graph => p.2.2) (hpair 0 2 (by decide))
    calc
      comp (val v.2.2) (val v.2.2) = comp (val (graph (seq 1) (seq 2))) (val (graph (seq 0) (seq 1))) := by rw [h12, h01]
      _ = val (graph (seq 0) (seq 2)) := (hcomp _ _ _ (hmono (by decide)) (hmono (by decide))).symm
      _ = val v.2.2 := by rw [h02]

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/FiniteGraphs.lean -/

namespace NishtAbel2024V2.SCTPort


instance : Finite EdgeRel := Finite.of_injective (fun e : EdgeRel => match e with | .lt => false | .le => true) (by intro a b h; cases a <;> cases b <;> simp_all)

def graphFromCode (N : Nat) (a b : Fin (N+1)) (m : Fin N → Fin N → Option EdgeRel) : InvGraph :=
  ⟨a.val, b.val, InvGraph.canonicalEdges a.val b.val fun i j =>
    if hi : i < N then if hj : j < N then m ⟨i, hi⟩ ⟨j, hj⟩ else none else none⟩

theorem finite_normalized_graphs (N : Nat) :
    {G : InvGraph | G.leftArity ≤ N ∧ G.rightArity ≤ N ∧ G = G.normalize}.Finite := by
  classical
  let _ : Fintype EdgeRel := Fintype.ofFinite EdgeRel
  let codes := Set.range (fun c : Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel) => graphFromCode N c.1 c.2.1 c.2.2)
  have hfin : codes.Finite := by
    simpa only [Set.image_univ] using Set.Finite.image _ (Set.finite_univ (α := Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel)))
  apply hfin.subset
  intro G hG
  rcases hG with ⟨hleft, hright, hnorm⟩
  refine ⟨(⟨G.leftArity, by omega⟩, ⟨G.rightArity, by omega⟩, fun i j => G.edgeAt i.val j.val), ?_⟩
  dsimp [graphFromCode]
  calc
    _ = G.normalize := by
      simp only [InvGraph.normalize, InvGraph.mk.injEq, true_and]
      unfold InvGraph.canonicalEdges
      apply List.flatMap_congr
      intro i hi
      apply List.filterMap_congr
      intro j hj
      have hiN : i < N := by simp only [List.mem_range] at hi; omega
      have hjN : j < N := by simp only [List.mem_range] at hj; omega
      simp [hiN, hjN]
    _ = G := hnorm.symm

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/ClosureFinite.lean -/

namespace NishtAbel2024V2.SCTPort


def CanonicalGraph (G : InvGraph) : Prop :=
  ∃ lookup, G.edges = InvGraph.canonicalEdges G.leftArity G.rightArity lookup

theorem closure_invariants (𝒢 : InvGraphFamily) (hwf : 𝒢.ArityWf)
    {f g : FunName} {G : InvGraph} (h : InvGraphClosure 𝒢 f g G) :
    G.leftArity = 𝒢.arity g ∧ G.rightArity = 𝒢.arity f ∧ CanonicalGraph G := by
  induction h with
  | @base f g G hmem =>
    have hg := hwf.2 f g G hmem
    refine ⟨?_, ?_, ?_⟩
    · simpa [InvGraph.normalize] using hg.1
    · simpa [InvGraph.normalize] using hg.2.1
    · exact ⟨G.edgeAt, rfl⟩
  | @comp f h g G₁ G₂ h₁ h₂ ih₁ ih₂ =>
    exact ⟨ih₁.1, ih₂.2.1, ⟨_, rfl⟩⟩

theorem finite_canonical_graphs (N : Nat) :
    {G : InvGraph | G.leftArity ≤ N ∧ G.rightArity ≤ N ∧ CanonicalGraph G}.Finite := by
  classical
  let _ : Fintype EdgeRel := Fintype.ofFinite EdgeRel
  let codes := Set.range (fun c : Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel) => graphFromCode N c.1 c.2.1 c.2.2)
  have hfin : codes.Finite := by
    simpa only [Set.image_univ] using Set.Finite.image _ (Set.finite_univ (α := Fin (N+1) × Fin (N+1) × (Fin N → Fin N → Option EdgeRel)))
  apply hfin.subset
  intro G hG
  rcases hG with ⟨hleft, hright, lookup, hlookup⟩
  refine ⟨(⟨G.leftArity, by omega⟩, ⟨G.rightArity, by omega⟩, fun i j => lookup i.val j.val), ?_⟩
  dsimp [graphFromCode]
  cases G with
  | mk left right edges =>
    simp only [InvGraph.mk.injEq, true_and] at *
    rw [hlookup]
    unfold InvGraph.canonicalEdges
    apply List.flatMap_congr
    intro i hi
    apply List.filterMap_congr
    intro j hj
    have hiN : i < N := by simp only [List.mem_range] at hi; omega
    have hjN : j < N := by simp only [List.mem_range] at hj; omega
    simp [hiN, hjN]

theorem closure_support (𝒢 : InvGraphFamily) (dom : List FunName)
    (hsupp : ∀ f g, 𝒢.graphs f g ≠ [] → f ∈ dom ∧ g ∈ dom)
    {f g : FunName} {G : InvGraph} (h : InvGraphClosure 𝒢 f g G) :
    f ∈ dom ∧ g ∈ dom := by
  induction h with
  | base hmem => exact hsupp _ _ (List.ne_nil_of_mem hmem)
  | comp _ _ ih₁ ih₂ => exact ⟨ih₂.1, ih₁.2⟩

private theorem arity_bounded (arity : FunName → Nat) (dom : List FunName) (f : FunName)
    (hf : f ∈ dom) : arity f ≤ (dom.map arity).foldr max 0 := by
  induction dom with
  | nil => simp at hf
  | cons a dom ih =>
    simp only [List.mem_cons] at hf
    simp only [List.map_cons, List.foldr_cons]
    rcases hf with rfl | hf
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih hf) (Nat.le_max_right _ _)

theorem finite_closure_graphs (𝒢 : InvGraphFamily) (hwf : 𝒢.ArityWf) :
    {G : InvGraph | ∃ f g, InvGraphClosure 𝒢 f g G}.Finite := by
  obtain ⟨dom, hsupp⟩ := hwf.1
  let N := (dom.map 𝒢.arity).foldr max 0
  apply (finite_canonical_graphs N).subset
  intro G hG
  obtain ⟨f, g, hg⟩ := hG
  obtain ⟨hgf, hgg⟩ := closure_support 𝒢 dom hsupp hg
  obtain ⟨hl, hr, hc⟩ := closure_invariants 𝒢 hwf hg
  exact ⟨hl ▸ arity_bounded 𝒢.arity dom g hgg,
         hr ▸ arity_bounded 𝒢.arity dom f hgf, hc⟩

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/GraphCompat.lean -/

namespace NishtAbel2024V2.SCTPort


/-- Universe-polymorphic copy of `ConformsToGraph`. -/
def ConformsU {S : Type u} (ltRel leRel : S → S → Prop) (G : InvGraph) (s s' : List S) : Prop :=
  s.length = G.leftArity ∧
  s'.length = G.rightArity ∧
  ∀ (i j : Nat) (hi : i < s.length) (hj : j < s'.length),
    (G.edgeAt i j = some .lt → ltRel (s.get ⟨i, hi⟩) (s'.get ⟨j, hj⟩)) ∧
    (G.edgeAt i j = some .le → leRel (s.get ⟨i, hi⟩) (s'.get ⟨j, hj⟩))

private theorem fold_choose {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind
    done

private theorem edgeAt_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := fold_choose (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx
  done

private theorem fold_choose_optional {α : Type} (f : α → Option EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (f x)) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = some r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (f x)) h
    cases a <;> cases hfx : f x <;> cases r <;> simp_all [EdgeRel.combine] <;> grind
    done

private theorem comp_edge_witness (G₁ G₂ : InvGraph) (i j : Nat)
    (hi : i < G₁.leftArity) (hj : j < G₂.rightArity) (r : EdgeRel)
    (h : (G₁.comp G₂).edgeAt i j = some r) :
    ∃ k < G₁.rightArity, ∃ r₁ r₂,
      G₁.edgeAt i k = some r₁ ∧ G₂.edgeAt k j = some r₂ ∧
      EdgeRel.seq r₁ r₂ = r := by
  have he := edgeAt_mem (G₁.comp G₂) i j r h
  simp only [InvGraph.comp, InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range] at he
  simp only [Option.map_eq_some_iff, Prod.mk.injEq] at he
  rcases he with ⟨i', _, j', _, r', hf, rfl, rfl, rfl⟩
  have step (acc : Option EdgeRel) (k : Nat) :
      (match G₁.edgeAt i' k, G₂.edgeAt k j' with
       | some a, some b => EdgeRel.combine acc (some (a.seq b))
       | _, _ => acc) =
      EdgeRel.combine acc (do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b)) := by
    cases acc with
    | none => cases G₁.edgeAt i' k <;> cases G₂.edgeAt k j' <;> rfl
    | some a => cases a <;> cases G₁.edgeAt i' k <;> cases G₂.edgeAt k j' <;> rfl
  have heq : (fun acc k => match G₁.edgeAt i' k, G₂.edgeAt k j' with
      | some a, some b => EdgeRel.combine acc (some (a.seq b))
      | _, _ => acc) =
      (fun acc k => EdgeRel.combine acc (do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b))) := by
    funext acc k
    exact step acc k
  have samefold := congrArg (fun f => List.foldl f none (List.range G₁.rightArity)) heq
  have hf' := samefold.symm.trans hf
  have hw := fold_choose_optional (fun k => do let a ← G₁.edgeAt i' k; let b ← G₂.edgeAt k j'; some (a.seq b)) (List.range G₁.rightArity) none r' hf'
  simp only [reduceCtorEq, false_or, List.mem_range] at hw
  rcases hw with ⟨k, hk, hk'⟩
  cases e₁ : G₁.edgeAt i' k <;> cases e₂ : G₂.edgeAt k j' <;> simp_all <;> grind
  done

theorem graph_compat {S : Type u} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (G₁ G₂ : InvGraph) (a b c : List S)
    (h₁ : ConformsU ltRel leRel G₁ a b)
    (h₂ : ConformsU ltRel leRel G₂ b c) :
    ConformsU ltRel leRel (G₁.comp G₂) a c := by
  rcases h₁ with ⟨ha, hb₁, h₁⟩
  rcases h₂ with ⟨hb₂, hc, h₂⟩
  refine ⟨ha, hc, ?_⟩
  intro i j hi hj
  constructor
  · intro h
    obtain ⟨k, hk, r₁, r₂, e₁, e₂, es⟩ := comp_edge_witness G₁ G₂ i j (ha ▸ hi) (hc ▸ hj) .lt h
    have hk' : k < b.length := by omega
    have ha' := h₁ i k hi hk'
    have hc' := h₂ k j hk' hj
    cases r₁ <;> cases r₂ <;> simp_all [EdgeRel.seq] <;> grind
    done
  · intro h
    obtain ⟨k, hk, r₁, r₂, e₁, e₂, es⟩ := comp_edge_witness G₁ G₂ i j (ha ▸ hi) (hc ▸ hj) .le h
    have hk' : k < b.length := by omega
    have ha' := h₁ i k hi hk'
    have hc' := h₂ k j hk' hj
    cases r₁ <;> cases r₂ <;> simp_all [EdgeRel.seq] <;> grind

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/CanonicalLookup.lean -/

namespace NishtAbel2024V2.SCTPort


theorem canonical_mem (n m i j : Nat) (f : Nat → Nat → Option EdgeRel) (r : EdgeRel) :
    (i, j, r) ∈ InvGraph.canonicalEdges n m f ↔ i < n ∧ j < m ∧ f i j = some r := by
  simp [InvGraph.canonicalEdges, List.mem_flatMap, List.mem_filterMap, List.mem_range,
    Option.map_eq_some_iff, Prod.mk.injEq]
  try grind

private theorem fold_ne_none {α : Type} (f : α → EdgeRel) (xs : List α) (r : EdgeRel) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) (some r) ≠ none := by
  induction xs generalizing r with
  | nil => simp
  | cons x xs ih =>
    cases r <;> cases h : f x <;> simp_all [EdgeRel.combine]

private theorem fold_eq_none_iff {α : Type} (f : α → EdgeRel) (xs : List α) :
    xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) none = none ↔ xs = [] := by
  cases xs with
  | nil => simp
  | cons x xs =>
    simp only [List.foldl_cons, List.cons_ne_nil, iff_false]
    have hn := fold_ne_none f xs (f x)
    cases h : f x <;> simpa [EdgeRel.combine, h] using hn

private theorem fold_choose_canon {α : Type} (f : α → EdgeRel) (xs : List α)
    (a : Option EdgeRel) (r : EdgeRel)
    (h : xs.foldl (fun acc x => EdgeRel.combine acc (some (f x))) a = some r) :
    a = some r ∨ ∃ x ∈ xs, f x = r := by
  induction xs generalizing a with
  | nil => simpa using h
  | cons x xs ih =>
    have h' := ih (EdgeRel.combine a (some (f x))) h
    cases a <;> cases r <;> cases hfx : f x <;> simp_all [EdgeRel.combine] <;> grind

private theorem edgeAt_mem_canon (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (h : G.edgeAt i j = some r) : (i, j, r) ∈ G.edges := by
  have h' := fold_choose_canon (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j)) none r h
  simp only [reduceCtorEq, false_or, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with ⟨⟨x, y, z⟩, ⟨hx, rfl, rfl⟩, rfl⟩
  exact hx

private theorem edgeAt_ne_none_of_mem (G : InvGraph) (i j : Nat) (r : EdgeRel)
    (hm : (i, j, r) ∈ G.edges) : G.edgeAt i j ≠ none := by
  intro h
  have hf := (fold_eq_none_iff (fun (e : Nat × Nat × EdgeRel) => e.2.2)
    (G.edges.filter (fun e => e.1 == i && e.2.1 == j))).mp h
  have hm' : (i, j, r) ∈ G.edges.filter (fun e => e.1 == i && e.2.1 == j) := by
    simp [hm]
  rw [hf] at hm'
  exact List.not_mem_nil hm'

theorem canonical_lookup (n m : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat)
    (hi : i < n) (hj : j < m) :
    (InvGraph.mk n m (InvGraph.canonicalEdges n m f)).edgeAt i j = f i j := by
  let G : InvGraph := ⟨n, m, InvGraph.canonicalEdges n m f⟩
  change G.edgeAt i j = f i j
  cases he : G.edgeAt i j with
  | none =>
    cases hf : f i j with
    | none => rfl
    | some r =>
      have hm : (i, j, r) ∈ G.edges := (canonical_mem n m i j f r).2 ⟨hi, hj, hf⟩
      exact False.elim (edgeAt_ne_none_of_mem G i j r hm he)
  | some r =>
    have hm : (i, j, r) ∈ G.edges := edgeAt_mem_canon G i j r he
    exact ((canonical_mem n m i j f r).1 hm).2.2.symm

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/GraphAssoc.lean -/

namespace NishtAbel2024V2.SCTPort


/-- Composition of optional edge labels; absence absorbs composition. -/
def edgeMul : Option EdgeRel → Option EdgeRel → Option EdgeRel
  | some a, some b => some (a.seq b)
  | _, _ => none

theorem edgeMul_assoc (a b c : Option EdgeRel) :
    edgeMul (edgeMul a b) c = edgeMul a (edgeMul b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem combine_assoc (a b c : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) c = EdgeRel.combine a (EdgeRel.combine b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem combine_comm (a b : Option EdgeRel) :
    EdgeRel.combine a b = EdgeRel.combine b a := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rfl

theorem edgeMul_left_distrib (a b c : Option EdgeRel) :
    edgeMul a (EdgeRel.combine b c) = EdgeRel.combine (edgeMul a b) (edgeMul a c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem edgeMul_right_distrib (a b c : Option EdgeRel) :
    edgeMul (EdgeRel.combine a b) c = EdgeRel.combine (edgeMul a c) (edgeMul b c) := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rcases c with _ | (_ | _) <;> rfl

theorem edgeMul_sum_right (a : Option EdgeRel) (xs : List (Option EdgeRel)) :
    edgeMul a (xs.foldr EdgeRel.combine none) =
      (xs.map (edgeMul a)).foldr EdgeRel.combine none := by
  induction xs with
  | nil => rcases a with _ | (_ | _) <;> rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, edgeMul_left_distrib, ih]

theorem edgeMul_sum_left (xs : List (Option EdgeRel)) (a : Option EdgeRel) :
    edgeMul (xs.foldr EdgeRel.combine none) a =
      (xs.map (fun x => edgeMul x a)).foldr EdgeRel.combine none := by
  induction xs with
  | nil => rcases a with _ | (_ | _) <;> rfl
  | cons x xs ih =>
    simp only [List.foldr_cons, List.map_cons, edgeMul_right_distrib, ih]

theorem combine_interchange (a b c d : Option EdgeRel) :
    EdgeRel.combine (EdgeRel.combine a b) (EdgeRel.combine c d) =
    EdgeRel.combine (EdgeRel.combine a c) (EdgeRel.combine b d) := by
  rw [combine_assoc, ← combine_assoc b c d, combine_comm b c, combine_assoc, ← combine_assoc]

theorem sum_map_combine {α : Type} (xs : List α) (f g : α → Option EdgeRel) :
    (xs.map (fun x => EdgeRel.combine (f x) (g x))).foldr EdgeRel.combine none =
    EdgeRel.combine ((xs.map f).foldr EdgeRel.combine none) ((xs.map g).foldr EdgeRel.combine none) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons, ih]
    exact combine_interchange _ _ _ _

theorem finite_sum_swap {α β : Type} (xs : List α) (ys : List β) (f : α → β → Option EdgeRel) :
    (xs.map (fun x => (ys.map (f x)).foldr EdgeRel.combine none)).foldr EdgeRel.combine none =
    (ys.map (fun y => (xs.map (fun x => f x y)).foldr EdgeRel.combine none)).foldr EdgeRel.combine none := by
  induction xs with
  | nil =>
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      simp only [List.map_nil, List.foldr_nil] at ih
      simp only [List.map_nil, List.foldr_nil, List.map_cons, List.foldr_cons]
      rw [← ih]
      rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, ← sum_map_combine]

theorem combine_none_right (a : Option EdgeRel) : EdgeRel.combine a none = a := by
  rcases a with _ | (_ | _) <;> rfl

theorem combine_foldl_eq_foldr (xs : List (Option EdgeRel)) :
    xs.foldl EdgeRel.combine none = xs.foldr EdgeRel.combine none := by
  have h : ∀ acc, xs.foldl EdgeRel.combine acc = EdgeRel.combine acc (xs.foldr EdgeRel.combine none) := by
    induction xs with
    | nil => intro acc; simp only [List.foldl_nil, List.foldr_nil, combine_none_right]
    | cons x xs ih =>
      intro acc
      simp only [List.foldl_cons, List.foldr_cons, ih, combine_assoc]
  rw [h none]
  rcases xs.foldr EdgeRel.combine none with _ | (_ | _) <;> rfl

/-- Without compatible middle arities, associativity can fail, even for finite graphs. -/
theorem comp_not_assoc_without_arity :
    ∃ G₁ G₂ G₃ : InvGraph, (G₁.comp G₂).comp G₃ ≠ G₁.comp (G₂.comp G₃) := by
  refine ⟨⟨1, 1, [(0, 0, .le)]⟩, ⟨0, 1, [(0, 0, .le)]⟩, ⟨1, 1, [(0, 0, .le)]⟩, ?_⟩
  decide

def edgeSum (n : Nat) (f : Nat → Option EdgeRel) : Option EdgeRel :=
  ((List.range n).map f).foldr EdgeRel.combine none

theorem edgeSum_congr {n : Nat} {f g : Nat → Option EdgeRel}
    (h : ∀ i < n, f i = g i) : edgeSum n f = edgeSum n g := by
  unfold edgeSum
  congr 1
  apply List.map_congr_left
  intro x hx
  exact h x (List.mem_range.mp hx)

theorem matrix_assoc (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (_hbc : B.rightArity = C.leftArity)
    (compLookup : ∀ (X Y : InvGraph) (i j : Nat),
      i < X.leftArity → j < Y.rightArity →
      (X.comp Y).edgeAt i j = edgeSum X.rightArity (fun k => edgeMul (X.edgeAt i k) (Y.edgeAt k j)))
    (i j : Nat) (hi : i < A.leftArity) (hj : j < C.rightArity) :
    edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) ((B.comp C).edgeAt k j)) =
    edgeSum B.rightArity (fun k => edgeMul ((A.comp B).edgeAt i k) (C.edgeAt k j)) := by
  calc
    _ = edgeSum A.rightArity (fun k => edgeSum B.rightArity (fun l => edgeMul (A.edgeAt i k) (edgeMul (B.edgeAt k l) (C.edgeAt l j)))) := by
      apply edgeSum_congr
      intro k hk
      rw [compLookup B C k j (hab ▸ hk) hj]
      unfold edgeSum
      simpa only [List.map_map, Function.comp_def] using edgeMul_sum_right (A.edgeAt i k) ((List.range B.rightArity).map (fun l => edgeMul (B.edgeAt k l) (C.edgeAt l j)))
    _ = edgeSum B.rightArity (fun l => edgeSum A.rightArity (fun k => edgeMul (edgeMul (A.edgeAt i k) (B.edgeAt k l)) (C.edgeAt l j))) := by
      unfold edgeSum
      simp only [edgeMul_assoc]
      exact finite_sum_swap _ _ _
    _ = _ := by
      apply edgeSum_congr
      intro l hl
      rw [compLookup A B i l hi hl]
      unfold edgeSum
      simpa only [List.map_map, Function.comp_def] using (edgeMul_sum_left ((List.range A.rightArity).map (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k l))) (C.edgeAt l j)).symm

def compEdges (A B : InvGraph) (i j : Nat) : Option EdgeRel :=
  (List.range A.rightArity).foldl
    (fun acc k => match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) none

theorem compEdges_eq (A B : InvGraph) (i j : Nat) :
    compEdges A B i j = edgeSum A.rightArity (fun k => edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
  unfold compEdges edgeSum
  have hstep : ∀ acc k, (match A.edgeAt i k, B.edgeAt k j with
      | some r₁, some r₂ => EdgeRel.combine acc (some (EdgeRel.seq r₁ r₂))
      | _, _ => acc) = EdgeRel.combine acc (edgeMul (A.edgeAt i k) (B.edgeAt k j)) := by
    intro acc k
    rcases acc with _ | (_ | _) <;> rcases A.edgeAt i k with _ | (_ | _) <;> rcases B.edgeAt k j with _ | (_ | _) <;> rfl
  simp only [hstep, ← List.foldl_map, combine_foldl_eq_foldr]

theorem comp_def (A B : InvGraph) :
    A.comp B = ⟨A.leftArity, B.rightArity, InvGraph.canonicalEdges A.leftArity B.rightArity (compEdges A B)⟩ := rfl

theorem comp_assoc_of_lookup (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity)
    (compLookup : ∀ (X Y : InvGraph) (i j : Nat),
      i < X.leftArity → j < Y.rightArity →
      (X.comp Y).edgeAt i j = edgeSum X.rightArity (fun k => edgeMul (X.edgeAt i k) (Y.edgeAt k j))) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  rw [comp_def (A.comp B) C, comp_def A (B.comp C)]
  simp only [InvGraph.comp, InvGraph.mk.injEq, true_and]
  change InvGraph.canonicalEdges A.leftArity C.rightArity (compEdges (A.comp B) C) =
    InvGraph.canonicalEdges A.leftArity C.rightArity (compEdges A (B.comp C))
  unfold InvGraph.canonicalEdges
  apply List.flatMap_congr
  intro i hi
  apply List.filterMap_congr
  intro j hj
  have hi' : i < A.leftArity := List.mem_range.mp hi
  have hj' : j < C.rightArity := List.mem_range.mp hj
  have h := (matrix_assoc A B C hab hbc compLookup i j hi' hj').symm
  rw [compEdges_eq, compEdges_eq]
  change Option.map _ (edgeSum B.rightArity _) = Option.map _ (edgeSum A.rightArity _)
  rw [h]

theorem comp_assoc_of_canonical_lookup (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity)
    (lookup : ∀ (l r : Nat) (f : Nat → Nat → Option EdgeRel) (i j : Nat),
      i < l → j < r → (InvGraph.mk l r (InvGraph.canonicalEdges l r f)).edgeAt i j = f i j) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  apply comp_assoc_of_lookup A B C hab hbc
  intro X Y i j hi hj
  rw [comp_def, lookup X.leftArity Y.rightArity (compEdges X Y) i j hi hj, compEdges_eq]

theorem comp_assoc_compatible (A B C : InvGraph)
    (hab : A.rightArity = B.leftArity) (hbc : B.rightArity = C.leftArity) :
    (A.comp B).comp C = A.comp (B.comp C) := by
  exact comp_assoc_of_canonical_lookup A B C hab hbc canonical_lookup

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/Intervals.lean -/

namespace NishtAbel2024V2.SCTPort


/-- `segment g i n` composes the `n + 1` consecutive graphs starting at `i`.
The later graph is on the left because it compares callee sizes to caller sizes. -/
def segment (g : Nat → InvGraph) (i : Nat) : Nat → InvGraph
  | 0 => g i
  | n + 1 => (g (i + n + 1)).comp (segment g i n)

def interval (g : Nat → InvGraph) (i j : Nat) : InvGraph :=
  segment g i (j - i - 1)

theorem segment_closed (family : InvGraphFamily) (name : Nat → FunName)
    (g : Nat → InvGraph)
    (hbase : ∀ i, InvGraphClosure family (name i) (name (i + 1)) (g i))
    (i n : Nat) :
    InvGraphClosure family (name i) (name (i + n + 1)) (segment g i n) := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, Nat.add_assoc] using InvGraphClosure.comp (hbase (i + n + 1)) ih

theorem interval_closed (family : InvGraphFamily) (name : Nat → FunName)
    (g : Nat → InvGraph)
    (hbase : ∀ i, InvGraphClosure family (name i) (name (i + 1)) (g i))
    (i j : Nat) (hij : i < j) :
    InvGraphClosure family (name i) (name j) (interval g i j) := by
  have h := segment_closed family name g hbase i (j - i - 1)
  have hid : i + (j - i - 1) + 1 = j := by omega
  simpa [interval, hid] using h

theorem segment_conforms {S : Type u} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsU ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i n : Nat) :
    ConformsU ltRel leRel (segment g i n) (sizes (i + n + 1)) (sizes i) := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, Nat.add_assoc] using
      graph_compat ltRel leRel hle htt htl hlt (g (i + n + 1)) (segment g i n)
        (sizes (i + n + 1 + 1)) (sizes (i + n + 1)) (sizes i) (hbase (i + n + 1)) ih

theorem interval_conforms {S : Type u} (ltRel leRel : S → S → Prop)
    (hle : ∀ x y, ltRel x y → leRel x y)
    (htt : ∀ x y z, leRel x y → leRel y z → leRel x z)
    (htl : ∀ x y z, ltRel x y → leRel y z → ltRel x z)
    (hlt : ∀ x y z, leRel x y → ltRel y z → ltRel x z)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsU ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i j : Nat) (hij : i < j) :
    ConformsU ltRel leRel (interval g i j) (sizes j) (sizes i) := by
  have h := segment_conforms ltRel leRel hle htt htl hlt g sizes hbase i (j - i - 1)
  have hid : i + (j - i - 1) + 1 = j := by omega
  simpa [interval, hid] using h

theorem segment_arities (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (i n : Nat) :
    (segment g i n).leftArity = arity (i + n + 1) ∧
    (segment g i n).rightArity = arity i := by
  induction n with
  | zero => simpa [segment] using hbase i
  | succ n ih =>
    simpa [segment, InvGraph.comp, Nat.add_assoc] using ⟨(hbase (i + n + 1)).1, ih.2⟩

theorem segment_concat (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (assoc : ∀ A B C : InvGraph, A.rightArity = B.leftArity → B.rightArity = C.leftArity →
      (A.comp B).comp C = A.comp (B.comp C))
    (i n m : Nat) :
    segment g i (n + m + 1) = (segment g (i + n + 1) m).comp (segment g i n) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change (g (i + (n + m + 1) + 1)).comp (segment g i (n + m + 1)) =
      ((g ((i + n + 1) + m + 1)).comp (segment g (i + n + 1) m)).comp (segment g i n)
    rw [ih]
    have idx : i + (n + m + 1) + 1 = i + n + 1 + m + 1 := by omega
    rw [idx]
    apply Eq.symm
    apply assoc
    · exact (hbase _).2.trans (segment_arities g arity hbase (i + n + 1) m).1.symm
    · exact (segment_arities g arity hbase (i + n + 1) m).2.trans
        (segment_arities g arity hbase i n).1.symm

theorem interval_concat (g : Nat → InvGraph) (arity : Nat → Nat)
    (hbase : ∀ i, (g i).leftArity = arity (i + 1) ∧ (g i).rightArity = arity i)
    (assoc : ∀ A B C : InvGraph, A.rightArity = B.leftArity → B.rightArity = C.leftArity →
      (A.comp B).comp C = A.comp (B.comp C))
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    interval g i k = (interval g j k).comp (interval g i j) := by
  have h := segment_concat g arity hbase assoc i (j - i - 1) (k - j - 1)
  have hstart : i + (j - i - 1) + 1 = j := by omega
  have hlen : (j - i - 1) + (k - j - 1) + 1 = k - i - 1 := by omega
  simpa [interval, hstart, hlen] using h

theorem interval_concat_of_conforms {S : Type u} (ltRel leRel : S → S → Prop)
    (g : Nat → InvGraph) (sizes : Nat → List S)
    (hbase : ∀ i, ConformsU ltRel leRel (g i) (sizes (i + 1)) (sizes i))
    (i j k : Nat) (hij : i < j) (hjk : j < k) :
    interval g i k = (interval g j k).comp (interval g i j) := by
  have harity : ∀ i, (g i).leftArity = (sizes (i + 1)).length ∧
      (g i).rightArity = (sizes i).length := by
    intro i
    exact ⟨(hbase i).1.symm, (hbase i).2.1.symm⟩
  exact interval_concat g (fun i => (sizes i).length) harity comp_assoc_compatible i j k hij hjk
end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/SCTWellFounded.lean -/

namespace NishtAbel2024V2.SCTPort


/-- A homogeneous chain with a strict diagonal contradicts ordinal well-foundedness. -/
theorem no_infinite_strict_diagonal_chain {S : Type u} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (G : InvGraph) (s : Nat → List S) (k : Nat)
    (hk : k < G.leftArity) (hedge : G.edgeAt k k = some .lt)
    (hchain : ∀ n, ConformsU ltRel leRel G (s (n + 1)) (s n)) : False := by
  have hlen : ∀ n, k < (s (n + 1)).length := by
    intro n
    simpa only [(hchain n).1] using hk
  let chain : Nat → S := fun n => (s (n + 1)).get ⟨k, hlen n⟩
  have hdescending : ∀ n, ltRel (chain (n + 1)) (chain n) := by
    intro n
    exact ((hchain (n + 1)).2.2 k k (hlen (n + 1)) (hlen n)).1 hedge
  have impossible (x : S) (hacc : Acc ltRel x) : ∀ n, chain n = x → False := by
    induction hacc with
    | intro x _ ih =>
      intro n hn
      exact ih (chain (n + 1)) (hn ▸ hdescending n) (n + 1) rfl
  exact impossible (chain 0) (wf.apply (chain 0)) 0 rfl

/-- An idempotent graph in a valid closure cannot label an infinite conforming chain. -/
theorem no_infinite_idempotent_chain {S : Type u} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (family : InvGraphFamily) (valid : SCTValid family)
    (f : FunName) (G : InvGraph) (closed : InvGraphClosure family f f G)
    (idempotent : G.comp G = G) (s : Nat → List S)
    (hchain : ∀ n, ConformsU ltRel leRel G (s (n + 1)) (s n)) : False := by
  obtain ⟨k, hk, hedge⟩ := valid.2 f G closed idempotent
  exact no_infinite_strict_diagonal_chain ltRel leRel wf G s k hk hedge hchain

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/SCTRamseyContradiction.lean -/

namespace NishtAbel2024V2.SCTPort


/-- Once finite interval colors have the concatenation, closure and conformance
properties, Ramsey's theorem rules out an infinite invocation chain. -/
theorem no_chain_from_interval_coloring {S : Type u} {Name Graph : Type}
    [Finite Name] [Finite Graph]
    (ltRel leRel : S → S → Prop) (wf : WellFounded ltRel)
    (family : InvGraphFamily) (valid : SCTValid family)
    (name : Nat → Name) (nameVal : Name → FunName)
    (graph : Nat → Nat → Graph) (graphVal : Graph → InvGraph)
    (sizes : Nat → List S)
    (hcomp : ∀ i j k, i < j → j < k →
      graphVal (graph i k) = (graphVal (graph j k)).comp (graphVal (graph i j)))
    (hclosed : ∀ i j, i < j →
      InvGraphClosure family (nameVal (name i)) (nameVal (name j)) (graphVal (graph i j)))
    (hconform : ∀ i j, i < j →
      ConformsU ltRel leRel (graphVal (graph i j)) (sizes j) (sizes i))
    (ramsey : ∀ (color : Finset Nat → Name × Name × Graph),
      ∃ (M : Set Nat) (b : Name × Name × Graph), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) : False := by
  obtain ⟨seq, f, G, hmono, hname, hgraph, hidem⟩ :=
    homogeneous_idempotent_intervals name graph graphVal InvGraph.comp hcomp ramsey
  have hclose : InvGraphClosure family (nameVal f) (nameVal f) (graphVal G) := by
    have h := hclosed (seq 0) (seq 1) (hmono (by decide))
    rw [hname 0, hname 1, hgraph 0 1 (by decide)] at h
    exact h
  apply no_infinite_idempotent_chain ltRel leRel wf family valid (nameVal f) (graphVal G) hclose hidem (fun n => sizes (seq n))
  intro n
  have h := hconform (seq n) (seq (n + 1)) (hmono (Nat.lt_succ_self n))
  rw [hgraph n (n + 1) (Nat.lt_succ_self n)] at h
  exact h

end NishtAbel2024V2.SCTPort

/-! ## Solutions/V3/SCT/SCTFiniteIntervals.lean -/

namespace NishtAbel2024V2.SCTPort


/-- Instantiate the finite-color contradiction with actual invocation graphs. -/
theorem no_chain_from_finite_intervals {S : Type u} (ltRel leRel : S → S → Prop)
    (wf : WellFounded ltRel) (family : InvGraphFamily) (valid : SCTValid family)
    (dom : List FunName) (name : Nat → FunName) (hdom : ∀ n, name n ∈ dom)
    (interval : Nat → Nat → InvGraph) (sizes : Nat → List S)
    (hcomp : ∀ i j k, i < j → j < k →
      interval i k = (interval j k).comp (interval i j))
    (hclosed : ∀ i j, i < j → InvGraphClosure family (name i) (name j) (interval i j))
    (hconform : ∀ i j, i < j →
      ConformsU ltRel leRel (interval i j) (sizes j) (sizes i))
    (ramsey : ∀ {C : Type} [Finite C] (color : Finset Nat → C),
      ∃ (M : Set Nat) (b : C), M.Infinite ∧
        ∀ s : Finset Nat, (↑s : Set Nat) ⊆ M → s.card = 2 → color s = b) : False := by
  classical
  let names : Set FunName := {f | f ∈ dom}
  let : Finite names := dom.finite_toSet.to_subtype
  let graphs : Set InvGraph := {G | ∃ f g, InvGraphClosure family f g G}
  let : Finite graphs := (finite_closure_graphs family valid.1).to_subtype
  let coloredName (n : Nat) : names := ⟨name n, hdom n⟩
  let coloredGraph (i j : Nat) : graphs :=
    if h : i < j then ⟨interval i j, ⟨name i, name j, hclosed i j h⟩⟩
    else ⟨interval 0 1, ⟨name 0, name 1, hclosed 0 1 (by decide)⟩⟩
  apply no_chain_from_interval_coloring ltRel leRel wf family valid coloredName Subtype.val coloredGraph Subtype.val sizes
  · intro i j k hij hjk
    simpa [coloredGraph, hij, hjk, lt_trans hij hjk] using hcomp i j k hij hjk
  · intro i j hij
    simpa [coloredName, coloredGraph, hij] using hclosed i j hij
  · intro i j hij
    simpa [coloredGraph, hij] using hconform i j hij
  · exact ramsey

end NishtAbel2024V2.SCTPort


