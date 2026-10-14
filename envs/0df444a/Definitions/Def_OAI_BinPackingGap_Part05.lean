-- Prove2me | Definitions.Def_OAI_BinPackingGap_Part05
-- name    : OAI_BinPackingGap_Part05
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T18:21:20.764591+00:00
-- url     : https://prove2.me/theorems/d9f68882-1afe-4bdc-bb7c-27d85614e95b
-- title:
--   Structural additive gap for bin packing, part 5 of 10 (port of OpenAI's formalization)
-- statement:
--   Part 5 of 10 of a port of OpenAI's Lean formalization of the structural additive gap from the manuscript *Additive hardness and unbounded configuration gaps in bin packing* (OpenAI, September 24, 2026). For every $c$, it constructs an instance with $5B$ items of sizes in $(1/6,1)$ whose individual and type configuration LPs both equal $B$, while the optimum exceeds $B+c$. This part contains the modules `Packing/PackingSelections`, `Packing/CoordinateOrder`, `Trees/TestGeometry`, `Packing/PackingCoordinates`, `Inventory/InventoryPrefixConservation`.
--
--   **Attribution.** The code is adapted from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, directory `lean/OAI/Computability/BinPacking`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order, with their imports replaced by the previous part. The model definitions come from the platform definition `BinPackingGap`, which matches upstream `Model.lean` up to two private lemmas and a section wrapper.
--
--   The development is split into 10 parts only so that each compiles within the platform's time limit. The final part proves `OAI.BinPackingGap.structural_additive_gap`, the first clause of `OAI.BinPackingGap.main_results`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/Computability/BinPacking: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PackingSelections.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/CoordinateOrder.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Trees/TestGeometry.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Packing/PackingCoordinates.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/BinPacking/Inventory/InventoryPrefixConservation.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026/Additive-hardness-and-unbounded-configuration-gaps-in-bin-packing-September-24-2026.pdf

/-
Structural additive gap for bin packing (port of OpenAI's formalization), part 5 of 10.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/Computability/BinPacking/: Packing/PackingSelections.lean, Packing/CoordinateOrder.lean, Trees/TestGeometry.lean, Packing/PackingCoordinates.lean, Inventory/InventoryPrefixConservation.lean
These files formalize part of the manuscript "Additive hardness and unbounded configuration gaps in
bin packing" (OpenAI, September 24, 2026). Copyright OpenAI. Licensed under the Apache License,
Version 2.0 (http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same
license, on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions (Model.lean) come from the platform definition `BinPackingGap`, to which upstream Model.lean
is identical up to two private lemmas and a section wrapper.
-/
import Mathlib
import Definitions.Def_OAI_BinPackingGap_Part04

set_option autoImplicit false

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/PackingSelections.lean =====
namespace OAI

noncomputable section

section
open scoped BigOperators

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def subclass (e : D.Item ≃ I.Item) : I.Item → Subclass :=
  D.itemSubclass ∘ e.symm

def label (e : D.Item ≃ I.Item) : I.Item → Option D.Vertex :=
  D.itemLabel ∘ e.symm

def globalResources (e : D.Item ≃ I.Item) (s : GlobalSpecies D.graph) :
    Finset I.Item := by
  classical
  exact Finset.univ.image fun i : Fin (D.globalStock s) => e ⟨.«global», ⟨s, i⟩⟩

theorem globalCopy_injective (e : D.Item ≃ I.Item) (s : GlobalSpecies D.graph) :
    Function.Injective (fun i : Fin (D.globalStock s) => e ⟨.«global», ⟨s, i⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hg := @sigma_mk_injective Role D.RoleCopies .«global» _ _ h
  exact @sigma_mk_injective (GlobalSpecies D.graph)
    (fun s => Fin (D.globalStock s)) s i j hg

@[simp] theorem globalResources_card (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) :
    (globalResources e s).card = D.globalStock s := by
  classical
  simp only [globalResources, Finset.card_image_of_injective _ (globalCopy_injective e s),
    Finset.card_univ, Fintype.card_fin]

@[simp] theorem mem_globalResources (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (x : I.Item) :
    x ∈ globalResources e s ↔
      ∃ i : Fin (D.globalStock s), e ⟨.«global», ⟨s, i⟩⟩ = x := by
  classical
  simp [globalResources]

theorem globalResources_disjoint (e : D.Item ≃ I.Item)
    {s t : GlobalSpecies D.graph} (hst : s ≠ t) :
    Disjoint (globalResources e s) (globalResources e t) := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, hi⟩ := (mem_globalResources e s x).mp hx
  obtain ⟨j, hj⟩ := (mem_globalResources e t x).mp hy
  have h := e.injective (hi.trans hj.symm)
  have hg : (⟨s, i⟩ : D.GlobalCopy) = ⟨t, j⟩ := by
    exact @sigma_mk_injective Role D.RoleCopies .«global» _ _ h
  exact hst (congrArg Sigma.fst hg)

def fundedTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) : Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    p.itemAtRole (subclass e) t .«global» ∈ globalResources e s

@[simp] theorem mem_fundedTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ fundedTuples p e s v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
      p.itemAtRole (subclass e) t .«global» ∈ globalResources e s := by
  classical
  simp [fundedTuples]

theorem fundedTuples_subset_main (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) (v : D.Vertex) :
    fundedTuples p e s v ⊆ Coverage.mainTuplesAt p (subclass e) (label e) v := by
  classical
  exact Finset.filter_subset _ _

theorem fundedTuples_disjoint_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) {v w : D.Vertex} (hvw : v ≠ w) :
    Disjoint (fundedTuples p e s v) (fundedTuples p e s w) :=
  (Coverage.mainTuplesAt_disjoint_label p (subclass e) (label e) hvw).mono
    (fundedTuples_subset_main p e s v) (fundedTuples_subset_main p e s w)

theorem sum_card_main_subsets_le_resources (p : Packing I b) (e : D.Item ≃ I.Item)
    (S : D.Vertex → Finset (p.TableBin (subclass e)))
    (hS : ∀ v, S v ⊆ Coverage.mainTuplesAt p (subclass e) (label e) v)
    (r : Role) (resources : Finset I.Item)
    (hres : ∀ v t, t ∈ S v → p.itemAtRole (subclass e) t r ∈ resources) :
    (∑ v, (S v).card) ≤ resources.card := by
  classical
  have hdis : ∀ v ∈ (Finset.univ : Finset D.Vertex),
      ∀ w ∈ (Finset.univ : Finset D.Vertex), v ≠ w → Disjoint (S v) (S w) := by
    intro v _ w _ hvw
    exact (Coverage.mainTuplesAt_disjoint_label p (subclass e) (label e) hvw).mono
      (hS v) (hS w)
  calc
    (∑ v, (S v).card) = (Finset.univ.biUnion S).card :=
      (Finset.card_biUnion hdis).symm
    _ ≤ resources.card := by
      apply Coverage.card_le_role_resources p (subclass e) _ r resources
      intro t ht
      obtain ⟨v, _, htv⟩ := Finset.mem_biUnion.mp ht
      exact hres v t htv

theorem fundedTuples_sum_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (s : GlobalSpecies D.graph) :
    (∑ v, (fundedTuples p e s v).card) ≤ D.globalStock s := by
  rw [← globalResources_card e s]
  apply sum_card_main_subsets_le_resources p e (fundedTuples p e s)
    (fundedTuples_subset_main p e s) .«global» (globalResources e s)
  intro v t ht
  exact ((mem_fundedTuples p e s v t).mp ht).2

def xplus (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) : ℕ :=
  (fundedTuples p e (.up true) v).card

def xminus (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) : ℕ :=
  (fundedTuples p e (.um true) v).card

theorem xplus_budget (p : Packing I b) (e : D.Item ≃ I.Item) :
    (∑ v, xplus p e v) ≤ D.d * D.k :=
  fundedTuples_sum_card_le p e (.up true)

theorem xminus_budget (p : Packing I b) (e : D.Item ≃ I.Item) :
    (∑ v, xminus p e v) ≤ D.d * (D.graph.n - D.k) :=
  fundedTuples_sum_card_le p e (.um true)

theorem total_budget (p : Packing I b) (e : D.Item ≃ I.Item) (hk : D.k ≤ D.graph.n) :
    (∑ v, (xplus p e v + xminus p e v)) ≤ D.d * D.graph.n := by
  rw [Finset.sum_add_distrib]
  calc
    _ ≤ D.d * D.k + D.d * (D.graph.n - D.k) :=
      Nat.add_le_add (xplus_budget p e) (xminus_budget p e)
    _ = D.d * D.graph.n := by
      have hsum : D.k + (D.graph.n - D.k) = D.graph.n := by omega
      rw [← Nat.mul_add, hsum]

def localDepthResources (e : D.Item ≃ I.Item) (v : D.Vertex) (ell : D.Depth) :
    Finset I.Item := by
  classical
  exact Finset.univ.image fun i : Fin (D.quota ell.val) =>
    e ⟨.«local», ⟨v, Sum.inl (Sum.inl ⟨ell, i⟩)⟩⟩

theorem localDepthCopy_injective (e : D.Item ≃ I.Item) (v : D.Vertex) (ell : D.Depth) :
    Function.Injective (fun i : Fin (D.quota ell.val) =>
      e ⟨.«local», ⟨v, Sum.inl (Sum.inl ⟨ell, i⟩)⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hl := @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  have hv := @sigma_mk_injective D.Vertex D.LocalAt v _ _ hl
  have hp : (⟨ell, i⟩ : D.PositiveLocal) = ⟨ell, j⟩ :=
    Sum.inl.inj (Sum.inl.inj hv)
  exact @sigma_mk_injective D.Depth (fun ell => Fin (D.quota ell.val)) ell i j hp

@[simp] theorem localDepthResources_card (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) :
    (localDepthResources e v ell).card = D.quota ell.val := by
  classical
  simp only [localDepthResources,
    Finset.card_image_of_injective _ (localDepthCopy_injective e v ell),
    Finset.card_univ, Fintype.card_fin]

theorem card_le_localDepth_stock (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) (S : Finset (p.TableBin (subclass e)))
    (hres : ∀ t ∈ S,
      p.itemAtRole (subclass e) t .«local» ∈ localDepthResources e v ell) :
    S.card ≤ D.quota ell.val := by
  rw [← localDepthResources_card e v ell]
  exact Coverage.card_le_role_resources p (subclass e) S .«local» _ hres

def positiveLocalResources (e : D.Item ≃ I.Item) (v : D.Vertex) : Finset I.Item := by
  classical
  exact Finset.univ.image fun i : D.PositiveLocal =>
    e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩

@[simp] theorem mem_positiveLocalResources (e : D.Item ≃ I.Item)
    (v : D.Vertex) (x : I.Item) :
    x ∈ positiveLocalResources e v ↔
      ∃ i : D.PositiveLocal, e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩ = x := by
  classical
  simp [positiveLocalResources]

theorem positiveLocalCopy_injective (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Function.Injective (fun i : D.PositiveLocal =>
      e ⟨.«local», ⟨v, Sum.inl (Sum.inl i)⟩⟩) := by
  intro i j hij
  have h := e.injective hij
  have hl := @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  have hv := @sigma_mk_injective D.Vertex D.LocalAt v _ _ hl
  exact Sum.inl.inj (Sum.inl.inj hv)

@[simp] theorem positiveLocalResources_card (e : D.Item ≃ I.Item) (v : D.Vertex) :
    (positiveLocalResources e v).card = D.P := by
  classical
  rw [positiveLocalResources,
    Finset.card_image_of_injective _ (positiveLocalCopy_injective e v),
    Finset.card_univ, D.card_positiveLocal]

theorem card_le_positiveLocal_stock (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (S : Finset (p.TableBin (subclass e)))
    (hres : ∀ t ∈ S,
      p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v) :
    S.card ≤ D.P := by
  rw [← positiveLocalResources_card e v]
  exact Coverage.card_le_role_resources p (subclass e) S .«local» _ hres

end PackingCounts
end BinPackingGap

end

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

private def elementAtRole (i : D.Item) (r : Role) (h : i.1 = r) : D.RoleCopies r :=
  h ▸ i.2

private theorem elementAtRole_mk (i : D.Item) (r : Role) (h : i.1 = r) :
    (⟨r, elementAtRole i r h⟩ : D.Item) = i := by
  rcases i with ⟨s, i⟩
  dsimp at h
  cases h
  rfl

theorem selected_role (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    (e.symm (p.itemAtRole (subclass e) t r)).1 = r := by
  change D.itemRole (e.symm (p.itemAtRole (subclass e) t r)) = r
  rw [← D.itemSubclass_role]
  exact p.itemAtRole_role (subclass e) t r

def roleCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) : D.RoleCopies r :=
  elementAtRole (e.symm (p.itemAtRole (subclass e) t r)) r (selected_role p e t r)

@[simp] theorem roleCopy_item (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    e ⟨r, roleCopy p e t r⟩ = p.itemAtRole (subclass e) t r := by
  rw [roleCopy, elementAtRole_mk, e.apply_symm_apply]

theorem roleCopy_injective (p : Packing I b) (e : D.Item ≃ I.Item) (r : Role) :
    Function.Injective (fun t => roleCopy p e t r) := by
  intro t u h
  change roleCopy p e t r = roleCopy p e u r at h
  apply p.itemAtRole_injective (subclass e) r
  change p.itemAtRole (subclass e) t r = p.itemAtRole (subclass e) u r
  rw [← roleCopy_item p e t r, ← roleCopy_item p e u r, h]

theorem roleCopy_subclass (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (r : Role) :
    D.itemSubclass ⟨r, roleCopy p e t r⟩ = patternSubclass (p.tablePattern (subclass e) t) r := by
  have h := p.itemAtRole_subclass (subclass e) t r
  rw [← roleCopy_item p e t r] at h
  simpa only [subclass, Function.comp_apply, e.symm_apply_apply] using h

abbrev rowCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.RowAt v :=
  roleCopy p e t .x

abbrev anchorCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.AnchorAt v :=
  roleCopy p e t .anchor

abbrev globalCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : D.GlobalCopy :=
  roleCopy p e t .«global»

abbrev localCopy (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Σ v : D.Vertex, D.LocalAt v :=
  roleCopy p e t .«local»

theorem selected_global_resource_iff (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (s : GlobalSpecies D.graph) :
    p.itemAtRole (subclass e) t .«global» ∈ globalResources e s ↔
      (globalCopy p e t).1 = s := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := (mem_globalResources e s _).mp h
    rw [← roleCopy_item p e t .«global»] at hi
    have he := e.injective hi
    have hg : (⟨s, i⟩ : D.GlobalCopy) = globalCopy p e t := by
      exact @sigma_mk_injective Role D.RoleCopies .«global» _ _ he
    exact (congrArg Sigma.fst hg).symm
  · intro h
    rcases hg : globalCopy p e t with ⟨s', i⟩
    have hs : s' = s := by simpa only [hg] using h
    subst s'
    apply (mem_globalResources e s _).mpr
    refine ⟨i, ?_⟩
    rw [← roleCopy_item p e t .«global»]
    exact congrArg (fun x : D.GlobalCopy => e ⟨.«global», x⟩) hg.symm

@[simp] theorem selected_row_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .x) = some (rowCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .x)) =
    some (rowCopy p e t).1
  rw [← roleCopy_item p e t .x, e.symm_apply_apply]
  rfl

@[simp] theorem selected_anchor_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .anchor) = some (anchorCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .anchor)) =
    some (anchorCopy p e t).1
  rw [← roleCopy_item p e t .anchor, e.symm_apply_apply]
  rfl

@[simp] theorem selected_local_label (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    label e (p.itemAtRole (subclass e) t .«local») = some (localCopy p e t).1 := by
  change D.itemLabel (e.symm (p.itemAtRole (subclass e) t .«local»)) =
    some (localCopy p e t).1
  rw [← roleCopy_item p e t .«local», e.symm_apply_apply]
  rfl

theorem good_row_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (rowCopy p e t).1 = v := by
  have ht' := (Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht
  have h := ht'.1.1.trans ht'.2
  rw [selected_row_label] at h
  exact Option.some.inj h

theorem good_anchor_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (anchorCopy p e t).1 = v := by
  have h := ((Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht).2
  rw [selected_anchor_label] at h
  exact Option.some.inj h

theorem good_local_vertex (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v) :
    (localCopy p e t).1 = v := by
  have ht' := (Coverage.mem_goodTuplesAt p (subclass e) (label e) v t).mp ht
  have h := ht'.1.2.trans ht'.2
  rw [selected_local_label] at h
  exact Option.some.inj h

def zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) :
    Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    D.globalUnit (globalCopy p e t) = false ∧
      p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v

def tupleLocalDepth (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℕ :=
  ((D.localDepth (localCopy p e t).2).map Subtype.val).getD 0

@[simp] theorem mem_zeroPositiveTuples (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) :
    t ∈ zeroPositiveTuples p e v ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        D.globalUnit (globalCopy p e t) = false ∧
          p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v := by
  classical
  simp [zeroPositiveTuples, and_assoc]

theorem zeroPositiveTuples_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) : (zeroPositiveTuples p e v).card ≤ D.P := by
  apply card_le_positiveLocal_stock p e v
  intro t ht
  exact ((mem_zeroPositiveTuples p e v t).mp ht).2.2

theorem localCopy_eq_of_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (hpos : p.itemAtRole (subclass e) t .«local» ∈ positiveLocalResources e v) :
    ∃ i : D.PositiveLocal, localCopy p e t = ⟨v, Sum.inl (Sum.inl i)⟩ := by
  obtain ⟨i, hi⟩ := (mem_positiveLocalResources e v _).mp hpos
  refine ⟨i, ?_⟩
  rw [← roleCopy_item p e t .«local»] at hi
  have h := e.injective hi
  have h' : (⟨v, Sum.inl (Sum.inl i)⟩ : Σ w : D.Vertex, D.LocalAt w) =
      localCopy p e t := by
    exact @sigma_mk_injective Role D.RoleCopies .«local» _ _ h
  exact h'.symm

theorem selected_depth_mem (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) :
    tupleLocalDepth p e t ∈ Finset.Icc 1 D.L := by
  obtain ⟨i, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  have hd : tupleLocalDepth p e t = i.1.val := by
    unfold tupleLocalDepth
    rw [hi]
    rfl
  rw [hd]
  exact i.1.property

theorem selected_localDepth_resource (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) (t : p.TableBin (subclass e))
    (ht : t ∈ zeroPositiveTuples p e v) (hell : tupleLocalDepth p e t = ell.val) :
    p.itemAtRole (subclass e) t .«local» ∈ localDepthResources e v ell := by
  classical
  obtain ⟨⟨depth, i⟩, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  have hd : tupleLocalDepth p e t = depth.val := by
    unfold tupleLocalDepth
    rw [hi]
    rfl
  have hdepth : depth = ell := Subtype.ext (hd.symm.trans hell)
  subst depth
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_univ _, ?_⟩
  rw [← roleCopy_item p e t .«local»]
  exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩) hi.symm

theorem zeroPositiveTuples_depth_card_le (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (ell : D.Depth) :
    ((zeroPositiveTuples p e v).filter (fun t => tupleLocalDepth p e t = ell.val)).card ≤
      D.quota ell.val := by
  classical
  apply card_le_localDepth_stock p e v ell
  intro t ht
  obtain ⟨ht, he⟩ := Finset.mem_filter.mp ht
  exact selected_localDepth_resource p e v ell t ht he

end PackingCounts
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/CoordinateOrder.lean =====
namespace OAI

namespace BinPackingGap.Geometry

variable {m R : ℕ}

def posLT (r s : Position m R) : Prop :=
  r.1.val < s.1.val ∨ r.1 = s.1 ∧ r.2.val < s.2.val

def posLE (r s : Position m R) : Prop := r = s ∨ posLT r s

theorem posLT_irrefl (r : Position m R) : ¬ posLT r r := by
  simp [posLT]

theorem posLT_trans {r s t : Position m R}
    (hrs : posLT r s) (hst : posLT s t) : posLT r t := by
  simp only [posLT, Fin.ext_iff] at *
  omega

theorem posLT_asymm {r s : Position m R} (h : posLT r s) : ¬ posLT s r :=
  fun h' => posLT_irrefl r (posLT_trans h h')

theorem posLT_trichotomy (r s : Position m R) :
    posLT r s ∨ r = s ∨ posLT s r := by
  simp only [posLT, Prod.ext_iff, Fin.ext_iff]
  omega

theorem posLT_or_posLT_of_ne {r s : Position m R} (hne : r ≠ s) :
    posLT r s ∨ posLT s r := by
  rcases posLT_trichotomy r s with hrs | hrs | hsr
  · exact Or.inl hrs
  · exact (hne hrs).elim
  · exact Or.inr hsr

theorem posLE_iff_not_posLT {r s : Position m R} : posLE r s ↔ ¬ posLT s r := by
  simp only [posLE, posLT, Prod.ext_iff, Fin.ext_iff]
  omega

theorem posLE_refl (r : Position m R) : posLE r r := Or.inl rfl

theorem posLE_trans {r s t : Position m R}
    (hrs : posLE r s) (hst : posLE s t) : posLE r t := by
  rcases hrs with rfl | hrs
  · exact hst
  rcases hst with rfl | hst
  · exact Or.inr hrs
  exact Or.inr (posLT_trans hrs hst)

theorem heightCode_ge_theta (R : ℕ) (r : Position m R) :
    theta R r.1 ≤ heightCode R r := by
  have hj : (0 : ℚ) ≤ r.2.val := Nat.cast_nonneg _
  have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
  unfold theta heightCode
  nlinarith

theorem heightCode_le_edgeMax (R : ℕ) (r : Position m R) :
    heightCode R r ≤ (R : ℚ) * ((R : ℚ) + 1) ^ r.1.val - 1 := by
  have hj : (r.2.val : ℚ) + 1 ≤ R := by
    exact_mod_cast Nat.succ_le_of_lt r.2.isLt
  have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
  have hmul := mul_le_mul_of_nonneg_right hj hp
  unfold heightCode
  linarith

theorem heightCode_same_edge_sub (R : ℕ) (e : Fin m) (j k : Fin R) :
    heightCode R (e, k) - heightCode R (e, j) =
      ((k.val : ℚ) - j.val) * ((R : ℚ) + 1) ^ e.val := by
  unfold heightCode
  ring

theorem heightCode_next_rep_sub (R : ℕ) (e : Fin m) (j k : Fin R)
    (hnext : k.val = j.val + 1) :
    heightCode R (e, k) - heightCode R (e, j) = ((R : ℚ) + 1) ^ e.val := by
  rw [heightCode_same_edge_sub]
  have hk : (k.val : ℚ) = (j.val : ℚ) + 1 := by exact_mod_cast hnext
  rw [hk]
  ring

theorem heightCode_next_edge_sub (R : ℕ) (e f : Fin m) (j k : Fin R)
    (hnext : f.val = e.val + 1) (hlast : j.val + 1 = R) (hfirst : k.val = 0) :
    heightCode R (f, k) - heightCode R (e, j) = ((R : ℚ) + 1) ^ e.val := by
  have hj : (j.val : ℚ) + 1 = R := by exact_mod_cast hlast
  change ((k.val : ℚ) + 1) * ((R : ℚ) + 1) ^ f.val - 1 -
    (((j.val : ℚ) + 1) * ((R : ℚ) + 1) ^ e.val - 1) = _
  rw [hnext, hfirst, hj, pow_succ]
  ring

theorem theta_next_sub (R : ℕ) (e f : Fin m) (hnext : f.val = e.val + 1) :
    theta R f - theta R e = (R : ℚ) * ((R : ℚ) + 1) ^ e.val := by
  unfold theta
  rw [hnext, pow_succ]
  ring

theorem heightCode_jump {r s : Position m R} (h : posLT r s) :
    theta R r.1 + 1 ≤ heightCode R s - heightCode R r := by
  rcases h with he | ⟨he, hj⟩
  · have hp : ((R : ℚ) + 1) ^ (r.1.val + 1) ≤
        ((R : ℚ) + 1) ^ s.1.val :=
      pow_le_pow_right₀ (base_one_le R) (Nat.succ_le_of_lt he)
    rw [pow_succ] at hp
    have hlo := heightCode_ge_theta R s
    have hhi := heightCode_le_edgeMax R r
    unfold theta at hlo ⊢
    nlinarith
  · have hj' : (r.2.val : ℚ) + 1 ≤ s.2.val := by
      exact_mod_cast Nat.succ_le_of_lt hj
    have hp : (0 : ℚ) ≤ ((R : ℚ) + 1) ^ r.1.val := pow_nonneg (by positivity) _
    have hmul := mul_le_mul_of_nonneg_right hj' hp
    simp only [heightCode, theta, ← he]
    nlinarith

theorem theta_jump {e f : Fin m} (hef : e < f) :
    (R : ℚ) * ((R : ℚ) + 1) ^ e.val ≤ theta R f - theta R e := by
  have hp : ((R : ℚ) + 1) ^ (e.val + 1) ≤ ((R : ℚ) + 1) ^ f.val :=
    pow_le_pow_right₀ (base_one_le R) (Nat.succ_le_of_lt hef)
  rw [pow_succ] at hp
  unfold theta
  nlinarith

theorem theta_jump_ge_heightCode {r : Position m R} {f : Fin m} (hef : r.1 < f) :
    heightCode R r + 1 ≤ theta R f - theta R r.1 :=
  (by linarith [heightCode_le_edgeMax R r] :
    heightCode R r + 1 ≤ (R : ℚ) * ((R : ℚ) + 1) ^ r.1.val).trans (theta_jump hef)

theorem heightCode_strictMono {r s : Position m R} (h : posLT r s) :
    heightCode R r < heightCode R s := by
  have hjump := heightCode_jump h
  have hn := theta_nonneg R r.1
  linarith

theorem heightCode_lt_iff {r s : Position m R} :
    heightCode R r < heightCode R s ↔ posLT r s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact hrs
    · subst s
      exact (lt_irrefl _ h).elim
    · exact (not_lt_of_ge (heightCode_strictMono hsr).le h).elim
  · exact heightCode_strictMono

theorem baseline_gap_of_posLT {r s : Position m R} (h : posLT r s) :
    gap m R ≤ baseline m R s - baseline m R r := by
  have hjump := heightCode_jump h
  have ht := theta_nonneg R r.1
  have hheight : (1 : ℚ) ≤ heightCode R s - heightCode R r := by linarith
  have hmul := mul_le_mul_of_nonneg_left hheight (gap_pos m R).le
  unfold baseline
  nlinarith

theorem gap_le_abs_baseline_sub {r s : Position m R} (hne : r ≠ s) :
    gap m R ≤ |baseline m R s - baseline m R r| := by
  rcases posLT_or_posLT_of_ne hne with hrs | hsr
  · exact (baseline_gap_of_posLT hrs).trans (le_abs_self _)
  · rw [abs_sub_comm]
    exact (baseline_gap_of_posLT hsr).trans (le_abs_self _)

theorem baseline_lt_iff {r s : Position m R} :
    baseline m R r < baseline m R s ↔ posLT r s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact hrs
    · subst s
      exact (lt_irrefl _ h).elim
    · have hg := baseline_gap_of_posLT hsr
      have hp := gap_pos m R
      linarith
  · intro h
    have hg := baseline_gap_of_posLT h
    have hp := gap_pos m R
    linarith

theorem baseline_le_iff {r s : Position m R} :
    baseline m R r ≤ baseline m R s ↔ posLE r s := by
  rw [posLE_iff_not_posLT, ← baseline_lt_iff]
  constructor
  · intro hle hlt
    linarith
  · intro h
    by_contra h'
    apply h
    linarith

theorem baseline_eq_iff {r s : Position m R} :
    baseline m R r = baseline m R s ↔ r = s := by
  constructor
  · intro h
    rcases posLT_trichotomy r s with hrs | hrs | hsr
    · exact (ne_of_lt (baseline_lt_iff.mpr hrs) h).elim
    · exact hrs
    · exact (ne_of_lt (baseline_lt_iff.mpr hsr) h.symm).elim
  · rintro rfl
    rfl

theorem baseline_le_jobInterior_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    baseline m R s ≤ baseline m R r - Δ / 2 ↔ posLT s r := by
  constructor
  · intro hs
    apply baseline_lt_iff.mp
    linarith
  · intro hsr
    have hgap := baseline_gap_of_posLT hsr
    linarith

theorem jobInterior_lt_baseline_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    baseline m R r - Δ / 2 < baseline m R s ↔ posLE r s := by
  rw [posLE_iff_not_posLT, ← baseline_le_jobInterior_iff hΔ hΔg]
  exact lt_iff_not_ge

theorem jobInterior_mem_current {Δ : ℚ} (hΔ : 0 < Δ) (r : Position m R) :
    baseline m R r - Δ ≤ baseline m R r - Δ / 2 ∧
      baseline m R r - Δ / 2 < baseline m R r := by
  constructor <;> linarith

theorem jobInterior_mem_job_iff {Δ : ℚ} (hΔ : 0 < Δ)
    (hΔg : Δ < gap m R) {r s : Position m R} :
    (baseline m R s - Δ ≤ baseline m R r - Δ / 2 ∧
      baseline m R r - Δ / 2 < baseline m R s) ↔ s = r := by
  constructor
  · rintro ⟨hleft, hright⟩
    rcases posLT_trichotomy s r with hsr | hsr | hrs
    · have hp := (baseline_le_jobInterior_iff hΔ hΔg).mpr hsr
      linarith
    · exact hsr
    · have hgap := baseline_gap_of_posLT hrs
      linarith
  · intro hsr
    subst s
    exact jobInterior_mem_current hΔ r

theorem baseline_le_actualJobInterior_iff (D L : ℕ) {r s : Position m R} :
    baseline m R s ≤ baseline m R r - delta m R D L / 2 ↔ posLT s r :=
  baseline_le_jobInterior_iff (delta_pos m R D L) (delta_lt_gap m R D L)

theorem actualJobInterior_mem_job_iff (D L : ℕ) {r s : Position m R} :
    (baseline m R s - delta m R D L ≤ baseline m R r - delta m R D L / 2 ∧
      baseline m R r - delta m R D L / 2 < baseline m R s) ↔ s = r :=
  jobInterior_mem_job_iff (delta_pos m R D L) (delta_lt_gap m R D L)

end BinPackingGap.Geometry

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Trees/TestGeometry.lean =====
namespace OAI

namespace BinPackingGap.Geometry

variable {m R D L : ℕ}

def jobLeft (m R D L : ℕ) (r : Position m R) : ℚ :=
  baseline m R r - delta m R D L

def closedJobCell (m R D L : ℕ) (r : Position m R) : Set ℚ :=
  Set.Icc (jobLeft m R D L r) (baseline m R r)

def jobTestInterval (m R D L : ℕ) (r : Position m R) : Set ℚ :=
  Set.Ico (jobLeft m R D L r) (baseline m R r)

def jobInterior (m R D L : ℕ) (r : Position m R) : ℚ :=
  baseline m R r - delta m R D L / 2

theorem closed_interval_gap_le_length {a b l₁ u₁ l₂ u₂ : ℚ}
    (h₁ : (Set.Icc a b ∩ Set.Icc l₁ u₁).Nonempty)
    (h₂ : (Set.Icc a b ∩ Set.Icc l₂ u₂).Nonempty) :
    l₂ - u₁ ≤ b - a := by
  rcases h₁ with ⟨x, hx⟩
  rcases h₂ with ⟨y, hy⟩
  have hax := hx.1.1
  have hxu := hx.2.2
  have hly := hy.2.1
  have hyb := hy.1.2
  linarith

theorem closed_interval_cannot_meet_of_lt_gap {a b l₁ u₁ l₂ u₂ : ℚ}
    (hlen : b - a < l₂ - u₁)
    (h₁ : (Set.Icc a b ∩ Set.Icc l₁ u₁).Nonempty)
    (h₂ : (Set.Icc a b ∩ Set.Icc l₂ u₂).Nonempty) : False :=
  (not_le_of_gt hlen) (closed_interval_gap_le_length h₁ h₂)

theorem jobLeft_lt_baseline (m R D L : ℕ) (r : Position m R) :
    jobLeft m R D L r < baseline m R r := by
  have h := delta_pos m R D L
  unfold jobLeft
  linarith

theorem one_tenth_lt_jobLeft (m R D L : ℕ) (r : Position m R) :
    1 / 10 < jobLeft m R D L r := by
  have hb := baseline_lower m R r
  have hd := delta_lt_gap m R D L
  have hg := gap_le_one_sixteen m R
  unfold jobLeft
  linarith

theorem job_baseline_lt_one (m R : ℕ) (r : Position m R) :
    baseline m R r < 1 := by
  have h := baseline_upper m R r
  linarith

theorem closedJobCell_bounds {r : Position m R} {x : ℚ}
    (hx : x ∈ closedJobCell m R D L r) : 1 / 10 < x ∧ x < 1 := by
  exact ⟨lt_of_lt_of_le (one_tenth_lt_jobLeft m R D L r) hx.1,
    lt_of_le_of_lt hx.2 (job_baseline_lt_one m R r)⟩

theorem closedJobCell_subset_plusRoot (m R D L : ℕ) (r : Position m R) :
    closedJobCell m R D L r ⊆ Set.Icc 0 1 := by
  intro x hx
  obtain ⟨hleft, hright⟩ := closedJobCell_bounds hx
  exact ⟨by linarith, hright.le⟩

theorem jobTestInterval_subset_closedJobCell (m R D L : ℕ) (r : Position m R) :
    jobTestInterval m R D L r ⊆ closedJobCell m R D L r := by
  intro x hx
  exact ⟨hx.1, hx.2.le⟩

theorem job_gap_of_posLT (D L : ℕ) {r s : Position m R} (hrs : posLT r s) :
    gap m R - delta m R D L ≤ jobLeft m R D L s - baseline m R r := by
  have h := baseline_gap_of_posLT hrs
  unfold jobLeft
  linarith

theorem baseline_lt_jobLeft_of_posLT (D L : ℕ) {r s : Position m R}
    (hrs : posLT r s) : baseline m R r < jobLeft m R D L s := by
  have hgap := job_gap_of_posLT D L hrs
  have hd := delta_lt_gap m R D L
  linarith

theorem closedJobCell_disjoint {r s : Position m R} (hrs : r ≠ s) :
    Disjoint (closedJobCell m R D L r) (closedJobCell m R D L s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases posLT_or_posLT_of_ne hrs with hlt | hlt
  · have h := baseline_lt_jobLeft_of_posLT D L hlt
    exact (not_le_of_gt h) (hy.1.trans hx.2)
  · have h := baseline_lt_jobLeft_of_posLT D L hlt
    exact (not_le_of_gt h) (hx.1.trans hy.2)

theorem jobTestInterval_disjoint {r s : Position m R} (hrs : r ≠ s) :
    Disjoint (jobTestInterval m R D L r) (jobTestInterval m R D L s) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact Set.disjoint_left.mp (closedJobCell_disjoint hrs)
    (jobTestInterval_subset_closedJobCell m R D L r hx)
    (jobTestInterval_subset_closedJobCell m R D L s hy)

theorem closedJobCell_unique_of_short_interval (hL : 1 ≤ L)
    {a b : ℚ} {r s : Position m R}
    (hlen : b - a ≤ lambda m R D 1 + delta m R D L)
    (hr : (Set.Icc a b ∩ closedJobCell m R D L r).Nonempty)
    (hs : (Set.Icc a b ∩ closedJobCell m R D L s).Nonempty) : r = s := by
  have hwidth := lambda_one_add_two_delta_lt_gap m R D hL
  rcases posLT_trichotomy r s with hrs | hrs | hsr
  · have hgap := job_gap_of_posLT D L hrs
    have hspan := closed_interval_gap_le_length hr hs
    linarith
  · exact hrs
  · have hgap := job_gap_of_posLT D L hsr
    have hspan := closed_interval_gap_le_length hs hr
    linarith

theorem closedJobCell_unique_of_short_halfOpen (hL : 1 ≤ L)
    {a b : ℚ} {r s : Position m R}
    (hlen : b - a ≤ lambda m R D 1 + delta m R D L)
    (hr : (Set.Ico a b ∩ closedJobCell m R D L r).Nonempty)
    (hs : (Set.Ico a b ∩ closedJobCell m R D L s).Nonempty) : r = s := by
  apply closedJobCell_unique_of_short_interval hL hlen
  · rcases hr with ⟨x, hx⟩
    exact ⟨x, ⟨hx.1.1, hx.1.2.le⟩, hx.2⟩
  · rcases hs with ⟨x, hx⟩
    exact ⟨x, ⟨hx.1.1, hx.1.2.le⟩, hx.2⟩

theorem jobInterior_mem_jobTestInterval (m R D L : ℕ) (r : Position m R) :
    jobInterior m R D L r ∈ jobTestInterval m R D L r :=
  jobInterior_mem_current (delta_pos m R D L) r

theorem jobInterior_mem_closedJobCell (m R D L : ℕ) (r : Position m R) :
    jobInterior m R D L r ∈ closedJobCell m R D L r :=
  jobTestInterval_subset_closedJobCell m R D L r
    (jobInterior_mem_jobTestInterval m R D L r)

theorem baseline_le_jobInterior (D L : ℕ) {r s : Position m R} :
    baseline m R s ≤ jobInterior m R D L r ↔ posLT s r :=
  baseline_le_actualJobInterior_iff D L

theorem jobInterior_mem_jobTestInterval_iff (D L : ℕ) {r s : Position m R} :
    jobInterior m R D L r ∈ jobTestInterval m R D L s ↔ s = r :=
  actualJobInterior_mem_job_iff D L

end BinPackingGap.Geometry

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def geometryBound : ℕ := TreeGeometry.commonBranchBound D.plus D.minus

theorem plus_branch_le_geometryBound : D.plus.branchBound ≤ D.geometryBound :=
  TreeGeometry.plus_branch_le D.plus D.minus

theorem minus_branch_le_geometryBound : D.minus.branchBound ≤ D.geometryBound :=
  TreeGeometry.minus_branch_le D.plus D.minus

def incidencePosition {v : D.Vertex} (j : D.IncidencePosition v) : D.Position :=
  (j.1.val.1, j.2)

theorem incidencePosition_injective (v : D.Vertex) :
    Function.Injective (D.incidencePosition (v := v)) := by
  rintro ⟨⟨⟨e, s⟩, hes⟩, i⟩ ⟨⟨⟨f, t⟩, hft⟩, j⟩ h
  change (e, i) = (f, j) at h
  have he : e = f := congrArg Prod.fst h
  have hij : i = j := congrArg Prod.snd h
  subst f
  subst j
  have hst : s = t := D.graph.endpoint_injective e (hes.trans hft.symm)
  subst t
  rfl

def testLeft {v : D.Vertex} : D.TestAt v → ℚ
  | .inl p => TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus p.val.val
  | .inr (.inl p) =>
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val
  | .inr (.inr j) =>
      Geometry.jobLeft D.graph.edges.length D.R D.geometryBound D.L (D.incidencePosition j)

def testRight {v : D.Vertex} : D.TestAt v → ℚ
  | .inl p => TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus p.val.val
  | .inr (.inl p) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus p.val.val
  | .inr (.inr j) => Geometry.baseline D.graph.edges.length D.R (D.incidencePosition j)

def testCell {v : D.Vertex} (t : D.TestAt v) : Set ℚ :=
  Set.Icc (D.testLeft t) (D.testRight t)

def testInterval {v : D.Vertex} (t : D.TestAt v) : Set ℚ :=
  Set.Ico (D.testLeft t) (D.testRight t)

theorem testLeft_lt_testRight {v : D.Vertex} (t : D.TestAt v) :
    D.testLeft t < D.testRight t := by
  rcases t with p | p | j
  · exact TreeGeometry.left_lt_right _ _ _ .plus p.val.val
  · exact TreeGeometry.left_lt_right _ _ _ .minus p.val.val
  · exact Geometry.jobLeft_lt_baseline _ _ _ _ (D.incidencePosition j)

private theorem tree_endpoints_in_root {T : UniformTree} (v : T.Node)
    (s : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    TreeGeometry.rootOffset s ≤
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound s v.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound s v.val ≤
        TreeGeometry.rootOffset s + 1 := by
  simpa only [TreeGeometry.left_nil, TreeGeometry.right_nil] using
    TreeGeometry.prefix_endpoints D.graph.edges.length D.R D.geometryBound s
      (u := []) (v := v.val) List.nil_prefix (TreeGeometry.boundedAddress_node v hT)

theorem test_endpoints_bounds {v : D.Vertex} (t : D.TestAt v) :
    0 ≤ D.testLeft t ∧ D.testRight t ≤ 5 := by
  rcases t with p | p | j
  · have h := D.tree_endpoints_in_root p.val .plus D.plus_branch_le_geometryBound
    norm_num only [TreeGeometry.rootOffset] at h
    change 0 ≤ D.testLeft (.inl p : D.TestAt v) ∧
      D.testRight (.inl p : D.TestAt v) ≤ 1 at h
    exact ⟨h.1, by linarith [h.2]⟩
  · have h := D.tree_endpoints_in_root p.val .minus D.minus_branch_le_geometryBound
    norm_num only [TreeGeometry.rootOffset] at h
    change 4 ≤ D.testLeft (.inr (.inl p) : D.TestAt v) ∧
      D.testRight (.inr (.inl p) : D.TestAt v) ≤ 5 at h
    exact ⟨by linarith [h.1], h.2⟩
  · have hl := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R
      D.geometryBound D.L (D.incidencePosition j)
    have hr := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.incidencePosition j)
    change 0 ≤ Geometry.jobLeft _ _ _ _ _ ∧ Geometry.baseline _ _ _ ≤ 5
    constructor <;> linarith

theorem testLeft_nonneg {v : D.Vertex} (t : D.TestAt v) : 0 ≤ D.testLeft t :=
  (D.test_endpoints_bounds t).1

theorem testRight_le_five {v : D.Vertex} (t : D.TestAt v) : D.testRight t ≤ 5 :=
  (D.test_endpoints_bounds t).2

theorem testCell_subset_range {v : D.Vertex} (t : D.TestAt v) :
    D.testCell t ⊆ Set.Icc (0 : ℚ) 5 := by
  intro x hx
  exact ⟨(D.testLeft_nonneg t).trans hx.1, hx.2.trans (D.testRight_le_five t)⟩

theorem testInterval_subset_testCell {v : D.Vertex} (t : D.TestAt v) :
    D.testInterval t ⊆ D.testCell t := fun _ hx => ⟨hx.1, hx.2.le⟩

private theorem disjoint_of_endpoint_lt {a b c d : ℚ} (h : b < c) :
    Disjoint (Set.Icc a b) (Set.Icc c d) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  exact (not_le_of_gt h) (hy.1.trans hx.2)

private theorem same_depth_cells_disjoint {s t : TreeGeometry.Side} {u w : List ℕ}
    (hu : u.length = D.L) (hw : w.length = D.L)
    (hbu : TreeGeometry.BoundedAddress D.geometryBound u)
    (hbw : TreeGeometry.BoundedAddress D.geometryBound w) (hne : (s, u) ≠ (t, w)) :
    Disjoint (TreeGeometry.cell D.graph.edges.length D.R D.geometryBound s u)
      (TreeGeometry.cell D.graph.edges.length D.R D.geometryBound t w) := by
  have hg := TreeGeometry.same_depth_gap D.graph.edges.length D.R D.geometryBound D.L
    hu hw hbu hbw hne
  have hp := Geometry.lambda_pos D.graph.edges.length D.R D.geometryBound D.L
  rcases hg with hg | hg
  · exact disjoint_of_endpoint_lt (by linarith)
  · exact (disjoint_of_endpoint_lt (by linarith)).symm

private theorem plusLeaf_right_lt_tenth (hplusheight : D.plus.height = D.L)
    (hL : 1 ≤ D.L) (p : D.PlusLeaf) :
    TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus p.val.val < 1 / 10 := by
  have hlength : p.val.val.length = D.L := (D.plus.length_leaf _ p.property).trans hplusheight
  have hn : p.val.val ≠ [] := by
    intro h
    rw [h] at hlength
    simp only [List.length_nil] at hlength
    omega
  have hb := TreeGeometry.nonroot_endpoints D.graph.edges.length D.R D.geometryBound .plus
    hn (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
  simpa only [TreeGeometry.rootOffset, zero_add] using hb.2

private theorem plusLeaf_job_disjoint (hplusheight : D.plus.height = D.L)
    (hL : 1 ≤ D.L) {v : D.Vertex} (p : D.PlusLeaf) (j : D.IncidencePosition v) :
    Disjoint (D.testCell (.inl p : D.TestAt v)) (D.testCell (.inr (.inr j))) := by
  have hp := D.plusLeaf_right_lt_tenth hplusheight hL p
  have hj := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R D.geometryBound D.L
    (D.incidencePosition j)
  exact disjoint_of_endpoint_lt (hp.trans hj)

private theorem minusLeaf_job_disjoint {v : D.Vertex} (p : D.MinusLeaf)
    (j : D.IncidencePosition v) :
    Disjoint (D.testCell (.inr (.inl p) : D.TestAt v)) (D.testCell (.inr (.inr j))) := by
  have hp := D.tree_endpoints_in_root p.val .minus D.minus_branch_le_geometryBound
  have hj := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.incidencePosition j)
  norm_num only [TreeGeometry.rootOffset] at hp
  change 4 ≤ TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val ∧
    _ ≤ 5 at hp
  have hgap : Geometry.baseline D.graph.edges.length D.R (D.incidencePosition j) <
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus p.val.val := by
    linarith [hp.1]
  exact (disjoint_of_endpoint_lt hgap).symm

theorem testCell_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    {v : D.Vertex} {s t : D.TestAt v} (hne : s ≠ t) :
    Disjoint (D.testCell s) (D.testCell t) := by
  rcases s with p | p | j <;> rcases t with q | q | k
  · apply D.same_depth_cells_disjoint
      ((D.plus.length_leaf _ p.property).trans hplusheight)
      ((D.plus.length_leaf _ q.property).trans hplusheight)
      (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.plus_branch_le_geometryBound)
    intro h
    have hpq : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd h))
    exact hne (congrArg Sum.inl hpq)
  · apply D.same_depth_cells_disjoint
      ((D.plus.length_leaf _ p.property).trans hplusheight)
      ((D.minus.length_leaf _ q.property).trans hminusheight)
      (TreeGeometry.boundedAddress_node p.val D.plus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.minus_branch_le_geometryBound)
    intro h
    have hs := congrArg Prod.fst h
    cases hs
  · exact D.plusLeaf_job_disjoint hplusheight hL p k
  · apply D.same_depth_cells_disjoint
      ((D.minus.length_leaf _ p.property).trans hminusheight)
      ((D.plus.length_leaf _ q.property).trans hplusheight)
      (TreeGeometry.boundedAddress_node p.val D.minus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.plus_branch_le_geometryBound)
    intro h
    have hs := congrArg Prod.fst h
    cases hs
  · apply D.same_depth_cells_disjoint
      ((D.minus.length_leaf _ p.property).trans hminusheight)
      ((D.minus.length_leaf _ q.property).trans hminusheight)
      (TreeGeometry.boundedAddress_node p.val D.minus_branch_le_geometryBound)
      (TreeGeometry.boundedAddress_node q.val D.minus_branch_le_geometryBound)
    intro h
    have hpq : p = q := Subtype.ext (Subtype.ext (congrArg Prod.snd h))
    exact hne (congrArg (fun l => Sum.inr (Sum.inl l)) hpq)
  · exact D.minusLeaf_job_disjoint p k
  · exact (D.plusLeaf_job_disjoint hplusheight hL q j).symm
  · exact (D.minusLeaf_job_disjoint q j).symm
  · apply Geometry.closedJobCell_disjoint
    intro h
    have hjk := D.incidencePosition_injective v h
    exact hne (congrArg (fun r => Sum.inr (Sum.inr r)) hjk)

theorem testCell_pairwise_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L) (v : D.Vertex) :
    Pairwise (fun s t : D.TestAt v => Disjoint (D.testCell s) (D.testCell t)) :=
  fun _ _ hne => D.testCell_disjoint hplusheight hminusheight hL hne

theorem testInterval_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L)
    {v : D.Vertex} {s t : D.TestAt v} (hne : s ≠ t) :
    Disjoint (D.testInterval s) (D.testInterval t) :=
  (D.testCell_disjoint hplusheight hminusheight hL hne).mono
    (D.testInterval_subset_testCell s) (D.testInterval_subset_testCell t)

theorem testInterval_pairwise_disjoint (hplusheight : D.plus.height = D.L)
    (hminusheight : D.minus.height = D.L) (hL : 1 ≤ D.L) (v : D.Vertex) :
    Pairwise (fun s t : D.TestAt v => Disjoint (D.testInterval s) (D.testInterval t)) :=
  fun _ _ hne => D.testInterval_disjoint hplusheight hminusheight hL hne

end BinPackingGap.InventoryData

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Packing/PackingCoordinates.lean =====
namespace OAI

namespace BinPackingGap.InventoryData

variable (D : InventoryData)

def treeBaseline : D.TreeRow → ℚ
  | .inl (node, _) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus node.val
  | .inr (.inl (node, _)) =>
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus node.val
  | .inr (.inr _) => 1

def rowBaseline {v : D.Vertex} : D.RowAt v → ℚ
  | .inl r => D.treeBaseline r
  | .inr (_, j) => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)

def mainBaseline {v : D.Vertex} : D.MBase v → ℚ
  | .inl r => D.treeBaseline r
  | .inr j => Geometry.baseline D.graph.edges.length D.R (D.jobPosition j)

def treeDeadline : D.TreeRow → ℚ
  | .inl (node, _) =>
      if node.val ∈ D.plus.leaves then
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound .plus node.val
      else TreeGeometry.right D.graph.edges.length D.R D.geometryBound .plus node.val
  | .inr (.inl (node, _)) =>
      if node.val ∈ D.minus.leaves then
        TreeGeometry.left D.graph.edges.length D.R D.geometryBound .minus node.val
      else TreeGeometry.right D.graph.edges.length D.R D.geometryBound .minus node.val
  | .inr (.inr _) => 1

def deadline {v : D.Vertex} : D.MBase v → ℚ
  | .inl r => D.treeDeadline r
  | .inr j => Geometry.jobLeft D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition j)

def rowCoordinate {v : D.Vertex} (r : D.RowAt v) : ℚ :=
  D.rowBaseline r - if D.rowShort r then
    Geometry.delta D.graph.edges.length D.R D.geometryBound D.L else 0

def anchorCoordinate {v : D.Vertex} : D.AnchorAt v → ℚ
  | .inl z => -D.deadline z
  | .inr j => -Geometry.baseline D.graph.edges.length D.R (D.jobPosition j) -
      Geometry.beta D.graph.edges.length D.R (D.jobPosition j).1

def globalLength : D.GlobalCopy → ℚ
  | ⟨.up one, _⟩ => if one then 1 else 0
  | ⟨.um one, _⟩ => if one then 1 else 0
  | ⟨.edge _ _, _⟩ => 0

def globalCoordinate : D.GlobalCopy → ℚ
  | ⟨.up one, _⟩ => -(if one then 1 else 0)
  | ⟨.um one, _⟩ => -(if one then 1 else 0)
  | ⟨.edge e permit, _⟩ => Geometry.beta D.graph.edges.length D.R e +
      if permit then 0 else Geometry.delta D.graph.edges.length D.R D.geometryBound D.L

def localLength {v : D.Vertex} : D.LocalAt v → ℚ
  | .inl (.inl ⟨ell, _⟩) =>
      Geometry.lambda D.graph.edges.length D.R D.geometryBound ell.val
  | _ => 0

def localCoordinate {v : D.Vertex} (i : D.LocalAt v) : ℚ := -D.localLength i

def itemCoordinate : D.Item → ℚ
  | ⟨.x, ⟨_, r⟩⟩ => D.rowCoordinate r
  | ⟨.anchor, ⟨_, a⟩⟩ => D.anchorCoordinate a
  | ⟨.«global», u⟩ => D.globalCoordinate u
  | ⟨.«local», ⟨_, l⟩⟩ => D.localCoordinate l
  | ⟨.flag, _⟩ => 0

theorem mainBaseline_designated {v : D.Vertex} (q : D.TestAt v × Fin D.d) :
    D.mainBaseline (D.designated q) = D.testRight q.1 := by
  rcases q with ⟨t, j⟩
  rcases t with p | p | r <;> rfl

theorem deadline_designated {v : D.Vertex} (q : D.TestAt v × Fin D.d) :
    D.deadline (D.designated q) = D.testLeft q.1 := by
  rcases q with ⟨t, j⟩
  rcases t with p | p | r
  · simp [designated, deadline, treeDeadline, p.property, testLeft]
  · simp [designated, deadline, treeDeadline, p.property, testLeft]
  · rfl

theorem globalLength_nonneg (u : D.GlobalCopy) : 0 ≤ D.globalLength u := by
  rcases u with ⟨s, i⟩
  cases s with
  | up b => cases b <;> norm_num [globalLength]
  | um b => cases b <;> norm_num [globalLength]
  | edge e b => simp [globalLength]

theorem globalLength_le_one (u : D.GlobalCopy) : D.globalLength u ≤ 1 := by
  rcases u with ⟨s, i⟩
  cases s with
  | up b => cases b <;> norm_num [globalLength]
  | um b => cases b <;> norm_num [globalLength]
  | edge e b => simp [globalLength]

private theorem node_endpoint_bounds {T : UniformTree} (node : T.Node)
    (side : TreeGeometry.Side) (hT : T.branchBound ≤ D.geometryBound) :
    (0 ≤ TreeGeometry.left D.graph.edges.length D.R D.geometryBound side node.val ∧
      TreeGeometry.left D.graph.edges.length D.R D.geometryBound side node.val ≤ 5) ∧
    (0 ≤ TreeGeometry.right D.graph.edges.length D.R D.geometryBound side node.val ∧
      TreeGeometry.right D.graph.edges.length D.R D.geometryBound side node.val ≤ 5) := by
  have hroot := TreeGeometry.prefix_endpoints D.graph.edges.length D.R D.geometryBound side
    (u := []) (v := node.val) List.nil_prefix (TreeGeometry.boundedAddress_node node hT)
  simp only [TreeGeometry.left_nil, TreeGeometry.right_nil] at hroot
  have hwidth := TreeGeometry.left_lt_right D.graph.edges.length D.R D.geometryBound side node.val
  cases side <;> simp only [TreeGeometry.rootOffset] at hroot <;>
    constructor <;> constructor <;> linarith [hroot.1, hroot.2]

theorem treeBaseline_bounds (r : D.TreeRow) :
    0 ≤ D.treeBaseline r ∧ D.treeBaseline r ≤ 5 := by
  rcases r with p | p | padding
  · exact (D.node_endpoint_bounds p.1 .plus D.plus_branch_le_geometryBound).2
  · exact (D.node_endpoint_bounds p.1 .minus D.minus_branch_le_geometryBound).2
  · norm_num [treeBaseline]

theorem treeDeadline_bounds (r : D.TreeRow) :
    0 ≤ D.treeDeadline r ∧ D.treeDeadline r ≤ 5 := by
  rcases r with p | p | padding
  · have h := D.node_endpoint_bounds p.1 .plus D.plus_branch_le_geometryBound
    dsimp only [treeDeadline]
    split_ifs
    · exact h.1
    · exact h.2
  · have h := D.node_endpoint_bounds p.1 .minus D.minus_branch_le_geometryBound
    dsimp only [treeDeadline]
    split_ifs
    · exact h.1
    · exact h.2
  · norm_num [treeDeadline]

private theorem jobBaseline_bounds (p : D.Position) :
    0 ≤ Geometry.baseline D.graph.edges.length D.R p ∧
      Geometry.baseline D.graph.edges.length D.R p ≤ 5 := by
  have h := Geometry.baseline_range D.graph.edges.length D.R p
  constructor <;> linarith [h.1, h.2]

theorem rowBaseline_bounds {v : D.Vertex} (r : D.RowAt v) :
    0 ≤ D.rowBaseline r ∧ D.rowBaseline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeBaseline_bounds tree
  · exact D.jobBaseline_bounds (D.jobPosition job.2)

theorem mainBaseline_bounds {v : D.Vertex} (r : D.MBase v) :
    0 ≤ D.mainBaseline r ∧ D.mainBaseline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeBaseline_bounds tree
  · exact D.jobBaseline_bounds (D.jobPosition job)

theorem deadline_bounds {v : D.Vertex} (r : D.MBase v) :
    0 ≤ D.deadline r ∧ D.deadline r ≤ 5 := by
  rcases r with tree | job
  · exact D.treeDeadline_bounds tree
  · have hl := Geometry.one_tenth_lt_jobLeft D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition job)
    have hu := Geometry.jobLeft_lt_baseline D.graph.edges.length D.R D.geometryBound D.L
      (D.jobPosition job)
    have hb := Geometry.job_baseline_lt_one D.graph.edges.length D.R (D.jobPosition job)
    change 0 ≤ Geometry.jobLeft _ _ _ _ _ ∧ Geometry.jobLeft _ _ _ _ _ ≤ 5
    constructor <;> linarith

theorem rowCoordinate_bounds {v : D.Vertex} (r : D.RowAt v) :
    0 ≤ D.rowCoordinate r ∧ D.rowCoordinate r ≤ 5 := by
  rcases r with tree | ⟨short, job⟩
  · simpa only [rowCoordinate, rowBaseline, rowShort, Bool.false_eq_true, ite_false,
      sub_zero] using D.treeBaseline_bounds tree
  · have hb := Geometry.baseline_range D.graph.edges.length D.R (D.jobPosition job)
    have hd := Geometry.delta_lt_gap D.graph.edges.length D.R D.geometryBound D.L
    have hg := Geometry.gap_le_one_sixteen D.graph.edges.length D.R
    have hd0 := Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L
    cases short <;>
      simp only [rowCoordinate, rowBaseline, rowShort, Bool.false_eq_true, ite_false,
        ite_true, sub_zero] <;>
      constructor <;> linarith [hb.1, hb.2]

theorem anchorCoordinate_bounds {v : D.Vertex} (a : D.AnchorAt v) :
    -5 ≤ D.anchorCoordinate a ∧ D.anchorCoordinate a ≤ 0 := by
  rcases a with deadline | key
  · have h := D.deadline_bounds deadline
    change -5 ≤ -D.deadline deadline ∧ -D.deadline deadline ≤ 0
    constructor <;> linarith [h.1, h.2]
  · have hb := Geometry.baseline_range D.graph.edges.length D.R (D.jobPosition key)
    have hβ0 := Geometry.beta_nonneg D.graph.edges.length D.R (D.jobPosition key).1
    have hβ := Geometry.beta_lt_one_sixteen D.graph.edges.length D.R (D.jobPosition key).1
    dsimp only [anchorCoordinate]
    constructor <;> linarith [hb.1, hb.2]

theorem globalCoordinate_bounds (u : D.GlobalCopy) :
    -1 ≤ D.globalCoordinate u ∧ D.globalCoordinate u ≤ 1 := by
  rcases u with ⟨species, copy⟩
  cases species with
  | up one => cases one <;> norm_num [globalCoordinate]
  | um one => cases one <;> norm_num [globalCoordinate]
  | edge edge permit =>
      have hβ0 := Geometry.beta_nonneg D.graph.edges.length D.R edge
      have hβ := Geometry.beta_lt_one_sixteen D.graph.edges.length D.R edge
      have hd0 := Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L
      have hd := Geometry.delta_lt_gap D.graph.edges.length D.R D.geometryBound D.L
      have hg := Geometry.gap_le_one_sixteen D.graph.edges.length D.R
      cases permit <;>
        simp only [globalCoordinate, Bool.false_eq_true, ite_false, ite_true, add_zero] <;>
        constructor <;> linarith

theorem localLength_nonneg {v : D.Vertex} (i : D.LocalAt v) : 0 ≤ D.localLength i := by
  rcases i with (⟨ell, copy⟩ | zero) | edge
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound ell.val
  · exact le_rfl
  · exact le_rfl

theorem localLength_le_lambda_one {v : D.Vertex} (i : D.LocalAt v) :
    D.localLength i ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 := by
  rcases i with (⟨ell, copy⟩ | zero) | edge
  · exact Geometry.lambda_antitone D.graph.edges.length D.R D.geometryBound
      (Finset.mem_Icc.mp ell.property).1
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound 1
  · exact Geometry.lambda_nonneg D.graph.edges.length D.R D.geometryBound 1

theorem localLength_le_one {v : D.Vertex} (i : D.LocalAt v) : D.localLength i ≤ 1 :=
  (D.localLength_le_lambda_one i).trans
    (Geometry.lambda_le_one D.graph.edges.length D.R D.geometryBound 1)

theorem localCoordinate_bounds {v : D.Vertex} (i : D.LocalAt v) :
    -1 ≤ D.localCoordinate i ∧ D.localCoordinate i ≤ 0 := by
  have h0 := D.localLength_nonneg i
  have h1 := D.localLength_le_one i
  unfold localCoordinate
  constructor <;> linarith

theorem itemCoordinate_bounds (i : D.Item) :
    -5 ≤ D.itemCoordinate i ∧ D.itemCoordinate i ≤ 5 := by
  rcases i with ⟨role, i⟩
  cases role with
  | x =>
      rcases i with ⟨v, r⟩
      have h := D.rowCoordinate_bounds r
      change -5 ≤ D.rowCoordinate r ∧ D.rowCoordinate r ≤ 5
      exact ⟨by linarith [h.1], h.2⟩
  | anchor =>
      rcases i with ⟨v, a⟩
      have h := D.anchorCoordinate_bounds a
      change -5 ≤ D.anchorCoordinate a ∧ D.anchorCoordinate a ≤ 5
      exact ⟨h.1, by linarith [h.2]⟩
  | «global» =>
      have h := D.globalCoordinate_bounds i
      change -5 ≤ D.globalCoordinate i ∧ D.globalCoordinate i ≤ 5
      constructor <;> linarith [h.1, h.2]
  | «local» =>
      rcases i with ⟨v, l⟩
      have h := D.localCoordinate_bounds l
      change -5 ≤ D.localCoordinate l ∧ D.localCoordinate l ≤ 5
      constructor <;> linarith [h.1, h.2]
  | flag => norm_num [itemCoordinate]

theorem itemCoordinate_abs_le_six (i : D.Item) : |D.itemCoordinate i| ≤ 6 := by
  have h := D.itemCoordinate_bounds i
  apply abs_le.mpr
  constructor <;> linarith [h.1, h.2]

def stateRowEquiv (v : D.Vertex) (selected : Bool) : D.LocalBin v ≃ D.RowAt v where
  toFun
    | .inl (.inl t) => .inl t
    | .inl (.inr j) => .inr (!selected, j)
    | .inr j => .inr (selected, j)
  invFun
    | .inl t => .inl (.inl t)
    | .inr (short, j) => if short = selected then .inr j else .inl (.inr j)
  left_inv i := by
    rcases i with (t | j) | j <;> cases selected <;> simp
  right_inv r := by
    rcases r with t | ⟨b, j⟩
    · rfl
    · cases b <;> cases selected <;> simp

@[simp] theorem stateRowEquiv_tree (v : D.Vertex) (selected : Bool) (t : D.TreeRow) :
    D.stateRowEquiv v selected (.inl (.inl t)) = .inl t := rfl

@[simp] theorem stateRowEquiv_mainJob (v : D.Vertex) (selected : Bool) (j : D.JobCopy v) :
    D.stateRowEquiv v selected (.inl (.inr j)) = .inr (!selected, j) := rfl

@[simp] theorem stateRowEquiv_edgeJob (v : D.Vertex) (selected : Bool) (j : D.JobCopy v) :
    D.stateRowEquiv v selected (.inr j) = .inr (selected, j) := rfl

def stateMainRow (v : D.Vertex) (selected : Bool) (b : D.MBase v) : D.RowAt v :=
  D.stateRowEquiv v selected (.inl b)

theorem stateMainRow_injective (v : D.Vertex) (selected : Bool) :
    Function.Injective (D.stateMainRow v selected) := by
  intro b c h
  exact Sum.inl.inj ((D.stateRowEquiv v selected).injective h)

@[simp] theorem stateMainRow_baseline (v : D.Vertex) (selected : Bool) (b : D.MBase v) :
    D.rowBaseline (D.stateMainRow v selected b) = D.mainBaseline b := by
  rcases b with t | j <;> rfl

def stateFlagSpecies {v : D.Vertex} : D.LocalBin v → FlagSpecies
  | .inl (.inl _) => .tree
  | .inl (.inr _) => .main
  | .inr _ => .edge

def stateMainGlobalSpecies {v : D.Vertex} (selected : Bool) :
    D.MBase v → GlobalSpecies D.graph
  | .inl (.inl (node, _)) => .up (selected && decide (node = D.plus.root))
  | .inl (.inr (.inl (node, _))) => .um (!selected && decide (node = D.minus.root))
  | .inl (.inr (.inr _)) => .up false
  | .inr _ => .up false

def stateGlobalSpecies {v : D.Vertex} (selected : Bool) :
    D.LocalBin v → GlobalSpecies D.graph
  | .inl b => D.stateMainGlobalSpecies selected b
  | .inr j => .edge (D.jobPosition j).1 (!selected)

def globalSpeciesLength : GlobalSpecies D.graph → ℚ
  | .up one => if one then 1 else 0
  | .um one => if one then 1 else 0
  | .edge _ _ => 0

theorem globalLength_eq_species (u : D.GlobalCopy) :
    D.globalLength u = D.globalSpeciesLength u.1 := by
  rcases u with ⟨s, i⟩
  cases s <;> rfl

def stateMainLength {v : D.Vertex} (selected : Bool) (b : D.MBase v) : ℚ :=
  D.globalSpeciesLength (D.stateMainGlobalSpecies selected b)

theorem stateMainLength_nonneg {v : D.Vertex} (selected : Bool) (b : D.MBase v) :
    0 ≤ D.stateMainLength selected b := by
  rcases b with (⟨p, i⟩ | ⟨m, i⟩ | i) | j
  all_goals simp only [stateMainLength, stateMainGlobalSpecies, globalSpeciesLength]
  all_goals split_ifs <;> norm_num

theorem stateMainLength_le_one {v : D.Vertex} (selected : Bool) (b : D.MBase v) :
    D.stateMainLength selected b ≤ 1 := by
  rcases b with (⟨p, i⟩ | ⟨m, i⟩ | i) | j
  all_goals simp only [stateMainLength, stateMainGlobalSpecies, globalSpeciesLength]
  all_goals split_ifs <;> norm_num

def fundedRoot {v : D.Vertex} (selected : Bool) (j : Fin D.d) : D.MBase v :=
  if selected then .inl (.inl (D.plus.root, j))
  else .inl (.inr (.inl (D.minus.root, j)))

theorem fundedRoot_injective (v : D.Vertex) (selected : Bool) :
    Function.Injective (D.fundedRoot (v := v) selected) := by
  intro i j h
  cases selected <;> simpa [fundedRoot] using h

@[simp] theorem stateMainLength_fundedRoot {v : D.Vertex} (selected : Bool) (j : Fin D.d) :
    D.stateMainLength selected (D.fundedRoot (v := v) selected j) = 1 := by
  cases selected <;> simp [fundedRoot, stateMainLength, stateMainGlobalSpecies,
    globalSpeciesLength]

abbrev PhysicalBins := Σ v : D.Vertex, D.LocalBin v

theorem card_physicalBins : Fintype.card D.PhysicalBins = D.B := by
  simp only [PhysicalBins, Fintype.card_sigma, D.card_localBin, B]

structure LocalState (v : D.Vertex) (selected : Bool) where
  localEquiv : D.MBase v ≃ D.DMAt v
  anchorEquiv : D.MBase v ≃ D.MBase v
  completion_le_deadline : ∀ b,
    D.rowCoordinate (D.stateMainRow v selected b) - D.stateMainLength selected b -
      D.localLength (.inl (localEquiv b)) ≤ D.deadline (anchorEquiv b)

namespace LocalState

variable {D} {v : D.Vertex} {selected : Bool} (S : D.LocalState v selected)

def anchorAtEquiv : D.LocalBin v ≃ D.AnchorAt v :=
  Equiv.sumCongr S.anchorEquiv (Equiv.refl _)

def localAtEquiv : D.LocalBin v ≃ D.LocalAt v :=
  Equiv.sumCongr S.localEquiv (Equiv.refl _)

@[simp] theorem anchorAtEquiv_main (b : D.MBase v) :
    S.anchorAtEquiv (.inl b) = .inl (S.anchorEquiv b) := rfl

@[simp] theorem anchorAtEquiv_edge (j : D.JobCopy v) :
    S.anchorAtEquiv (.inr j) = .inr j := rfl

@[simp] theorem localAtEquiv_main (b : D.MBase v) :
    S.localAtEquiv (.inl b) = .inl (S.localEquiv b) := rfl

@[simp] theorem localAtEquiv_edge (j : D.JobCopy v) :
    S.localAtEquiv (.inr j) = .inr j := rfl

end LocalState

end BinPackingGap.InventoryData

noncomputable section

namespace BinPackingGap
namespace PackingCounts

variable {D : InventoryData} {I : Instance} {b : ℕ}

def tupleBaseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.rowBaseline (rowCopy p e t).2

def tupleShort (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Bool := D.rowShort (rowCopy p e t).2

def tupleGlobalLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.globalLength (globalCopy p e t)

def tupleLocalLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ := D.localLength (localCopy p e t).2

def tupleFinish (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : ℚ :=
  completion (tupleBaseline p e t) (tupleShort p e t)
    (tupleGlobalLength p e t) (tupleLocalLength p e t)
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L)

def tupleClosedInterval (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Set ℚ :=
  Set.Icc (tupleFinish p e t) (tupleBaseline p e t)

def tupleCoveringInterval (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : Set ℚ :=
  Set.Ico (tupleFinish p e t) (tupleBaseline p e t)

def tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item) (v : D.Vertex) (a : ℚ) :
    Finset (p.TableBin (subclass e)) := by
  classical
  exact (Coverage.mainTuplesAt p (subclass e) (label e) v).filter fun t =>
    tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t

@[simp] theorem mem_tupleCovering (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (a : ℚ) (t : p.TableBin (subclass e)) :
    t ∈ tupleCovering p e v a ↔
      t ∈ Coverage.mainTuplesAt p (subclass e) (label e) v ∧
        tupleFinish p e t ≤ a ∧ a < tupleBaseline p e t := by
  classical
  simp [tupleCovering, and_assoc]

theorem tupleGlobalLength_nonneg (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : 0 ≤ tupleGlobalLength p e t :=
  D.globalLength_nonneg _

theorem tupleGlobalLength_le_one (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : tupleGlobalLength p e t ≤ 1 :=
  D.globalLength_le_one _

theorem tupleGlobalLength_eq_of_unit_false (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) (hu : D.globalUnit (globalCopy p e t) = false) :
    tupleGlobalLength p e t = 0 := by
  have h : D.globalLength (globalCopy p e t) =
      if D.globalUnit (globalCopy p e t) then 1 else 0 := by
    rcases globalCopy p e t with ⟨s, i⟩
    cases s <;> rfl
  simpa only [tupleGlobalLength, hu, Bool.false_eq_true, ↓reduceIte] using h

private theorem localLength_nonneg {v : D.Vertex} (l : D.LocalAt v) : 0 ≤ D.localLength l := by
  rcases l with ((⟨ell, i⟩ | z) | g)
  · exact Geometry.lambda_nonneg _ _ _ _
  · rfl
  · rfl

private theorem localLength_le_first {v : D.Vertex} (l : D.LocalAt v) :
    D.localLength l ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 := by
  rcases l with ((⟨ell, i⟩ | z) | g)
  · exact Geometry.lambda_antitone _ _ _ (Finset.mem_Icc.mp ell.property).1
  · exact Geometry.lambda_nonneg _ _ _ _
  · exact Geometry.lambda_nonneg _ _ _ _

theorem tupleLocalLength_nonneg (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : 0 ≤ tupleLocalLength p e t :=
  localLength_nonneg _

theorem tupleLocalLength_le_first (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) :
    tupleLocalLength p e t ≤ Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 :=
  localLength_le_first _

theorem tupleLocalLength_eq_zero_of_not_positive (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e))
    (ht : t ∈ Coverage.goodTuplesAt p (subclass e) (label e) v)
    (hnot : p.itemAtRole (subclass e) t .«local» ∉ positiveLocalResources e v) :
    tupleLocalLength p e t = 0 := by
  rcases hc : localCopy p e t with ⟨w, ((i | z) | g)⟩
  · have hw : w = v := by simpa only [hc] using good_local_vertex p e v t ht
    subst w
    exfalso
    apply hnot
    apply (mem_positiveLocalResources e v _).mpr
    refine ⟨i, ?_⟩
    rw [← roleCopy_item p e t .«local»]
    exact congrArg (fun x : (Σ w : D.Vertex, D.LocalAt w) => e ⟨.«local», x⟩) hc.symm
  · unfold tupleLocalLength
    rw [hc]
    rfl
  · unfold tupleLocalLength
    rw [hc]
    rfl

theorem tupleFinish_le_baseline (p : Packing I b) (e : D.Item ≃ I.Item)
    (t : p.TableBin (subclass e)) : tupleFinish p e t ≤ tupleBaseline p e t :=
  completion_le_baseline _ _ _ _ _ (tupleGlobalLength_nonneg p e t)
    (tupleLocalLength_nonneg p e t) (Geometry.delta_nonneg _ _ _ _)

theorem selected_localLength (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleLocalLength p e t =
      Geometry.lambda D.graph.edges.length D.R D.geometryBound (tupleLocalDepth p e t) := by
  obtain ⟨i, hi⟩ := localCopy_eq_of_positive p e v t
    (((mem_zeroPositiveTuples p e v t).mp ht).2.2)
  unfold tupleLocalLength tupleLocalDepth
  rw [hi]
  rfl

theorem selected_interval_length (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleBaseline p e t - tupleFinish p e t ≤
      Geometry.lambda D.graph.edges.length D.R D.geometryBound (tupleLocalDepth p e t) +
        Geometry.delta D.graph.edges.length D.R D.geometryBound D.L := by
  have hu := ((mem_zeroPositiveTuples p e v t).mp ht).2.1
  unfold tupleFinish
  rw [tupleGlobalLength_eq_of_unit_false p e t hu, selected_localLength p e v t ht]
  exact completion_zero_global_length_le _ _ _ _ (Geometry.delta_nonneg _ _ _ _)

theorem selected_interval_length_first (p : Packing I b) (e : D.Item ≃ I.Item)
    (v : D.Vertex) (t : p.TableBin (subclass e)) (ht : t ∈ zeroPositiveTuples p e v) :
    tupleBaseline p e t - tupleFinish p e t ≤
      Geometry.lambda D.graph.edges.length D.R D.geometryBound 1 +
        Geometry.delta D.graph.edges.length D.R D.geometryBound D.L := by
  have hu := ((mem_zeroPositiveTuples p e v t).mp ht).2.1
  unfold tupleFinish
  rw [tupleGlobalLength_eq_of_unit_false p e t hu]
  apply le_trans (completion_zero_global_length_le
    (tupleBaseline p e t) (tupleShort p e t) (tupleLocalLength p e t)
    (Geometry.delta D.graph.edges.length D.R D.geometryBound D.L)
    (Geometry.delta_nonneg D.graph.edges.length D.R D.geometryBound D.L))
  exact add_le_add (tupleLocalLength_le_first p e t) le_rfl

end PackingCounts
end BinPackingGap

end

end OAI

-- ===== Adapted from lean/OAI/Computability/BinPacking/Inventory/InventoryPrefixConservation.lean =====
namespace OAI

noncomputable section

namespace BinPackingGap

section

open scoped BigOperators

namespace InventoryData

variable (D : InventoryData)

def itemSize (i : D.Item) : ℚ :=
  encodedSize (D.itemSubclass i) (D.itemLabel i) (D.itemCoordinate i)

theorem itemSize_mem_interval (i : D.Item) :
    1 / 6 < D.itemSize i ∧ D.itemSize i < 1 :=
  encodedSize_mem_interval _ _ _ (D.itemCoordinate_abs_le_six i)

theorem itemSize_pos (i : D.Item) : 0 < D.itemSize i :=
  lt_trans (by norm_num) (D.itemSize_mem_interval i).1

theorem itemSize_le_one (i : D.Item) : D.itemSize i ≤ 1 :=
  (D.itemSize_mem_interval i).2.le

def packingInstance : Instance :=
  Instance.ofFintype D.itemSize D.itemSize_pos D.itemSize_le_one

def itemEquiv : D.Item ≃ D.packingInstance.Item := Fintype.equivFin D.Item

def encodedSubclass (i : D.packingInstance.Item) : Subclass :=
  D.itemSubclass (D.itemEquiv.symm i)

def encodedLabel (i : D.packingInstance.Item) : Option D.Vertex :=
  D.itemLabel (D.itemEquiv.symm i)

def encodedCoordinate (i : D.packingInstance.Item) : ℚ :=
  D.itemCoordinate (D.itemEquiv.symm i)

theorem packingInstance_size_eq (i : D.packingInstance.Item) :
    D.packingInstance.size i =
      encodedSize (D.encodedSubclass i) (D.encodedLabel i) (D.encodedCoordinate i) := rfl

theorem encodedCoordinate_abs_le_six (i : D.packingInstance.Item) :
    |D.encodedCoordinate i| ≤ 6 := D.itemCoordinate_abs_le_six _

theorem packingInstance_size_mem_interval (i : D.packingInstance.Item) :
    1 / 6 < D.packingInstance.size i ∧ D.packingInstance.size i < 1 :=
  D.itemSize_mem_interval _

theorem packingInstance_n (hk : D.k ≤ D.graph.n) :
    D.packingInstance.n = 5 * D.B := D.card_item hk

theorem encoded_primaryScore_sum_eq_zero (hk : D.k ≤ D.graph.n) :
    (∑ i : D.packingInstance.Item, primaryScore (D.encodedSubclass i)) = 0 := by
  change (∑ i, primaryScore (D.itemSubclass (D.itemEquiv.symm i))) = 0
  rw [D.itemEquiv.symm.sum_comp (fun i : D.Item => primaryScore (D.itemSubclass i))]
  exact D.total_primaryScore_eq_zero hk

theorem encoded_secondaryScore_sum_eq_zero :
    (∑ i : D.packingInstance.Item,
      secondaryScore (D.encodedSubclass i) (D.encodedLabel i)) = 0 := by
  change (∑ i, secondaryScore (D.itemSubclass (D.itemEquiv.symm i))
    (D.itemLabel (D.itemEquiv.symm i))) = 0
  rw [D.itemEquiv.symm.sum_comp
    (fun i : D.Item => secondaryScore (D.itemSubclass i) (D.itemLabel i))]
  exact D.total_secondaryScore_eq_zero

theorem encoded_labelledRoleCount (r : Role) (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel r v =
      labelledRoleCount D.itemSubclass D.itemLabel r v := by
  unfold labelledRoleCount encodedSubclass encodedLabel
  exact D.itemEquiv.symm.sum_comp
    (fun i : D.Item => if (D.itemSubclass i).role = r ∧ D.itemLabel i = some v
      then (1 : ℤ) else 0)

theorem encoded_labelledRoleCount_x (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .x v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_x]

theorem encoded_labelledRoleCount_anchor (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .anchor v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_anchor]

theorem encoded_labelledRoleCount_local (v : D.Vertex) :
    labelledRoleCount D.encodedSubclass D.encodedLabel .«local» v =
      ((D.t + 2 * D.J v : ℕ) : ℤ) := by
  rw [D.encoded_labelledRoleCount, D.labelledRoleCount_local]

theorem itemLabel_some_of_labelled (i : D.Item)
    (h : D.itemRole i = .x ∨ D.itemRole i = .anchor ∨ D.itemRole i = .«local») :
    ∃ v, D.itemLabel i = some v := by
  rcases i with ⟨r, i⟩
  cases r <;> simp only [itemRole] at h
  · exact ⟨i.1, rfl⟩
  · exact ⟨i.1, rfl⟩
  · simp at h
  · exact ⟨i.1, rfl⟩
  · simp at h

theorem itemLabel_none_of_unlabelled (i : D.Item)
    (h : D.itemRole i = .«global» ∨ D.itemRole i = .flag) :
    D.itemLabel i = none := by
  rcases i with ⟨r, i⟩
  cases r <;> simp_all [itemRole, itemLabel]

theorem encodedLabel_some_of_labelled (i : D.packingInstance.Item)
    (h : (D.encodedSubclass i).role = .x ∨ (D.encodedSubclass i).role = .anchor ∨
      (D.encodedSubclass i).role = .«local») :
    ∃ v, D.encodedLabel i = some v := by
  apply D.itemLabel_some_of_labelled (D.itemEquiv.symm i)
  simpa only [encodedSubclass, D.itemSubclass_role] using h

theorem encodedLabel_none_of_unlabelled (i : D.packingInstance.Item)
    (h : (D.encodedSubclass i).role = .«global» ∨ (D.encodedSubclass i).role = .flag) :
    D.encodedLabel i = none := by
  apply D.itemLabel_none_of_unlabelled (D.itemEquiv.symm i)
  simpa only [encodedSubclass, D.itemSubclass_role] using h

end InventoryData

end

namespace InventoryData

open scoped BigOperators

variable (D : InventoryData)

def roleLabelData : RoleLabelData D.encodedSubclass D.encodedLabel :=
  RoleLabelData.of_valid D.encodedSubclass D.encodedLabel
    D.encodedLabel_some_of_labelled D.encodedLabel_none_of_unlabelled

theorem roleLabelData_anchor_row_count (v : D.Vertex) :
    (Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card =
      (Finset.univ.filter fun i => D.roleLabelData.row i = v).card := by
  classical
  have h : ((Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card : ℤ) =
      ((Finset.univ.filter fun i => D.roleLabelData.row i = v).card : ℤ) := by
    rw [D.roleLabelData.anchor_count, D.roleLabelData.row_count,
      D.encoded_labelledRoleCount_anchor, D.encoded_labelledRoleCount_x]
  exact_mod_cast h

theorem roleLabelData_anchor_local_count (v : D.Vertex) :
    (Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card =
      (Finset.univ.filter fun i => D.roleLabelData.localLabel i = v).card := by
  classical
  have h : ((Finset.univ.filter fun i => D.roleLabelData.anchor i = v).card : ℤ) =
      ((Finset.univ.filter fun i => D.roleLabelData.localLabel i = v).card : ℤ) := by
    rw [D.roleLabelData.anchor_count, D.roleLabelData.local_count,
      D.encoded_labelledRoleCount_anchor, D.encoded_labelledRoleCount_local]
  exact_mod_cast h

theorem outsideTableItems_card_lt_lossAllowance {b c : ℕ}
    (hk : D.k ≤ D.graph.n) (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) :
    (p.outsideTableItems D.encodedSubclass).card < lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    p.outsideTableItems_card_lt D.encodedSubclass D.encodedLabel D.encodedCoordinate
      D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)

theorem badAnchorsAt_card_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex) :
    (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel v).card ≤
      3 * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.badAnchorsAt_card_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count v

theorem anchor_subset_loss_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (v : D.Vertex)
    (s : Finset D.packingInstance.Item)
    (hs : s ⊆ Coverage.anchorItemsAt D.encodedSubclass D.encodedLabel v) :
    (s \ Coverage.roleItems p D.encodedSubclass
      (Coverage.goodTuplesAt p D.encodedSubclass D.encodedLabel v) .anchor).card ≤
      3 * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.anchor_subset_loss_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count v s hs

theorem badAnchors_global_card_le {b c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) :
    ((Finset.univ : Finset D.Vertex).biUnion
      (Coverage.badAnchorsAt p D.encodedSubclass D.encodedLabel)).card ≤
      3 * D.graph.n * lossAllowance c := by
  simpa only [lossAllowance, primaryScoreBound, primaryBound] using
    Coverage.badAnchors_global_card_le p D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six D.B c
      (D.packingInstance_n hk) hb (D.encoded_primaryScore_sum_eq_zero hk)
      D.roleLabelData_anchor_row_count D.roleLabelData_anchor_local_count

end InventoryData
end BinPackingGap

namespace BinPackingGap.InventoryData

open scoped BigOperators

variable (D : InventoryData)

def taggedItem (r : Role) : D.RoleCopies r ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk r).trans D.itemEquiv.toEmbedding

@[simp] theorem taggedItem_apply (r : Role) (c : D.RoleCopies r) :
    D.taggedItem r c = D.itemEquiv ⟨r, c⟩ := rfl

def globalCopyEmbedding (s : GlobalSpecies D.graph) :
    Fin (D.globalStock s) ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk s).trans (D.taggedItem .«global»)

def flagCopyEmbedding (s : FlagSpecies) :
    Fin (D.flagStock s) ↪ D.packingInstance.Item :=
  (Function.Embedding.sigmaMk s).trans (D.taggedItem .flag)

@[simp] theorem globalCopyEmbedding_apply (s : GlobalSpecies D.graph)
    (j : Fin (D.globalStock s)) :
    D.globalCopyEmbedding s j = D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ := rfl

@[simp] theorem flagCopyEmbedding_apply (s : FlagSpecies) (j : Fin (D.flagStock s)) :
    D.flagCopyEmbedding s j = D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ := rfl

def physicalGlobalPool (s : GlobalSpecies D.graph) : Finset D.packingInstance.Item :=
  Finset.univ.map (D.globalCopyEmbedding s)

def physicalFlagPool (s : FlagSpecies) : Finset D.packingInstance.Item :=
  Finset.univ.map (D.flagCopyEmbedding s)

def labeledItems : Finset D.packingInstance.Item :=
  Finset.univ.filter (fun i =>
    (D.itemEquiv.symm i).1 = .x ∨ (D.itemEquiv.symm i).1 = .anchor ∨
      (D.itemEquiv.symm i).1 = .«local»)

@[simp] theorem card_physicalGlobalPool (s : GlobalSpecies D.graph) :
    (D.physicalGlobalPool s).card = D.globalStock s := by
  simp [physicalGlobalPool]

@[simp] theorem card_physicalFlagPool (s : FlagSpecies) :
    (D.physicalFlagPool s).card = D.flagStock s := by
  simp [physicalFlagPool]

theorem physicalGlobalPool_nonempty_iff (s : GlobalSpecies D.graph) :
    (D.physicalGlobalPool s).Nonempty ↔ 0 < D.globalStock s := by
  rw [← Finset.card_pos, card_physicalGlobalPool]

theorem physicalFlagPool_nonempty_iff (s : FlagSpecies) :
    (D.physicalFlagPool s).Nonempty ↔ 0 < D.flagStock s := by
  rw [← Finset.card_pos, card_physicalFlagPool]

theorem mem_physicalGlobalPool (s : GlobalSpecies D.graph) (i : D.packingInstance.Item) :
    i ∈ D.physicalGlobalPool s ↔
      ∃ j : Fin (D.globalStock s), D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ = i := by
  simp only [physicalGlobalPool, Finset.mem_map, Finset.mem_univ, true_and,
    globalCopyEmbedding_apply]

theorem mem_physicalFlagPool (s : FlagSpecies) (i : D.packingInstance.Item) :
    i ∈ D.physicalFlagPool s ↔
      ∃ j : Fin (D.flagStock s), D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ = i := by
  simp only [physicalFlagPool, Finset.mem_map, Finset.mem_univ, true_and,
    flagCopyEmbedding_apply]

theorem itemEquiv_mem_physicalGlobalPool_iff (a : D.Item) (s : GlobalSpecies D.graph) :
    D.itemEquiv a ∈ D.physicalGlobalPool s ↔
      ∃ j : Fin (D.globalStock s), a = ⟨.«global», ⟨s, j⟩⟩ := by
  rw [mem_physicalGlobalPool]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (D.itemEquiv.injective hj).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

theorem itemEquiv_mem_physicalFlagPool_iff (a : D.Item) (s : FlagSpecies) :
    D.itemEquiv a ∈ D.physicalFlagPool s ↔
      ∃ j : Fin (D.flagStock s), a = ⟨.flag, ⟨s, j⟩⟩ := by
  rw [mem_physicalFlagPool]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (D.itemEquiv.injective hj).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j, rfl⟩

@[simp] theorem mem_labeledItems (i : D.packingInstance.Item) :
    i ∈ D.labeledItems ↔
      (D.itemEquiv.symm i).1 = .x ∨ (D.itemEquiv.symm i).1 = .anchor ∨
        (D.itemEquiv.symm i).1 = .«local» := by
  simp [labeledItems]

@[simp] theorem itemEquiv_mem_labeledItems (r : Role) (c : D.RoleCopies r) :
    D.itemEquiv ⟨r, c⟩ ∈ D.labeledItems ↔
      r = .x ∨ r = .anchor ∨ r = .«local» := by
  simp only [mem_labeledItems, Equiv.symm_apply_apply]

@[simp] theorem globalItem_mem_physicalGlobalPool (s t : GlobalSpecies D.graph)
    (j : Fin (D.globalStock s)) :
    D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ ∈ D.physicalGlobalPool t ↔ s = t := by
  rw [itemEquiv_mem_physicalGlobalPool_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hcopy : (⟨s, j⟩ : D.GlobalCopy) = ⟨t, q⟩ :=
      sigma_mk_injective (β := D.RoleCopies) (i := Role.«global») hq
    exact congrArg Sigma.fst hcopy
  · intro h
    subst t
    exact ⟨j, rfl⟩

@[simp] theorem flagItem_mem_physicalFlagPool (s t : FlagSpecies)
    (j : Fin (D.flagStock s)) :
    D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ ∈ D.physicalFlagPool t ↔ s = t := by
  rw [itemEquiv_mem_physicalFlagPool_iff]
  constructor
  · rintro ⟨q, hq⟩
    have hcopy : (⟨s, j⟩ : D.FlagCopy) = ⟨t, q⟩ :=
      sigma_mk_injective (β := D.RoleCopies) (i := Role.flag) hq
    exact congrArg Sigma.fst hcopy
  · intro h
    subst t
    exact ⟨j, rfl⟩

theorem role_eq_global_of_mem_physicalGlobalPool (s : GlobalSpecies D.graph)
    {i : D.packingInstance.Item} (hi : i ∈ D.physicalGlobalPool s) :
    (D.itemEquiv.symm i).1 = .«global» := by
  obtain ⟨j, rfl⟩ := (D.mem_physicalGlobalPool s i).mp hi
  simp only [Equiv.symm_apply_apply]

theorem role_eq_flag_of_mem_physicalFlagPool (s : FlagSpecies)
    {i : D.packingInstance.Item} (hi : i ∈ D.physicalFlagPool s) :
    (D.itemEquiv.symm i).1 = .flag := by
  obtain ⟨j, rfl⟩ := (D.mem_physicalFlagPool s i).mp hi
  simp only [Equiv.symm_apply_apply]

theorem physicalGlobalPool_disjoint {s t : GlobalSpecies D.graph} (hst : s ≠ t) :
    Disjoint (D.physicalGlobalPool s) (D.physicalGlobalPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  obtain ⟨j, rfl⟩ := (D.mem_physicalGlobalPool s i).mp hi
  exact hst ((D.globalItem_mem_physicalGlobalPool s t j).mp ht)

theorem physicalFlagPool_disjoint {s t : FlagSpecies} (hst : s ≠ t) :
    Disjoint (D.physicalFlagPool s) (D.physicalFlagPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  obtain ⟨j, rfl⟩ := (D.mem_physicalFlagPool s i).mp hi
  exact hst ((D.flagItem_mem_physicalFlagPool s t j).mp ht)

theorem physicalGlobalPool_disjoint_physicalFlagPool
    (s : GlobalSpecies D.graph) (t : FlagSpecies) :
    Disjoint (D.physicalGlobalPool s) (D.physicalFlagPool t) := by
  apply Finset.disjoint_left.mpr
  intro i hi ht
  have h := (D.role_eq_global_of_mem_physicalGlobalPool s hi).symm.trans
    (D.role_eq_flag_of_mem_physicalFlagPool t ht)
  cases h

theorem labeledItems_disjoint_physicalGlobalPool (s : GlobalSpecies D.graph) :
    Disjoint D.labeledItems (D.physicalGlobalPool s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hg
  have hr := D.role_eq_global_of_mem_physicalGlobalPool s hg
  have hl := (D.mem_labeledItems i).mp hi
  simp [hr] at hl

theorem labeledItems_disjoint_physicalFlagPool (s : FlagSpecies) :
    Disjoint D.labeledItems (D.physicalFlagPool s) := by
  apply Finset.disjoint_left.mpr
  intro i hi hf
  have hr := D.role_eq_flag_of_mem_physicalFlagPool s hf
  have hl := (D.mem_labeledItems i).mp hi
  simp [hr] at hl

private theorem not_mem_physicalGlobalPool_of_role_ne (r : Role) (c : D.RoleCopies r)
    (s : GlobalSpecies D.graph) (hr : r ≠ .«global») :
    D.itemEquiv ⟨r, c⟩ ∉ D.physicalGlobalPool s := by
  intro hi
  have h := D.role_eq_global_of_mem_physicalGlobalPool s hi
  exact hr (by simpa only [Equiv.symm_apply_apply] using h)

private theorem not_mem_physicalFlagPool_of_role_ne (r : Role) (c : D.RoleCopies r)
    (s : FlagSpecies) (hr : r ≠ .flag) :
    D.itemEquiv ⟨r, c⟩ ∉ D.physicalFlagPool s := by
  intro hi
  have h := D.role_eq_flag_of_mem_physicalFlagPool s hi
  exact hr (by simpa only [Equiv.symm_apply_apply] using h)

theorem physicalInventory_indicator_partition (i : D.packingInstance.Item) :
    (if i ∈ D.labeledItems then (1 : ℝ) else 0) +
      (∑ s, if i ∈ D.physicalGlobalPool s then (1 : ℝ) else 0) +
      (∑ s, if i ∈ D.physicalFlagPool s then (1 : ℝ) else 0) = 1 := by
  classical
  obtain ⟨⟨r, c⟩, rfl⟩ := D.itemEquiv.surjective i
  cases r with
  | x =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | anchor =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | «global» =>
    rcases c with ⟨s, j⟩
    have hflag : ∀ t : FlagSpecies,
        D.itemEquiv ⟨.«global», ⟨s, j⟩⟩ ∉ D.physicalFlagPool t := fun t =>
      not_mem_physicalFlagPool_of_role_ne D .«global» ⟨s, j⟩ t (by decide)
    simp [hflag]
  | «local» =>
    simp [not_mem_physicalGlobalPool_of_role_ne, not_mem_physicalFlagPool_of_role_ne]
  | flag =>
    rcases c with ⟨s, j⟩
    have hglobal : ∀ t : GlobalSpecies D.graph,
        D.itemEquiv ⟨.flag, ⟨s, j⟩⟩ ∉ D.physicalGlobalPool t := fun t =>
      not_mem_physicalGlobalPool_of_role_ne D .flag ⟨s, j⟩ t (by decide)
    simp [hglobal]

end BinPackingGap.InventoryData

namespace BinPackingGap
namespace InventoryData

variable (D : InventoryData) {b : ℕ}

def rowPrefixExports (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.exports D.roleLabelData.anchor D.roleLabelData.row
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .x) h

def localPrefixExports (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.exports D.roleLabelData.anchor D.roleLabelData.localLabel
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .«local») h

def outsideAnchorPrefix (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.prefixOutside D.roleLabelData.anchor
    (p.roleItemAt D.encodedSubclass .anchor) h

def outsideRowPrefix (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.prefixOutside D.roleLabelData.row
    (p.roleItemAt D.encodedSubclass .x) h

def outsideLocalPrefix (p : Packing D.packingInstance b) (h : ℕ) :=
  LabelConservation.prefixOutside D.roleLabelData.localLabel
    (p.roleItemAt D.encodedSubclass .«local») h

theorem rowPrefixExports_add_outsideRow_eq (p : Packing D.packingInstance b) (h : ℕ) :
    (D.rowPrefixExports p h).card + (D.outsideRowPrefix p h).card =
      (D.outsideAnchorPrefix p h).card := by
  apply LabelConservation.exports_add_outsideRole_eq_outsideAnchor
    D.roleLabelData.anchor D.roleLabelData.row
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .x)
    (p.roleItemAt_injective D.encodedSubclass .anchor)
    (p.roleItemAt_injective D.encodedSubclass .x)
  · intro t
    exact (p.roleItemAt_labels_le D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six t).1
  · exact D.roleLabelData_anchor_row_count

theorem localPrefixExports_add_outsideLocal_eq (p : Packing D.packingInstance b) (h : ℕ) :
    (D.localPrefixExports p h).card + (D.outsideLocalPrefix p h).card =
      (D.outsideAnchorPrefix p h).card := by
  apply LabelConservation.exports_add_outsideRole_eq_outsideAnchor
    D.roleLabelData.anchor D.roleLabelData.localLabel
    (p.roleItemAt D.encodedSubclass .anchor) (p.roleItemAt D.encodedSubclass .«local»)
    (p.roleItemAt_injective D.encodedSubclass .anchor)
    (p.roleItemAt_injective D.encodedSubclass .«local»)
  · intro t
    exact (p.roleItemAt_labels_le D.encodedSubclass D.encodedLabel D.roleLabelData
      D.encodedCoordinate D.packingInstance_size_eq D.encodedCoordinate_abs_le_six t).2
  · exact D.roleLabelData_anchor_local_count

theorem rowPrefixExports_eq_outside_sub (p : Packing D.packingInstance b) (h : ℕ) :
    ((D.rowPrefixExports p h).card : ℤ) =
      (D.outsideAnchorPrefix p h).card - (D.outsideRowPrefix p h).card := by
  have heq := D.rowPrefixExports_add_outsideRow_eq p h
  omega

theorem localPrefixExports_eq_outside_sub (p : Packing D.packingInstance b) (h : ℕ) :
    ((D.localPrefixExports p h).card : ℤ) =
      (D.outsideAnchorPrefix p h).card - (D.outsideLocalPrefix p h).card := by
  have heq := D.localPrefixExports_add_outsideLocal_eq p h
  omega

theorem rowPrefixExports_card_lt_lossAllowance {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (h : ℕ) :
    (D.rowPrefixExports p h).card < lossAllowance c := by
  have heq := D.rowPrefixExports_add_outsideRow_eq p h
  have hprefix : (D.outsideAnchorPrefix p h).card ≤
      (LabelConservation.outsideItems (p.roleItemAt D.encodedSubclass .anchor)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hout := (p.outside_roleItems_card_le D.encodedSubclass .anchor).trans_lt
    (D.outsideTableItems_card_lt_lossAllowance hk p hb)
  omega

theorem localPrefixExports_card_lt_lossAllowance {c : ℕ} (hk : D.k ≤ D.graph.n)
    (p : Packing D.packingInstance b) (hb : b ≤ D.B + c) (h : ℕ) :
    (D.localPrefixExports p h).card < lossAllowance c := by
  have heq := D.localPrefixExports_add_outsideLocal_eq p h
  have hprefix : (D.outsideAnchorPrefix p h).card ≤
      (LabelConservation.outsideItems (p.roleItemAt D.encodedSubclass .anchor)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  have hout := (p.outside_roleItems_card_le D.encodedSubclass .anchor).trans_lt
    (D.outsideTableItems_card_lt_lossAllowance hk p hb)
  omega

end InventoryData
end BinPackingGap

end

end OAI


