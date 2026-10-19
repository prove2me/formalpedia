-- Prove2me | Definitions.Def_OAIQWLLH000
-- name    : OAIQWLLH000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T02:45:22.340095+00:00
-- url     : https://prove2.me/theorems/93a54b74-5d30-4389-b1b7-4887b74ad7ac
-- title:
--   OpenAI linear list-Hadwiger split: definitions bundle
-- statement:
--   This is the definitions bundle for the split of OpenAI's proof of `OAI.LinearListHadwiger.main_theorem`. That theorem says $\chi_{\mathrm{list}}(G) \le C\,h(G)$ for every finite nonempty graph, with an absolute constant $C$. This is the Linear List Hadwiger conjecture.
--
--   The bundle holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/ListHadwiger`, ported to Lean 4.33.1 and Mathlib 0df444a. The source is OpenAI, *A linear list-coloring bound in terms of the Hadwiger number*, OpenAI Math Release, September 23, 2026, result family 157, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0.
--
--   The definitions include:
--   - fractional colourings and the fractional chromatic number (`Stable`, `Cover`, `number`, `Dual`);
--   - the Reed–Seymour notions (`CliqueBound`, `Independent`, `mass`, egg covers);
--   - $k$-connectivity on a vertex set (`KConnectedOn`) and degeneracy on a vertex set (`DegenerateOn`);
--   - the fractional obstruction (`FractionalObstruction`);
--   - the list chromatic number of an induced subgraph (`ell`);
--   - routings, weavings, districts and stage histories;
--   - the sampling constructions and the explicit constants.
--
--   It also holds the lemmas these definitions use in their bodies, and OpenAI's `@[simp]` lemmas about them.
--
--   The definitions of the published statement (list colourings, `listChromaticNumber`, `HasCliqueMinor`, `hadwigerNumber`) are not repeated. The bundle imports them from the published bundle `Def_ListHadwiger`, and imports no other bundle.
-- source:
--   OpenAI, A linear list-coloring bound in terms of the Hadwiger number, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 157; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-linear-list-coloring-bound-in-terms-of-the-Hadwiger-number-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/ListHadwiger at commit adc7f12

import Mathlib
import Definitions.Def_ListHadwiger

section
-- module Solutions.OAIQW_ListHadwiger.Compat
namespace OAI
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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
end OAICompat434


end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

def KConnectedOn {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S : Finset V) (k : ℕ) : Prop :=
  k < S.card ∧ ∀ Z ⊆ S, Z.card < k → (G.induce (↑(S \ Z) : Set V)).Connected

structure SeparatorSplit {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (S V₁ Z V₂ : Finset V) : Prop where
  union_eq : V₁ ∪ Z ∪ V₂ = S
  left_sep : Disjoint V₁ Z
  left_right : Disjoint V₁ V₂
  sep_right : Disjoint Z V₂
  left_nonempty : V₁.Nonempty
  right_nonempty : V₂.Nonempty
  anticomplete : ∀ v ∈ V₁, ∀ w ∈ V₂, ¬G.Adj v w

def ProperOn {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (c : V → Color) : Prop :=
  ∀ ⦃v⦄, v ∈ S → ∀ ⦃w⦄, w ∈ S → G.Adj v w → c v ≠ c w

def ValidOn {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) : Prop :=
  (∀ v ∈ S, c v ∈ L v) ∧ ProperOn G S c

def vertexCost {V Color : Type} [DecidableEq V] (k : ℕ)
    (A : Finset V) (B : V → Finset Color) (v : V) : ℕ :=
  if v ∈ A then k else (B v).card

def constraintCost {V Color : Type} [DecidableEq V] (S : Finset V)
    (k : ℕ) (A : Finset V) (B : V → Finset Color) : ℕ :=
  ∑ v ∈ S, vertexCost k A B v

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Separators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

noncomputable def extraForbidden {V Color : Type} [DecidableEq V]
    (Z : Finset V) (B : V → Finset Color) (F : Finset Color) : V → Finset Color := by
  classical
  exact fun v => if v ∈ Z then B v ∪ F else B v

noncomputable def neighborPairs {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (X : Finset V) (v : V) : Finset (Sym2 V) := by
  classical
  exact (X.filter (G.Adj v)).offDiag.image Sym2.mk.uncurry

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Connectivity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

open scoped Classical

def DegenerateOn {V : Type} (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Prop :=
  ∀ T ⊆ S, T.Nonempty → ∃ v ∈ T, (T.filter (G.Adj v)).card ≤ d

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Palette
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open scoped Classical

namespace PaletteReservation

noncomputable def weight {α : Type} [Fintype α] (p : ℝ) (σ : α → Bool) : ℝ :=
  ∏ a, if σ a then p else 1 - p

noncomputable def count {α : Type} (X : Finset α) (σ : α → Bool) : ℕ :=
  (X.filter fun a => σ a = true).card

end PaletteReservation

noncomputable def prune {V Color : Type} (G : SimpleGraph V) (S : Finset V)
    (L : V → Finset Color) (c : V → Color) (v : V) : Finset Color :=
  L v \ (S.filter (G.Adj v)).image c

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.PathPacking
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.PathPacking

open SimpleGraph

def AvoidingConnection {V : Type} (G : SimpleGraph V) (A B X : Finset V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∃ p : G.Walk a b, ∀ v ∈ p.support, v ∉ X

section Orbits
variable {V : Type} [Fintype V] [DecidableEq V]
variable (A B : Finset V) (f : {v // v ∉ B} → {v // v ∉ A})

noncomputable def next (v : V) : V := if h : v ∈ B then v else (f ⟨v, h⟩).val

end Orbits

structure FullPacking {V : Type} (G : SimpleGraph V) (A B : Finset V) where
  target : ↥A → ↥B
  route : ∀ a : ↥A, G.Path a.val (target a).val
  disjoint : ∀ a b : ↥A, a ≠ b →
    Disjoint {v | v ∈ (route a).val.support} {v | v ∈ (route b).val.support}
  source_only : ∀ a : ↥A, ∀ v ∈ (route a).val.support, v ∈ A → v = a.val
  target_only : ∀ a : ↥A, ∀ v ∈ (route a).val.support, v ∈ B → v = (target a).val

end LinearListHadwiger.PathPacking

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Routing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

open SimpleGraph PathPacking

noncomputable def deletedFibers {V W : Type} [Fintype V] (π : W → V) (X : Finset W) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v => ∀ w, π w = v → w ∈ X

namespace PathPacking
lemma FullPacking.target_injective {V : Type} {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) : Function.Injective P.target := by
  intro a b hab
  by_contra hn
  have hh := Set.disjoint_left.mp (P.disjoint a b hn)
  apply hh (show (P.target a).val ∈ (P.route a).val.support by simp)
  simpa only [hab, Set.mem_ofPred_eq] using
    (show (P.target b).val ∈ (P.route b).val.support by simp)
end PathPacking

structure DoublePacking {V : Type} (G : SimpleGraph V) (A B : Finset V) where
  target : (↥A × Bool) → ↥B
  target_injective : Function.Injective target
  route : ∀ i : ↥A × Bool, G.Path i.1.val (target i).val
  source_only : ∀ i, ∀ v ∈ (route i).val.support, v ∈ A → v = i.1.val
  target_only : ∀ i, ∀ v ∈ (route i).val.support, v ∈ B → v = (target i).val
  overlap : ∀ i j, i ≠ j → ∀ v ∈ (route i).val.support,
    v ∈ (route j).val.support → v = i.1.val ∧ v = j.1.val

structure MinorModel {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W) where
  branch : W → Set V
  connected : ∀ w, (G.induce (branch w)).Connected
  disjoint : ∀ u v, u ≠ v → Disjoint (branch u) (branch v)
  adjacent : ∀ ⦃u v⦄, H.Adj u v → ∃ x ∈ branch u, ∃ y ∈ branch v, G.Adj x y

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.MinorModels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking

namespace MinorModel
variable {V W : Type} {G : SimpleGraph V} {H : SimpleGraph W}

def expand (M : MinorModel G H) (S : Set W) : Set V :=
  {v | ∃ w ∈ S, v ∈ M.branch w}

lemma branch_subset_expand (M : MinorModel G H) {S : Set W} {w : W} (hw : w ∈ S) :
    M.branch w ⊆ M.expand S := fun _ hv => ⟨w, hw, hv⟩

lemma expand_connected (M : MinorModel G H) {S : Set W}
    (hS : (H.induce S).Connected) : (G.induce (M.expand S)).Connected := by
  have hsame (w : S) (a b : M.branch w.val) :
      (G.induce (M.expand S)).Reachable
        ⟨a.val, M.branch_subset_expand w.property a.property⟩
        ⟨b.val, M.branch_subset_expand w.property b.property⟩ :=
    ((M.connected w.val).preconnected a b).map
      (G.induceHomOfLE (M.branch_subset_expand w.property)).toHom
  have hwalk : ∀ {u v : S} (p : (H.induce S).Walk u v)
      (a : M.branch u.val) (b : M.branch v.val),
      (G.induce (M.expand S)).Reachable
        ⟨a.val, M.branch_subset_expand u.property a.property⟩
        ⟨b.val, M.branch_subset_expand v.property b.property⟩ := by
    intro u v p
    induction p with
    | nil => exact hsame _
    | @cons u v z hadj p ih =>
      intro a b
      obtain ⟨x, hx, y, hy, hxy⟩ := M.adjacent hadj
      have hxy' : (G.induce (M.expand S)).Adj
          ⟨x, M.branch_subset_expand u.property hx⟩
          ⟨y, M.branch_subset_expand v.property hy⟩ := hxy
      exact (hsame u a ⟨x, hx⟩).trans (hxy'.reachable.trans (ih ⟨y, hy⟩ b))
  refine { preconnected := ?_, nonempty := ?_ }
  · intro a b
    obtain ⟨u, hu, hau⟩ := a.property
    obtain ⟨v, hv, hbv⟩ := b.property
    obtain ⟨p⟩ := hS.preconnected ⟨u, hu⟩ ⟨v, hv⟩
    exact hwalk p ⟨a.val, hau⟩ ⟨b.val, hbv⟩
  · obtain ⟨w⟩ := hS.nonempty
    obtain ⟨v⟩ := (M.connected w.val).nonempty
    exact ⟨⟨v.val, M.branch_subset_expand w.property v.property⟩⟩

lemma expand_disjoint (M : MinorModel G H) {S T : Set W} (hST : Disjoint S T) :
    Disjoint (M.expand S) (M.expand T) := by
  apply Set.disjoint_left.mpr
  rintro v ⟨a, ha, hva⟩ ⟨b, hb, hvb⟩
  by_cases hab : a = b
  · exact Set.disjoint_left.mp hST ha (hab ▸ hb)
  · exact Set.disjoint_left.mp (M.disjoint a b hab) hva hvb

end MinorModel

structure BagRouting {V I J : Type} (G : SimpleGraph V) (s : I → V)
    (B : J → Set V) where
  paths : ∀ i, Σ v, G.Path (s i) v
  bag : I → J
  bag_injective : Function.Injective bag
  endpoint_mem : ∀ i, (paths i).1 ∈ B (bag i)
  overlap : ∀ i j, i ≠ j → ∀ v,
    v ∈ (paths i).2.val.support → v ∈ (paths j).2.val.support →
      v = s i ∧ v = s j

namespace BagRouting
variable {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

noncomputable def totalLength [Fintype I] (D : BagRouting G s B) : ℕ :=
  ∑ i, (D.paths i).2.val.length

noncomputable def truncate [DecidableEq V] [DecidableEq I]
    (D : BagRouting G s B) (i : I) (j : J) (hj : j ∉ Set.range D.bag)
    (v : V) (hv : v ∈ (D.paths i).2.val.support) (hB : v ∈ B j) :
    BagRouting G s B := by
  classical
  let p : G.Path (s i) v :=
    ⟨(D.paths i).2.val.takeUntil v hv, (D.paths i).2.property.takeUntil hv⟩
  let paths : ∀ a, Σ w, G.Path (s a) w :=
    fun a => if h : a = i then h.symm ▸ (⟨v, p⟩ : Σ w, G.Path (s i) w) else D.paths a
  let f : I → J := Function.update D.bag i j
  refine ⟨paths, f, ?_, ?_, ?_⟩
  · intro a b hab
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact ha.trans hb.symm
    · subst a
      have h : j = D.bag b := by simpa [f, Function.update, hb] using hab
      exact (hj ⟨b, h.symm⟩).elim
    · subst b
      have h : D.bag a = j := by simpa [f, Function.update, ha] using hab
      exact (hj ⟨a, h⟩).elim
    · exact D.bag_injective (by simpa [f, Function.update, ha, hb] using hab)
  · intro a
    by_cases ha : a = i
    · subst a; simpa [paths, f, p] using hB
    · simpa [paths, f, ha] using D.endpoint_mem a
  · intro a b hab w hwa hwb
    have hsub (z : I) : (paths z).2.val.support ⊆ (D.paths z).2.val.support := by
      by_cases hz : z = i
      · subst z
        have heq : paths i = ⟨v, p⟩ := dite_eq_left rfl
        rw [heq]
        exact (D.paths i).2.val.support_takeUntil_subset_support hv
      · have heq : paths z = D.paths z := dite_eq_right hz
        rw [heq]
        exact fun _ h => h
    exact D.overlap a b hab w (hsub a hwa) (hsub b hwb)

lemma truncate_length_lt [Fintype I] [DecidableEq V] [DecidableEq I]
    (D : BagRouting G s B) (hdis : ∀ a b, a ≠ b → Disjoint (B a) (B b))
    (i : I) (j : J) (hj : j ∉ Set.range D.bag)
    (v : V) (hv : v ∈ (D.paths i).2.val.support) (hB : v ∈ B j) :
    (D.truncate i j hj v hv hB).totalLength < D.totalLength := by
  classical
  have hne : v ≠ (D.paths i).1 := by
    intro heq
    have hx : j ≠ D.bag i := fun h => hj ⟨i, h.symm⟩
    exact Set.disjoint_left.mp (hdis j (D.bag i) hx) hB (heq ▸ D.endpoint_mem i)
  have hlt : ((D.paths i).2.val.takeUntil v hv).length < (D.paths i).2.val.length := by
    have hh := (D.paths i).2.val.length_takeUntil_le_length hv
    apply lt_of_le_of_ne hh
    intro heq
    have h := Walk.getVert_length_takeUntil hv
    rw [heq, Walk.getVert_length] at h
    exact hne h.symm
  have hi : (D.truncate i j hj v hv hB).paths i =
      ⟨v, ⟨(D.paths i).2.val.takeUntil v hv, (D.paths i).2.property.takeUntil hv⟩⟩ :=
    dite_eq_left rfl
  have ha : ∀ a, a ≠ i → (D.truncate i j hj v hv hB).paths a = D.paths a :=
    fun a h => dite_eq_right h
  apply Finset.sum_lt_sum
  · intro a _
    by_cases h : a = i
    · subst a
      rw [hi]
      exact hlt.le
    · rw [ha a h]
  · refine ⟨i, Finset.mem_univ _, ?_⟩
    rw [hi]
    exact hlt

end BagRouting

open scoped Classical

structure RootedCliqueModel {V I : Type} (G : SimpleGraph V) (roots : I → V) where
  branch : I → Set V
  connected : ∀ i, (G.induce (branch i)).Connected
  disjoint : ∀ i j, i ≠ j → Disjoint (branch i) (branch j)
  adjacent : ∀ i j, i ≠ j → ∃ x ∈ branch i, ∃ y ∈ branch j, G.Adj x y
  root_mem : ∀ i, roots i ∈ branch i

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.BagContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking
open scoped Classical

namespace BagContraction
variable {V J : Type} (G : SimpleGraph V) (B : J → Set V)

def Remnant : Set V := {v | ∀ j, v ∉ B j}
abbrev Vertex := ↥(Remnant B) ⊕ J

def branch : Vertex B → Set V
  | .inl v => {v.val}
  | .inr j => B j

def graph : SimpleGraph (Vertex B) where
  Adj u v := u ≠ v ∧ ∃ x ∈ branch B u, ∃ y ∈ branch B v, G.Adj x y
  symm := ⟨by
    rintro u v ⟨huv, x, hx, y, hy, hxy⟩
    exact ⟨huv.symm, y, hy, x, hx, hxy.symm⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

noncomputable instance instFintypeVertex [Fintype V] [Fintype J] : Fintype (Vertex B) := by
  classical
  exact Fintype.ofFinite _

lemma branch_disjoint (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j))
    (u v : Vertex B) (huv : u ≠ v) : Disjoint (branch B u) (branch B v) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  cases u with
  | inl u =>
    have hxu : x = u.val := hx
    cases v with
    | inl v => exact huv (congrArg Sum.inl (Subtype.ext (hxu.symm.trans hy)))
    | inr j => exact u.property j (hxu ▸ hy)
  | inr i =>
    cases v with
    | inl v => exact v.property i ((show x = v.val from hy) ▸ hx)
    | inr j => exact Set.disjoint_left.mp (hd i j (fun h => huv (h ▸ rfl))) hx hy

def model (hc : ∀ j, (G.induce (B j)).Connected)
    (hd : ∀ i j, i ≠ j → Disjoint (B i) (B j)) : MinorModel G (graph G B) where
  branch := branch B
  connected := by
    intro w
    cases w with
    | inl v =>
      change (G.induce {v.val}).Connected
      exact SimpleGraph.Connected.of_subsingleton
    | inr j => exact hc j
  disjoint := branch_disjoint B hd
  adjacent := by intro u v h; exact h.2

def liftSet (C : Set V) : Set (Vertex B) :=
  {w | match w with | .inl v => v.val ∈ C | .inr _ => False}

end BagContraction

namespace BagRouting
variable {V J : Type} {G : SimpleGraph V} {A : Finset V} {B : J → Set V}

def region (D : BagRouting G (fun i : ↥A × Bool => i.1.val) B)
    (i : ↥A × Bool) : Set V :=
  {v | v ∈ (D.paths i).2.val.support} ∪ B (D.bag i)

end BagRouting

def RootedCliqueModel.reindex {V I J : Type} {G : SimpleGraph V} {r : I → V}
    (M : RootedCliqueModel G r) (f : J → I) (hf : Function.Injective f) :
    RootedCliqueModel G (r ∘ f) where
  branch j := M.branch (f j)
  connected j := M.connected (f j)
  disjoint i j h := M.disjoint (f i) (f j) (fun hh => h (hf hh))
  adjacent i j h := M.adjacent (f i) (f j) (fun hh => h (hf hh))
  root_mem j := M.root_mem (f j)

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Exchanges
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph PathPacking
open scoped Classical

namespace BagRouting
variable {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

def used (D : BagRouting G s B) : Set V :=
  {v | ∃ i, v ∈ (D.paths i).2.val.support}

def Minimal [Fintype I] (D : BagRouting G s B) : Prop :=
  ∀ E : BagRouting G s B, D.totalLength ≤ E.totalLength

noncomputable def replace [DecidableEq I] (D : BagRouting G s B) (i : I)
    (p : G.Path (s i) (D.paths i).1)
    (hp : ∀ j, i ≠ j → ∀ v ∈ p.val.support,
      v ∈ (D.paths j).2.val.support → v = s i ∧ v = s j) : BagRouting G s B := by
  let paths : ∀ a, Σ w, G.Path (s a) w :=
    fun a => if h : a = i then h.symm ▸ (⟨(D.paths i).1, p⟩ : Σ w, G.Path (s i) w) else D.paths a
  refine ⟨paths, D.bag, D.bag_injective, ?_, ?_⟩
  · intro a
    by_cases ha : a = i
    · subst a
      have he : paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
      rw [he]
      exact D.endpoint_mem i
    · have he : paths a = D.paths a := dite_eq_right ha
      rw [he]
      exact D.endpoint_mem a
  · intro a b hab v hva hvb
    by_cases ha : a = i
    · subst a
      have he : paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
      have he' : paths b = D.paths b := dite_eq_right (Ne.symm hab)
      rw [he] at hva
      rw [he'] at hvb
      exact hp b hab v hva hvb
    · have he : paths a = D.paths a := dite_eq_right ha
      rw [he] at hva
      by_cases hb : b = i
      · subst b
        have he' : paths i = ⟨(D.paths i).1, p⟩ := dite_eq_left rfl
        rw [he'] at hvb
        exact (hp a (Ne.symm ha) v hvb hva).symm
      · have he' : paths b = D.paths b := dite_eq_right hb
        rw [he'] at hvb
        exact D.overlap a b hab v hva hvb

noncomputable def usedFinset [Fintype I] [DecidableEq V] (D : BagRouting G s B) : Finset V :=
  Finset.univ.biUnion fun i => (D.paths i).2.val.support.toFinset

lemma mem_take_indices {u w : V} (p : G.Walk u w) (a : ℕ) {v : V}
    (hv : v ∈ (p.take a).support) :
    ∃ n, n ≤ a ∧ n ≤ p.length ∧ p.getVert n = v := by
  obtain ⟨n, hn, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  rw [Walk.take_length] at hlen
  have hna := (Nat.le_min.mp hlen).1
  have hnl := (Nat.le_min.mp hlen).2
  rw [Walk.take_getVert, Nat.min_eq_right hna] at hn
  exact ⟨n, hna, hnl, hn⟩

lemma mem_drop_indices {u w : V} (p : G.Walk u w) (b : ℕ) (hb : b ≤ p.length)
    {v : V} (hv : v ∈ (p.drop b).support) :
    ∃ n, b ≤ n ∧ n ≤ p.length ∧ p.getVert n = v := by
  obtain ⟨n, hn, hlen⟩ := Walk.mem_support_iff_exists_getVert.mp hv
  rw [Walk.drop_length] at hlen
  rw [Walk.drop_getVert] at hn
  exact ⟨b + n, by omega, by omega, hn⟩

lemma take_drop_disjoint {u w : V} (p : G.Path u w) (a b : ℕ)
    (hab : a < b) (hb : b ≤ p.val.length) :
    Disjoint {v | v ∈ (p.val.take a).support} {v | v ∈ (p.val.drop b).support} := by
  rw [Set.disjoint_left]
  intro v hv ht
  obtain ⟨c, hca, hcl, hc⟩ := mem_take_indices p.val a hv
  obtain ⟨d, hbd, hdl, hd⟩ := mem_drop_indices p.val b hb ht
  have he := p.property.getVert_injOn hcl hdl (hc.trans hd.symm)
  omega

lemma source_not_mem_drop {u w : V} (p : G.Path u w) (b : ℕ)
    (hpos : 0 < b) (hb : b ≤ p.val.length) : u ∉ (p.val.drop b).support := by
  intro hu
  obtain ⟨n, hbn, hnl, hn⟩ := mem_drop_indices p.val b hb hu
  have h0 : p.val.getVert 0 = u := p.val.getVert_zero
  have he := p.property.getVert_injOn (show 0 ≤ p.val.length by omega) hnl (h0.trans hn.symm)
  omega

structure Exchange (D : BagRouting G s B) where
  active : Finset I
  e : Equiv.Perm I
  fixed : ∀ i, i ∉ active → e i = i
  stable : ∀ i, i ∈ active ↔ e i ∈ active
  a : I → ℕ
  b : I → ℕ
  bounds : ∀ i ∈ active, a i + 2 ≤ b i ∧ b i ≤ (D.paths i).2.val.length
  edge : ∀ i ∈ active,
    G.Adj ((D.paths i).2.val.getVert (a i)) ((D.paths (e i)).2.val.getVert (b (e i)))

namespace Exchange
variable [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}

noncomputable def front (E : D.Exchange) (i : I) : Set V :=
  if i ∈ E.active then {v | v ∈ ((D.paths i).2.val.take (E.a i)).support}
  else {v | v ∈ (D.paths i).2.val.support}

noncomputable def tail (E : D.Exchange) (i : I) : Set V :=
  if i ∈ E.active then {v | v ∈ ((D.paths i).2.val.drop (E.b i)).support} else ∅

lemma front_subset {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : E.front i ⊆ {v | v ∈ (D.paths i).2.val.support} := by
  intro v hv
  by_cases hi : i ∈ E.active
  · rw [front, ite_eq_left hi] at hv
    rw [Walk.support_take] at hv
    exact List.mem_of_mem_take hv
  · simpa [front, hi] using hv

lemma tail_subset {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : E.tail i ⊆ {v | v ∈ (D.paths i).2.val.support} := by
  intro v hv
  by_cases hi : i ∈ E.active
  · rw [tail, ite_eq_left hi] at hv
    rw [Walk.drop_support_eq_support_drop_min] at hv
    exact List.mem_of_mem_drop hv
  · simp [tail, hi] at hv

lemma not_source_tail {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : s i ∉ E.tail i := by
  by_cases hi : i ∈ E.active
  · rw [tail, ite_eq_left hi]
    exact source_not_mem_drop _ _ (by have := (E.bounds i hi).1; omega) (E.bounds i hi).2
  · simp [tail, hi]

lemma front_tail_disjoint {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) : Disjoint (E.front i) (E.tail i) := by
  by_cases hi : i ∈ E.active
  · rw [front, tail, ite_eq_left hi, ite_eq_left hi]
    exact take_drop_disjoint _ _ _ (by have := (E.bounds i hi).1; omega) (E.bounds i hi).2
  · simp [tail, hi]

noncomputable def walk (E : D.Exchange) (i : I) (hi : i ∈ E.active) :
    G.Walk (s i) (D.paths (E.e i)).1 :=
  (((D.paths i).2.val.take (E.a i)).concat (E.edge i hi)).append
    ((D.paths (E.e i)).2.val.drop (E.b (E.e i)))

lemma walk_support {V I J : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}
    [DecidableEq V] [DecidableEq I] {D : BagRouting G s B}
    (E : D.Exchange) (i : I) (hi : i ∈ E.active) {v : V}
    (hv : v ∈ (E.walk i hi).support) : v ∈ E.front i ∪ E.tail (E.e i) := by
  have hei := (E.stable i).mp hi
  rw [front, tail, ite_eq_left hi, ite_eq_left hei]
  simp only [walk, Walk.mem_support_append_iff, Walk.support_concat, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with (hv | hv) | hv
  · exact Or.inl hv
  · subst v
    exact Or.inr (Walk.start_mem_support _)
  · exact Or.inr hv

lemma support_overlap (E : D.Exchange) (i j : I) (hij : i ≠ j) (v : V)
    (hi : v ∈ E.front i ∪ E.tail (E.e i))
    (hj : v ∈ E.front j ∪ E.tail (E.e j)) : v = s i ∧ v = s j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact D.overlap i j hij v (E.front_subset i hi) (E.front_subset j hj)
  · by_cases he : i = E.e j
    · subst i
      exact (Set.disjoint_left.mp (E.front_tail_disjoint _) hi hj).elim
    · have h := D.overlap i (E.e j) he v (E.front_subset i hi) (E.tail_subset _ hj)
      exact (E.not_source_tail _ (h.2 ▸ hj)).elim
  · by_cases he : j = E.e i
    · subst j
      exact (Set.disjoint_left.mp (E.front_tail_disjoint _) hj hi).elim
    · have h := D.overlap j (E.e i) he v (E.front_subset j hj) (E.tail_subset _ hi)
      exact (E.not_source_tail _ (h.2 ▸ hi)).elim
  · have he : E.e i ≠ E.e j := fun h => hij (E.e.injective h)
    have h := D.overlap _ _ he v (E.tail_subset _ hi) (E.tail_subset _ hj)
    exact (E.not_source_tail _ (h.1 ▸ hi)).elim

noncomputable def routing (E : D.Exchange) : BagRouting G s B := by
  let paths : ∀ i, Σ v, G.Path (s i) v := fun i =>
    if hi : i ∈ E.active then ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ else D.paths i
  refine ⟨paths, D.bag ∘ E.e, D.bag_injective.comp E.e.injective, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ E.active
    · have he : paths i = ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ := dite_eq_left hi
      rw [he]
      exact D.endpoint_mem _
    · have he : paths i = D.paths i := dite_eq_right hi
      rw [he]
      simpa [E.fixed i hi] using D.endpoint_mem i
  · intro i j hij v hvi hvj
    apply E.support_overlap i j hij v
    · by_cases hi : i ∈ E.active
      · have he : paths i = ⟨(D.paths (E.e i)).1, (E.walk i hi).toPath⟩ := dite_eq_left hi
        rw [he] at hvi
        exact E.walk_support i hi ((E.walk i hi).support_toPath_subset_support hvi)
      · have he : paths i = D.paths i := dite_eq_right hi
        rw [he] at hvi
        exact Or.inl (by simpa [front, hi] using hvi)
    · by_cases hj : j ∈ E.active
      · have he : paths j = ⟨(D.paths (E.e j)).1, (E.walk j hj).toPath⟩ := dite_eq_left hj
        rw [he] at hvj
        exact E.walk_support j hj ((E.walk j hj).support_toPath_subset_support hvj)
      · have he : paths j = D.paths j := dite_eq_right hj
        rw [he] at hvj
        exact Or.inl (by simpa [front, hj] using hvj)

end Exchange

end BagRouting

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Concentration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.FiniteConcentration
open scoped BigOperators

noncomputable def mean {α : Type} [Fintype α] (w f : α → ℝ) : ℝ := ∑ a, w a * f a

noncomputable def mass {α : Type} [Fintype α] {n : ℕ}
    (w : Fin n → α → ℝ) (x : Fin n → α) : ℝ := ∏ i, w i (x i)

def BoundedChanges {α : Type} {n : ℕ} (f : (Fin n → α) → ℝ) (b : ℝ) : Prop :=
  ∀ i x y, (∀ j, j ≠ i → x j = y j) → |f x - f y| ≤ b

noncomputable def probability {α : Type} [Fintype α] (w : α → ℝ) (p : α → Prop) : ℝ := by
  classical
  exact ∑ a, if p a then w a else 0

end LinearListHadwiger.FiniteConcentration

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.ConnectivityTests
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

namespace ConnectivityTests

open SimpleGraph

variable {V : Type} [Fintype V] [DecidableEq V]

def IsCutMatching (G : SimpleGraph V) (B : Finset V) (E : Finset (V × V)) : Prop :=
  (∀ e ∈ E, e.1 ∈ B ∧ e.2 ∉ B ∧ G.Adj e.1 e.2) ∧
  (E : Set (V × V)).Pairwise (fun e f => e.1 ≠ f.1 ∧ e.2 ≠ f.2)

def endpoints (E : Finset (V × V)) : Finset V :=
  E.image Prod.fst ∪ E.image Prod.snd

def smallSets (s : ℕ) : Finset (Finset V) :=
  (Finset.range (s + 1)).biUnion fun i => Finset.univ.powersetCard i

noncomputable def neighborhoodUnion (G : SimpleGraph V) (R : Finset V) : Finset V :=
  by classical exact Finset.univ.filter fun v => ∃ r ∈ R, G.Adj r v

end ConnectivityTests

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.DistrictPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger

open SimpleGraph

structure WeavingWithin {V : Type} (G : SimpleGraph V) (J : Set V)
    {a p : ℕ} (roots : Fin a → V) (x y : Fin p → V) where
  model : RootedCliqueModel G roots
  branch_subset : ∀ j, model.branch j ⊆ J
  paths : ∀ i, G.Path (x i) (y i)
  path_subset : ∀ i v, v ∈ (paths i).val.support → v ∈ J
  disjoint : ∀ i j, i ≠ j → Disjoint
    {v | v ∈ (paths i).val.support} {v | v ∈ (paths j).val.support}
  clean : ∀ i j v, v ∈ (paths i).val.support → v ∈ model.branch j →
    v ∈ Set.range roots ∧ (v = x i ∨ v = y i)

def WovenOn {V : Type} (G : SimpleGraph V) (J : Set V) (a b : ℕ) : Prop :=
  ∀ (roots : Fin a → V), Function.Injective roots → (∀ i, roots i ∈ J) →
    ∀ p ≤ b, ∀ x y : Fin p → V,
      (∀ i, x i ∈ J ∧ y i ∈ J) →
      (∀ i j, i ≠ j → Disjoint ({x i, y i} : Set V) {x j, y j}) →
      Nonempty (WeavingWithin G J roots x y)

def Woven {V : Type} (G : SimpleGraph V) (a b : ℕ) : Prop :=
  WovenOn G Set.univ a b

structure DistrictVisits {V : Type} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (J : Set V) where
  entry : V
  exit : V
  entry_mem : entry ∈ J
  exit_mem : exit ∈ J
  initial : G.Walk u entry
  terminal : G.Walk exit v
  initial_part : ∃ q : G.Walk entry v, p = initial.append q
  terminal_part : ∃ q : G.Walk u exit, p = q.append terminal
  first : ∀ z, z ∈ initial.support → z ∈ J → z = entry
  last : ∀ z, z ∈ terminal.support → z ∈ J → z = exit

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Density
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger
open SimpleGraph

namespace Density
variable {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def darts (S : Finset V) : Finset (V × V) :=
  (S ×ˢ S).filter (fun e => G.Adj e.1 e.2)

def neighbors (S : Finset V) (v : V) : Finset V := S.filter (G.Adj v)

@[simp] lemma mem_darts {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {e : V × V} :
    e ∈ darts G S ↔ e.1 ∈ S ∧ e.2 ∈ S ∧ G.Adj e.1 e.2 := by
  simp [darts, and_assoc]

@[simp] lemma mem_neighbors {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V} {v w : V} :
    w ∈ neighbors G S v ↔ w ∈ S ∧ G.Adj v w := by simp [neighbors]

lemma darts_mono {S T : Finset V} (h : S ⊆ T) : darts G S ⊆ darts G T := by
  intro e he
  obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp he
  exact (mem_darts G).mpr ⟨h hx,h hy,ha⟩

lemma darts_erase {S : Finset V} {v : V} (hv : v ∈ S) :
    (darts G S).card = (darts G (S.erase v)).card + 2 * (neighbors G S v).card := by
  let A := (neighbors G S v).image (fun w => (v,w))
  let B := (neighbors G S v).image (fun w => (w,v))
  have hA : A.card = (neighbors G S v).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)
  have hB : B.card = (neighbors G S v).card :=
    Finset.card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)
  have hDA : Disjoint (darts G (S.erase v)) A := by
    apply Finset.disjoint_left.mpr
    intro e he hA
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
    exact (Finset.mem_erase.mp ((mem_darts G).mp he).1).1 rfl
  have hDB : Disjoint (darts G (S.erase v)) B := by
    apply Finset.disjoint_left.mpr
    intro e he hB
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hB
    exact (Finset.mem_erase.mp ((mem_darts G).mp he).2.1).1 rfl
  have hAB : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hf
    have h : v = w := congrArg Prod.snd heq
    exact ((mem_neighbors G).mp hw).2.ne h
  have heq : darts G S = darts G (S.erase v) ∪ A ∪ B := by
    ext ⟨x,y⟩
    simp only [Finset.mem_union]
    constructor
    · intro h
      obtain ⟨hx,hy,ha⟩ := (mem_darts G).mp h
      by_cases hxv : x = v
      · subst x
        exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨y,(mem_neighbors G).mpr ⟨hy,ha⟩,rfl⟩))
      by_cases hyv : y = v
      · subst y
        exact Or.inr (Finset.mem_image.mpr ⟨x,(mem_neighbors G).mpr ⟨hx,ha.symm⟩,rfl⟩)
      exact Or.inl (Or.inl ((mem_darts G).mpr
        ⟨Finset.mem_erase.mpr ⟨hxv,hx⟩,Finset.mem_erase.mpr ⟨hyv,hy⟩,ha⟩))
    · rintro ((h | h) | h)
      · exact darts_mono G (Finset.erase_subset _ _) h
      · obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp h
        rw [← heq]
        exact (mem_darts G).mpr ⟨hv,((mem_neighbors G).mp hw).1,((mem_neighbors G).mp hw).2⟩
      · obtain ⟨w,hw,heq⟩ := Finset.mem_image.mp h
        rw [← heq]
        exact (mem_darts G).mpr ⟨((mem_neighbors G).mp hw).1,hv,((mem_neighbors G).mp hw).2.symm⟩
  rw [heq,Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hDB,hAB⟩),
    Finset.card_union_of_disjoint hDA,hA,hB]
  omega

lemma darts_univ {V : Type} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] [Fintype V] : (darts G Finset.univ).card = 2 * G.edgeFinset.card := by
  simpa [darts] using G.two_mul_card_edgeFinset.symm

end Density

end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Fractional
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def Stable (G : SimpleGraph V) (I : Finset V) : Prop :=
  ∀ v ∈ I, ∀ w ∈ I, ¬G.Adj v w

@[simp] lemma stable_empty {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Stable G ∅ := by simp [Stable]
@[simp] lemma stable_singleton {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (v : V) : Stable G {v} := by
  simp [Stable]

def Cover (G : SimpleGraph V) (μ : Finset V → ℝ) : Prop :=
  (∀ I, 0 ≤ μ I) ∧ (∀ I, ¬Stable G I → μ I = 0) ∧
    ∀ v, 1 ≤ ∑ I, if v ∈ I then μ I else 0

noncomputable def cost (μ : Finset V → ℝ) : ℝ := ∑ I, μ I

noncomputable def number (G : SimpleGraph V) : ℝ :=
  sInf {c : ℝ | ∃ μ, Cover G μ ∧ cost μ = c}

noncomputable def singletonWeights (I : Finset V) : ℝ :=
  ∑ v : V, if I = {v} then 1 else 0

def Dual (G : SimpleGraph V) (w : V → ℝ) : Prop :=
  (∀ v, 0 ≤ w v) ∧ ∀ I, Stable G I → ∑ v ∈ I, w v ≤ 1

noncomputable def indicator (I : Finset V) : V → ℝ := fun v => if v ∈ I then 1 else 0

noncomputable def transport {α β : Type} [Fintype α] [DecidableEq β]
    (μ : α → ℝ) (f : α → β) (b : β) : ℝ := ∑ a, if f a = b then μ a else 0

noncomputable def marginal (μ : Finset V → ℝ) (v : V) : ℝ :=
  ∑ I, if v ∈ I then μ I else 0

noncomputable def prune (μ : Finset V → ℝ) (v : V) (p : ℝ) : Finset V → ℝ :=
  fun I => p * μ I + (1-p) * transport μ (fun J => J.erase v) I

noncomputable def splitWeights (μ : Finset V → ℝ)
    (P : Finset V → Finset (Finset V)) (J : Finset V) : ℝ :=
  ∑ I, if J ∈ P I then μ I else 0

end LinearListHadwiger.Fractional

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.FractionalSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

noncomputable def productMass (μ : ι → Ω → ℝ) (x : ι → Ω) : ℝ := ∏ i, μ i (x i)
noncomputable def expectation (μ f : Ω → ℝ) : ℝ := ∑ ω, μ ω * f ω
noncomputable def probability (μ : Ω → ℝ) (A : Ω → Prop) : ℝ :=
  by classical exact ∑ ω, if A ω then μ ω else 0

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open scoped BigOperators
open Fractional
variable {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq ι] [DecidableEq V]

noncomputable def otherCopies (W : Ω → Finset V) (i : ι) (x : ι → Ω) : Finset V :=
  (Finset.univ.erase i).biUnion fun j => W (x j)

noncomputable def privateCopy (W : Ω → Finset V) (i : ι) (x : ι → Ω) : Finset V :=
  W (x i) \ otherCopies W i x

noncomputable def collision (W : Ω → Finset V) (φ : Ω → V → ℝ) (i : ι)
    (x : ι → Ω) : ℝ := ∑ j ∈ Finset.univ.erase i, ∑ v,
      φ (x i) v * (if v ∈ W (x j) then 1 else 0)

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SamplingBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω V : Type} [Fintype ι] [Fintype Ω] [Fintype V]
  [DecidableEq ι] [DecidableEq V]

noncomputable def remainder (E : ι → Finset V) (I : Ω → Finset V)
    (x : ι → Ω) : Finset V :=
  Finset.univ \ Finset.univ.biUnion (fun j => I (x j) ∩ E j)

end LinearListHadwiger.Sampling

namespace LinearListHadwiger.Sampling
open scoped BigOperators
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

variable {κ V : Type} [Fintype κ] [Fintype V] [DecidableEq κ] [DecidableEq V]

noncomputable def unionRemainders (E : ι → Finset V) (I : Ω → Finset V)
    (x : κ × ι → Ω) : Finset V :=
  Finset.univ.biUnion (fun k => remainder E I (fun i => x (k,i)))

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Separability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Fractional
open scoped BigOperators
variable {V : Type} [Fintype V] [DecidableEq V]

def cliqueBlowup (G : SimpleGraph V) (m : ℕ) : SimpleGraph (V × Fin m) where
  Adj u v := G.Adj u.1 v.1 ∨ (u.1 = v.1 ∧ u.2 ≠ v.2)
  symm := ⟨by
    intro u v h
    rcases h with h | ⟨h₁,h₂⟩
    · exact Or.inl h.symm
    · exact Or.inr ⟨h₁.symm,h₂.symm⟩⟩
  loopless := ⟨by intro u; simp⟩

end LinearListHadwiger.Fractional

namespace LinearListHadwiger
namespace FixedDecomposition
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}

inductive Tree (G : SimpleGraph V) (k : ℕ) : Finset V → Type
  | leaf {S} (stop : S.card ≤ 2*k ∨ KConnectedOn G S k) : Tree G k S
  | branch {S A Z B} (split : SeparatorSplit G S A Z B) (small : Z.card < k)
      (left : Tree G k (A ∪ Z)) (right : Tree G k (B ∪ Z)) : Tree G k S

def Tree.leaves {S : Finset V} : Tree G k S → List (Finset V)
  | .leaf _ => [S]
  | .branch _ _ l r => l.leaves ++ r.leaves

def Tree.separators {S : Finset V} : Tree G k S → List (Finset V)
  | .leaf _ => []
  | @Tree.branch _ _ _ _ _ _ Z _ _ _ l r => Z :: (l.separators ++ r.separators)

def budget (k u : ℕ) : ℕ := if u ≤ 2*k then 1 else (u-k)^2

end FixedDecomposition
end LinearListHadwiger

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.PairedSources
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.PairedSources
open SimpleGraph PathPacking
variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def graph (G : SimpleGraph V) (s : I → Bool → V) (U : Set V) : SimpleGraph (I ⊕ V) where
  Adj x y := match x,y with
    | .inl _, .inl _ => False
    | .inl i, .inr v => v ∈ U ∧ (∀ j b, v ≠ s j b) ∧ ∃ b, G.Adj (s i b) v
    | .inr v, .inl i => v ∈ U ∧ (∀ j b, v ≠ s j b) ∧ ∃ b, G.Adj (s i b) v
    | .inr v, .inr w => v ∈ U ∧ w ∈ U ∧ (∀ j b, v ≠ s j b) ∧
        (∀ j b, w ≠ s j b) ∧ G.Adj v w
  symm := ⟨by
    intro x y h
    cases x <;> cases y
    · exact h.elim
    · exact h
    · exact h
    · exact ⟨h.2.1,h.1,h.2.2.2.1,h.2.2.1,h.2.2.2.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    cases x
    · exact h
    · exact h.2.2.2.2.ne rfl⟩

variable {G : SimpleGraph V} {s : I → Bool → V} {U : Set V}

noncomputable def routeHom (i : I) (b : Bool) {v : V}
    (p : G.Path (s i b) v)
    (hU : ∀ w ∈ p.val.support, w ∈ U)
    (hsource : ∀ w ∈ p.val.support, ∀ j c, w = s j c → w = s i b) :
    G.induce {w | w ∈ p.val.support} →g graph G s U where
  toFun w := if w.val = s i b then .inl i else .inr w.val
  map_rel' := by
    intro x y hxy
    change G.Adj x.val y.val at hxy
    dsimp
    split_ifs with hx hy hy
    · exact (hxy.ne (hx.trans hy.symm)).elim
    · exact ⟨hU _ y.property,fun j c he => hy (hsource _ y.property j c he),
        b,by simpa only [hx] using hxy⟩
    · exact ⟨hU _ x.property,fun j c he => hx (hsource _ x.property j c he),
        b,by simpa only [hy] using hxy.symm⟩
    · exact ⟨hU _ x.property,hU _ y.property,
        fun j c he => hx (hsource _ x.property j c he),
        fun j c he => hy (hsource _ y.property j c he),hxy⟩

structure Packing (G : SimpleGraph V) (s : I → Bool → V) (D : Finset V)
    (U : Set V) where
  choose : I → Bool
  target : I → ↥D
  route : ∀ i, G.Path (s i (choose i)) (target i).val
  disjoint : ∀ i j, i ≠ j → Disjoint {v | v ∈ (route i).val.support}
    {v | v ∈ (route j).val.support}
  source_only : ∀ i v, v ∈ (route i).val.support →
    (∃ j b, v = s j b) → v = s i (choose i)
  target_only : ∀ i v, v ∈ (route i).val.support → v ∈ D → v = (target i).val
  inside : ∀ i v, v ∈ (route i).val.support → v ∈ U

def Valid (s : I → Bool → V) (U : Set V) : I ⊕ V → Prop
  | .inl _ => True
  | .inr v => v ∈ U ∧ ∀ j b, v ≠ s j b

end LinearListHadwiger.PairedSources

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Knitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def packedBranch {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b : ↥B) : Set V :=
  {b.val} ∪ {v | ∃ a, P.target a = b ∧ v ∈ (P.route a).val.support}

lemma packedBranch_target {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b : ↥B) : b.val ∈ packedBranch P b := Or.inl rfl

lemma packedBranch_connected {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b : ↥B) : (G.induce (packedBranch P b)).Connected := by
  classical
  by_cases hh : ∃ a, P.target a = b
  · obtain ⟨a,rfl⟩ := hh
    have he : packedBranch P (P.target a) = {v | v ∈ (P.route a).val.support} := by
      ext v
      constructor
      · rintro (rfl | ⟨a',ha',hv⟩)
        · exact (P.route a).val.end_mem_support
        · have heq := P.target_injective ha'
          cases heq
          exact hv
      · exact fun hv => Or.inr ⟨a,rfl,hv⟩
    rw [he]
    exact (P.route a).val.connected_induce_support
  · have he : packedBranch P b = {b.val} := by
      ext v
      constructor
      · rintro (hv | ⟨a,ha,_⟩)
        · exact hv
        · exact (hh ⟨a,ha⟩).elim
      · exact Or.inl
    rw [he]
    exact SimpleGraph.Connected.of_subsingleton

lemma packedBranch_disjoint {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) (b c : ↥B) (hbc : b ≠ c) :
    Disjoint (packedBranch P b) (packedBranch P c) := by
  apply Set.disjoint_left.mpr
  intro v hv hv'
  rcases hv with hv | ⟨a,ha,hva⟩ <;> rcases hv' with hv' | ⟨a',ha',hva'⟩
  · exact hbc (Subtype.ext (hv.symm.trans hv'))
  · have ht := P.target_only a' v hva' (hv ▸ b.property)
    exact hbc (Subtype.ext (hv.symm.trans (ht.trans (congrArg Subtype.val ha'))))
  · have ht := P.target_only a v hva (hv' ▸ c.property)
    exact hbc (Subtype.ext ((congrArg Subtype.val ha).symm.trans (ht.symm.trans hv')))
  · have hne : a ≠ a' := by
      rintro rfl
      exact hbc (ha.symm.trans ha')
    exact Set.disjoint_left.mp (P.disjoint a a' hne) hva hva'

noncomputable def absorb_packing {G : SimpleGraph V} {A B : Finset V}
    (P : FullPacking G A B) : MinorModel G (G.induce (↑B : Set V)) where
  branch := packedBranch P
  connected := packedBranch_connected P
  disjoint := packedBranch_disjoint P
  adjacent := by
    intro b c hbc
    exact ⟨b.val,packedBranch_target P b,c.val,packedBranch_target P c,hbc⟩

def compose_model {W U : Type} {G : SimpleGraph V} {H : SimpleGraph W}
    {K : SimpleGraph U} (M : MinorModel G H) (N : MinorModel H K) : MinorModel G K where
  branch u := M.expand (N.branch u)
  connected u := M.expand_connected (N.connected u)
  disjoint u v huv := M.expand_disjoint (N.disjoint u v huv)
  adjacent := by
    intro u v huv
    obtain ⟨a,ha,b,hb,hab⟩ := N.adjacent huv
    obtain ⟨x,hx,y,hy,hxy⟩ := M.adjacent hab
    exact ⟨x,⟨a,ha,hx⟩,y,⟨b,hb,hy⟩,hxy⟩

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.TerminalGrouping
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Knitting
open SimpleGraph PathPacking
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def density (G : SimpleGraph V) : ℚ :=
  (G.edgeFinset.card : ℚ) / Fintype.card V

noncomputable def model_singletons (G : SimpleGraph V) : MinorModel G G where
  branch v := {v}
  connected v := by
    have : Nonempty ({v} : Set V) := ⟨⟨v,rfl⟩⟩
    exact Connected.of_subsingleton
  disjoint u v hn := Set.disjoint_singleton.mpr hn
  adjacent := by intro u v h; exact ⟨_,rfl,_,rfl,h⟩

noncomputable def model_relabel {W W' : Type} {G : SimpleGraph V}
    {H : SimpleGraph W} {H' : SimpleGraph W'} (M : MinorModel G H)
    (e : H ≃g H') : MinorModel G H' where
  branch w := M.branch (e.symm w)
  connected w := M.connected _
  disjoint u v hn := M.disjoint _ _ (fun h => hn (e.symm.injective h))
  adjacent := by intro u v h; exact M.adjacent (e.symm.map_rel_iff.mpr h)

def contractEdge (G : SimpleGraph V) (u v : V) : SimpleGraph {w : V // w ≠ v} where
  Adj a b := a ≠ b ∧ (G.Adj a.val b.val ∨
    (a.val = u ∧ G.Adj v b.val) ∨ (b.val = u ∧ G.Adj v a.val))
  symm := ⟨by
    intro a b h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

noncomputable def contract_model (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    MinorModel G (contractEdge G u v) where
  branch w := if w.val = u then {u,v} else {w.val}
  connected w := by
    by_cases hw : w.val = u
    · rw [ite_eq_left hw]
      have he : {w | w ∈ (Walk.cons huv Walk.nil).support} = ({u,v} : Set V) := by
        ext w
        simp
      rw [← he]
      exact (Walk.cons huv Walk.nil).connected_induce_support
    · rw [ite_eq_right hw]
      have : Nonempty ({w.val} : Set V) := ⟨⟨w.val,rfl⟩⟩
      exact Connected.of_subsingleton
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro w ha hb
    by_cases hau : a.val=u <;> by_cases hbu : b.val=u
    · exact hab (Subtype.ext (hau.trans hbu.symm))
    · simp only [ite_eq_left hau,ite_eq_right hbu,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
      rcases ha with rfl | rfl
      · exact hbu hb.symm
      · exact b.property hb.symm
    · simp only [ite_eq_right hau,ite_eq_left hbu,Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
      rcases hb with rfl | rfl
      · exact hau ha.symm
      · exact a.property ha.symm
    · simp only [ite_eq_right hau,ite_eq_right hbu,Set.mem_singleton_iff] at ha hb
      exact hab (Subtype.ext (ha.symm.trans hb))
  adjacent := by
    intro a b h
    have ha : a.val ∈ if a.val=u then ({u,v} : Set V) else {a.val} := by split_ifs with he <;> simp [*]
    have hb : b.val ∈ if b.val=u then ({u,v} : Set V) else {b.val} := by split_ifs with he <;> simp [*]
    rcases h.2 with h | h | h
    · exact ⟨_,ha,_,hb,h⟩
    · refine ⟨v,?_,b.val,hb,h.2⟩
      simp [h.1]
    · refine ⟨a.val,ha,v,?_,h.2.symm⟩
      simp [h.1]

noncomputable def common (G : SimpleGraph V) (u v : V) : Finset V :=
  Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w

def edgeGood (G : SimpleGraph V) (u v : V) (a b : V) : Prop :=
  G.Adj a b ∧ (a=v → b≠u ∧ ¬G.Adj u b) ∧ (b=v → a≠u ∧ ¬G.Adj u a)

def proj (u v : V) (huv : u≠v) (w : V) : {z : V // z≠v} :=
  ⟨if w=v then u else w, by split_ifs with h; exact huv; exact h⟩

noncomputable def model_induce (G : SimpleGraph V) (S : Finset V) :
    MinorModel G (G.induce (↑S : Set V)) where
  branch w := {w.val}
  connected w := by
    have : Nonempty ({w.val} : Set V) := ⟨⟨w.val,rfl⟩⟩
    exact Connected.of_subsingleton
  disjoint u v hn := Set.disjoint_singleton.mpr (fun he => hn (Subtype.ext he))
  adjacent := by intro u v h; exact ⟨_,rfl,_,rfl,h⟩

end LinearListHadwiger.Knitting

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.CoarseDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.CoarseDensity
open SimpleGraph Finset
open Knitting
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def domBudget (N k : ℕ) : ℕ :=
  3*(N/k+1)*⌈10*((N:ℝ)/(3*k))*Real.log (2*N)⌉₊

end LinearListHadwiger.CoarseDensity

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Incidence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Incidence
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V  :  Type} [Fintype V] [DecidableEq V]

structure BoundedBags (G : SimpleGraph V) (q b : ℕ) where
  bag : Fin q → Finset V
  connected : ∀ i, (G.induce (↑(bag i) : Set V)).Connected
  disjoint : ∀ i j, i ≠ j → Disjoint (bag i) (bag j)
  adjacent : ∀ i j, i ≠ j → ∃ v ∈ bag i, ∃ w ∈ bag j, G.Adj v w
  small : ∀ i, (bag i).card ≤ b

def addStar (H : SimpleGraph V) (u : V) (N : Finset V) : SimpleGraph V where
  Adj a b := H.Adj a b ∨ (a = u ∧ b ∈ N ∧ a ≠ b) ∨ (b = u ∧ a ∈ N ∧ a ≠ b)
  symm := ⟨by
    intro a b h
    rcases h with h | h | h
    · exact Or.inl h.symm
    · exact Or.inr (Or.inr ⟨h.1,h.2.1,h.2.2.symm⟩)
    · exact Or.inr (Or.inl ⟨h.1,h.2.1,h.2.2.symm⟩)⟩
  loopless := ⟨by intro v h; rcases h with h | h | h
                  · exact H.irrefl h
                  · exact h.2.2 rfl
                  · exact h.2.2 rfl⟩

lemma connected_insert {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {S : Set V} (hc : (G.induce S).Connected)
    {u v : V} (hu : u ∈ S) (he : G.Adj v u) : (G.induce (insert v S)).Connected := by
  have hS : S ⊆ insert v S := Set.subset_insert _ _
  have hv : v ∈ insert v S := Set.mem_insert _ _
  have hr : ∀ a : (insert v S : Set V), (G.induce (insert v S)).Reachable a ⟨u,hS hu⟩ := by
    rintro ⟨a,ha⟩
    rcases ha with ha | ha
    · subst a
      exact (show (G.induce (insert v S)).Adj ⟨v,hv⟩ ⟨u,hS hu⟩ from he).reachable
    · exact (hc.preconnected ⟨a,ha⟩ ⟨u,hu⟩).map (G.induceHomOfLE hS).toHom
  exact {preconnected := fun a b => (hr a).trans (hr b).symm, nonempty := ⟨⟨v,hv⟩⟩}

noncomputable def extendModel {W : Type} [DecidableEq W] {P : SimpleGraph V}
    {H : SimpleGraph W} (M : MinorModel P H) (root : W → V)
    (hroot : ∀ a, root a ∈ M.branch a) (v : V)
    (hv : ∀ a, v ∉ M.branch a) (N : Finset W)
    (hneigh : ∀ a ∈ N, P.Adj v (root a)) (u : W) (hu : u ∈ N) :
    MinorModel P (addStar H u N) where
  branch a := if a=u then insert v (M.branch a) else M.branch a
  connected a := by
    by_cases ha : a=u
    · rw [ite_eq_left ha]
      exact connected_insert (M.connected a) (hroot a) (hneigh a (ha ▸ hu))
    · rw [ite_eq_right ha]
      exact M.connected a
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro w ha hb
    by_cases hau : a=u <;> by_cases hbu : b=u
    · exact hab (hau.trans hbu.symm)
    · simp only [ite_eq_left hau,ite_eq_right hbu,Set.mem_insert_iff] at ha hb
      rcases ha with rfl | ha
      · exact hv b hb
      · exact Set.disjoint_left.mp (M.disjoint a b hab) ha hb
    · simp only [ite_eq_right hau,ite_eq_left hbu,Set.mem_insert_iff] at ha hb
      rcases hb with rfl | hb
      · exact hv a ha
      · exact Set.disjoint_left.mp (M.disjoint a b hab) ha hb
    · simp only [ite_eq_right hau,ite_eq_right hbu] at ha hb
      exact Set.disjoint_left.mp (M.disjoint a b hab) ha hb
  adjacent := by
    intro a b h
    have hsub (c : W) : M.branch c ⊆ if c=u then insert v (M.branch c) else M.branch c := by
      split_ifs <;> simp
    rcases h with h | h | h
    · obtain ⟨x,hx,y,hy,he⟩ := M.adjacent h
      exact ⟨x,hsub a hx,y,hsub b hy,he⟩
    · exact ⟨v,by simp [h.1],root b,hsub b (hroot b),hneigh b h.2.1⟩
    · exact ⟨root a,hsub a (hroot a),v,by simp [h.1],(hneigh a h.2.1).symm⟩

end LinearListHadwiger.Incidence

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.District
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.District
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V]

def Statement : Prop := ∀ K : ℕ, 0 < K → ∃ D : ℕ,
  max (400*3202) (12800*K) < D ∧ ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t →
  ∀ (W : Type) [Fintype W] [Nonempty W] [DecidableEq W] (P : SimpleGraph W),
  hadwigerNumber P < t → (D*t*Fintype.card W : ℕ) ≤ P.edgeFinset.card →
  ∃ S : Finset W, KConnectedOn P S (K*t) ∧ (S.card : ℝ) ≤ (t:ℝ)^(53/50:ℝ)

def outside (G : SimpleGraph V) (H : Finset V) : Finset V :=
  univ.filter fun w => w ∉ H ∧ ∃ v ∈ H, G.Adj v w

@[simp] lemma mem_outside (G : SimpleGraph V) (H : Finset V) (w : V) :
    w ∈ outside G H ↔ w ∉ H ∧ ∃ v ∈ H, G.Adj v w := by simp [outside]

lemma degree_sum_comm {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H S : Finset V) :
    ∑ v ∈ H, (S.filter (G.Adj v)).card = ∑ w ∈ S, (H.filter (G.Adj w)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro w hw
  apply sum_congr rfl
  intro v hv
  simp only [G.adj_comm]

lemma degree_sum_split (G : SimpleGraph V) (H S : Finset V) :
    ∑ v ∈ H, (S.filter (G.Adj v)).card =
      ∑ w ∈ S ∩ H, (H.filter (G.Adj w)).card +
      ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card := by
  rw [degree_sum_comm]
  have hsub : S ∩ H ⊆ S := inter_subset_left
  rw [←sum_sdiff hsub]
  have he : ∑ w ∈ S \ (S ∩ H), (H.filter (G.Adj w)).card =
      ∑ w ∈ S ∩ outside G H, (H.filter (G.Adj w)).card := by
    apply (sum_subset ?_ ?_).symm
    · intro w hw
      obtain ⟨hs,ho⟩ := mem_inter.mp hw
      exact mem_sdiff.mpr ⟨hs, fun hh => ((mem_outside _ _ _).mp ho).1 (mem_inter.mp hh).2⟩
    · intro w hw hn
      obtain ⟨hs,hh⟩ := mem_sdiff.mp hw
      apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvH,hvw⟩ := mem_filter.mp hv
      apply hn
      refine mem_inter.mpr ⟨hs,(mem_outside _ _ _).mpr ⟨?_,v,hvH,hvw.symm⟩⟩
      intro hwH
      exact hh (mem_inter.mpr ⟨hs,hwH⟩)
  rw [he,add_comm]

def loss2 (G : SimpleGraph V) (H : Finset V) : ℕ :=
  (Density.darts G H).card + 2*∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1)

lemma outside_pos (G : SimpleGraph V) (H : Finset V) {w : V}
    (hw : w ∈ outside G H) : 1 ≤ (H.filter (G.Adj w)).card := by
  obtain ⟨_,v,hv,hvw⟩ := (mem_outside _ _ _).mp hw
  exact card_pos.mpr ⟨v,mem_filter.mpr ⟨hv,hvw.symm⟩⟩

lemma darts_sum {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (H : Finset V) :
    (Density.darts G H).card = ∑ v ∈ H, (H.filter (G.Adj v)).card := by
  simp only [Density.darts]
  rw [card_eq_sum_ones, sum_filter, sum_product]
  simp only [card_eq_sum_ones, sum_filter]

lemma loss2_identity (G : SimpleGraph V) (H : Finset V) :
    loss2 G H + (Density.darts G H).card + 2*(outside G H).card =
      2*∑ v ∈ H, G.degree v := by
  have hx := degree_sum_split G H univ
  simp only [univ_inter] at hx
  have hd : ∀ v, (univ.filter (G.Adj v)).card = G.degree v := by
    intro v
    have he : univ.filter (G.Adj v) = G.neighborFinset v := by ext w; simp
    rw [he,SimpleGraph.card_neighborFinset_eq_degree]
  simp only [hd] at hx
  have hc : (∑ w ∈ outside G H, ((H.filter (G.Adj w)).card-1)) + (outside G H).card =
      ∑ w ∈ outside G H, (H.filter (G.Adj w)).card := by
    rw [show (outside G H).card = (∑ _w ∈ outside G H, (1:ℕ)) by simp,←sum_add_distrib]
    apply sum_congr rfl
    intro w hw
    exact Nat.sub_add_cancel (outside_pos G H hw)
  rw [←darts_sum] at hx
  unfold loss2
  omega

@[simp] lemma loss2_singleton (G : SimpleGraph V) (v : V) : loss2 G {v} = 0 := by
  unfold loss2
  have hd : Density.darts G {v} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    obtain ⟨hx,hy,h⟩ := (Density.mem_darts G).mp hx
    have h1 : x.1=v := mem_singleton.mp hx
    have h2 : x.2=v := mem_singleton.mp hy
    exact h.ne (h1.trans h2.symm)
  rw [hd,card_empty,zero_add]
  apply (mul_eq_zero).mpr
  right
  apply sum_eq_zero
  intro w hw
  have hh : (({v}:Finset V).filter (G.Adj w)).card ≤ 1 := (card_filter_le _ _).trans (by simp)
  omega

abbrev ContractVertex (H : Finset V) := ↥Hᶜ ⊕ Unit

def contractSet (G : SimpleGraph V) (H : Finset V) : SimpleGraph (ContractVertex H) where
  Adj a b := match a,b with
    | .inl a,.inl b => G.Adj a.val b.val
    | .inl a,.inr _ => ∃ v ∈ H, G.Adj a.val v
    | .inr _,.inl b => ∃ v ∈ H, G.Adj v b.val
    | .inr _,.inr _ => False
  symm := ⟨by
    rintro (a|a) (b|b) h
    · exact h.symm
    · obtain ⟨v,hv,ha⟩ := h; exact ⟨v,hv,ha.symm⟩
    · obtain ⟨v,hv,ha⟩ := h; exact ⟨v,hv,ha.symm⟩
    · exact h⟩
  loopless := ⟨by rintro (a|a) h; exact h.ne rfl; exact h⟩

def contractSet_model (G : SimpleGraph V) (H : Finset V)
    (hc : (G.induce (↑H:Set V)).Connected) : MinorModel G (contractSet G H) where
  branch a := match a with | .inl a => {a.val} | .inr _ => ↑H
  connected a := by
    cases a with
    | inl a => exact Connected.of_subsingleton
    | inr a => exact hc
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v hv hw
    cases a with
    | inl a =>
      have hva : v=a.val := hv
      cases b with
      | inl b => exact hab (congrArg Sum.inl (Subtype.ext (hva.symm.trans hw)))
      | inr b => exact (mem_compl.mp a.property) (hva ▸ hw)
    | inr a =>
      cases b with
      | inl b => exact (mem_compl.mp b.property) ((show v=b.val from hw) ▸ hv)
      | inr b => exact hab (by congr)
  adjacent := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact ⟨_,rfl,_,rfl,h⟩
      | inr b => obtain ⟨v,hv,ha⟩ := h; exact ⟨_,rfl,v,hv,ha⟩
    | inr a =>
      cases b with
      | inl b => obtain ⟨v,hv,ha⟩ := h; exact ⟨v,hv,_,rfl,ha⟩
      | inr b => exact h.elim

lemma contract_card (H : Finset V) :
    Fintype.card (ContractVertex H) = Fintype.card V - H.card + 1 := by
  simp [ContractVertex]

lemma contract_root_degree (G : SimpleGraph V) (H : Finset V) :
    (Density.neighbors (contractSet G H) univ (.inr ())).card = (outside G H).card := by
  symm
  apply card_bij (fun w hw => Sum.inl ⟨w,mem_compl.mpr (((mem_outside _ _ _).mp hw).1)⟩)
  · intro w hw
    obtain ⟨_,v,hv,ha⟩ := (mem_outside _ _ _).mp hw
    exact (Density.mem_neighbors _).mpr ⟨mem_univ _,v,hv,ha⟩
  · intro a ha b hb heq
    exact congrArg Subtype.val (Sum.inl.inj heq)
  · intro a ha
    have h := ((Density.mem_neighbors _).mp ha).2
    cases a with
    | inl a =>
      obtain ⟨v,hv,ha⟩ := h
      refine ⟨a.val,(mem_outside _ _ _).mpr ⟨mem_compl.mp a.property,v,hv,ha⟩,rfl⟩
    | inr a => exact h.elim

lemma contract_remaining_darts (G : SimpleGraph V) (H : Finset V) :
    (Density.darts (contractSet G H) (univ.erase (.inr ()))).card =
      (Density.darts G Hᶜ).card := by
  symm
  apply card_bij (fun e he =>
    (Sum.inl ⟨e.1,((Density.mem_darts G).mp he).1⟩,
     Sum.inl ⟨e.2,((Density.mem_darts G).mp he).2.1⟩))
  · intro e he
    obtain ⟨ha,hb,he⟩ := (Density.mem_darts G).mp he
    exact (Density.mem_darts _).mpr ⟨by simp,by simp,he⟩
  · intro a ha b hb he
    apply Prod.ext
    · exact congrArg Subtype.val (Sum.inl.inj (congrArg Prod.fst he))
    · exact congrArg Subtype.val (Sum.inl.inj (congrArg Prod.snd he))
  · rintro ⟨a,b⟩ he
    obtain ⟨ha,hb,he⟩ := (Density.mem_darts _).mp he
    cases a with
    | inr a => exact (mem_erase.mp ha).1 (by congr) |>.elim
    | inl a =>
      cases b with
      | inr b => exact (mem_erase.mp hb).1 (by congr) |>.elim
      | inl b => exact ⟨(a.val,b.val),(Density.mem_darts G).mpr ⟨a.property,b.property,he⟩,rfl⟩

lemma contract_darts (G : SimpleGraph V) (H : Finset V) :
    2*(contractSet G H).edgeFinset.card = (Density.darts G Hᶜ).card + 2*(outside G H).card := by
  have hh := Density.darts_erase (contractSet G H) (mem_univ (.inr ()))
  rwa [Density.darts_univ,contract_remaining_darts,contract_root_degree] at hh

lemma degree_partition (G : SimpleGraph V) (H : Finset V) (v : V) :
    G.degree v = (H.filter (G.Adj v)).card + (Hᶜ.filter (G.Adj v)).card := by
  have he : G.neighborFinset v = H.filter (G.Adj v) ∪ Hᶜ.filter (G.Adj v) := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset,mem_union,mem_filter,mem_compl]
    tauto
  have hd : Disjoint (H.filter (G.Adj v)) (Hᶜ.filter (G.Adj v)) :=
    disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) disjoint_compl_right)
  rw [←SimpleGraph.card_neighborFinset_eq_degree,he,card_union_of_disjoint hd]

lemma darts_partition (G : SimpleGraph V) (H : Finset V) :
    2*G.edgeFinset.card + (Density.darts G H).card =
      (Density.darts G Hᶜ).card + 2*∑v∈H,G.degree v := by
  have hH : (∑v∈H,G.degree v) = (Density.darts G H).card + ∑v∈H,(Hᶜ.filter (G.Adj v)).card := by
    simp only [degree_partition G H, sum_add_distrib, darts_sum]
  have hC : (∑v∈Hᶜ,G.degree v) = (Density.darts G Hᶜ).card + ∑v∈Hᶜ,(H.filter (G.Adj v)).card := by
    have hh : ∀ v, G.degree v = (Hᶜ.filter (G.Adj v)).card + (H.filter (G.Adj v)).card := by
      intro v; simpa only [compl_compl] using degree_partition G Hᶜ v
    simp only [hh,sum_add_distrib,darts_sum]
  rw [degree_sum_comm] at hH
  have hs := sum_add_sum_compl H (fun v => G.degree v)
  rw [G.sum_degrees_eq_twice_card_edges] at hs
  omega

theorem loss2_contract (G : SimpleGraph V) (H : Finset V) :
    2*(contractSet G H).edgeFinset.card + loss2 G H = 2*G.edgeFinset.card := by
  have h1 := contract_darts G H
  have h2 := darts_partition G H
  have h3 := loss2_identity G H
  omega

lemma expand_card {W : Type} [DecidableEq W] (G : SimpleGraph V) (Q : SimpleGraph W)
    (M : MinorModel G Q) (H : Finset W) :
    (M.expand (↑H:Set W)).toFinset.card = ∑ w ∈ H, (M.branch w).toFinset.card := by
  have he : (M.expand (↑H:Set W)).toFinset = H.biUnion (fun w => (M.branch w).toFinset) := by
    ext v
    rw [@Set.mem_toFinset V (M.expand (↑H:Set W)) _ v]
    simp only [MinorModel.expand, Set.mem_ofPred_eq, mem_coe,mem_biUnion,Set.mem_toFinset]
  rw [he]
  apply card_biUnion
  intro a ha b hb hab
  exact Set.disjoint_toFinset.mpr (M.disjoint a b hab)

structure CheapMinor (G : SimpleGraph V) (p : ℕ) (lam : ℚ) where
  W : Type
  [fintype : Fintype W]
  graph : SimpleGraph W
  model : MinorModel G graph
  sizes : ∀ w, (model.branch w).toFinset.card = 1 ∨ (model.branch w).toFinset.card = p
  budget : (G.edgeFinset.card:ℚ) - graph.edgeFinset.card ≤ lam*(Fintype.card V-(Fintype.card W:ℚ))
  upper : graph.edgeFinset.card ≤ G.edgeFinset.card
attribute [instance] CheapMinor.fintype

noncomputable def CheapMinor.initial (G : SimpleGraph V) (p : ℕ) (lam : ℚ) : CheapMinor G p lam where
  W := V
  graph := G
  model := Knitting.model_singletons G
  sizes w := Or.inl (by
    rw [Set.toFinset_congr (show (Knitting.model_singletons G).branch w = {w} from rfl)]
    simp)
  budget := by simp
  upper := le_rfl

noncomputable def CheapMinor.big {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) : Finset M.W := univ.filter fun w => (M.model.branch w).toFinset.card=p

lemma CheapMinor.small {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) {w : M.W} (hw : w ∉ M.big) : (M.model.branch w).toFinset.card=1 := by
  have hn : (M.model.branch w).toFinset.card≠p := by simpa [CheapMinor.big] using hw
  exact (M.sizes w).resolve_right hn

noncomputable def CheapMinor.contract {G : SimpleGraph V} {p : ℕ} {lam : ℚ}
    (M : CheapMinor G p lam) (H : Finset M.W) (hc : (M.graph.induce (↑H:Set M.W)).Connected)
    (hcard : H.card=p) (hsmall : ∀ w ∈ H, w ∉ M.big)
    (hcheap : (loss2 M.graph H:ℚ) ≤ 2*lam*(H.card-1:ℚ)) : CheapMinor G p lam where
  W := ContractVertex H
  graph := contractSet M.graph H
  model := Knitting.compose_model M.model (contractSet_model M.graph H hc)
  sizes w := by
    cases w with
    | inl w =>
      have he : (Knitting.compose_model M.model (contractSet_model M.graph H hc)).branch (.inl w) =
          M.model.branch w.val := by ext v; simp [Knitting.compose_model,MinorModel.expand,contractSet_model]
      rw [he]
      exact M.sizes w.val
    | inr w =>
      right
      change (M.model.expand (↑H:Set M.W)).toFinset.card = p
      rw [expand_card]
      calc
        _ = ∑_w∈H,(1:ℕ) := sum_congr rfl (fun w hw => M.small (hsmall w hw))
        _ = p := by simp [hcard]
  budget := by
    have hcW : H.card ≤ Fintype.card M.W := card_le_univ H
    have he := loss2_contract M.graph H
    have he' : 2*((contractSet M.graph H).edgeFinset.card:ℚ)+(loss2 M.graph H:ℚ)=2*M.graph.edgeFinset.card := by exact_mod_cast he
    have horder : (Fintype.card (ContractVertex H):ℚ)=(Fintype.card M.W:ℚ)-H.card+1 := by
      rw [contract_card,Nat.cast_add,Nat.cast_sub hcW,Nat.cast_one]
    rw [horder]
    have hbudget := M.budget
    nlinarith
  upper := by
    have hh := loss2_contract M.graph H
    have hle : (contractSet M.graph H).edgeFinset.card ≤ M.graph.edgeFinset.card := by omega
    exact hle.trans M.upper

def badY (R : SimpleGraph V) (X : Finset V) (d : ℚ) : Finset V :=
  Xᶜ.filter fun v => d/400 ≤ ((X.filter (R.Adj v)).card:ℚ)
def badZ (R : SimpleGraph V) (d : ℚ) (q : ℕ) : Finset V :=
  univ.filter fun v => d*q^4 ≤ (R.degree v:ℚ)
def badSet (R : SimpleGraph V) (X : Finset V) (d : ℚ) (q : ℕ) : Finset V :=
  X ∪ badY R X d ∪ badZ R d q

end
end LinearListHadwiger.District

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.ColorBins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.ColorBins
open Finset Sampling
attribute [local instance] Classical.propDecidable
noncomputable section
variable {ι Ω : Type} [Fintype ι] [Fintype Ω] [DecidableEq ι]

variable {Color Bin : Type} [Fintype Color] [Fintype Bin] [DecidableEq Color] [DecidableEq Bin]

def uniform (b : Bin) : ℝ := (fun _ : Bin => (1 : ℝ) / Fintype.card Bin) b

def occupied (L : Finset Color) (T : Finset Bin) (f : Color → Bin) : Finset Bin :=
  T ∩ L.image f

end
end LinearListHadwiger.ColorBins

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.SmallList
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.SmallList
open Finset Filter

noncomputable def rate (t : ℝ) (j : ℕ) : ℝ := 4*t/(2:ℝ)^j
noncomputable def bins (t : ℝ) (j : ℕ) : ℕ :=
  ⌈192*rate t j*Real.log (2*max 1 (t/rate t j))⌉₊

end LinearListHadwiger.SmallList

namespace LinearListHadwiger.SmallList
open Finset Fractional
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

def FractionalObstruction (G : SimpleGraph V) : Prop :=
  ∃ S : Finset V, 4*(hadwigerNumber (G.induce (↑S:Set V)):ℝ) <
    number (G.induce (↑S:Set V))

noncomputable def singletonModel {W : Type} (G : SimpleGraph V) (H : SimpleGraph W)
    (f : W → V) (hf : Function.Injective f)
    (ha : ∀ ⦃u v⦄, H.Adj u v → G.Adj (f u) (f v)) : MinorModel G H where
  branch w := {f w}
  connected w := by
    have : Nonempty ({f w}:Set V) := ⟨⟨f w,rfl⟩⟩
    exact SimpleGraph.Connected.of_subsingleton
  disjoint u v hn := Set.disjoint_singleton.mpr (fun he => hn (hf he))
  adjacent := by intro u v h; exact ⟨_,rfl,_,rfl,ha h⟩

noncomputable def induceImageIso (G : SimpleGraph V) (R : Finset V)
    (A : Finset (↑R:Set V)) :
    (G.induce (↑R:Set V)).induce (↑A:Set (↑R:Set V)) ≃g
      G.induce (↑(A.image Subtype.val):Set V) where
  toFun a := ⟨a.val.val,mem_image.mpr ⟨a.val,a.property,rfl⟩⟩
  invFun v := ⟨⟨v.val,by obtain ⟨a,_,he⟩ := mem_image.mp v.property; exact he ▸ a.property⟩,
    by
      obtain ⟨a,ha,he⟩ := mem_image.mp v.property
      have ha' : a=⟨v.val,by exact he ▸ a.property⟩ := Subtype.ext he
      change (⟨v.val,_⟩ : (↑R:Set V)) ∈ A
      simpa only [ha'] using ha⟩
  left_inv a := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv v := rfl
  map_rel_iff' := by intros; rfl

abbrev RunPalette (t m : ℕ) := ((j : Fin m) × Fin (bins t j.val)) ⊕ Fin (16*t)

def stageBin (t m : ℕ) (j : Fin m) (b : Fin (bins t j.val)) : RunPalette t m :=
  Sum.inl ⟨j,b⟩

def binIndex {t m : ℕ} : RunPalette t m → ℕ :=
  Sum.elim (fun b => b.1.val) (fun _ => m)

lemma stageBin_injective (t m : ℕ) (j : Fin m) :
    Function.Injective (stageBin t m j) := by
  intro a b h
  exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inl.inj h)).2

noncomputable def runBlock (t m : ℕ) : Option (Fin m) → Finset (RunPalette t m)
  | none => univ.map Function.Embedding.inr
  | some j => univ.map ⟨stageBin t m j,stageBin_injective t m j⟩

end LinearListHadwiger.SmallList

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

noncomputable def exceptional {V J : Type} [Fintype V] [Fintype J] [DecidableEq V]
    (G : SimpleGraph V) (B : J → Finset V) (F : Finset V) (t : ℕ) : Finset V :=
  univ.filter (fun v => v ∉ F ∧
    3202*t ≤ (univ.filter (fun j => ∃ w ∈ B j, G.Adj v w)).card)

end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint
open Filter Real

noncomputable def rounds (t : ℝ) : ℕ := ⌈(Real.log t)^2⌉₊*(⌈(Real.log t)^2⌉₊+1)/2

end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

structure System {V : Type} [DecidableEq V] (G : SimpleGraph V) where
  domain : Finset V
  n : ℕ
  source : Fin n → ↥(↑domain : Set V)
  target : Finset ↥(↑domain : Set V)
  routes : BagRouting (G.induce (↑domain : Set V)) source (fun v : ↥target => {v.val})
  minimal : routes.Minimal

namespace System
variable {V : Type} [DecidableEq V] {G : SimpleGraph V}
noncomputable def path (S : System G) (i : Fin S.n) : Finset V :=
  (S.routes.paths i).2.val.support.toFinset.image Subtype.val
noncomputable def used (S : System G) : Finset V := S.routes.usedFinset.image Subtype.val
noncomputable def starts (S : System G) : Finset V := univ.image (fun i => (S.source i).val)
noncomputable def ends (S : System G) : Finset V :=
  univ.image (fun i => (S.routes.paths i).1.val)
noncomputable def stripped (S : System G) (i : Fin S.n) : Finset V :=
  S.path i \ {(S.source i).val}

lemma overlap (S : System G) {i j : Fin S.n} (hij : i ≠ j) {v : V}
    (hvi : v ∈ S.path i) (hvj : v ∈ S.path j) :
    v = (S.source i).val ∧ v = (S.source j).val := by
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hvi
  obtain ⟨w,hw,he⟩ := mem_image.mp hvj
  have he' : w=u := Subtype.ext he
  subst w
  have hh := S.routes.overlap i j hij u (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hw)
  exact ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩

end System
end LinearListHadwiger.Footprint

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.History
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

structure History {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (t : ℕ) where
  q : ℕ
  footprint : ℕ → Finset V
  initial_card : (footprint 0).card ≤ t
  tips : Fin q → Finset V
  district : Fin q → Finset V
  junction : Fin q → Finset V
  roots : Fin q → Finset V
  first : Fin q → System G
  second : Fin q → System G
  tips_subset : ∀ i, tips i ⊆ footprint i.val
  tips_card : ∀ i, (tips i).card ≤ t
  district_card : ∀ i, ((district i).card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  junction_card : ∀ i, ((junction i).card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  district_disjoint : ∀ i, Disjoint (district i) (footprint i.val)
  junction_disjoint : ∀ i, Disjoint (junction i) (footprint i.val ∪ district i)
  roots_subset : ∀ i, roots i ⊆ district i
  first_domain : ∀ i, (first i).domain = univ \ (footprint i.val \ tips i)
  first_starts : ∀ i, (first i).starts ⊆ tips i ∪ roots i
  tips_start : ∀ i, tips i ⊆ (first i).starts
  first_ends : ∀ i, (first i).ends ⊆ junction i
  first_count : ∀ i, (first i).n ≤ 4*t
  second_domain : ∀ i, (second i).domain = univ \ (footprint i.val ∪ roots i)
  second_starts : ∀ i, Disjoint (second i).starts
    (footprint i.val ∪ district i ∪ junction i ∪ (first i).used)
  second_injective : ∀ i, Function.Injective (second i).source
  second_ends : ∀ i, (second i).ends ⊆ junction i
  second_count : ∀ i, (second i).n ≤ 2*t
  next : ∀ i, footprint (i.val+1) = footprint i.val ∪ district i ∪ junction i ∪
    (first i).used ∪ (second i).used

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}
namespace History

abbrev FirstIndex (H : History G t) := Σ i : Fin H.q, Fin (H.first i).n
abbrev SecondIndex (H : History G t) := Σ i : Fin H.q, Fin (H.second i).n
noncomputable def firstPath (H : History G t) (i : H.FirstIndex) : Finset V :=
  (H.first i.1).stripped i.2
noncomputable def secondPath (H : History G t) (i : H.SecondIndex) : Finset V :=
  (H.second i.1).path i.2

end History
end LinearListHadwiger.Footprint

namespace LinearListHadwiger.Footprint.History
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

abbrev FirstPast (H : History G t) (r : ℕ) := {i : H.FirstIndex // i.1.val < r}
abbrev SecondPast (H : History G t) (r : ℕ) := {i : H.SecondIndex // i.1.val < r}

noncomputable def firstException (H : History G t) (r : ℕ) : Finset V :=
  exceptional G (fun i : H.FirstPast r => H.firstPath i.val) (H.footprint r) t
noncomputable def secondException (H : History G t) (r : ℕ) : Finset V :=
  exceptional G (fun i : H.SecondPast r => H.secondPath i.val) (H.footprint r) t

noncomputable def small (H : History G t) : Finset V :=
  H.footprint 0 ∪ univ.biUnion (fun i : Fin H.q =>
    H.district i ∪ H.junction i ∪ H.tips i ∪ (H.first i).starts ∪
      (H.first i).ends ∪ (H.second i).starts ∪ (H.second i).ends)

noncomputable def deleted (H : History G t) : Finset V :=
  H.small ∪ (univ.biUnion (fun r : Fin (H.q+1) => H.firstException r ∪ H.secondException r))

end LinearListHadwiger.Footprint.History

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.HistoryBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Footprint.History
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

noncomputable def firstPhase (H : History G t) (i : Fin H.q) : Finset V :=
  ((H.first i).used \ H.footprint i.val) \ H.deleted
noncomputable def secondPhase (H : History G t) (i : Fin H.q) : Finset V :=
  ((H.second i).used \ (H.footprint i.val ∪ (H.first i).used)) \ H.deleted

end LinearListHadwiger.Footprint.History

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.Stage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V W : Type} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

noncomputable def ell (G : SimpleGraph V) (S : Finset V) : ℕ :=
  listChromaticNumber (G.induce (↑S : Set V))

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Footprint
open Finset
attribute [local instance] Classical.propDecidable

structure Round {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (t : ℕ) (F : Finset V) where
  tips : Finset V
  district : Finset V
  junction : Finset V
  roots : Finset V
  first : System G
  second : System G
  tips_subset : tips ⊆ F
  tips_card : tips.card ≤ t
  district_card : (district.card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  junction_card : (junction.card:ℝ) ≤ (t:ℝ)^(106/100:ℝ)
  district_disjoint : Disjoint district F
  junction_disjoint : Disjoint junction (F∪district)
  roots_subset : roots ⊆ district
  first_domain : first.domain = univ\(F\tips)
  first_starts : first.starts ⊆ tips∪roots
  tips_start : tips ⊆ first.starts
  first_ends : first.ends ⊆ junction
  first_count : first.n ≤ 4*t
  second_domain : second.domain = univ\(F∪roots)
  second_starts : Disjoint second.starts (F∪district∪junction∪first.used)
  second_injective : Function.Injective second.source
  second_ends : second.ends ⊆ junction
  second_count : second.n ≤ 2*t

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t : ℕ}

noncomputable def Round.final {F : Finset V} (R : Round G t F) : Finset V :=
  F∪R.district∪R.junction∪R.first.used∪R.second.used

namespace History

def initial (W : Finset V) (hW : W.card ≤ t) : History G t where
  q := 0
  footprint := fun _ => W
  initial_card := hW
  tips := Fin.elim0
  district := Fin.elim0
  junction := Fin.elim0
  roots := Fin.elim0
  first := Fin.elim0
  second := Fin.elim0
  tips_subset := by intro i; exact Fin.elim0 i
  tips_card := by intro i; exact Fin.elim0 i
  district_card := by intro i; exact Fin.elim0 i
  junction_card := by intro i; exact Fin.elim0 i
  district_disjoint := by intro i; exact Fin.elim0 i
  junction_disjoint := by intro i; exact Fin.elim0 i
  roots_subset := by intro i; exact Fin.elim0 i
  first_domain := by intro i; exact Fin.elim0 i
  first_starts := by intro i; exact Fin.elim0 i
  tips_start := by intro i; exact Fin.elim0 i
  first_ends := by intro i; exact Fin.elim0 i
  first_count := by intro i; exact Fin.elim0 i
  second_domain := by intro i; exact Fin.elim0 i
  second_starts := by intro i; exact Fin.elim0 i
  second_injective := by intro i; exact Fin.elim0 i
  second_ends := by intro i; exact Fin.elim0 i
  second_count := by intro i; exact Fin.elim0 i
  next := by intro i; exact Fin.elim0 i

noncomputable def append (H : History G t) (R : Round G t (H.footprint H.q)) : History G t where
  q := H.q+1
  footprint j := if j ≤ H.q then H.footprint j else R.final
  initial_card := by simpa using H.initial_card
  tips := Fin.lastCases R.tips H.tips
  district := Fin.lastCases R.district H.district
  junction := Fin.lastCases R.junction H.junction
  roots := Fin.lastCases R.roots H.roots
  first := Fin.lastCases R.first H.first
  second := Fin.lastCases R.second H.second
  tips_subset := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.tips_subset
    · simpa [j.isLt.le] using H.tips_subset j
  tips_card := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.tips_card
    · simpa using H.tips_card j
  district_card := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.district_card
    · simpa using H.district_card j
  junction_card := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.junction_card
    · simpa using H.junction_card j
  district_disjoint := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.district_disjoint
    · simpa [j.isLt.le] using H.district_disjoint j
  junction_disjoint := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.junction_disjoint
    · simpa [j.isLt.le] using H.junction_disjoint j
  roots_subset := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.roots_subset
    · simpa using H.roots_subset j
  first_domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_domain
    · simpa [j.isLt.le] using H.first_domain j
  first_starts := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_starts
    · simpa using H.first_starts j
  tips_start := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.tips_start
    · simpa using H.tips_start j
  first_ends := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_ends
    · simpa using H.first_ends j
  first_count := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.first_count
    · simpa using H.first_count j
  second_domain := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_domain
    · simpa [j.isLt.le] using H.second_domain j
  second_starts := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_starts
    · simpa [j.isLt.le] using H.second_starts j
  second_injective := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.lastCases_last]; exact R.second_injective
    · rw [Fin.lastCases_castSucc]; exact H.second_injective j
  second_ends := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_ends
    · simpa using H.second_ends j
  second_count := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using R.second_count
    · simpa using H.second_count j
  next := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [Round.final]
    · simpa [j.isLt.le,Nat.succ_le_iff.mpr j.isLt] using H.next j

end History
end LinearListHadwiger.Footprint

namespace LinearListHadwiger.BagRouting
open Finset SimpleGraph
variable {V I J K : Type} {G : SimpleGraph V} {s : I → V} {B : J → Set V}

def reindex (D : BagRouting G s B) (e : K ≃ I) : BagRouting G (s ∘ e) B where
  paths i := D.paths (e i)
  bag i := D.bag (e i)
  bag_injective := D.bag_injective.comp e.injective
  endpoint_mem i := D.endpoint_mem (e i)
  overlap i j hij := D.overlap (e i) (e j) (fun h => hij (e.injective h))

lemma reindex_totalLength [Fintype I] [Fintype K] (D : BagRouting G s B) (e : K ≃ I) :
    (D.reindex e).totalLength = D.totalLength := by
  exact Equiv.sum_comp e (fun i => (D.paths i).2.val.length)

lemma minimal_reindex [Fintype I] [Fintype K] {D : BagRouting G s B}
    (hD : D.Minimal) (e : K ≃ I) : (D.reindex e).Minimal := by
  intro E
  let F : BagRouting G s B := {
    paths i := ⟨(E.paths (e.symm i)).1,
      ⟨(E.paths (e.symm i)).2.val.copy (by simp) rfl,
        by simpa only [Walk.isPath_copy] using (E.paths (e.symm i)).2.property⟩⟩
    bag i := E.bag (e.symm i)
    bag_injective := E.bag_injective.comp e.symm.injective
    endpoint_mem i := E.endpoint_mem (e.symm i)
    overlap i j hij v hvi hvj := by
      have hh := E.overlap (e.symm i) (e.symm j)
        (fun he => hij (e.symm.injective he)) v
        (by simpa only [Walk.support_copy] using hvi)
        (by simpa only [Walk.support_copy] using hvj)
      simpa using hh }
  rw [reindex_totalLength]
  have hF : F.totalLength = E.totalLength := by
    simpa only [totalLength,F,Walk.length_copy] using
      Equiv.sum_comp e.symm (fun i => (E.paths i).2.val.length)
  exact hF ▸ hD F

lemma minimal_target_only [Fintype I] [DecidableEq I] [DecidableEq V]
    {T : Finset V} {D : BagRouting G s (fun v : ↥T => {v.val})}
    (hD : D.Minimal) (hST : ∀ i, s i ∉ T) (i : I) (v : V)
    (hv : v∈(D.paths i).2.val.support) (hT : v∈T) : v=(D.paths i).1 := by
  classical
  let b : ↥T := ⟨v,hT⟩
  by_cases hb : b∈Set.range D.bag
  · obtain ⟨j,hj⟩ := hb
    have hvj : v=(D.paths j).1 := by
      have hh := D.endpoint_mem j
      simpa only [hj,Set.mem_singleton_iff,b] using hh.symm
    by_cases hij : i=j
    · subst j; exact hvj
    · have hh := D.overlap i j hij v hv (hvj ▸ (D.paths j).2.val.end_mem_support)
      exact (hST i (hh.1 ▸ hT)).elim
  · exact ((not_lt_of_ge (hD (D.truncate i b hb v hv rfl)))
      (D.truncate_length_lt (fun a b hab => Set.disjoint_singleton.mpr
        (fun h => hab (Subtype.ext h))) i b hb v hv rfl)).elim

end LinearListHadwiger.BagRouting

namespace LinearListHadwiger.DoublePacking
variable {V : Type} {G : SimpleGraph V} {A B : Finset V}

def routing (D : DoublePacking G A B) :
    BagRouting G (fun i : ↥A × Bool => i.1.val) (fun b : ↥B => {b.val}) where
  paths i := ⟨(D.target i).val,D.route i⟩
  bag := D.target
  bag_injective := D.target_injective
  endpoint_mem _ := rfl
  overlap := D.overlap

end LinearListHadwiger.DoublePacking

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

structure Segment {V : Type} (G : SimpleGraph V) (A B : Finset V) where
  left : ↥A
  walk : Σ v, G.Path left.val v
  right_mem : walk.1∈B

structure Unpaired {V : Type} (G : SimpleGraph V) (A B : Finset V) (n : ℕ) where
  segment : Fin n → Segment G A B
  disjoint : ∀ i j, i≠j → Disjoint {v | v∈(segment i).walk.2.val.support}
    {v | v∈(segment j).walk.2.val.support}

namespace Unpaired
variable {V : Type} {G : SimpleGraph V} {A B : Finset V} {n : ℕ}

def totalLength (D : Unpaired G A B n) : ℕ := ∑ i, (D.segment i).walk.2.val.length

def Minimal (D : Unpaired G A B n) : Prop := ∀ E : Unpaired G A B n,
  D.totalLength ≤ E.totalLength

lemma source_injective (D : Unpaired G A B n) :
    Function.Injective (fun i => (D.segment i).left) := by
  intro i j hij
  by_contra hne
  exact Set.disjoint_left.mp (D.disjoint i j hne)
    (D.segment i).walk.2.val.start_mem_support
    (by simpa only [hij,Set.mem_ofPred_eq] using (D.segment j).walk.2.val.start_mem_support)

lemma target_injective (D : Unpaired G A B n) :
    Function.Injective (fun i => (D.segment i).walk.1) := by
  intro i j hij
  by_contra hne
  exact Set.disjoint_left.mp (D.disjoint i j hne)
    (D.segment i).walk.2.val.end_mem_support
    (by simpa only [hij,Set.mem_ofPred_eq] using (D.segment j).walk.2.val.end_mem_support)

def replace (D : Unpaired G A B n) (i : Fin n) (P : Segment G A B)
    (hP : ∀ v, v∈P.walk.2.val.support → v∈(D.segment i).walk.2.val.support) :
    Unpaired G A B n where
  segment := Function.update D.segment i P
  disjoint a b hab := by
    apply Set.disjoint_left.mpr
    intro v hva hvb
    have hs (j : Fin n) : {v | v∈(Function.update D.segment i P j).walk.2.val.support} ⊆
        {v | v∈(D.segment j).walk.2.val.support} := by
      by_cases hj : j=i
      · subst j
        rw [Function.update_self]
        exact hP
      · rw [Function.update_of_ne hj]
    exact Set.disjoint_left.mp (D.disjoint a b hab) (hs a hva) (hs b hvb)

def routing (D : Unpaired G A B n) : BagRouting G (fun i => (D.segment i).left.val)
    (fun b : ↥B => {b.val}) where
  paths i := (D.segment i).walk
  bag i := ⟨(D.segment i).walk.1,(D.segment i).right_mem⟩
  bag_injective _ _ h := D.target_injective (congrArg Subtype.val h)
  endpoint_mem _ := rfl
  overlap i j hij _ hvi hvj := (Set.disjoint_left.mp (D.disjoint i j hij) hvi hvj).elim

lemma routing_minimal {D : Unpaired G A B n} (hD : D.Minimal) : D.routing.Minimal := by
  intro E
  let F : Unpaired G A B n := {
    segment := fun i => ⟨(D.segment i).left,E.paths i,
      (E.endpoint_mem i) ▸ (E.bag i).property⟩
    disjoint := by
      intro i j hij
      apply Set.disjoint_left.mpr
      intro v hvi hvj
      have he := E.overlap i j hij v hvi hvj
      exact hij (D.source_injective (Subtype.ext (he.1.symm.trans he.2))) }
  exact hD F

def ofFullPacking {A₀ : Finset V} (P : PathPacking.FullPacking G A₀ B)
    (hA : A₀ ⊆ A) (e : Fin n ≃ ↥A₀) : Unpaired G A B n where
  segment i := ⟨⟨(e i).val,hA (e i).property⟩,⟨(P.target (e i)).val,P.route (e i)⟩,
    (P.target (e i)).property⟩
  disjoint i j hij := P.disjoint (e i) (e j) (fun h => hij (e.injective h))

end Unpaired
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V]

noncomputable def under (U A : Finset V) : Finset ↥(↑U : Set V) :=
  univ.filter (fun v => v.val∈A)

omit [Fintype V] in
@[simp] lemma mem_under {U A : Finset V} (v : ↥(↑U : Set V)) :
    v∈under U A ↔ v.val∈A := by simp [under]

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Footprint.System
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V I : Type} [DecidableEq V] [Fintype I] {G : SimpleGraph V}

noncomputable def ofMinimal (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) : System G where
  domain := U
  n := Fintype.card I
  source := s ∘ (Fintype.equivFin I).symm
  target := T
  routes := D.reindex (Fintype.equivFin I).symm
  minimal := BagRouting.minimal_reindex hD _

lemma ofMinimal_starts (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) :
    (ofMinimal U s T D hD).starts=univ.image (fun i => (s i).val) := by
  change univ.image (fun i : Fin (Fintype.card I) => (s ((Fintype.equivFin I).symm i)).val) = _
  ext v
  simp only [mem_image,mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩; exact ⟨_,hi⟩
  · rintro ⟨i,hi⟩; exact ⟨Fintype.equivFin I i,by simpa using hi⟩

lemma ofMinimal_ends (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) : (ofMinimal U s T D hD).ends ⊆ T.image Subtype.val := by
  rintro v hv
  obtain ⟨i,_,rfl⟩ := mem_image.mp hv
  have he := D.endpoint_mem ((Fintype.equivFin I).symm i)
  exact mem_image.mpr ⟨_,(D.bag _).property,congrArg Subtype.val he.symm⟩

lemma ofMinimal_injective (U : Finset V) (s : I → ↥(↑U : Set V))
    (T : Finset ↥(↑U : Set V))
    (D : BagRouting (G.induce (↑U : Set V)) s (fun b : ↥T => {b.val}))
    (hD : D.Minimal) (hs : Function.Injective s) :
    Function.Injective (ofMinimal U s T D hD).source :=
  hs.comp (Fintype.equivFin I).symm.injective

noncomputable def route (S : System G) (i : Fin S.n) :
    G.Path (S.source i).val (S.routes.paths i).1.val :=
  ⟨(S.routes.paths i).2.val.map ⟨Subtype.val,fun h => h⟩,
    (S.routes.paths i).2.property.map Subtype.val_injective⟩

noncomputable def empty (U : Finset V) : System G where
  domain := U
  n := 0
  source := Fin.elim0
  target := ∅
  routes := {
    paths := by intro i; exact Fin.elim0 i
    bag := Fin.elim0
    bag_injective := by intro i; exact Fin.elim0 i
    endpoint_mem := by intro i; exact Fin.elim0 i
    overlap := by intro i; exact Fin.elim0 i }
  minimal := by intro E; simp [BagRouting.totalLength]

@[simp] lemma empty_starts (U : Finset V) : (empty (G:=G) U).starts=∅ := by
  ext v
  simp only [starts,mem_image,Finset.notMem_empty,iff_false]
  rintro ⟨i,_,_⟩
  exact Fin.elim0 i

@[simp] lemma empty_ends (U : Finset V) : (empty (G:=G) U).ends=∅ := by
  ext v
  simp only [ends,mem_image,Finset.notMem_empty,iff_false]
  rintro ⟨i,_,_⟩
  exact Fin.elim0 i

end LinearListHadwiger.Footprint.System

namespace LinearListHadwiger.DoublePacking
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {A B : Finset V}

noncomputable def ofMinimal
    (D : BagRouting G (fun i : ↥A×Bool => i.1.val) (fun b : ↥B => {b.val}))
    (hD : D.Minimal) (hAB : Disjoint A B) : DoublePacking G A B where
  target := D.bag
  target_injective := D.bag_injective
  route i := ⟨(D.paths i).2.val.copy rfl (Set.mem_singleton_iff.mp (D.endpoint_mem i)),
    by rw [SimpleGraph.Walk.isPath_copy]; exact (D.paths i).2.property⟩
  source_only i v hv ha := by
    rw [SimpleGraph.Walk.support_copy] at hv
    by_contra hn
    let j : ↥A×Bool := (⟨v,ha⟩,false)
    have hij : i≠j := fun he => hn (congrArg (fun x : ↥A×Bool => x.1.val) he).symm
    exact hn (D.overlap i j hij v hv (D.paths j).2.val.start_mem_support).1
  target_only i v hv hb := by
    rw [SimpleGraph.Walk.support_copy] at hv
    exact (BagRouting.minimal_target_only hD
      (fun i hi => Finset.disjoint_left.mp hAB i.1.property hi) i v hv hb).trans (Set.mem_singleton_iff.mp (D.endpoint_mem i))
  overlap i j hij v hv hw := by
    rw [SimpleGraph.Walk.support_copy] at hv hw
    exact D.overlap i j hij v hv hw

@[simp] lemma ofMinimal_support
    (D : BagRouting G (fun i : ↥A×Bool => i.1.val) (fun b : ↥B => {b.val}))
    (hD : D.Minimal) (hAB : Disjoint A B) (i : ↥A×Bool) :
    ((ofMinimal D hD hAB).route i).val.support=(D.paths i).2.val.support := by
  simp only [ofMinimal,SimpleGraph.Walk.support_copy]

def liftIndex {U A : Finset V} (hA : A⊆U) (i : ↥A×Bool) : ↥(Stage.under U A)×Bool :=
  (⟨⟨i.1.val,hA i.1.property⟩,Stage.mem_under _ |>.mpr i.1.property⟩,i.2)

lemma liftIndex_injective {U A : Finset V} (hA : A⊆U) :
    Function.Injective (liftIndex hA) := by
  intro i j he
  apply Prod.ext
  · exact Subtype.ext (congrArg (fun x : ↥(Stage.under U A)×Bool => x.1.val.val) he)
  · exact congrArg (fun x : ↥(Stage.under U A)×Bool => x.2) he

noncomputable def lift {U A B : Finset V} (hA : A⊆U) (_hB : B⊆U)
    (P : DoublePacking (G.induce (↑U : Set V)) (Stage.under U A) (Stage.under U B)) :
    DoublePacking G A B where
  target i := ⟨(P.target (liftIndex hA i)).val.val,
    (Stage.mem_under _).mp (P.target (liftIndex hA i)).property⟩
  target_injective := by
    intro i j he
    apply liftIndex_injective hA
    apply P.target_injective
    have hh : (P.target (liftIndex hA i)).val.val = (P.target (liftIndex hA j)).val.val :=
      congrArg (fun x : ↥B => x.val) he
    exact Subtype.ext (Subtype.ext hh)
  route i := ⟨(P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩,
    (P.route (liftIndex hA i)).property.map Subtype.val_injective⟩
  source_only i v hv ha := by
    change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hv
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact congrArg Subtype.val (P.source_only _ w hw ((Stage.mem_under _).mpr ha))
  target_only i v hv hb := by
    change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hv
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    exact congrArg Subtype.val (P.target_only _ w hw ((Stage.mem_under _).mpr hb))
  overlap i j hij v hv hw := by
    change v∈((P.route (liftIndex hA i)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hv
    change v∈((P.route (liftIndex hA j)).val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩).support at hw
    rw [SimpleGraph.Walk.support_map,List.mem_map] at hv hw
    obtain ⟨a,ha,rfl⟩ := hv
    obtain ⟨b,hb,he⟩ := hw
    have hab : b=a := Subtype.ext he
    subst b
    have hh := P.overlap _ _ (fun he => hij (liftIndex_injective hA he)) a ha hb
    exact ⟨congrArg Subtype.val hh.1,congrArg Subtype.val hh.2⟩

end LinearListHadwiger.DoublePacking

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageDeletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset SimpleGraph Footprint
attribute [local instance] Classical.propDecidable

structure Second {V : Type} [DecidableEq V] (G : SimpleGraph V)
    (U H D : Finset V) (n : ℕ) where
  sys : Unpaired (G.induce (↑U : Set V)) (under U H) (under U D) n
  minimal : sys.Minimal

namespace Second
variable {V : Type} [DecidableEq V] {G : SimpleGraph V} {U H D : Finset V} {n : ℕ}

noncomputable def record (Q : Second G U H D n) : System G :=
  System.ofMinimal U (fun i => (Q.sys.segment i).left.val) (under U D)
    Q.sys.routing (Unpaired.routing_minimal Q.minimal)

def source (Q : Second G U H D n) (i : Fin n) : V := (Q.sys.segment i).left.val.val

def target (Q : Second G U H D n) (i : Fin n) : ↥D :=
  ⟨(Q.sys.segment i).walk.1.val,(mem_under _).mp (Q.sys.segment i).right_mem⟩

noncomputable def route (Q : Second G U H D n) (i : Fin n) :
    G.Path (Q.source i) (Q.target i).val :=
  ⟨(Q.sys.segment i).walk.2.val.map ⟨Subtype.val,fun h => SimpleGraph.induce_adj.mp h⟩,
    (Q.sys.segment i).walk.2.property.map Subtype.val_injective⟩

lemma source_mem (Q : Second G U H D n) (i : Fin n) : Q.source i∈H :=
  (mem_under _).mp (Q.sys.segment i).left.property

lemma source_injective (Q : Second G U H D n) : Function.Injective Q.source := by
  intro i j he
  exact Q.sys.source_injective (Subtype.ext (Subtype.ext he))

@[simp] lemma record_domain (Q : Second G U H D n) : Q.record.domain=U := rfl
@[simp] lemma record_count (Q : Second G U H D n) : Q.record.n=n := by
  simp only [record,System.ofMinimal,Fintype.card_fin]

lemma record_starts (Q : Second G U H D n) : Q.record.starts=univ.image Q.source :=
  System.ofMinimal_starts _ _ _ _ _

lemma record_source_injective (Q : Second G U H D n) :
    Function.Injective Q.record.source := by
  apply System.ofMinimal_injective
  intro i j he
  exact Q.sys.source_injective (Subtype.ext he)

lemma record_ends (Q : Second G U H D n) : Q.record.ends⊆D := by
  intro v hv
  have hh := System.ofMinimal_ends U _ _ Q.sys.routing (Unpaired.routing_minimal Q.minimal) hv
  obtain ⟨w,hw,rfl⟩ := mem_image.mp hh
  exact (mem_under _).mp hw

end Second
end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

abbrev Roles (t a : ℕ) := Fin t ⊕ (Fin a ⊕ Fin t)

def roleOwner {t a : ℕ} (label : Fin a → Fin t) : Roles t a → Fin t :=
  Sum.elim id (Sum.elim label id)

def roleStart {V : Type} {t a : ℕ} (w : Fin t → V) (u : Fin a → V)
    (w' : Fin t → V) : Roles t a → V := Sum.elim w (Sum.elim u w')

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

variable {V : Type} [DecidableEq V] {t a : ℕ}

noncomputable def oldSources (w : Fin t → V) (u : Fin a → V) : Finset V :=
  univ.image w ∪ univ.image u

@[simp] lemma mem_oldSources (w : Fin t → V) (u : Fin a → V) (v : V) :
    v∈oldSources w u ↔ (∃ i, w i=v) ∨ ∃ j, u j=v := by
  simp [oldSources]

noncomputable def roleTo (w : Fin t → V) (u : Fin a → V) : Roles t a → (↥(oldSources w u)⊕Fin t)
  | .inl i => .inl ⟨w i,(mem_oldSources w u _).mpr (Or.inl ⟨i,rfl⟩)⟩
  | .inr (.inl j) => .inl ⟨u j,(mem_oldSources w u _).mpr (Or.inr ⟨j,rfl⟩)⟩
  | .inr (.inr i) => .inr i

lemma roleTo_bijective (w : Fin t → V) (u : Fin a → V)
    (hw : Function.Injective w) (hu : Function.Injective u) (hwu : ∀ i j, w i≠u j) :
    Function.Bijective (roleTo w u) := by
  constructor
  · rintro (i|j|i) (i'|j'|i') he
    · exact congrArg Sum.inl (hw (congrArg Subtype.val (Sum.inl.inj he)))
    · exact (hwu i j' (congrArg Subtype.val (Sum.inl.inj he))).elim
    · cases he
    · exact (hwu i' j (congrArg Subtype.val (Sum.inl.inj he)).symm).elim
    · exact congrArg (Sum.inr ∘ Sum.inl) (hu (congrArg Subtype.val (Sum.inl.inj he)))
    · cases he
    · cases he
    · cases he
    · exact congrArg (Sum.inr ∘ Sum.inr) (Sum.inr.inj he)
  · rintro (z|i)
    · rcases (mem_oldSources w u z.val).mp z.property with ⟨i,hi⟩|⟨j,hj⟩
      · exact ⟨Sum.inl i,congrArg Sum.inl (Subtype.ext hi)⟩
      · exact ⟨Sum.inr (Sum.inl j),congrArg Sum.inl (Subtype.ext hj)⟩
    · exact ⟨Sum.inr (Sum.inr i),rfl⟩

noncomputable def roleEquiv (w : Fin t → V) (u : Fin a → V)
    (hw : Function.Injective w) (hu : Function.Injective u) (hwu : ∀ i j, w i≠u j) :
    Roles t a ≃ (↥(oldSources w u)⊕Fin t) := Equiv.ofBijective _ (roleTo_bijective w u hw hu hwu)

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RoleRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open SimpleGraph Finset
attribute [local instance] Classical.propDecidable

structure RoleRouting {V : Type} (G : SimpleGraph V) {t a : ℕ}
    (w : Fin t → V) (u : Fin a → V) (F H : Set V) (D : Finset V) (U : Set V) where
  fresh : Fin t → V
  fresh_injective : Function.Injective fresh
  fresh_mem : ∀ i, fresh i∈H
  target : Roles t a → ↥D
  route : ∀ p, G.Path (roleStart w u fresh p) (target p).val
  disjoint : ∀ p q, p≠q → Disjoint {v | v∈(route p).val.support} {v | v∈(route q).val.support}
  old_only : ∀ p v, v∈(route p).val.support → v∈F → ∃ i, p=Sum.inl i ∧ v=w i
  new_only : ∀ p v, v∈(route p).val.support → v∈H → ∃ i, p=Sum.inr (Sum.inr i) ∧ v=fresh i
  root_only : ∀ p j, u j∈(route p).val.support → u j=roleStart w u fresh p
  target_only : ∀ p v, v∈(route p).val.support → v∈D → v=(target p).val
  inside : ∀ p v, v∈(route p).val.support → v∈U

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset SimpleGraph
attribute [local instance] Classical.propDecidable

def attached {V P : Type} {G : SimpleGraph V} (C : P → Set V)
    (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (p : P) : Set V :=
  C p ∪ {v | v∈(paths p).val.support}

def extended {V P I : Type} {G : SimpleGraph V} (E : I → Set V) (C : P → Set V)
    (owner : P → I) (x y : P → V) (paths : ∀ p, G.Path (x p) (y p)) (i : I) : Set V :=
  E i ∪ {v | ∃ p, owner p=i ∧ v∈attached C x y paths p}

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.PaletteSampling
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Sampling
open Finset ConnectivityTests
variable {V Ω : Type} [Fintype V] [DecidableEq V] [Fintype Ω]

noncomputable def coin (p : ℝ) (b : Bool) : ℝ := if b then p else 1-p

noncomputable def chosen (x : V → Bool) : Finset V := univ.filter (fun v => x v = true)

open Filter

end LinearListHadwiger.Sampling

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageAdvance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

abbrev K₀ : ℕ := 100000*65536
abbrev cf : ℕ := 4*32768+6*3202+25
abbrev ch : ℕ := cf+6*(K₀+1)+2

def Inseparable {V : Type} [DecidableEq V] (G : SimpleGraph V) (r b : ℕ) : Prop :=
  ∀ A B : Finset V, Disjoint A B → r ≤ ell G A+b → r ≤ ell G B+b → False

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable

structure State {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (t r : ℕ) where
  history : History G t
  bag : Fin t → Set V
  tip : Fin t → V
  connected : ∀ i, (G.induce (bag i)).Connected
  disjoint : ∀ i j, i≠j → Disjoint (bag i) (bag j)
  inside : ∀ i, bag i⊆(↑(history.footprint history.q) : Set V)
  tip_mem : ∀ i, tip i∈bag i
  tip_injective : Function.Injective tip
  region : Finset V
  region_conn : KConnectedOn G region (K₀*t)
  region_list : r≤ell G region+ch*t
  intersection : region∩history.footprint history.q=univ.image tip

variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t r : ℕ}

namespace State

lemma tip_footprint (A : State G t r) (i : Fin t) : A.tip i∈A.history.footprint A.history.q :=
  A.inside i (A.tip_mem i)

end State

noncomputable def firstRound (A : State G t r) (J D : Finset V)
    (hJ : (J.card:ℝ)≤(t:ℝ)^(53/50:ℝ)) (hD : (D.card:ℝ)≤(t:ℝ)^(53/50:ℝ))
    (hJF : Disjoint J (A.history.footprint A.history.q))
    (hDFJ : Disjoint D (A.history.footprint A.history.q∪J))
    {a : ℕ} (u : Fin a → V) (huJ : ∀ j, u j∈J)
    (R : System G) (hRU : R.domain=univ\(A.history.footprint A.history.q\univ.image A.tip))
    (hRS : R.starts=oldSources A.tip u) (hRE : R.ends⊆D) (hRn : R.n≤4*t) :
    Round G t (A.history.footprint A.history.q) where
  tips := univ.image A.tip
  district := J
  junction := D
  roots := univ.image u
  first := R
  second := System.empty (univ\(A.history.footprint A.history.q∪univ.image u))
  tips_subset := by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact A.tip_footprint i
  tips_card := by simp only [card_image_of_injective _ A.tip_injective,card_univ,Fintype.card_fin,le_refl]
  district_card := by simpa only [show (106/100:ℝ)=53/50 by norm_num] using hJ
  junction_card := by simpa only [show (106/100:ℝ)=53/50 by norm_num] using hD
  district_disjoint := hJF
  junction_disjoint := hDFJ
  roots_subset := by rintro v hv; obtain ⟨i,hi,rfl⟩ := mem_image.mp hv; exact huJ i
  first_domain := hRU
  first_starts := by rw [hRS]; exact subset_refl _
  tips_start := by rw [hRS]; exact subset_union_left
  first_ends := hRE
  first_count := hRn
  second_domain := rfl
  second_starts := by simp
  second_injective := by intro i; exact Fin.elim0 i
  second_ends := by simp
  second_count := Nat.zero_le _

end LinearListHadwiger.Stage

namespace LinearListHadwiger.Stage
open Finset Footprint SmallList
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {t r : ℕ}

noncomputable def completeRound {F H : Finset V} (R : Round G t F)
    (Q : Second G (univ\(F∪R.roots)) H R.junction (2*t))
    (hH : Disjoint H (F∪R.district∪R.junction∪R.first.used)) : Round G t F :=
  { R with
    second := Q.record
    second_domain := Q.record_domain
    second_starts := by
      apply hH.mono_left
      intro v hv
      rw [Q.record_starts] at hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
      exact Q.source_mem i
    second_injective := Q.record_source_injective
    second_ends := Q.record_ends
    second_count := (Q.record_count).le }

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.StageSeparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Stage
open Finset Filter
attribute [local instance] Classical.propDecidable

def block (t m : ℕ) (b : Fin m) : Finset (Fin t) :=
  univ.filter (fun i => i.val % m=b.val)

noncomputable def roundSet (t m : ℕ) : Sym2 (Fin m) → Finset (Fin t) :=
  Sym2.lift ⟨fun b c => block t m b∪block t m c,fun b c => union_comm (block t m b) (block t m c)⟩

end LinearListHadwiger.Stage

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.RecursiveDistricts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace LinearListHadwiger.Recursion
open Finset
attribute [local instance] Classical.propDecidable

def child (a : ℕ) : ℕ := 2*((a+2)/3)

def triBlock {a : ℕ} (i : Fin a) : Fin 3 := ⟨i.val%3,Nat.mod_lt _ (by decide)⟩

def district {a : ℕ} (o : Fin a × Fin 2) : Fin 3 := (triBlock o.1).succAbove o.2

def districtLabels (a : ℕ) (d : Fin 3) : Finset (Fin a) :=
  univ.filter (fun i => triBlock i≠d)

end LinearListHadwiger.Recursion

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.EggCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ReedSeymour
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

def Shortest {a b : V} (p : G.Walk a b) : Prop :=
  ∀ q : G.Walk a b, p.length ≤ q.length

def ReachOn (G : SimpleGraph V) (S : Set V) (a b : V) : Prop :=
  ∃ p : G.Walk a b, ∀ x ∈ p.support, x ∈ S

lemma ReachOn.symm {S : Set V} {a b : V} (h : ReachOn G S a b) : ReachOn G S b a := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p.reverse, by simpa using hp⟩
lemma ReachOn.trans {S : Set V} {a b c : V} (h : ReachOn G S a b)
    (h' : ReachOn G S b c) : ReachOn G S a c := by
  obtain ⟨p, hp⟩ := h
  obtain ⟨q, hq⟩ := h'
  exact ⟨p.append q, fun x hx => (Walk.mem_support_append_iff p q).mp hx |>.elim
    (hp x) (hq x)⟩
lemma ReachOn.mono {S T : Set V} {a b : V} (h : ReachOn G S a b) (hst : S ⊆ T) :
    ReachOn G T a b := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p, fun x hx => hst (hp x hx)⟩
lemma ReachOn.adj {S : Set V} {a b : V} (ha : a ∈ S) (hb : b ∈ S)
    (hab : G.Adj a b) : ReachOn G S a b :=
  ⟨hab.toWalk, by simpa using (show a ∈ S ∧ b ∈ S from ⟨ha,hb⟩)⟩

lemma connected_iff_reachOn {S : Set V} :
    (G.induce S).Connected ↔ S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, ReachOn G S a b := by
  constructor
  · intro h
    refine ⟨by obtain ⟨a, ha⟩ := Classical.choice h.nonempty; exact ⟨a,ha⟩, ?_⟩
    intro a ha b hb
    obtain ⟨p⟩ := h ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨p.map (SimpleGraph.Embedding.induce S).toHom, ?_⟩
    intro x hx
    have hh : x ∈ p.support.map (SimpleGraph.Embedding.induce S).toHom :=
      (Walk.support_map ..) ▸ hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hh
    exact y.property
  · rintro ⟨hne, h⟩
    refine { preconnected := ?_, nonempty := hne.to_subtype }
    intro a b
    obtain ⟨p, hp⟩ := h a a.property b b.property
    exact ⟨p.induce S hp⟩

lemma connected_reachOn {S : Set V} (h : (G.induce S).Connected)
    {a b : V} (ha : a ∈ S) (hb : b ∈ S) : ReachOn G S a b :=
  (connected_iff_reachOn.mp h).2 a ha b hb

def component (G : SimpleGraph V) (S : Set V) (a : V) : Set V :=
  {b | ReachOn G S a b}

structure BetweenMin (G : SimpleGraph V) (A B : Set V) (a b : V) (p : G.Walk a b) : Prop where
  source : a ∈ A
  target : b ∈ B
  minimal : ∀ x ∈ A, ∀ y ∈ B, ∀ q : G.Walk x y, p.length ≤ q.length

structure MinimalConnector {ι : Type*} (G : SimpleGraph V) (N : ι → Set V) : Prop where
  connected : G.Connected
  interfaces : ∀ i, (N i).Nonempty
  minimal : ∀ S : Set V, (G.induce S).Connected → S ≠ Set.univ →
    ∃ i, Disjoint S (N i)

def Gate (G : SimpleGraph V) (N C : Set V) (v : V) : Prop :=
  ∀ a ∈ N, ∀ b ∈ C, ¬ReachOn G {x | x ≠ v} a b

structure Tail {ι : Type*} (G : SimpleGraph V) (N : ι → Set V) (C : Set V) (v : V) where
  index : ι
  start : V
  path : G.Walk start v
  minimum : BetweenMin G (N index) C start v path
  gate : Gate G (N index) C v

structure SplitConnector {ι : Type*} (G : SimpleGraph V) (N : ι → Set V) where
  left : ι
  right : ι
  distinct : left ≠ right
  carrier : Set V
  connected : (G.induce carrier).Connected
  color : V → Fin 2
  proper : ∀ x ∈ carrier, ∀ y ∈ carrier, G.Adj x y → color x ≠ color y
  meets_left : (carrier ∩ N left).Nonempty
  meets_right : (carrier ∩ N right).Nonempty
  left_color : ∀ x ∈ carrier, x ∈ N left → color x = 0
  right_color : ∀ x ∈ carrier, x ∈ N right → color x = 1

def parity (n : ℕ) : Fin 2 := ⟨n % 2, Nat.mod_lt _ (by decide)⟩

lemma connected_union_of_adj {A B : Set V} (hA : (G.induce A).Connected)
    (hB : (G.induce B).Connected) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (hab : G.Adj a b) : (G.induce (A ∪ B)).Connected := by
  have hr : ∀ x ∈ A ∪ B, ReachOn G (A ∪ B) a x := by
    intro x hx
    rcases hx with hx | hx
    · exact (connected_reachOn hA ha hx).mono Set.subset_union_left
    · exact (ReachOn.adj (G := G) (S := A ∪ B) (Or.inl ha) (Or.inr hb) hab).trans
        ((connected_reachOn hB hb hx).mono Set.subset_union_right)
  exact connected_iff_reachOn.mpr ⟨⟨a,Or.inl ha⟩, fun x hx y hy => (hr x hx).symm.trans (hr y hy)⟩

noncomputable def extendColor (U : Set V) (c : U → Fin 2) (x : V) : Fin 2 := by
  classical
  exact if hx : x ∈ U then c ⟨x,hx⟩ else 0

lemma extendColor_apply {U : Set V} (c : U → Fin 2) {x : V} (hx : x ∈ U) :
    extendColor U c x = c ⟨x,hx⟩ := by simp [extendColor, hx]

lemma connected_image_val {U : Set V} {S : Set U}
    (h : ((G.induce U).induce S).Connected) :
    (G.induce (Subtype.val '' S)).Connected := by
  obtain ⟨hne, hc⟩ := connected_iff_reachOn.mp h
  refine connected_iff_reachOn.mpr ⟨hne.image _, ?_⟩
  rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
  obtain ⟨p,hp⟩ := hc a ha b hb
  refine ⟨p.map (Embedding.induce U).toHom, ?_⟩
  intro x hx
  have hh : x ∈ p.support.map (Embedding.induce U).toHom := (Walk.support_map ..) ▸ hx
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hh
  exact ⟨z,hp z hz,rfl⟩

noncomputable def SplitConnector.lift {ι : Type*} {U : Set V} {N : ι → Set V}
    (s : SplitConnector (G.induce U) (fun i => {x | x.val ∈ N i})) :
    SplitConnector G N where
  left := s.left
  right := s.right
  distinct := s.distinct
  carrier := Subtype.val '' s.carrier
  connected := connected_image_val s.connected
  color := extendColor U s.color
  proper := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩ hxy
    simpa only [extendColor_apply s.color a.property, extendColor_apply s.color b.property] using
      s.proper a ha b hb hxy
  meets_left := by
    obtain ⟨a,ha,hn⟩ := s.meets_left
    exact ⟨a,⟨a,ha,rfl⟩,hn⟩
  meets_right := by
    obtain ⟨a,ha,hn⟩ := s.meets_right
    exact ⟨a,⟨a,ha,rfl⟩,hn⟩
  left_color := by
    rintro x ⟨a,ha,rfl⟩ hn
    simpa only [extendColor_apply s.color a.property] using s.left_color a ha hn
  right_color := by
    rintro x ⟨a,ha,rfl⟩ hn
    simpa only [extendColor_apply s.color a.property] using s.right_color a ha hn

def Touch (G : SimpleGraph V) (A B : Set V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, G.Adj a b

lemma Touch.symm {A B : Set V} (h : Touch G A B) : Touch G B A := by
  obtain ⟨a,ha,b,hb,hab⟩ := h
  exact ⟨b,hb,a,ha,hab.symm⟩

lemma Touch.mono {A B A' B' : Set V} (h : Touch G A B) (hA : A ⊆ A') (hB : B ⊆ B') :
    Touch G A' B' := by
  obtain ⟨a,ha,b,hb,hab⟩ := h
  exact ⟨a,hA ha,b,hB hb,hab⟩

lemma Touch.left_nonempty {A B : Set V} (h : Touch G A B) : A.Nonempty := by
  obtain ⟨a,ha,_,_,_⟩ := h
  exact ⟨a,ha⟩

lemma Touch.right_nonempty {A B : Set V} (h : Touch G A B) : B.Nonempty := h.symm.left_nonempty

lemma touch_union_left {A B C : Set V} : Touch G (A ∪ B) C ↔ Touch G A C ∨ Touch G B C := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact ha.elim (fun ha => Or.inl ⟨a,ha,b,hb,hab⟩) (fun ha => Or.inr ⟨a,ha,b,hb,hab⟩)
  · rintro (⟨a,ha,b,hb,hab⟩ | ⟨a,ha,b,hb,hab⟩)
    · exact ⟨a,Or.inl ha,b,hb,hab⟩
    · exact ⟨a,Or.inr ha,b,hb,hab⟩

lemma touch_union_right {A B C : Set V} : Touch G A (B ∪ C) ↔ Touch G A B ∨ Touch G A C := by
  constructor
  · rintro ⟨a,ha,b,hb,hab⟩
    exact hb.elim (fun hb => Or.inl ⟨a,ha,b,hb,hab⟩) (fun hb => Or.inr ⟨a,ha,b,hb,hab⟩)
  · rintro (⟨a,ha,b,hb,hab⟩ | ⟨a,ha,b,hb,hab⟩)
    · exact ⟨a,ha,b,Or.inl hb,hab⟩
    · exact ⟨a,ha,b,Or.inr hb,hab⟩

lemma connected_union_of_touch {A B : Set V} (hA : (G.induce A).Connected)
    (hB : (G.induce B).Connected) (ht : Touch G A B) : (G.induce (A ∪ B)).Connected := by
  obtain ⟨a,ha,b,hb,hab⟩ := ht
  exact connected_union_of_adj hA hB ha hb hab

def Independent (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ¬G.Adj a b

lemma independent_empty : Independent G ∅ := by simp [Independent]

lemma Independent.mono {S T : Set V} (h : Independent G T) (hst : S ⊆ T) :
    Independent G S := fun a ha b hb => h a (hst ha) b (hst hb)

lemma independent_union {S T : Set V} (hS : Independent G S) (hT : Independent G T)
    (hnt : ¬Touch G S T) : Independent G (S ∪ T) := by
  intro a ha b hb hab
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact hS a ha b hb hab
  · exact hnt ⟨a,ha,b,hb,hab⟩
  · exact hnt ⟨b,hb,a,ha,hab.symm⟩
  · exact hT a ha b hb hab

end ReedSeymour

end OAI
end

section
-- module Solutions.OAIQW_ListHadwiger.WeightedBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ReedSeymour
open SimpleGraph
universe u
variable {V : Type u} {G : SimpleGraph V}

section Weights
variable [Fintype V]

noncomputable def mass (w : V → ℝ) (S : Set V) : ℝ := by
  classical
  exact ∑ v, if v ∈ S then w v else 0

lemma mass_empty (w : V → ℝ) : mass w ∅ = 0 := by simp [mass]

lemma mass_union {w : V → ℝ} {S T : Set V} (h : Disjoint S T) :
    mass w (S ∪ T) = mass w S + mass w T := by
  classical
  unfold mass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  have hh : ¬(v ∈ S ∧ v ∈ T) := fun hv => Set.disjoint_left.mp h hv.1 hv.2
  by_cases hs : v ∈ S <;> by_cases ht : v ∈ T <;> simp_all

def Outside (B : V → Set V) : Set V := {x | ∀ i, x ∉ B i}

structure EggCover (G : SimpleGraph V) (w : V → ℝ) (k : ℕ) where
  bag : V → Set V
  yolk : V → Set V
  color : V → Fin k
  root : ∀ i, (bag i).Nonempty → i ∈ bag i
  connected : ∀ i, (bag i).Nonempty → (G.induce (bag i)).Connected
  disjoint : ∀ i j, i ≠ j → Disjoint (bag i) (bag j)
  yolk_subset : ∀ i, yolk i ⊆ bag i
  stable : ∀ i, Independent G (yolk i)
  half : ∀ i, mass w (bag i) ≤ 2 * mass w (yolk i)
  proper : ∀ i j, i ≠ j → Touch G (bag i) (bag j) → color i ≠ color j
  frontier : ∀ X : Set V, X ⊆ Outside bag → (G.induce X).Connected →
    ∀ i j, i ≠ j → Touch G X (bag i) → Touch G X (bag j) → Touch G (bag i) (bag j)

noncomputable def EggCover.empty (G : SimpleGraph V) (w : V → ℝ) {k : ℕ} (hk : 0 < k) :
    EggCover G w k where
  bag := fun _ => ∅
  yolk := fun _ => ∅
  color := fun _ => ⟨0,hk⟩
  root := by simp
  connected := by simp
  disjoint := by simp
  yolk_subset := by simp
  stable := fun _ => independent_empty
  half := by simp [mass_empty]
  proper := by simp [Touch]
  frontier := by simp [Touch]

lemma EggCover.outside_disjoint {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    {S : Set V} (hS : S ⊆ Outside P.bag) (i : V) : Disjoint S (P.bag i) := by
  exact Set.disjoint_left.mpr (fun x hx hi => hS hx i hi)

structure Region {w : V → ℝ} {k : ℕ} (P : EggCover G w k) (X : Set V) : Prop where
  subset : X ⊆ Outside P.bag
  connected : (G.induce X).Connected
  closed : ∀ x ∈ X, ∀ y ∈ Outside P.bag, G.Adj x y → y ∈ X

lemma ReachOn.stays {V : Type u} {G : SimpleGraph V} [Fintype V] {R X : Set V} {a b : V} (h : ReachOn G R a b) (ha : a ∈ X)
    (hstep : ∀ x ∈ X, ∀ y ∈ R, G.Adj x y → y ∈ X) : b ∈ X := by
  obtain ⟨p,hp⟩ := h
  induction p with
  | nil => exact ha
  | @cons a c b hac p ih =>
    apply ih
    · exact hstep a ha c (hp c (by simp)) hac
    · exact fun x hx => hp x (by simp [hx])

lemma Region.contains_connected {w : V → ℝ} {k : ℕ} {P : EggCover G w k}
    {X D : Set V} (hX : Region P X) (hD : D ⊆ Outside P.bag)
    (hc : (G.induce D).Connected) (hinter : (D ∩ X).Nonempty) : D ⊆ X := by
  obtain ⟨a,haD,haX⟩ := hinter
  intro b hb
  exact ((connected_reachOn hc haD hb).mono hD).stays haX hX.closed

lemma Region.contains_of_touch {w : V → ℝ} {k : ℕ} {P : EggCover G w k}
    {X D Q : Set V} (hX : Region P X) (hD : D ⊆ Outside P.bag)
    (hc : (G.induce D).Connected) (hQ : Q ⊆ X) (ht : Touch G D Q) : D ⊆ X := by
  obtain ⟨a,ha,b,hb,hab⟩ := ht
  exact hX.contains_connected hD hc ⟨a,ha,hX.closed b (hQ hb) a (hD ha) hab.symm⟩

lemma outside_update_subset {V : Type u} [Fintype V] [DecidableEq V] {B : V → Set V} {i : V} {S : Set V}
    (hi : B i ⊆ S) : Outside (Function.update B i S) ⊆ Outside B := by
  intro x hx j
  by_cases hj : j = i
  · subst j
    intro hm
    have hh := hx i
    simp only [Function.update_self] at hh
    exact hh (hi hm)
  · have hh := hx j
    simpa only [Function.update_of_ne hj] using hh

noncomputable def EggCover.replace [DecidableEq V] {w : V → ℝ} {k : ℕ} (P : EggCover G w k)
    (i : V) (B Y : Set V) (c : Fin k) (hinc : P.bag i ⊆ B)
    (hroot : B.Nonempty → i ∈ B) (hconn : (G.induce B).Connected)
    (hdisj : ∀ j, j ≠ i → Disjoint B (P.bag j))
    (hY : Y ⊆ B) (hstable : Independent G Y) (hhalf : mass w B ≤ 2 * mass w Y)
    (hproper : ∀ j, i ≠ j → Touch G B (P.bag j) → c ≠ P.color j)
    (hfront : ∀ D : Set V, D ⊆ Outside (Function.update P.bag i B) →
      (G.induce D).Connected → ∀ j, i ≠ j →
      Touch G D B → Touch G D (P.bag j) → Touch G B (P.bag j)) : EggCover G w k := by
  classical
  refine {
    bag := Function.update P.bag i B
    yolk := Function.update P.yolk i Y
    color := Function.update P.color i c
    root := ?_
    connected := ?_
    disjoint := ?_
    yolk_subset := ?_
    stable := ?_
    half := ?_
    proper := ?_
    frontier := ?_ }
  · intro j hj
    by_cases he : j = i
    · subst j; simpa using hroot (by simpa using hj)
    · simpa [Function.update_of_ne he] using P.root j (by simpa [Function.update_of_ne he] using hj)
  · intro j hj
    by_cases he : j = i
    · subst j
      rw [Function.update_self]
      exact hconn
    · rw [Function.update_of_ne he]
      exact P.connected j (by simpa [Function.update_of_ne he] using hj)
  · intro a b hab
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact (hab (ha.trans hb.symm)).elim
    · subst a; simpa [Function.update_of_ne hb] using hdisj b hb
    · subst b; simpa [Function.update_of_ne ha] using (hdisj a ha).symm
    · simpa [Function.update_of_ne ha,Function.update_of_ne hb] using P.disjoint a b hab
  · intro j
    by_cases he : j = i
    · subst j; simpa using hY
    · simpa [Function.update_of_ne he] using P.yolk_subset j
  · intro j
    by_cases he : j = i
    · subst j; simpa using hstable
    · simpa [Function.update_of_ne he] using P.stable j
  · intro j
    by_cases he : j = i
    · subst j; simpa using hhalf
    · simpa [Function.update_of_ne he] using P.half j
  · intro a b hab ht
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact (hab (ha.trans hb.symm)).elim
    · subst a
      simpa [Function.update_of_ne hb] using hproper b hab (by simpa [Function.update_of_ne hb] using ht)
    · subst b
      simpa [Function.update_of_ne ha] using
        (hproper a hab.symm (by simpa [Function.update_of_ne ha] using ht.symm)).symm
    · simpa [Function.update_of_ne ha,Function.update_of_ne hb] using
        P.proper a b hab (by simpa [Function.update_of_ne ha,Function.update_of_ne hb] using ht)
  · intro D hD hc a b hab hDa hDb
    have hDold := hD.trans (outside_update_subset hinc)
    by_cases ha : a = i <;> by_cases hb : b = i
    · exact (hab (ha.trans hb.symm)).elim
    · subst a
      simpa [Function.update_of_ne hb] using hfront D hD hc b hab (by simpa using hDa)
        (by simpa [Function.update_of_ne hb] using hDb)
    · subst b
      simpa [Function.update_of_ne ha] using (hfront D hD hc a hab.symm (by simpa using hDb)
        (by simpa [Function.update_of_ne ha] using hDa)).symm
    · simpa [Function.update_of_ne ha,Function.update_of_ne hb] using
        P.frontier D hDold hc a b hab
          (by simpa [Function.update_of_ne ha] using hDa)
          (by simpa [Function.update_of_ne hb] using hDb)

noncomputable def EggCover.absorb [DecidableEq V] {w : V → ℝ} {k : ℕ}
    (P : EggCover G w k) {X : Set V} (hX : Region P X) (i : V)
    (Q J : Set V) (hQX : Q ⊆ X) (hQ : (G.induce Q).Connected)
    (ht : Touch G Q (P.bag i)) (hJ : J ⊆ Q) (hstable : Independent G J)
    (hhalf : mass w Q ≤ 2 * mass w J) (hnot : ¬Touch G (P.yolk i) J) : EggCover G w k := by
  have hQO := hQX.trans hX.subset
  have hBQ := (P.outside_disjoint hQO i).symm
  have hYJ := hBQ.mono (P.yolk_subset i) hJ
  have hiX : Touch G X (P.bag i) := ht.mono hQX Set.Subset.rfl
  refine P.replace i (P.bag i ∪ Q) (P.yolk i ∪ J) (P.color i) Set.subset_union_left
    (fun _ => Or.inl (P.root i ht.right_nonempty))
    (connected_union_of_touch (P.connected i ht.right_nonempty) hQ ht.symm) ?_ ?_
    (independent_union (P.stable i) hstable hnot) ?_ ?_ ?_
  · intro j hji
    refine Set.disjoint_left.mpr ?_
    intro x hx hj
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp (P.disjoint i j hji.symm) hx hj
    · exact hQO hx j hj
  · intro x hx
    exact hx.elim (fun hx => Or.inl (P.yolk_subset i hx)) (fun hx => Or.inr (hJ hx))
  · rw [mass_union hBQ, mass_union hYJ]
    have hh := P.half i
    linarith
  · intro j hij htj
    apply P.proper i j hij
    rcases touch_union_left.mp htj with htj | htj
    · exact htj
    · exact P.frontier X hX.subset hX.connected i j hij hiX (htj.mono hQX Set.Subset.rfl)
  · intro D hD hconn j hij hDi hDj
    have hDold := hD.trans (outside_update_subset (show P.bag i ⊆ P.bag i ∪ Q from Set.subset_union_left))
    apply Touch.mono (hA := Set.subset_union_left) (hB := Set.Subset.rfl)
    rcases touch_union_right.mp hDi with hDi | hDi
    · exact P.frontier D hDold hconn i j hij hDi hDj
    · have hDX := hX.contains_of_touch hDold hconn hQX hDi
      exact P.frontier X hX.subset hX.connected i j hij hiX (hDj.mono hDX Set.Subset.rfl)

def CliqueBound (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ (I : Type u) [Fintype I] (B : I → Set V),
    (∀ i, (G.induce (B i)).Connected) →
    (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
    (∀ i j, i ≠ j → Touch G (B i) (B j)) → Fintype.card I ≤ k

def Interface (G : SimpleGraph V) (B : Set V) : Set V := {x | ∃ y ∈ B, G.Adj x y}

def EggCover.colorYolk {w : V → ℝ} {k : ℕ} (P : EggCover G w k) (c : Fin k) : Set V :=
  ⋃ i, {v | v ∈ P.yolk i ∧ P.color i = c}

end Weights
end ReedSeymour

end OAI
end


