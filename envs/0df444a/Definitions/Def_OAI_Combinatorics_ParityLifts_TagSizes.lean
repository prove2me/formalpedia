-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
-- name    : OAI_Combinatorics_ParityLifts_TagSizes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:11:31.192725+00:00
-- url     : https://prove2.me/theorems/4d89abbc-9508-4e52-9a0b-f28a20f60919
-- title:
--   Counting bijections for tags, pairs, helpers and template neighbourhoods
-- statement:
--   This file collects explicit bijections that are used to count the vertices of the parity lifts. Throughout, $T_t$ is the template with main vertices $[t]=\{0,\dots,t-1\}$, main pairs $(i,j)$ with $i<j$, and helpers $h_{ij;\ell}$ indexed by a main pair and a third index $\ell\notin\{i,j\}$; a helper is incident to $i$, $j$ and $\ell$.
--
--   1. **Fibres of the sum map.** For a finite set $I$, a fixed $a\in I$ and $\beta\in\mathbb{F}_2$, one has $\sum_{i\in I}f(i)=f(a)+\sum_{i\ne a}f(i)$, and restriction to $I\setminus\{a\}$ is a bijection
--   $$
--   \Bigl\{f\in\mathbb{F}_2^{I}:\ \sum_{i\in I}f(i)=\beta\Bigr\}\ \cong\ \mathbb{F}_2^{\,I\setminus\{a\}},
--   $$
--   whose inverse completes $f(a)=\beta-\sum_{i\ne a}f(i)$.
--   2. **Main pairs.** $\{(i,j):\ i<j<t\}\cong\{(j,i):\ j\in[t],\ i<j\}$.
--   3. **Helpers.** Helpers correspond to pairs consisting of a main pair $p$ and an index $\ell\in[t]$ outside $p$.
--   4. **Ordered pairs in a finite linear order.** For a finite linearly ordered set $J$, the pairs $x<y$ in $J$ correspond to the main pairs of $[\,|J|\,]$, via the order isomorphism $J\cong[\,|J|\,]$.
--   5. **Pairs and helpers through a main index $i$.** For a main pair $p$ containing $i$, $\mathrm{other}_i(p)\ne i$ is its other endpoint. Helpers whose third index is $i$ correspond to the pairs $x<y$ in $[t]\setminus\{i\}$, and helpers whose main pair contains $i$ correspond to pairs ($p\ni i$, $\ell\notin p$).
--   6. **Neighbourhood of a main vertex.**
--   $$
--   N_{T_t}(i)\ \cong\ \bigl([t]\setminus\{i\}\bigr)\ \sqcup\ \{h:\ h \text{ is a helper incident to } i\}.
--   $$
--
--   Item 1 shows that a vertex $u$ of the base graph whose type has positive template degree carries exactly $2^{\deg_{T_t}(\tau(u))-1}$ tags for either parity; since every template vertex has positive degree when $t\ge2$, the zero and star lifts then have the same number of vertices. Items 2 to 6 give $\binom t2$ main pairs, $3\binom t3$ helpers, helper degree $3$ and the bound $\deg_{T_t}(i)\le t-1+3\binom{t-1}{2}$; together these yield the vertex bound $A\bigl(t\,2^{t-2+3\binom{t-1}{2}}+12\binom t3\bigr)$ for the lifts when every domain and label set has at most $A$ elements.
--
--   **Formalization Note** The bijections are `sumFiberEquiv` (with the lemma `sum_split_at`), `mainPairEquiv`, `helperSigmaEquiv`, `orderedPairEquiv` on the type `OrderedPair J`, `pairOther` on `PairsThrough i`, `helperThirdEquiv`, `helperEndpointEquiv` and `templateMainNeighbors`. The private lemmas `dite_eq_left` and `dite_eq_right` are compatibility shims.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/TagSizes.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/TagSizes.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

namespace ParityWL

open scoped BigOperators

section TagSizes

open scoped Classical

variable {I : Type} [Fintype I]

lemma sum_split_at (a : I) (f : I → Bit) :
    ∑ i, f i = f a + ∑ i : {i : I // i ≠ a}, f i := by
  have hs := (Fintype.sum_subtype_add_sum_subtype (fun i => i = a) f).symm
  simp only [Fintype.sum_unique] at hs
  simpa only [(default : {i : I // i = a}).property] using hs

noncomputable def sumFiberEquiv (a : I) (b : Bit) :
    {f : I → Bit // ∑ i, f i = b} ≃ ({i : I // i ≠ a} → Bit) where
  toFun f i := f.1 i
  invFun f := ⟨fun i => if h : i = a then b - ∑ j, f j else f ⟨i, h⟩, by
    rw [sum_split_at a]
    have he : (∑ i : {i : I // i ≠ a},
        if h : (i : I) = a then b - ∑ j, f j else f ⟨i, h⟩) = ∑ i, f i := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [dite_eq_right i.property]
    rw [he]
    rw [dite_eq_left rfl]
    exact sub_add_cancel b (∑ j, f j)⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    by_cases h : i = a
    · subst i
      dsimp only
      rw [dite_eq_left rfl]
      have hf := f.2
      rw [sum_split_at a] at hf
      exact eq_sub_of_add_eq hf |>.symm
    · simp [h]
  right_inv := by
    intro f
    funext i
    simp [i.property]

noncomputable def mainPairEquiv (t : ℕ) : MainPair t ≃ ((j : Fin t) × Fin j.val) where
  toFun p := ⟨p.1.2, ⟨p.1.1.val, p.2⟩⟩
  invFun p := ⟨(⟨p.2.val, p.2.isLt.trans p.1.isLt⟩, p.1), p.2.isLt⟩
  left_inv _p := rfl
  right_inv _p := rfl

noncomputable def helperSigmaEquiv (t : ℕ) :
    Helper t ≃ ((p : MainPair t) × {i : Fin t // i ≠ p.1.1 ∧ i ≠ p.1.2}) where
  toFun h := ⟨h.1.1, ⟨h.1.2, h.2⟩⟩
  invFun h := ⟨(h.1, h.2.1), h.2.2⟩
  left_inv _h := rfl
  right_inv _h := rfl

abbrev OrderedPair (J : Type) [LT J] := {p : J × J // p.1 < p.2}

noncomputable def orderedPairEquiv {J : Type} [Fintype J] [LinearOrder J] :
    OrderedPair J ≃ MainPair (Fintype.card J) := by
  let e := (Fintype.orderIsoFinOfCardEq J rfl).symm
  exact
    { toFun := fun p => ⟨(e p.1.1, e p.1.2), e.strictMono p.2⟩
      invFun := fun p => ⟨(e.symm p.1.1, e.symm p.1.2), e.symm.strictMono p.2⟩
      left_inv := by intro p; apply Subtype.ext; simp
      right_inv := by intro p; apply Subtype.ext; simp }

abbrev PairsThrough {t : ℕ} (i : Fin t) :=
  {p : MainPair t // i = p.1.1 ∨ i = p.1.2}

noncomputable def pairOther {t : ℕ} (i : Fin t) (p : PairsThrough i) :
    {j : Fin t // j ≠ i} :=
  if h : i = p.1.1.1 then
    ⟨p.1.1.2, fun he => (ne_of_lt p.1.2) (h.symm.trans he.symm)⟩
  else ⟨p.1.1.1, fun he => h he.symm⟩

noncomputable def helperThirdEquiv {t : ℕ} (i : Fin t) :
    {h : Helper t // i = h.1.2} ≃ OrderedPair {j : Fin t // j ≠ i} where
  toFun h := ⟨(⟨h.1.1.1.1.1, by simpa [h.2] using h.1.2.1.symm⟩,
    ⟨h.1.1.1.1.2, by simpa [h.2] using h.1.2.2.symm⟩), h.1.1.1.2⟩
  invFun p := ⟨⟨(⟨(p.1.1.1, p.1.2.1), p.2⟩, i),
    ⟨p.1.1.2.symm, p.1.2.2.symm⟩⟩, rfl⟩
  left_inv h := by apply Subtype.ext; apply Subtype.ext; exact Prod.ext rfl h.2
  right_inv p := rfl

noncomputable def helperEndpointEquiv {t : ℕ} (i : Fin t) :
    {h : Helper t // i = h.1.1.1.1 ∨ i = h.1.1.1.2} ≃
      ((p : PairsThrough i) × {j : Fin t // j ≠ p.1.1.1 ∧ j ≠ p.1.1.2}) where
  toFun h := ⟨⟨h.1.1.1, h.2⟩, ⟨h.1.1.2, h.1.2⟩⟩
  invFun p := ⟨⟨(p.1.1, p.2.1), p.2.2⟩, p.1.2⟩
  left_inv _h := rfl
  right_inv _p := rfl

noncomputable def templateMainNeighbors {t : ℕ} (i : Fin t) :
    (template t).neighborSet (.inl i) ≃
      ({j : Fin t // j ≠ i} ⊕ {h : Helper t // helperIncident h i}) where
  toFun v := match v with
    | ⟨.inl j, h⟩ => .inl ⟨j, (show i ≠ j from h).symm⟩
    | ⟨.inr h, e⟩ => .inr ⟨h, e⟩
  invFun v := match v with
    | .inl j => ⟨.inl j.1, j.2.symm⟩
    | .inr h => ⟨.inr h.1, h.2⟩
  left_inv v := by rcases v with ⟨v, hv⟩; cases v <;> rfl
  right_inv v := by cases v <;> rfl

end TagSizes

end ParityWL

end OAI


