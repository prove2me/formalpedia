-- Prove2me | Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
-- name    : OAI_Combinatorics_MatchingPSD_ColoringCounts__MatchingAffineLift
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T13:04:52.304915+00:00
-- url     : https://prove2.me/theorems/3314187e-17f1-40f9-8182-339a641e43a5
-- title:
--   Histograms of colorings, colorings with prescribed color counts, and pair-constant colorings
-- statement:
--   Let $A$ be a finite set and $B$ a set of colors. The module defines the following objects.
--
--   1. **Histogram.** For a coloring $f : A \to B$, its histogram is the color-count function
--   $$
--   \operatorname{hist}(f)(b) = \bigl|\{a \in A : f(a) = b\}\bigr| \qquad (b \in B).
--   $$
--   2. **Colorings with prescribed counts.** For $s : B \to \mathbb{N}$, the set $\mathrm{Col}(A, B, s) = \{f : A \to B : \operatorname{hist}(f) = s\}$ of colorings in which every color $b$ is used exactly $s(b)$ times; it is finite when $B$ is finite.
--   3. **Fiber bijections and an aligning permutation.** If $\operatorname{hist}(f) = \operatorname{hist}(g)$, then for every color $b$ the fibers $f^{-1}(b)$ and $g^{-1}(b)$ have the same size, and a bijection between them is chosen; gluing these bijections gives a permutation $\sigma$ of $A$ with $g(\sigma(a)) = f(a)$ for all $a$. For arbitrary $f, g$, the permutations $\sigma$ of $A$ with $f \circ \sigma = g$ correspond bijectively to families $(\tau_b)_{b \in B}$ of bijections $\tau_b : g^{-1}(b) \to f^{-1}(b)$ (namely $\tau_b$ is the restriction of $\sigma$). Moreover $\operatorname{hist}(f \circ \sigma) = \operatorname{hist}(f)$ for every permutation $\sigma$ of $A$.
--   4. **Pair-constant colorings.** Let $H$ be a set and consider colorings of $H \times \{0, 1\}$, whose elements $(i,0)$ and $(i,1)$ form the pair indexed by $i$. A coloring $f$ is pair-constant if $f(i, 0) = f(i, 1)$ for every $i \in H$. The duplicate of $k : H \to B$ is $\hat k(i, \epsilon) = k(i)$, and the splice of $k, l : H \to B$ is the coloring equal to $k(i)$ at $(i,0)$ and to $l(i)$ at $(i,1)$. Restriction to the first copy identifies pair-constant colorings of $H \times \{0,1\}$ with colorings of $H$, the inverse being duplication. For finite $H$, histograms add under splicing, $\operatorname{hist}(\mathrm{splice}(k, l)) = \operatorname{hist}(k) + \operatorname{hist}(l)$, hence $\operatorname{hist}(\hat k) = 2\operatorname{hist}(k)$, and duplication restricts to a bijection between the pair-constant colorings in $\mathrm{Col}(H \times \{0,1\}, B, 2s)$ and $\mathrm{Col}(H, B, s)$ for every $s : B \to \mathbb{N}$.
--   5. **Bounded histogram.** For finite $H$ and $f : H \to B$, the histogram regarded as a map $B \to \{0, 1, \dots, |H|\}$, which is possible because no color is used more than $|H|$ times; two colorings have equal bounded histograms if and only if they have equal histograms.
--
--   These devices are used to show that $|\mathrm{Col}(A, B, \operatorname{hist}(f))|$ is a multinomial coefficient, to rewrite a sum over all permutations $\sigma$ of $A$ of a quantity depending on $f \circ \sigma$ as a weighted sum over the colorings with the same histogram, and to bound how many permutations of $H \times \{0,1\}$ keep a coloring pair-constant; the bounded histogram shows that for finite $B$ there are at most $(|H| + 1)^{|B|}$ distinct histograms.
--
--   **Formalization Note** `histogram f b` is `Fintype.card {a // f a = b}` and `Colorings α β s` is the subtype `{f : α → β // histogram f = s}`, with the `Fintype` instance `coloringsFintype`. `fiberEquivOfHistogram` and `permOfHistogram` are noncomputable choices (via `Fintype.equivOfCardEq`), `fiberPermEquiv` is the bijection of item 3, `pairConstant`, `duplicateColoring`, `spliceColoring`, `pairConstantEquiv` and `constantColoringsEquiv` are the objects of item 4, and `boundedHistogram` takes values in `Fin (Fintype.card H + 1)`. The lemmas `histogram_comp_perm`, `histogram_spliceColoring` and `histogram_duplicateColoring` are the histogram identities stated above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/ColoringCounts.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/ColoringCounts.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MatchingAffineLift mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PSDEvaluation
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Model
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings__MatchingAffineLift
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension__MatchingAffineLift

namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8

namespace MatchingSmoothing

variable {α : Type u_1} {β : Type u_2} [Fintype α] [DecidableEq β]

noncomputable def histogram (f : α → β) (b : β) : ℕ :=
  Fintype.card {a // f a = b}

abbrev Colorings (α : Type u_3) (β : Type u_4) [Fintype α] [DecidableEq β] (s : β → ℕ) :=
  {f : α → β // histogram f = s}

noncomputable instance coloringsFintype [Fintype β] (s : β → ℕ) :
    Fintype (Colorings α β s) := Fintype.ofFinite _

noncomputable def fiberEquivOfHistogram {f g : α → β} (h : histogram f = histogram g)
    (b : β) : {a // f a = b} ≃ {a // g a = b} :=
  Fintype.equivOfCardEq (congrFun h b)

noncomputable def permOfHistogram {f g : α → β} (h : histogram f = histogram g) :
    Equiv.Perm α :=
  (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight (fiberEquivOfHistogram h)).trans (Equiv.sigmaFiberEquiv g))

lemma histogram_comp_perm (f : α → β) (σ : Equiv.Perm α) :
    histogram (f ∘ σ) = histogram f := by
  funext b
  apply Fintype.card_congr
  exact { toFun := fun x => ⟨σ x, x.property⟩
          invFun := fun y => ⟨σ.symm y, by simpa using y.property⟩
          left_inv := by intro x; ext; simp
          right_inv := by intro x; ext; simp }

noncomputable def fiberPermEquiv (f g : α → β) :
    {σ : Equiv.Perm α // f ∘ σ = g} ≃
      (∀ b, {a // g a = b} ≃ {a // f a = b}) where
  toFun σ b :=
    { toFun := fun x => ⟨σ.1 x, (congrFun σ.2 x).trans x.property⟩
      invFun := fun y => ⟨σ.1.symm y, by
        exact (congrFun σ.2 (σ.1.symm y)).symm.trans (by simpa using y.property)⟩
      left_inv := by intro x; ext; simp
      right_inv := by intro x; ext; simp }
  invFun e := ⟨Equiv.ofFiberEquiv e, by
    funext a; exact Equiv.ofFiberEquiv_map e a⟩
  left_inv σ := by apply Subtype.ext; ext a; rfl
  right_inv e := by
    funext b
    apply Equiv.ext
    rintro ⟨a, ha⟩
    subst b
    rfl

variable {H : Type u_5} [Fintype H] [DecidableEq H]

def pairConstant (f : H × Bool → β) : Prop := ∀ i, f (i, false) = f (i, true)

instance pairConstantDecidable (f : H × Bool → β) : Decidable (pairConstant f) :=
  inferInstanceAs (Decidable (∀ i, f (i, false) = f (i, true)))

def duplicateColoring (k : H → β) : H × Bool → β := fun v => k v.1

noncomputable def pairConstantEquiv : {f : H × Bool → β // pairConstant f} ≃ (H → β) where
  toFun f i := f.1 (i, false)
  invFun k := ⟨duplicateColoring k, by intro i; rfl⟩
  left_inv f := by
    apply Subtype.ext
    funext ⟨i, b⟩
    cases b
    · rfl
    · exact f.2 i
  right_inv k := rfl

def spliceColoring (k l : H → β) : H × Bool → β :=
  fun v => if v.2 then l v.1 else k v.1

omit [DecidableEq H] in
lemma histogram_spliceColoring (k l : H → β) :
    histogram (spliceColoring k l) = histogram k + histogram l := by
  funext b
  change Fintype.card {v : H × Bool // spliceColoring k l v = b} = _
  let e : {v : H × Bool // spliceColoring k l v = b} ≃
      ({i // k i = b} ⊕ {i // l i = b}) :=
    { toFun := fun v => if h : v.1.2 = true then
        Sum.inr ⟨v.1.1, by simpa [spliceColoring, h] using v.2⟩ else
        Sum.inl ⟨v.1.1, by simpa [spliceColoring, h] using v.2⟩
      invFun := Sum.elim (fun i => ⟨(i.1, false), i.2⟩) (fun i => ⟨(i.1, true), i.2⟩)
      left_inv := by
        rintro ⟨⟨i, b⟩, h⟩
        cases b <;> rfl
      right_inv := by intro v; cases v <;> rfl }
  rw [Fintype.card_congr e, Fintype.card_sum]
  rfl

omit [DecidableEq H] in
lemma histogram_duplicateColoring (k : H → β) :
    histogram (duplicateColoring k) = fun b => 2 * histogram k b := by
  have he : duplicateColoring k = spliceColoring k k := by
    funext ⟨i, b⟩; cases b <;> rfl
  rw [he, histogram_spliceColoring]
  funext b
  simp [two_mul]

noncomputable def constantColoringsEquiv (s : β → ℕ) :
    {g : Colorings (H × Bool) β (fun b => 2 * s b) // pairConstant g.1} ≃
      Colorings H β s where
  toFun g := ⟨fun i => g.1.1 (i, false), by
    have he : duplicateColoring (fun i => g.1.1 (i, false)) = g.1.1 := by
      funext ⟨i, b⟩
      cases b
      · rfl
      · exact g.2 i
    have hh := congrArg histogram he
    rw [histogram_duplicateColoring, g.1.2] at hh
    funext b
    exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) (congrFun hh b)⟩
  invFun k := ⟨⟨duplicateColoring k.1, by rw [histogram_duplicateColoring, k.2]⟩,
    by intro i; rfl⟩
  left_inv g := by
    apply Subtype.ext
    apply Subtype.ext
    funext ⟨i, b⟩
    cases b
    · rfl
    · exact g.2 i
  right_inv k := by apply Subtype.ext; rfl

noncomputable def boundedHistogram (f : H → β) : β → Fin (Fintype.card H + 1) :=
  fun b => ⟨histogram f b, Nat.lt_succ_of_le
    (Fintype.card_le_of_injective (fun a : {a // f a = b} => a.1) Subtype.val_injective)⟩

end MatchingSmoothing

end OAI


