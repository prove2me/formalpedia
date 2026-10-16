-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Specht
-- name    : OAI_Probability_ThorpShuffle_Specht
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:48:41.028988+00:00
-- url     : https://prove2.me/theorems/92ed27fe-daed-4aee-a320-e4fa1e6672ee
-- title:
--   Polytabloids, the rank-one column antisymmetrizer, and irreducibility of Specht modules
-- statement:
--   This module establishes the basic properties of polytabloids and proves that Specht modules are irreducible complex representations of the symmetric group.
--
--   **Setting.** Let $\alpha$ be a finite set and $S_\alpha$ its group of permutations. A Young diagram $D$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$. Fix a bijection $t:\alpha\to D$ (a tableau) and write $r_t(x)$ and $c_t(x)$ for the row and the column of the cell $t(x)$.
--
--   - For a function $r:\alpha\to\mathbb{N}$, a *tabloid* of $r$ is a rearrangement $f=r\circ g$ with $g\in S_\alpha$; the group acts on tabloids by $(g\cdot f)(x)=f(g^{-1}x)$. For $r=r_t$, a tabloid assigns a row number to every element of $\alpha$, row $i$ receiving as many elements as row $i$ of $D$ has cells. The *base tabloid* is $\{t\}=r_t$.
--   - For $c:\alpha\to\mathbb{N}$, the fibre-preserving group is $G_c=\{g\in S_\alpha:\ c(g(x))=c(x)\text{ for all }x\}$, and the column group of $t$ is $C_t=G_{c_t}$. The sign $\operatorname{sgn}(g)\in\{1,-1\}$ is regarded as a complex number.
--   - $M_t$ is the space of complex-valued functions on the tabloids of $r_t$, with the Hermitian inner product $\langle v,w\rangle=\sum_f\overline{v(f)}\,w(f)$ and the permutation action $(\rho(g)v)(f)=v(g^{-1}\cdot f)$; $\delta_f\in M_t$ is the indicator of the tabloid $f$.
--   - The column antisymmetrizer, the polytabloid and the Specht module of $t$ are
--   $$
--   \kappa_t=\sum_{h\in C_t}\operatorname{sgn}(h)\,\rho(h),\qquad e_t=\kappa_t\,\delta_{\{t\}},\qquad S^D_t=\operatorname{span}_{\mathbb{C}}\{\rho(g)\,e_t:\ g\in S_\alpha\}\subseteq M_t .
--   $$
--
--   The module proves the following.
--
--   1. *Elementary facts.* For any tabloid $f$, $g\cdot f=f$ if and only if $f(g(x))=f(x)$ for all $x$. If $c(x)=c(y)$, the transposition $(x\,y)$ lies in $G_c$. The complex sign satisfies $\overline{\operatorname{sgn}(g)}=\operatorname{sgn}(g)=\operatorname{sgn}(g^{-1})$, and $\operatorname{sgn}((x\,y))=-1$ for $x\ne y$.
--   2. *Trivial intersection.* If $h\in C_t$ and $h\cdot\{t\}=\{t\}$, then $h=1$.
--   3. *Column collisions.* If $f$ is a tabloid of $r_t$ and $x\ne y$ lie in the same column of $t$ with $f(x)=f(y)$, then some $h\in C_t$ with $\operatorname{sgn}(h)=-1$ satisfies $h\cdot f=f$.
--   4. *Dichotomy.* For every tabloid $f$ of $r_t$, either some $h\in C_t$ with $\operatorname{sgn}(h)=-1$ fixes $f$, or $f=a\cdot\{t\}$ for some $a\in C_t$.
--   5. *Support and normalization.* If $e_t(f)\ne 0$, then $f=h\cdot\{t\}$ for some $h\in C_t$. Moreover $e_t(\{t\})=1$; in particular $e_t\ne 0$.
--   6. *Rank one.* For every $v\in M_t$,
--   $$
--   \kappa_t\,v=\langle e_t,v\rangle\,e_t .
--   $$
--   7. *Irreducibility.* $S^D_t$, with the restricted action of $S_\alpha$, is an irreducible complex representation of $S_\alpha$.
--
--   The rank-one identity says that the column antisymmetrizer maps the whole permutation module onto the line $\mathbb{C}e_t$; it is the key input for irreducibility. Together with the inequivalence of Specht modules of different shapes, proved in a companion module, this produces the irreducible representations of the symmetric group whose dimensions are the degrees $\deg(p)$ in the reciprocal-degree sums $\sum_p 1/\deg(p)$ studied in this project.
--
--   **Formalization Note** The objects `Tabloid`, `baseTabloid`, `fiberGroup`, `complexSign`, `tableauRow`, `tableauCol`, `tabloidRep`, `columnAlternator`, `polytabloid` and `module` are defined elsewhere in the project; this module contributes the lemmas `stabilizes_tabloid_iff`, `swap_preserves`, `complexSign_conj`, `complexSign_inv`, `complexSign_swap`, `row_col_free`, `collision_odd`, `collision_or_column`, `polytabloid_support`, `polytabloid_diag`, `polytabloid_ne_zero`, `columnAlternator_rank_one` and the theorem `irreducible`, plus a few simp lemmas. Tabloids are encoded as rearrangements of the row function rather than as row-equivalence classes of tableaux; the two descriptions are equivalent. The permutation module is `EuclideanSpace ℂ (Tabloid (tableauRow D t))`, whose inner product is conjugate-linear in the first argument. Irreducibility is Mathlib's `Representation.IsIrreducible`: the lattice of subrepresentations is a simple order, so the representation is nonzero and has no subrepresentations other than $0$ and itself. The private lemma `ite_eq_right` is a compatibility copy of `if_neg`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Specht.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Specht.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

universe uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht
open scoped Classical

variable {α : Type uα} [Fintype α]

omit [Fintype α] in
@[simp] lemma perm_apply_inv (g : Equiv.Perm α) (x : α) : g (g⁻¹ x) = x := g.apply_symm_apply x

omit [Fintype α] in
@[simp] lemma perm_inv_apply (g : Equiv.Perm α) (x : α) : g⁻¹ (g x) = x := g.symm_apply_apply x

omit [Fintype α] in
@[simp] lemma tabloid_smul_apply (r : α → ℕ) (g : Equiv.Perm α) (f : Tabloid r) (x : α) :
    (g • f).val x = f.val (g⁻¹ x) := rfl

omit [Fintype α] in
@[simp] lemma baseTabloid_apply (r : α → ℕ) (x : α) : (baseTabloid r).val x = r x := rfl

omit [Fintype α] in
lemma stabilizes_tabloid_iff (r : α → ℕ) (g : Equiv.Perm α) (f : Tabloid r) :
    g • f = f ↔ ∀ x, f.val (g x) = f.val x := by
  constructor
  · intro h x
    have hh := congrArg (fun t : Tabloid r => t.val (g x)) h
    simpa only [tabloid_smul_apply, perm_inv_apply] using hh.symm
  · intro h
    apply Subtype.ext
    funext x
    have hh := h (g⁻¹ x)
    simpa only [tabloid_smul_apply, perm_apply_inv] using hh.symm

omit [Fintype α] in
lemma swap_preserves {c : α → ℕ} {x y : α} (hc : c x = c y) :
    Equiv.swap x y ∈ fiberGroup c := by
  intro z
  by_cases hzx : z = x
  · subst z; simp [hc]
  by_cases hzy : z = y
  · subst z; simp [hc]
  rw [Equiv.swap_apply_of_ne_of_ne hzx hzy]

@[simp] lemma complexSign_conj (g : Equiv.Perm α) : conj (complexSign g) = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_inv (g : Equiv.Perm α) : complexSign g⁻¹ = complexSign g := by
  simp [complexSign]

@[simp] lemma complexSign_swap (x y : α) (h : x ≠ y) : complexSign (Equiv.swap x y) = -1 := by
  simp [complexSign, Equiv.Perm.sign_swap h]

variable (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D)

omit [Fintype α] in

lemma row_col_free (g : fiberGroup (tableauCol D t))
    (hg : (g : Equiv.Perm α) • baseTabloid (tableauRow D t) = baseTabloid (tableauRow D t)) : g = 1 := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro x
  apply t.injective
  apply Subtype.ext
  apply Prod.ext
  · exact (stabilizes_tabloid_iff _ _ _).mp hg x
  · exact g.property x

lemma collision_odd (f : Tabloid (tableauRow D t)) (x y : α) (hxy : x ≠ y)
    (hc : tableauCol D t x = tableauCol D t y) (hr : f.val x = f.val y) :
    ∃ g : fiberGroup (tableauCol D t), (g : Equiv.Perm α) • f = f ∧ complexSign (g : Equiv.Perm α) = -1 := by
  refine ⟨⟨Equiv.swap x y, swap_preserves hc⟩, ?_, complexSign_swap x y hxy⟩
  rw [stabilizes_tabloid_iff]
  exact swap_preserves hr

lemma collision_or_column (f : Tabloid (tableauRow D t)) :
    (∃ a : fiberGroup (tableauCol D t), (a : Equiv.Perm α) • f = f ∧
      complexSign (a : Equiv.Perm α) = -1) ∨
    ∃ a : fiberGroup (tableauCol D t), f = (a : Equiv.Perm α) • baseTabloid (tableauRow D t) := by
  classical
  by_cases hc : ∃ x y : α, x ≠ y ∧ tableauCol D t x = tableauCol D t y ∧ f.val x = f.val y
  · obtain ⟨x, y, hxy, hx, hy⟩ := hc
    exact Or.inl (collision_odd D t f x y hxy hx hy)
  right
  let r : Thorp.Young.Cells D → ℕ := fun z => f.val (t.symm z)
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 → r x = r y → x = y := by
    intro x y hcol hr
    by_contra hxy
    apply hc
    refine ⟨t.symm x, t.symm y, ?_, ?_, hr⟩
    · exact fun h => hxy (t.symm.injective h)
    · simpa only [tableauCol, Equiv.apply_symm_apply] using hcol
  have hs : ∑ z : Thorp.Young.Cells D, r z = ∑ z : Thorp.Young.Cells D, z.val.1 := by
    change ∑ z, f.val (t.symm z) = _
    rw [Equiv.sum_comp t.symm]
    obtain ⟨g, hg⟩ := f.property
    rw [hg]
    change ∑ x, tableauRow D t (g x) = _
    rw [Equiv.sum_comp g]
    exact Equiv.sum_comp t (fun z : Thorp.Young.Cells D => z.val.1)
  obtain ⟨σ, hσc, hσr⟩ := Thorp.Young.column_sort D r hi hs
  let a : Equiv.Perm α := (t.trans σ).trans t.symm
  have hac : a ∈ fiberGroup (tableauCol D t) := by
    intro x
    change (t (t.symm (σ (t x)))).val.2 = (t x).val.2
    simpa only [Equiv.apply_symm_apply] using hσc (t x)
  have har (x : α) : f.val (a x) = tableauRow D t x := hσr (t x)
  refine ⟨⟨a, hac⟩, ?_⟩
  apply Subtype.ext
  funext x
  have hh := har (a⁻¹ x)
  simpa only [tabloid_smul_apply, baseTabloid_apply, perm_apply_inv] using hh

lemma polytabloid_support (f : Tabloid (tableauRow D t)) (hf : polytabloid D t f ≠ 0) :
    ∃ h : fiberGroup (tableauCol D t), f = h.val • baseTabloid (tableauRow D t) := by
  by_contra hn
  push Not at hn
  apply hf
  change PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (EuclideanSpace.single (baseTabloid (tableauRow D t)) (1 : ℂ)) f = 0
  rw [PermutationSpace.alternator_coeff]
  apply Finset.sum_eq_zero
  intro h _
  have hne : h.val⁻¹ • f ≠ baseTabloid (tableauRow D t) := by
    intro he
    exact hn h (inv_smul_eq_iff.mp he)
  rw [PiLp.single_apply]
  change complexSign h.val * (if h.val⁻¹ • f = baseTabloid (tableauRow D t) then 1 else 0) = 0
  rw [ite_eq_right hne, mul_zero]

lemma polytabloid_diag : polytabloid D t (baseTabloid (tableauRow D t)) = 1 := by
  exact PermutationSpace.polytabloid_base (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (row_col_free D t)

lemma polytabloid_ne_zero : polytabloid D t ≠ 0 := by
  have hh := PermutationSpace.polytabloid_base (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (row_col_free D t)
  intro hz
  change polytabloid D t (baseTabloid (tableauRow D t)) = 1 at hh
  rw [hz] at hh
  norm_num at hh

lemma columnAlternator_rank_one (v : EuclideanSpace ℂ (Tabloid (tableauRow D t))) :
    columnAlternator D t v = ⟪polytabloid D t, v⟫_ℂ • polytabloid D t := by
  exact PermutationSpace.alternator_rank_one (fiberGroup (tableauCol D t)).subtype
    (complexSign.comp (fiberGroup (tableauCol D t)).subtype)
    (baseTabloid (tableauRow D t)) (fun h => complexSign_conj h.val)
    (fun h => complexSign_inv h.val) (row_col_free D t) (collision_or_column D t) v

theorem irreducible : Representation.IsIrreducible (module D t).toRepresentation := by
  exact cyclic_irreducible (tabloidRep D t) (polytabloid D t) (polytabloid_ne_zero D t)
    PermutationSpace.rep_unitary (columnAlternator D t) (columnAlternator_rank_one D t)
    (PermutationSpace.alternator_stable (fiberGroup (tableauCol D t)).subtype
      (complexSign.comp (fiberGroup (tableauCol D t)).subtype))

end Thorp.Specht

end

end OAI


