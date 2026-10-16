-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Classification
-- name    : OAI_Probability_ThorpShuffle_Classification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:56:52.406906+00:00
-- url     : https://prove2.me/theorems/cfe7407d-06da-43b2-b8b8-268705e72899
-- title:
--   Specht characters: linear independence, a basis of class functions, and the regular character
-- statement:
--   This module completes, at the level of characters, the description of the irreducible complex representations of a finite symmetric group by Specht modules.
--
--   **Setting.** Let $\alpha$ be a finite set with $|\alpha|=n$ and $S_\alpha$ its symmetric group. For a partition $p$ of $n$ (written $p\vdash n$), let $D_p$ be its Young diagram, whose rows have the lengths of the parts of $p$ in weakly decreasing order; fix a bijection $t_p:\alpha\to D_p$ and let $S^p$ be the Specht module of $t_p$, i.e. the complex span of the $S_\alpha$-translates of the polytabloid $e_{t_p}$ in the permutation module on tabloids. Let $\chi_p(g)=\operatorname{tr}\big(g\,|\,S^p\big)$ be its character and $\deg(p)=\dim_{\mathbb{C}}S^p$. The cycle type of $g\in S_\alpha$ is the partition of $n$ formed by the cycle lengths of $g$, fixed points counting as cycles of length $1$. For a finite group $G$ and $f,h:G\to\mathbb{C}$ put
--   $$
--   \langle f,h\rangle_G=\frac{1}{|G|}\sum_{g\in G}f(g)\,h(g^{-1}).
--   $$
--
--   The module proves:
--
--   1. *Diagram bookkeeping.* The number of cells of a Young diagram is the sum of its row lengths; the row lengths of $D_p$ are the parts of $p$ sorted in decreasing order; $p\mapsto D_p$ is injective; and a Young diagram with $n$ cells defines a partition of $n$ through its row lengths.
--   2. *Pairing.* $f\mapsto\langle f,h\rangle_G$ is linear and vanishes at $f=0$.
--   3. *Independence of irreducible characters.* If $(\rho_i)_{i\in I}$ is a family of finite-dimensional irreducible complex representations of a finite group $G$ such that $\rho_i\cong\rho_j$ only when $i=j$, then their characters are linearly independent.
--   4. *The Specht family.* Each $S^p$ is irreducible; $S^p\cong S^q$ implies $p=q$; the characters $(\chi_p)_{p\vdash n}$ are linearly independent; each $\chi_p$ is constant on conjugacy classes; and $\langle\chi_p,\chi_q\rangle_{S_\alpha}$ equals $1$ if $p=q$ and $0$ otherwise.
--   5. *Character basis.* For $f:S_\alpha\to\mathbb{C}$ let $\tilde f(p)=f(g)$ for a chosen permutation $g$ of cycle type $p$ (and $\tilde f(p)=0$ if there is none). If $f$ is a class function, then $\tilde f$ evaluated at the cycle type of $g$ equals $f(g)$. The functions $\tilde\chi_p$, $p\vdash n$, are linearly independent and therefore form a basis of the space of complex functions on partitions of $n$.
--   6. *Expansion of class functions.* Every class function $f$ on $S_\alpha$ satisfies
--   $$
--   f=\sum_{p\vdash n}\langle f,\chi_p\rangle_{S_\alpha}\,\chi_p ,
--   $$
--   and $\langle f,\chi_p\rangle_{S_\alpha}$ is the $p$-th coordinate of $\tilde f$ in the basis $(\tilde\chi_p)_{p\vdash n}$.
--   7. *Regular character.* For every $g\in S_\alpha$,
--   $$
--   \sum_{p\vdash n}\deg(p)\,\chi_p(g)=\begin{cases}|S_\alpha|,&g=1,\\ 0,&g\ne 1.\end{cases}
--   $$
--
--   Items 5 and 6 are the completeness half of the classification: the Specht characters span all class functions, so every irreducible character of $S_\alpha$ is one of the $\chi_p$. Item 7 is the character of the regular representation; at $g=1$ it gives $\sum_{p\vdash n}\deg(p)^2=n!$. These identities are the Fourier-analytic tools used to expand class functions and convolution operators on the symmetric group.
--
--   **Formalization Note** `Shape α` is `Nat.Partition (Fintype.card α)`, `family p` is the representation of the symmetric group on `Space p`, and the cycle type is Mathlib's `Equiv.Perm.partition`. The pairing is `Thorp.Fourier.charPair`, normalized by `Nat.card G` and using $h(g^{-1})$ in place of a complex conjugate, as in Mathlib's `Representation.char_orthonormal`. The lift $\tilde f$ is `classLift f`, defined with a choice of representative, and the basis is `characterBasis`, built with `basisOfPiSpaceOfLinearIndependent`. Other names: `toPartition`, `irreducible_char_independent`, `family_irreducible` (an instance), `family_inequiv`, `characters_independent`, `liftedCharacters_independent`, `class_expansion`, `char_orthogonal`, `class_coeff`, `regular_char`. The private lemmas `ite_eq_left` and `dite_eq_left` are compatibility copies of `if_pos` and `dif_pos`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Classification.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Classification.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

universe uG uI uV uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

lemma card_cells_eq_sum (D : YoungDiagram) : Fintype.card (Cells D) = D.rowLens.sum := by
  rw [Fintype.card_congr (rowCellsEquiv D), Fintype.card_sigma]
  simp only [Fintype.card_fin, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range, Finset.sum_range]

lemma rowLens_ofPartition {n : ℕ} (p : Nat.Partition n) :
    (ofPartition p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro x hx
  exact p.parts_pos ((Multiset.mem_sort _).mp hx)

lemma ofPartition_injective {n : ℕ} : Function.Injective (ofPartition (n := n)) := by
  intro p q hpq
  apply Nat.Partition.ext
  have hh := congrArg YoungDiagram.rowLens hpq
  rw [rowLens_ofPartition, rowLens_ofPartition] at hh
  simpa only [Multiset.sort_eq] using congrArg (fun x : List ℕ => (x : Multiset ℕ)) hh

def toPartition (D : YoungDiagram) (n : ℕ) (hn : Fintype.card (Cells D) = n) : Nat.Partition n where
  parts := D.rowLens
  parts_pos := fun hx => D.pos_of_mem_rowLens _ hx
  parts_sum := by simpa only [Multiset.sum_coe, ← card_cells_eq_sum] using hn

end Thorp.Young

namespace Thorp.Fourier
open scoped Classical

variable {G : Type uG} [Group G] [Fintype G]

def charPair (f h : G → ℂ) : ℂ := (Nat.card G : ℂ)⁻¹ * ∑ g, f g * h g⁻¹

lemma charPair_sum {I : Type uI} (s : Finset I) (a : I → ℂ) (f : I → G → ℂ) (h : G → ℂ) :
    charPair (∑ i ∈ s, a i • f i) h = ∑ i ∈ s, a i * charPair (f i) h := by
  simp only [charPair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [mul_assoc (a i)]
  rw [← Finset.mul_sum]
  ring

lemma charPair_zero (h : G → ℂ) : charPair (0 : G → ℂ) h = 0 := by simp [charPair]

lemma irreducible_char_independent {I : Type uI} {V : I → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (ρ : ∀ i, Representation ℂ G (V i)) [∀ i, Representation.IsIrreducible (ρ i)]
    (hne : ∀ i j, Nonempty (Representation.Equiv (ρ i) (ρ j)) → i = j) :
    LinearIndependent ℂ (fun i => (ρ i).character) := by
  let : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (NeZero.ne _)
  have ho (i j : I) : charPair (ρ i).character (ρ j).character = if i = j then 1 else 0 := by
    rw [charPair, Representation.char_orthonormal]
    congr 1
    apply propext
    constructor
    · exact fun h => (hne j i h).symm
    · intro h; subst j; exact ⟨Representation.Equiv.refl _⟩
  rw [linearIndependent_iff']
  intro s a ha i hi
  have hh := congrArg (fun f => charPair f (ρ i).character) ha
  rw [charPair_sum, charPair_zero] at hh
  simp only [ho] at hh
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', ite_eq_left hi] using hh

end Thorp.Fourier

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

def family (p : Shape α) : Representation ℂ (Equiv.Perm α) (Space p) :=
  (module (Thorp.Young.ofPartition p) (canonicalTableau p)).toRepresentation

instance family_irreducible (p : Shape α) : Representation.IsIrreducible (family p) :=
  irreducible (Thorp.Young.ofPartition p) (canonicalTableau p)

lemma family_inequiv (p q : Shape α) (he : Nonempty (Representation.Equiv (family p) (family q))) : p = q := by
  obtain ⟨e⟩ := he
  apply Thorp.Young.ofPartition_injective
  exact shape_eq_of_equiv _ _ _ _ e

lemma characters_independent : LinearIndependent ℂ (fun p : Shape α => (family p).character) :=
  Thorp.Fourier.irreducible_char_independent family family_inequiv

def classLift (f : Equiv.Perm α → ℂ) (p : Shape α) : ℂ :=
  if h : ∃ g : Equiv.Perm α, g.partition = p then f h.choose else 0

lemma classLift_apply (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) (g : Equiv.Perm α) :
    classLift f g.partition = f g := by
  unfold classLift
  have hh : ∃ a : Equiv.Perm α, a.partition = g.partition := ⟨g, rfl⟩
  rw [dite_eq_left hh]
  exact hf _ g (Equiv.Perm.partition_eq_of_isConj.mpr hh.choose_spec)

lemma character_isClass (p : Shape α) (g h : Equiv.Perm α) (hgh : IsConj g h) :
    (family p).character g = (family p).character h := by
  obtain ⟨x, hx⟩ := isConj_iff.mp hgh
  rw [← hx]
  exact (Representation.char_conj (family p) g x).symm

lemma liftedCharacters_independent :
    LinearIndependent ℂ (fun p : Shape α => classLift (family p).character) := by
  let E : (Shape α → ℂ) →ₗ[ℂ] (Equiv.Perm α → ℂ) := {
    toFun := fun f g => f g.partition
    map_add' := by intro f h; rfl
    map_smul' := by intro a f; rfl }
  apply LinearIndependent.of_comp E
  convert characters_independent (α := α) using 1
  funext p g
  exact classLift_apply _ (character_isClass p) g

def characterBasis : Module.Basis (Shape α) ℂ (Shape α → ℂ) :=
  basisOfPiSpaceOfLinearIndependent liftedCharacters_independent

lemma characterBasis_apply (p : Shape α) : characterBasis p = classLift (family p).character := by
  exact congrFun (coe_basisOfPiSpaceOfLinearIndependent liftedCharacters_independent) p

end Thorp.Specht

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

lemma class_expansion (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) :
    (∑ p : Shape α, (characterBasis.repr (classLift f)) p • (family p).character) = f := by
  funext g
  have he := congrFun (characterBasis.sum_repr (classLift f)) g.partition
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, characterBasis_apply,
    classLift_apply _ (character_isClass _), classLift_apply _ hf] at he
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using he

lemma char_orthogonal (p q : Shape α) :
    Thorp.Fourier.charPair (family p).character (family q).character = if p = q then 1 else 0 := by
  let : Invertible (Nat.card (Equiv.Perm α) : ℂ) := invertibleOfNonzero (NeZero.ne _)
  rw [Thorp.Fourier.charPair, Representation.char_orthonormal]
  congr 1
  apply propext
  exact ⟨fun h => (family_inequiv q p h).symm,
    fun h => by subst q; exact ⟨Representation.Equiv.refl _⟩⟩

lemma class_coeff (f : Equiv.Perm α → ℂ)
    (hf : ∀ g h, IsConj g h → f g = f h) (q : Shape α) :
    characterBasis.repr (classLift f) q = Thorp.Fourier.charPair f (family q).character := by
  have he := congrArg (fun x => Thorp.Fourier.charPair x (family q).character) (class_expansion f hf)
  rw [Thorp.Fourier.charPair_sum] at he
  simp only [char_orthogonal, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte] at he
  exact he

theorem regular_char (g : Equiv.Perm α) :
    ∑ p : Shape α, (degree p : ℂ) * (family p).character g =
      if g = 1 then (Nat.card (Equiv.Perm α) : ℂ) else 0 := by
  let δ : Equiv.Perm α → ℂ := fun h => if h = 1 then Nat.card (Equiv.Perm α) else 0
  have hδ : ∀ a b, IsConj a b → δ a = δ b := by
    intro a b hab
    have hh : a = 1 ↔ b = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hab
      rw [← hc]
      constructor
      · intro ha; simp [ha]
      · intro hb
        have hh := congrArg (fun z => c⁻¹ * z * c) hb
        simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, one_mul, mul_one] using hh
    simp only [δ, hh]
  have hc (p : Shape α) : Thorp.Fourier.charPair δ (family p).character = degree p := by
    rw [Thorp.Fourier.charPair]
    simp only [δ, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, inv_one,
      Representation.char_one]
    rw [← mul_assoc, inv_mul_cancel₀ (NeZero.ne _), one_mul]
    rfl
  have he := congrFun (class_expansion δ hδ) g
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, class_coeff δ hδ, hc] using he

end Thorp.Specht

end

end OAI


