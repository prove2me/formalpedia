-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
-- name    : OAI_RepresentationTheory_Saxl_SpechtClassification
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T23:16:31.949987+00:00
-- url     : https://prove2.me/theorems/3db6339c-180b-47de-9c7f-b4de43144176
-- title:
--   Cycle types, class functions and Specht characters of the symmetric group
-- statement:
--   Basic objects for the character-theoretic classification of the irreducible complex representations of $\mathfrak S_n$.
--
--   For $n,d\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $M_{n,d}$ be the complex vector space of functions $x:[d]^{[n]}\to\mathbb{C}$ on words $w:[n]\to[d]$ (positions $[n]$, letters $[d]$), with indicator vectors $\delta_w$; the symmetric group $\mathfrak S_n$ acts by $(g\cdot x)(w)=x(w\circ g)$, so that $g\cdot\delta_w=\delta_{w\circ g^{-1}}$. A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both indexed from $0$) closed under moving up or to the left; $|\mu|$ is its number of cells. A tableau of shape $\mu$ on the positions $[n]$ is a bijection $t:[n]\to\mu$; its column group $C_t\le\mathfrak S_n$ consists of the permutations $g$ such that $t(g(q))$ and $t(q)$ lie in the same column for every position $q$. For a Young diagram $\mu$ let $\mu_i$ be the length of row $i$ and $\ell(\mu)$ the number of nonempty rows. For a tableau $t:[n]\to\mu$, the row word $r_t:[n]\to[\ell(\mu)]$ sends $q$ to the row of $t(q)$, the polytabloid is $e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,g\cdot\delta_{r_t}$, and the Specht module $S^t\subseteq M_{n,\ell(\mu)}$ is the span of the vectors $g\cdot e_t$, $g\in\mathfrak S_n$. A partition of $n$ is a finite multiset of positive integers with sum $n$; $\mathcal P(n)$ is the set of partitions of $n$.
--
--   1. **Rows enumerate cells.** The cells of $\mu$ correspond bijectively to the pairs (row index $i<\ell(\mu)$, position $j<\mu_i$ inside that row), by $(i,j)\mapsto(i,j)$; consequently $|\mu|=\sum_i\mu_i$.
--
--   2. **Diagram of a partition.** For $p\in\mathcal P(n)$, $\mu(p)$ is the Young diagram whose row lengths are the parts of $p$ listed in nonincreasing order; its list of row lengths is exactly this sorted list and it has $n$ cells.
--
--   3. **Tableau of a partition.** $t_p:[n]\to\mu(p)$ is a fixed (canonical, otherwise unspecified) tableau of $\mu(p)$.
--
--   4. **Cycle type.** For $g\in\mathfrak S_n$, $\operatorname{ct}(g)\in\mathcal P(n)$ consists of the lengths of the cycles of $g$, fixed points counted as parts equal to $1$. Permutations with the same cycle type are conjugate.
--
--   5. **Class functions.** The complex subspace
--   $$
--   \mathcal C_n=\{f:\mathfrak S_n\to\mathbb{C}\ :\ f(g)=f(h)\ \text{whenever}\ \operatorname{ct}(g)=\operatorname{ct}(h)\}.
--   $$
--   The character $g\mapsto\operatorname{tr}\rho(g)$ of every finite-dimensional complex representation $\rho$ of $\mathfrak S_n$ lies in $\mathcal C_n$.
--
--   6. **Evaluation at representatives.** The linear map $\mathrm{ev}_n:\mathcal C_n\to\mathbb{C}^{\mathcal P(n)}$ sending $f$ to the function $p\mapsto f(g_p)$, where $g_p$ is a fixed chosen permutation with $\operatorname{ct}(g_p)=p$, and to the value $0$ at every $p$ for which no such permutation exists (the definition does not presuppose that every partition is a cycle type).
--
--   7. **Specht characters.** For $p\in\mathcal P(n)$, $\chi_p\in\mathcal C_n$ is the character $g\mapsto\operatorname{tr}\big(g\,|\,S^{t_p}\big)$ of the Specht module of $t_p$.
--
--   8. **Character pairing.** For a finite group $G$ and $y:G\to\mathbb{C}$, the linear functional on functions $x:G\to\mathbb{C}$ given by
--   $$
--   x\longmapsto\frac{1}{|G|}\sum_{g\in G}x(g)\,y(g^{-1}).
--   $$
--
--   These are the ingredients of the standard argument that the Specht characters $\chi_p$ are orthonormal for this pairing and span $\mathcal C_n$, whose dimension is at most $|\mathcal P(n)|$ because $\mathrm{ev}_n$ is injective; it follows that every irreducible complex representation of $\mathfrak S_n$ is isomorphic to a Specht module.
--
--   **Formalization Note** `rowCellEquiv μ` is an equivalence with the sigma type `(i : Fin (μ.colLen 0)) × Fin (μ.rowLen i)`, and `card_eq_sum_rowLens` gives the cardinality identity. `partitionDiagram p` is `YoungDiagram.ofRowLens` applied to `p.parts.sort (· ≥ ·)` (lemmas `partitionDiagram_rowLens`, `partitionDiagram_card`), and `partitionTableau p` is `canonicalTableau`. `permPartition g` transports Mathlib's `g.partition`, a partition of `Fintype.card (Fin n)`, to a partition of `n`; `isConj_of_permPartition_eq` and `char_mem_classFunctions` are the two facts stated in items 4 and 5. `classEvaluation n` picks representatives by classical choice, `spechtCharacter p` is the character of `spechtRep (partitionTableau p)`, and `charFunctional y` uses the factor `(Nat.card G : ℂ)⁻¹`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SpechtClassification.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/SpechtClassification.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

universe uV uG

namespace Saxl

/- Rows enumerate exactly the actual cells, including the empty diagram. -/
def rowCellEquiv (μ : YoungDiagram) : μ.cells ≃ (i : Fin (μ.colLen 0)) × Fin (μ.rowLen i) where
  toFun c := ⟨⟨c.val.1, YoungDiagram.mem_iff_lt_colLen.mp
      (μ.up_left_mem le_rfl (Nat.zero_le _) c.property)⟩,
    ⟨c.val.2, YoungDiagram.mem_iff_lt_rowLen.mp c.property⟩⟩
  invFun c := ⟨(c.1.val, c.2.val), YoungDiagram.mem_iff_lt_rowLen.mpr c.2.isLt⟩
  left_inv c := Subtype.ext rfl
  right_inv c := by rcases c with ⟨⟨i, hi⟩, ⟨j, hj⟩⟩; rfl

lemma card_eq_sum_rowLens (μ : YoungDiagram) : μ.card = μ.rowLens.sum := by
  classical
  have h := Fintype.card_congr (rowCellEquiv μ)
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fin] at h
  change μ.card = ∑ x : Fin (μ.colLen 0), μ.rowLen x at h
  rw [h, YoungDiagram.rowLens]
  rw [← List.sum_toFinset _ List.nodup_range]
  have he : (List.range (μ.colLen 0)).toFinset = Finset.range (μ.colLen 0) := by
    ext i; simp
  rw [he]
  exact Fin.sum_univ_eq_sum_range μ.rowLen (μ.colLen 0)

/- Conversion from Mathlib's partition type to its Young diagram. -/
def partitionDiagram {n : ℕ} (p : Nat.Partition n) : YoungDiagram :=
  YoungDiagram.ofRowLens (p.parts.sort (· ≥ ·)) (Multiset.pairwise_sort _ _).sortedGE

lemma partitionDiagram_rowLens {n : ℕ} (p : Nat.Partition n) :
    (partitionDiagram p).rowLens = p.parts.sort (· ≥ ·) := by
  apply YoungDiagram.rowLens_ofRowLens_eq_self
  intro a ha
  exact p.parts_pos (by simpa only [← Multiset.mem_coe, Multiset.sort_eq] using ha)

lemma partitionDiagram_card {n : ℕ} (p : Nat.Partition n) : (partitionDiagram p).card = n := by
  rw [card_eq_sum_rowLens, partitionDiagram_rowLens, ← Multiset.sum_coe,
    Multiset.sort_eq, p.parts_sum]

def partitionTableau {n : ℕ} (p : Nat.Partition n) : Tableau n (partitionDiagram p) :=
  canonicalTableau _ (partitionDiagram_card p)

/- Cycle-type partition, with only the definitional `card (Fin n)=n` transport. -/
def permPartition {n : ℕ} (g : Equiv.Perm (Fin n)) : Nat.Partition n :=
  ⟨g.partition.parts, g.partition.parts_pos, g.partition.parts_sum.trans (Fintype.card_fin n)⟩

lemma isConj_of_permPartition_eq {n : ℕ} {g h : Equiv.Perm (Fin n)}
    (hh : permPartition g = permPartition h) : IsConj g h := by
  apply Equiv.Perm.partition_eq_of_isConj.mpr
  have hp := congrArg (fun p : Nat.Partition n => p.parts) hh
  exact Nat.Partition.ext hp

/- Class functions on the symmetric group, indexed by cycle type. -/
def classFunctions (n : ℕ) : Submodule ℂ (Equiv.Perm (Fin n) → ℂ) where
  carrier := {f | ∀ g h, permPartition g = permPartition h → f g = f h}
  zero_mem' := by
    change ∀ g h, permPartition g = permPartition h → (0 : Equiv.Perm (Fin n) → ℂ) g = 0
    intro g h hh; rfl
  add_mem' := by intro f h hf hh g k hk; simp only [Pi.add_apply, hf g k hk, hh g k hk]
  smul_mem' := by intro c f hf g k hk; simp only [Pi.smul_apply, hf g k hk]

/- Select one representative where a cycle partition is realized; unused
coordinates are zero. This gives an injection even without surjectivity of
cycle-type realization. -/
def classEvaluation (n : ℕ) : (classFunctions n) →ₗ[ℂ] (Nat.Partition n → ℂ) where
  toFun f p := if h : ∃ g : Equiv.Perm (Fin n), permPartition g = p then f.val h.choose else 0
  map_add' f h := by
    ext p
    simp only [Pi.add_apply, Submodule.coe_add]
    split_ifs <;> simp
  map_smul' c f := by
    ext p
    simp only [Pi.smul_apply, Submodule.coe_smul, RingHom.id_apply]
    split_ifs <;> simp

lemma char_mem_classFunctions {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    [Module.Finite ℂ V] (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) :
    ρ.character ∈ classFunctions n := by
  intro g h he
  obtain ⟨k, rfl⟩ := isConj_iff.mp (isConj_of_permPartition_eq he)
  exact (Representation.char_conj ρ g k).symm

/- Character of the actual Specht module as an actual class function. -/
def spechtCharacter {n : ℕ} (p : Nat.Partition n) : classFunctions n :=
  ⟨(spechtRep (partitionTableau p)).character, char_mem_classFunctions _⟩

/- Bilinear character scalar product used by the finite-group orthogonality theorem. -/
def charFunctional {G : Type uG} [Group G] [Fintype G] (y : G → ℂ) : (G → ℂ) →ₗ[ℂ] ℂ where
  toFun x := (Nat.card G : ℂ)⁻¹ * ∑ g, x g * y g⁻¹
  map_add' x z := by simp [Finset.sum_add_distrib, add_mul, mul_add]
  map_smul' c x := by simp [Finset.mul_sum, mul_assoc, mul_left_comm]

/- A Specht constituent of a `d`-letter position representation has at most
`d` rows, proved by the genuine first-column antisymmetrizer. -/
end Saxl

end

end OAI


