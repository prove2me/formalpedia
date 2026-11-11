-- Prove2me | Definitions.Def_LabelSymmetricCollision215_Collision_Specht
-- name    : LabelSymmetricCollision215_Collision_Specht
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:57:47.715835+00:00
-- url     : https://prove2.me/theorems/8f34b703-d251-4073-abe6-d5b18cf6dcb9
-- title:
--   Published Specht factors and the full bottom representation
-- statement:
--   Partitions are Young diagrams with exactly $n$ boxes; the published height bound $n$ excludes no partition of $n$. Standard Young tableaux are the published order-increasing bijective fillings of the cells. The Specht module is the published complex Young left ideal in the regular symmetric-group module, with the published left action, transported from $\operatorname{Fin}N$ to cyclic labels by the canonical equivalence.
--
--   For every partition $\mu$ of $s$ and $N\ge2s$, the diagram $(N-s,\mu)$ is constructed by adding its first row. The bottom representation is the product, equivalently finite direct sum, of one such actual Specht module for each standard tableau of each $\mu$. Decomposition means existence of a complex linear equivalence intertwining the concrete label actions. Restrictions of ambient actions are expressed using the canonical orthogonal projection onto the invariant subspace.
--
--   No eigenspace identity, irreducibility, dimension estimate, or decomposition is assumed in this definition.
-- source:
--   Frédéric Magniez, Sebastian Zur, Tight Time-Space Lower Bounds for Collision Finding and Element Distinctness under Label Symmetry, STOC 2027 submission #215 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/215.pdf, §§2.2,4.3,6; PDF 11–12,24–26,43–46 / printed 9–10,22–24,41–44

import Definitions.Def_LabelSymmetricCollision215_Collision_Tensor
import Definitions.Def_QAlgorithms_Defs_SpechtModules
import Definitions.Def_OAI_RepresentationTheory_PartialPermutation_StandardTableaux

noncomputable section
open scoped ComplexConjugate

namespace LabelSymmetricCollision215.Collision
attribute [local instance] Classical.propDecidable

/-! Concrete Specht modules are the published complex Young left ideals. No spectral
or dimension property is part of this definition. Tableaux use the published standard fillings. -/
abbrev Shape (n : ℕ) := QAlgorithms.Schur.Partition n n
abbrev SYT {n : ℕ} (μ : Shape n) := OAI.PartialPermutation.Tableau.StandardFilling μ.val.cells

def shiftCell : (ℕ × ℕ) ↪ (ℕ × ℕ) :=
  ⟨fun c => (c.1+1,c.2), by intro a b h; cases a; cases b; simp_all⟩

/-- Adding a first row to a Young diagram; the width condition is structural. -/
def prepend (k : ℕ) (μ : YoungDiagram) (hk : μ.rowLen 0 ≤ k) : YoungDiagram where
  cells := ({0} ×ˢ Finset.range k) ∪ μ.cells.map shiftCell
  isLowerSet := by
    rintro ⟨i,j⟩ ⟨a,b⟩ ⟨ha,hb⟩ hc
    simp only [Finset.mem_coe, Finset.mem_union, Finset.mem_product,
      Finset.mem_singleton, Finset.mem_range, Finset.mem_map] at hc ⊢
    rcases hc with ⟨hi,hj⟩ | ⟨⟨r,c⟩,hcell,heq⟩
    · left; exact ⟨by omega, lt_of_le_of_lt hb hj⟩
    · change (r+1,c) = (i,j) at heq
      have he : i = r+1 ∧ j = c := Prod.mk.inj heq.symm
      have hc0 : c < μ.rowLen 0 :=
        (μ.mem_iff_lt_rowLen).mp (μ.up_left_mem (Nat.zero_le r) le_rfl hcell)
      by_cases h : a = 0
      · left; exact ⟨h, lt_of_le_of_lt hb (he.2 ▸ lt_of_lt_of_le hc0 hk)⟩
      · right
        refine ⟨(a-1,b), μ.up_left_mem (by omega) (by omega) hcell, ?_⟩
        change (a-1+1,b) = (a,b)
        have ha1 : a-1+1 = a := by omega
        rw [ha1]

/-- Cardinality API needed to number the new Young diagram. -/
theorem prepend_card (k : ℕ) (μ : YoungDiagram) (hk : μ.rowLen 0 ≤ k) :
    (prepend k μ hk).card = k + μ.card := by
  change (({0} ×ˢ Finset.range k) ∪ μ.cells.map shiftCell).card = _
  rw [Finset.card_union_of_disjoint]
  · simp [YoungDiagram.card]
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hx
    obtain ⟨c,hc,rfl⟩ := Finset.mem_map.mp hy
    simp [shiftCell] at hx

/-- First-row width is bounded by the number of cells, so every partition of s fits. -/
theorem width_le_card (μ : YoungDiagram) : μ.rowLen 0 ≤ μ.card := by
  rw [μ.rowLen_eq_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)

def liftedShape {N s : ℕ} (h : 2*s ≤ N) (μ : Shape s) : QAlgorithms.Schur.Partition (N+1) N := by
  have hw : μ.val.rowLen 0 ≤ N-s := by
    have hw := width_le_card μ.val
    rw [μ.property.1] at hw
    omega
  refine ⟨prepend (N-s) μ.val hw, ?_, ?_⟩
  · rw [prepend_card, μ.property.1]; omega
  · have hh : (prepend (N-s) μ.val hw).colLen 0 ≤ (prepend (N-s) μ.val hw).card := by
      rw [YoungDiagram.colLen_eq_card]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    rw [prepend_card, μ.property.1] at hh
    omega

abbrev Specht {d n : ℕ} (lam : QAlgorithms.Schur.Partition d n) :=
  QAlgorithms.Schur.spechtSpace lam

def labelFin {N : ℕ} [NeZero N] : ZMod N ≃ Fin N := (ZMod.finEquiv N).toEquiv.symm

def spechtAction {d N : ℕ} [NeZero N] (lam : QAlgorithms.Schur.Partition d N)
    (σ : Equiv.Perm (ZMod N)) : Specht lam →ₗ[ℂ] Specht lam :=
  QAlgorithms.Schur.spechtRepresentation lam ((labelFin).symm.trans (σ.trans labelFin))

abbrev BottomSum {N s : ℕ} (h : 2*s ≤ N) :=
  (μ : Shape s) → SYT μ → Specht (liftedShape h μ)

def bottomAction {N s : ℕ} [NeZero N] (h : 2*s ≤ N)
    (σ : Equiv.Perm (ZMod N)) (v : BottomSum h) : BottomSum h :=
  fun μ t => spechtAction (liftedShape h μ) σ (v μ t)

/-- Representation isomorphism expressed by a complex linear equivalence and its intertwining law. -/
def TensorDecomposition {N s : ℕ} [NeZero N] (h : 2*s ≤ N)
    (K : Submodule ℂ (H (Tuple N s))) : Prop :=
  ∃ e : K ≃ₗ[ℂ] BottomSum h, ∀ σ (v : K),
    e (K.orthogonalProjectionOnto (tupleAction N s σ (v : H (Tuple N s)))) =
      bottomAction h σ (e v)

def EigenDecomposition {N s : ℕ} [NeZero N] (h : 2*s ≤ N) (a : ℝ) : Prop :=
  ∃ e : eigenSpace N s a ≃ₗ[ℂ] BottomSum h, ∀ σ (v : eigenSpace N s a),
    e ((eigenSpace N s a).orthogonalProjectionOnto
      (injectiveAction N s σ (v : H (InjectiveTuple N s)))) = bottomAction h σ (e v)

end LabelSymmetricCollision215.Collision


