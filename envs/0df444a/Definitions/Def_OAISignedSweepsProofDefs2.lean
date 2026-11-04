-- Prove2me | Definitions.Def_OAISignedSweepsProofDefs2
-- name    : OAISignedSweepsProofDefs2
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:08:25.878916+00:00
-- url     : https://prove2.me/theorems/88cce06c-40ba-4cd2-a644-169e274c05b8
-- title:
--   Marked word spaces and marked type projections for signed sweep moments
-- statement:
--   This block extends `OAISignedSweepsProofDefs` with the objects of the marked-word trace in the signed sweep moment induction.
--
--   1. **Moving marks.** For $g\in S_n$ and an injection $z$ of $l$ marks into $n$ positions, `moveMarks` is $g\circ z$. `moveComplement`, `markedSpinTransport` and `markedTargetTransport` transport the unmarked positions, as permutations of $\{1,\dots,p\}$ with $p+l=n$.
--
--   2. **Marked word space.** `HilbertFibers Z E` is the $\ell^2$ sum of copies of $E$ over $Z$, with diagonal operators `fiberDiagonal`. `MarkedWordSpace p l n C` is the sum, over mark assignments, of word spaces on the unmarked sites in the alphabet $C\sqcup C$. `markedWordRepresentation` is the action of $S_n$ moving marks and transporting words with the signed action, and `markedTypeProjection` is the fibrewise signed type projection.
--
--   3. **Partitions.** `partitionFintype` makes the partitions of $n$ a finite type, using `partition_mem_bounds`.
--
--   These are the objects of Section 3.2 of the source, eq. (15).
--
--   **Formalization Note** The declarations are reproduced verbatim from the upstream modules, together with short structural lemmas their bodies need (for instance, that moving marks is an action).
-- source:
--   OpenAI, "Signed tensor densities and diagram budgets for the Thorp shuffle" (September 26, 2026), openai/math preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf, Section 3.2. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SignedSweeps/ (openai/math, Apache-2.0)

-- Carved from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0),
-- lean/OAI/Probability/SignedSweeps/, ported to Lean 4.33.1 / Mathlib 0df444a.
-- The mathematics and the Lean code are OpenAI's.

import Mathlib
import Definitions.Def_SignedSweepMoment
import Definitions.Def_OAISignedSweepsProofDefs

section
-- module OAI.Probability.SignedSweeps.BaseCases
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module

lemma partition_mem_bounds {n : ℕ} (lam : Partition n) {c : ℕ × ℕ}
    (hc : c ∈ lam.1.cells) : c.1 < n ∧ c.2 < n := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hc' := YoungDiagram.mem_iff_lt_colLen.mp hc
  have hrb : lam.1.rowLen c.1 ≤ n := by
    rw [YoungDiagram.rowLen_eq_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
  have hcb : lam.1.colLen c.2 ≤ n := by
    rw [YoungDiagram.colLen_eq_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq lam.2
  exact ⟨hc'.trans_le hcb, hr.trans_le hrb⟩

instance partitionFinite (n : ℕ) : Finite (Partition n) := by
  let f : Partition n → {s // s ∈ (Finset.range n ×ˢ Finset.range n).powerset} :=
    fun lam => ⟨lam.1.cells, Finset.mem_powerset.mpr (by
      intro c hc
      simpa only [Finset.mem_product, Finset.mem_range] using partition_mem_bounds lam hc)⟩
  apply Finite.of_injective f
  intro a b h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.TraceDecomposition
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct
open Module
open scoped BigOperators
open scoped BigOperators ComplexOrder Classical
open scoped BigOperators TensorProduct ComplexOrder Classical
open scoped BigOperators Classical

instance partitionFintype (n : ℕ) : Fintype (Partition n) := Fintype.ofFinite _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedSites
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def moveMarks {l n : ℕ} (g : SymmetricGroup n) (z : MarkedAssignment l n) :
    MarkedAssignment l n := z.trans g.toEmbedding

@[simp] lemma moveMarks_apply {l n : ℕ} (g : SymmetricGroup n)
    (z : MarkedAssignment l n) (a : Fin l) : moveMarks g z a = g (z a) := rfl

@[simp] lemma moveMarks_one {l n : ℕ} (z : MarkedAssignment l n) : moveMarks 1 z = z := by
  ext a; rfl

@[simp] lemma moveMarks_mul {l n : ℕ} (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) : moveMarks (g*t) z = moveMarks g (moveMarks t z) := by
  ext a; rfl

def moveComplement {l n : ℕ} (g : SymmetricGroup n) (z : MarkedAssignment l n) :
    MarkedComplement z ≃ MarkedComplement (moveMarks g z) where
  toFun x := ⟨g x.1, by
    rintro ⟨a,ha⟩
    exact x.2 ⟨a,g.injective ha⟩⟩
  invFun x := ⟨g.symm x.1, by
    rintro ⟨a,ha⟩
    apply x.2
    exact ⟨a,by simp only [moveMarks_apply, ha, Equiv.apply_symm_apply]⟩⟩
  left_inv x := by apply Subtype.ext; exact g.symm_apply_apply _
  right_inv x := by apply Subtype.ext; exact g.apply_symm_apply _

def markedSpinTransport {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : SymmetricGroup p :=
  (markedSites h z).trans ((moveComplement g z).trans (markedSites h (moveMarks g z)).symm)

lemma markedSpinTransport_sites {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) (i : Fin p) :
    markedInjection h (moveMarks g z) (markedSpinTransport h g z i) =
      g (markedInjection h z i) := by
  change ((markedSites h (moveMarks g z))
    ((markedSites h (moveMarks g z)).symm (moveComplement g z (markedSites h z i)))).1 = _
  rw [Equiv.apply_symm_apply]
  rfl

@[simp] lemma markedSpinTransport_one {p l n : ℕ} (h : p+l=n) (z : MarkedAssignment l n) :
    markedSpinTransport h 1 z = 1 := by
  apply Equiv.ext
  intro i
  apply (markedInjection h z).injective
  simpa using markedSpinTransport_sites h 1 z i

lemma markedSpinTransport_mul {p l n : ℕ} (h : p+l=n) (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedSpinTransport h (g*t) z = markedSpinTransport h g (moveMarks t z) *
      markedSpinTransport h t z := by
  apply Equiv.ext
  intro i
  apply (markedInjection h (moveMarks (g*t) z)).injective
  rw [markedSpinTransport_sites, moveMarks_mul]
  change (g*t) (markedInjection h z i) =
    markedInjection h (moveMarks g (moveMarks t z))
      (markedSpinTransport h g (moveMarks t z) (markedSpinTransport h t z i))
  rw [markedSpinTransport_sites, markedSpinTransport_sites]
  rfl

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.HilbertFibers
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module
variable {Z E : Type*} [Fintype Z]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

abbrev HilbertFibers (Z E : Type*) [Fintype Z] [NormedAddCommGroup E] :=
  PiLp 2 (fun _ : Z => E)

def fiberDiagonal (A : Z → E →ₗ[ℂ] E) : HilbertFibers Z E →ₗ[ℂ] HilbertFibers Z E where
  toFun x := WithLp.toLp 2 (fun z => A z (x.ofLp z))
  map_add' x y := by apply PiLp.ext; intro z; exact map_add (A z) _ _
  map_smul' c x := by apply PiLp.ext; intro z; exact map_smul (A z) _ _

end SignedSweeps
end

end OAI
end

section
-- module OAI.Probability.SignedSweeps.MarkedWords
namespace OAI

noncomputable section
namespace SignedSweeps
open scoped BigOperators TensorProduct Classical
open Module

def markedTargetTransport {p l n : ℕ} (h : p+l=n) (g : SymmetricGroup n)
    (z : MarkedAssignment l n) : SymmetricGroup p := (markedSpinTransport h g⁻¹ z)⁻¹

@[simp] lemma markedTargetTransport_one {p l n : ℕ} (h : p+l=n)
    (z : MarkedAssignment l n) : markedTargetTransport h 1 z = 1 := by
  simp [markedTargetTransport]

lemma markedTargetTransport_mul {p l n : ℕ} (h : p+l=n) (g t : SymmetricGroup n)
    (z : MarkedAssignment l n) :
    markedTargetTransport h (g*t) z = markedTargetTransport h g z *
      markedTargetTransport h t (moveMarks g⁻¹ z) := by
  simp only [markedTargetTransport, mul_inv_rev, markedSpinTransport_mul]

abbrev MarkedWordSpace (p l n : ℕ) (C : Type*) [Fintype C] :=
  HilbertFibers (MarkedAssignment l n) (WordSpace p (C ⊕ C))

def markedWordLinear {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) :
    MarkedWordSpace p l n C →ₗ[ℂ] MarkedWordSpace p l n C where
  toFun f := WithLp.toLp 2 (fun z =>
    signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)))
  map_add' f k := by apply PiLp.ext; intro z; exact map_add _ _ _
  map_smul' c f := by apply PiLp.ext; intro z; exact map_smul (signedWordRepresentation p C (markedTargetTransport h g z)) c _

@[simp] lemma markedWordLinear_apply {p l n : ℕ} {C : Type*} [Fintype C]
    (h : p+l=n) (g : SymmetricGroup n) (f : MarkedWordSpace p l n C)
    (z : MarkedAssignment l n) :
    (markedWordLinear h g f).ofLp z =
      signedWordRepresentation p C (markedTargetTransport h g z) (f.ofLp (moveMarks g⁻¹ z)) := rfl

def markedWordRepresentation {p l n : ℕ} (h : p+l=n) (C : Type*) [Fintype C] :
    Representation ℂ (SymmetricGroup n) (MarkedWordSpace p l n C) where
  toFun := markedWordLinear h
  map_one' := by
    apply LinearMap.ext
    intro f
    apply PiLp.ext
    intro z
    simp only [markedWordLinear_apply, inv_one, moveMarks_one, markedTargetTransport_one,
      map_one, Module.End.one_apply]
  map_mul' g t := by
    apply LinearMap.ext
    intro f
    apply PiLp.ext
    intro z
    simp only [Module.End.mul_apply, markedWordLinear_apply, markedTargetTransport_mul,
      map_mul, mul_inv_rev, moveMarks_mul]

def markedTypeProjection {u v p l n : ℕ} (hu : u+v=p) (_h : p+l=n)
    (a : Partition u) (b : Partition v) (C : Type*) [Fintype C] :
    MarkedWordSpace p l n C →ₗ[ℂ] MarkedWordSpace p l n C :=
  fiberDiagonal (fun _ => pairTypeProjection hu a b C)

end SignedSweeps
end

end OAI
end


