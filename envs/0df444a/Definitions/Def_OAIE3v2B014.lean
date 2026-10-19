-- Prove2me | Definitions.Def_OAIE3v2B014
-- name    : OAIE3v2B014
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:58:20.274197+00:00
-- url     : https://prove2.me/theorems/bf7df708-e419-4703-8c65-51a095958485
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 15 of 311
-- statement:
--   Definitions bundle 15 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/BooleanCubeProduct.lean`, `Estimates/CommonDependentWordLayers.lean`, `Estimates/DenseTranslate.lean`, `Estimates/FreimanFivefoldCardinality.lean`, `Estimates/FreimanInverseLift.lean`, `Estimates/ImageRepresentatives.lean`, `Estimates/LieTreeMultidegree.lean`, `Estimates/MixedPrimitiveGowers.lean`, `Estimates/NativeCrossFactorization.lean`, `Estimates/PositiveCyclicCorrelation.lean`, `Estimates/RationalTagConstraintSpaces.lean`, `Estimates/SmallDifferenceGrowth.lean`, `FixedDensity/BooleanCutReduction.lean`, `FixedDensity/BundleCountingRecurrence.lean`, `FixedDensity/CountExtraction.lean`, `FixedDensity/Energy.lean`, `FixedDensity/HypergraphBundleEnvelopeSelection.lean`, `FixedDensity/HypergraphBundleFiltration.lean`, `FixedDensity/OrderedRemovalAssembly.lean`, `FixedDensity/PolynomialApproximation.lean`, `FixedDensity/RankwiseBundleEnvelopeSelection.lean`, `FixedDensity/ShortInterval.lean`, `FixedDensity/SourceFullBundleRemovalParameters.lean`, `FixedDensity/SourceFullCoarseTargetRegularity.lean`, `FixedDensity/StrongOrderedComplexRegularity.lean`, `FixedDensity/TowerDominatingGrowth.lean`, `Geometry/DenseRealBoxCell.lean`, `Geometry/LieStructureTransport.lean`, `Lattices/CommonIntegerIntervalCorrelation.lean`, `Lattices/IntegerVectorFreimanEmbedding.lean`, `Lattices/NativeProperAffineRecovery.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G]

noncomputable def additiveQuadrupleCorrelation (g : G → G → ℂ) (a h k : G) : ℝ :=
  ‖𝔼 x, star (g h x) * g (h - a) (x + a) * g k x * star (g (k - a) (x + a))‖

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieStructureTransport
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

variable [DecidableEq ι] [DecidableEq κ]

theorem basisMatrix_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (S : Matrix ι κ ℚ)
    (hS : LinearMap.toMatrix e b φ * S = 1) (x : M) :
    φ (Matrix.toLin b e S x) = x := by
  apply b.equivFun.injective
  change (b.repr (φ (Matrix.toLin b e S x)) : κ → ℚ) = b.repr x
  rw [← LinearMap.toMatrix_mulVec_repr e b φ, Matrix.repr_toLin,
    Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

def integerCyclicMap (N : ℕ) : ℤ →+ ZMod N := Int.castAddHom (ZMod N)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable (I : Type*) [Fintype I]

noncomputable def finiteLieTrees : ℕ → Finset (FreeMagma I)
  | 0 => ∅
  | n + 1 => by
    classical
    exact (Finset.univ.image FreeMagma.of) ∪
      (((finiteLieTrees n).product (finiteLieTrees n)).image (fun z => z.1 * z.2))

theorem finiteLieTrees_card_le (n : ℕ) :
    (finiteLieTrees I n).card ≤ (Fintype.card I + 2) ^ (3 ^ n) := by
  classical
  induction n with
  | zero => simp only [finiteLieTrees, Finset.card_empty, Nat.zero_le]
  | succ n ih =>
    let B := (Fintype.card I + 2) ^ (3 ^ n)
    have hB : Fintype.card I + 2 ≤ B := by
      simpa only [pow_one] using Nat.pow_le_pow_right
        (show 0 < Fintype.card I + 2 by omega)
        (show 1 ≤ 3 ^ n from pow_pos (show 0 < (3 : ℕ) by norm_num) n)
    have hm : Fintype.card I ≤ B ^ 2 := by
      have h := Nat.le_mul_of_pos_right B (show 0 < B by omega)
      nlinarith
    have hrec : (finiteLieTrees I (n + 1)).card ≤
        Fintype.card I + (finiteLieTrees I n).card ^ 2 := by
      apply (Finset.card_union_le _ _).trans
      have h1 := Finset.card_image_le (s := (Finset.univ : Finset I)) (f := FreeMagma.of)
      have h2 : (((finiteLieTrees I n).product (finiteLieTrees I n)).image
          (fun z => z.1 * z.2)).card ≤ (finiteLieTrees I n).card * (finiteLieTrees I n).card := by
        exact Finset.card_image_le.trans_eq (Finset.card_product _ _)
      simp only [Finset.card_univ] at h1
      simpa only [pow_two] using Nat.add_le_add h1 h2
    calc
      _ ≤ Fintype.card I + B ^ 2 := hrec.trans (Nat.add_le_add_left (Nat.pow_le_pow_left ih 2) _)
      _ ≤ B ^ 2 + B ^ 2 := Nat.add_le_add_right hm _
      _ = 2 * B ^ 2 := by omega
      _ ≤ B * B ^ 2 := Nat.mul_le_mul_right (B ^ 2) (show 2 ≤ B by omega)
      _ = B ^ 3 := by ring
      _ = _ := by dsimp [B]; rw [show 3 ^ (n + 1) = 3 ^ n * 3 from pow_succ 3 n, pow_mul]

end Erdos3

end

section

namespace Erdos3

variable {I σ : Type*}

noncomputable def markedGeneratorGrade (w : I → ℕ) (marked : I → Bool) (i : I) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 (w i) + Finsupp.single 1 (if marked i then 1 else 0) + Finsupp.single 2 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ImageRepresentatives
namespace OAI

section

namespace Erdos3

open Module

def lieTreeHeight (d H n : ℕ) : ℕ := (d ^ 2 + H + 2) ^ ((3 * d ^ 2 + 3) ^ n)

theorem lieTreeHeight_ge_input (d H n : ℕ) : H ≤ lieTreeHeight d H n := by
  unfold lieTreeHeight
  have hE : 1 ≤ (3 * d ^ 2 + 3) ^ n := Nat.one_le_pow _ _ (by omega)
  calc
    H ≤ d ^ 2 + H + 2 := by omega
    _ = (d ^ 2 + H + 2) ^ 1 := (pow_one _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) hE

theorem lieTreeHeight_mono (d H : ℕ) : Monotone (lieTreeHeight d H) := by
  intro i j hij
  unfold lieTreeHeight
  exact Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by omega) hij)

theorem lieTreeHeight_step (d H n : ℕ) :
    (d ^ 2 + 1) * (H * lieTreeHeight d H n * lieTreeHeight d H n) ^ (d ^ 2) ≤
      lieTreeHeight d H (n + 1) := by
  let A := d ^ 2 + H + 2
  let N := d ^ 2
  let E := (3 * N + 3) ^ n
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hH : H ≤ A := by dsimp [A]; omega
  have hN : N + 1 ≤ A := by dsimp [A, N]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  change (N + 1) * (H * A ^ E * A ^ E) ^ N ≤ A ^ ((3 * N + 3) ^ (n + 1))
  calc
    _ ≤ A * (A * A ^ E * A ^ E) ^ N := by gcongr
    _ = A ^ (1 + (1 + 2 * E) * N) := by
      rw [← pow_succ', ← pow_add, ← pow_mul, ← pow_succ']
      congr 1
      ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right hA
      rw [pow_succ]
      change 1 + (1 + 2 * E) * N ≤ E * (3 * N + 3)
      nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def cubeCarryShift (d N : ℕ) (b : (Fin d → Bool) → Fin (d + 1)) : (Fin d → Bool) → ℤ :=
  fun ω => -((b ω).val : ℤ) * N

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonIntegerIntervalCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def integerGridEnd (b L : ℕ) : ℕ := L * (b / L)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DenseRealBoxCell
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem card_image_eq_of_same_fibers {α β γ : Type*} [Nonempty α]
    [DecidableEq β] [DecidableEq γ] (A : Finset α) (f : α → β) (g : α → γ)
    (hrel : ∀ x ∈ A, ∀ y ∈ A, f x = f y ↔ g x = g y) :
    (A.image f).card = (A.image g).card := by
  classical
  let r := Function.invFunOn f (A : Set α)
  have hr {y : β} (hy : y ∈ A.image f) : r y ∈ A ∧ f (r y) = y :=
    Function.invFunOn_pos (Finset.mem_image.mp hy)
  have hinj : Set.InjOn (g ∘ r) (A.image f : Set β) := by
    intro y hy z hz h
    have he := (hrel (r y) (hr hy).1 (r z) (hr hz).1).mpr h
    simpa only [(hr hy).2, (hr hz).2] using he
  have himage : (A.image f).image (g ∘ r) = A.image g := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image.mpr ⟨r y, (hr hy).1, rfl⟩
    · intro hz
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
      have hfx : f x ∈ A.image f := Finset.mem_image.mpr ⟨x, hx, rfl⟩
      exact Finset.mem_image.mpr ⟨f x, hfx,
        (hrel (r (f x)) (hr hfx).1 x hx).mp (hr hfx).2⟩
  rw [← himage, Finset.card_image_of_injOn hinj]

theorem card_difference_image_of_freiman {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (f : G → H)
    (hf : IsAddFreimanIso 2 (A : Set G) (A.image f : Set H) f) :
    ((A.image f - A.image f).card : ℕ) = (A - A).card := by
  have hrel : ∀ x ∈ A ×ˢ A, ∀ y ∈ A ×ˢ A,
      x.1 - x.2 = y.1 - y.2 ↔ f x.1 - f x.2 = f y.1 - f y.2 := by
    intro x hx y hy
    obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    rw [sub_eq_sub_iff_add_eq_add, sub_eq_sub_iff_add_eq_add]
    exact (hf.add_eq_add hx1 hy2 hy1 hx2).symm
  have hcard := card_image_eq_of_same_fibers (A ×ˢ A)
    (fun x => x.1 - x.2) (fun x => f x.1 - f x.2) hrel
  have hout : (A ×ˢ A).image (fun x => f x.1 - f x.2) = A.image f - A.image f := by
    ext z
    constructor
    · intro hz
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      exact Finset.mem_sub.mpr ⟨f x, Finset.mem_image.mpr ⟨x, hx, rfl⟩,
        f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩, rfl⟩
    · intro hz
      obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hz
      obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp hu
      obtain ⟨y, hy, hyv⟩ := Finset.mem_image.mp hv
      exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩,
        by change f x - f y = z; rw [hxu, hyv]; exact huv⟩
  simpa only [hout, Finset.image_sub_product] using hcard.symm

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCrossFactorization
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

noncomputable def nativeCrossResidual {N : ℕ} (f₀ f₁ : ZMod N → ℂ)
    (m : ZMod N → ZMod N → ℂ) (h : ZMod N) (_ : Unit) (x : ZMod N) : ℂ :=
  f₀ x * star (f₁ (x + h)) * star (m h x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTagConstraintSpaces
namespace OAI

section

namespace Erdos3.VectorPolynomial

structure RationalTagConstraint {m : ℕ} (J : Fin m → Type*) where
  tag : Fin m
  count : ℕ
  generators : Fin count → J tag → ℚ

namespace RationalTagConstraint

variable {m : ℕ} {J : Fin m → Type*}

def member (c : RationalTagConstraint J) {X : Type*}
    (point : (X ⊕ (Σ j, J j)) → ℝ) : Prop :=
  (fun i => point (Sum.inr ⟨c.tag, i⟩)) ∈
    Submodule.span ℝ (Set.range (fun a i => (c.generators a i : ℝ)))

end RationalTagConstraint

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonDependentWordLayers
namespace OAI

section

namespace Erdos3

def markedGradeRegion (d k l : ℕ) : Set (Fin 3 →₀ ℕ) :=
  {α | d ≤ α 0 ∧ k ≤ α 1 ∧ l ≤ α 2}

theorem markedGradeRegion_inter (d k l e m n : ℕ) :
    markedGradeRegion (max d e) (max k m) (max l n) =
      markedGradeRegion d k l ∩ markedGradeRegion e m n := by
  ext α
  simp only [markedGradeRegion, Set.mem_ofPred_eq, Set.mem_inter_iff, max_le_iff]
  tauto

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DenseTranslate
namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem exists_dense_translate {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A P : Finset G) (hA : A.Nonempty) {δ q : ℝ} (hδ : 0 < δ) (hq : 0 < q)
    (hbound : ((A - P).card : ℝ) ≤ q) (hsize : δ * q ≤ (P.card : ℝ)) :
    ∃ t ∈ A - P, ∃ F ⊆ A, F.Nonempty ∧ δ * A.card ≤ (F.card : ℝ) ∧
      ∀ a ∈ F, a - t ∈ P := by
  classical
  have hApos : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hPpos : (0 : ℝ) < P.card := (mul_pos hδ hq).trans_le hsize
  have hP : P.Nonempty := Finset.card_pos.mp (by exact_mod_cast hPpos)
  have hD : (A - P).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    obtain ⟨p, hp⟩ := hP
    exact ⟨a - p, Finset.mem_sub.mpr ⟨a, ha, p, hp, rfl⟩⟩
  have hcount : (A - P).card • (δ * (A.card : ℝ)) ≤ ((A ×ˢ P).card : ℝ) := by
    rw [nsmul_eq_mul, Finset.card_product, Nat.cast_mul]
    calc
      _ ≤ q * (δ * A.card) := mul_le_mul_of_nonneg_right hbound (by positivity)
      _ = (A.card : ℝ) * (δ * q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsize (Nat.cast_nonneg A.card)
  obtain ⟨t, ht, hlarge⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (s := A ×ˢ P) (t := A - P) (f := fun x => x.1 - x.2)
    (fun x hx => Finset.mem_sub.mpr
      ⟨x.1, (Finset.mem_product.mp hx).1, x.2, (Finset.mem_product.mp hx).2, rfl⟩)
    hD hcount
  let T := (A ×ˢ P).filter fun x => x.1 - x.2 = t
  let F := T.image Prod.fst
  have hinj : Set.InjOn (Prod.fst : G × G → G) (T : Set (G × G)) := by
    intro x hx y hy hxy
    have hx' := (Finset.mem_filter.mp hx).2
    have hy' := (Finset.mem_filter.mp hy).2
    apply Prod.ext hxy
    have h := hx'.trans hy'.symm
    rw [hxy] at h
    exact sub_right_inj.mp h
  have hcard : F.card = T.card := Finset.card_image_of_injOn hinj
  have hFlarge : δ * A.card ≤ (F.card : ℝ) := by rw [hcard]; exact hlarge
  have hFpos : (0 : ℝ) < F.card := (mul_pos hδ hApos).trans_le hFlarge
  refine ⟨t, ht, F, ?_, Finset.card_pos.mp (by exact_mod_cast hFpos), hFlarge, ?_⟩
  · intro a ha
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hx).1).1
  · intro a ha
    obtain ⟨x, hx, hxa⟩ := Finset.mem_image.mp ha
    have hx' := Finset.mem_filter.mp hx
    have heq : a - t = x.2 := by rw [← hxa, ← hx'.2]; abel
    rw [heq]
    exact (Finset.mem_product.mp hx'.1).2

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreimanInverseLift
namespace OAI

section

open scoped BigOperators Pointwise

namespace Erdos3.FreimanModel

def badMultipliers (q M : ℕ) [NeZero q] (x : ℤ) : Finset (ZMod q) :=
  Finset.univ.filter fun lam => M ∣ (lam * (x : ZMod q)).val

@[simp] lemma mem_badMultipliers {q M : ℕ} [NeZero q] {x : ℤ} {lam : ZMod q} :
    lam ∈ badMultipliers q M x ↔ M ∣ (lam * (x : ZMod q)).val := by
  simp [badMultipliers]

lemma card_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (_hM : 0 < M) {x : ℤ} (hx : (x : ZMod q) ≠ 0) :
    (badMultipliers q M x).card ≤ q / M + 1 := by
  let f : ZMod q → ℕ := fun lam => (lam * (x : ZMod q)).val / M
  rw [← Finset.card_range (q / M + 1)]
  apply Finset.card_le_card_of_injOn f
      (s := badMultipliers q M x) (t := Finset.range (q / M + 1))
  · intro lam hlam
    dsimp only [f]
    have hval := (lam * (x : ZMod q)).val_lt
    have hdiv : (lam * (x : ZMod q)).val / M ≤ q / M :=
      Nat.div_le_div_right hval.le
    simpa only [Finset.mem_coe, Finset.mem_range, Nat.succ_eq_add_one] using
      Nat.lt_succ_of_le hdiv
  · intro lam hlam mu hmu heq
    have hlamDiv : M ∣ (lam * (x : ZMod q)).val :=
      mem_badMultipliers.mp hlam
    have hmuDiv : M ∣ (mu * (x : ZMod q)).val :=
      mem_badMultipliers.mp hmu
    dsimp only [f] at heq
    have hval : (lam * (x : ZMod q)).val = (mu * (x : ZMod q)).val := by
      calc
        (lam * (x : ZMod q)).val =
            M * ((lam * (x : ZMod q)).val / M) :=
              (Nat.mul_div_cancel' hlamDiv).symm
        _ = M * ((mu * (x : ZMod q)).val / M) := by rw [heq]
        _ = (mu * (x : ZMod q)).val := Nat.mul_div_cancel' hmuDiv
    have hprod : lam * (x : ZMod q) = mu * (x : ZMod q) := by
      rw [← ZMod.natCast_zmod_val (lam * (x : ZMod q)),
        ← ZMod.natCast_zmod_val (mu * (x : ZMod q)), hval]
    exact mul_right_cancel₀ hx hprod

lemma intCast_zmod_ne_zero_of_natAbs_lt {q : ℕ} [NeZero q]
    {x : ℤ} (hx0 : x ≠ 0) (hxq : x.natAbs < q) :
    (x : ZMod q) ≠ 0 := by
  intro hx
  have hdiv : (q : ℤ) ∣ x :=
    (CharP.intCast_eq_zero_iff (ZMod q) q x).mp hx
  have hqle : q ≤ x.natAbs := by
    exact_mod_cast Int.natAbs_le_of_dvd_ne_zero hdiv hx0
  omega

lemma card_biUnion_badMultipliers_le {q M : ℕ} [NeZero q] [Fact q.Prime]
    (hM : 0 < M) {D : Finset ℤ}
    (hx : ∀ x ∈ D, (x : ZMod q) ≠ 0) :
    (D.biUnion (badMultipliers q M)).card ≤ D.card * (q / M + 1) := by
  calc
    (D.biUnion (badMultipliers q M)).card ≤
        ∑ x ∈ D, (badMultipliers q M x).card := Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ D, (q / M + 1) := by
      gcongr with x hxD
      exact card_badMultipliers_le hM (hx x hxD)
    _ = D.card * (q / M + 1) := by simp

lemma multiplier_union_card_lt {N q : ℕ} (hN : 0 < N)
    (hq : 4 * N < q) :
    N * (q / (2 * N) + 1) < q := by
  have hden : 0 < 2 * N := by omega
  have hdiv := Nat.mul_div_le q (2 * N)
  have hmul : 2 * (N * (q / (2 * N))) ≤ q := by
    calc
      2 * (N * (q / (2 * N))) = (2 * N) * (q / (2 * N)) := by ring
      _ ≤ q := hdiv
  nlinarith

theorem exists_good_multiplier {D : Finset ℤ} {N q : ℕ}
    [NeZero q] [Fact q.Prime] (hN : 0 < N) (hcard : D.card ≤ N)
    (habs : ∀ x ∈ D, x.natAbs < q) (hq : 4 * N < q) :
    ∃ lam : ZMod q, lam ≠ 0 ∧
      ∀ x ∈ D, x ≠ 0 → ¬ (2 * N ∣ (lam * (x : ZMod q)).val) := by
  classical
  let D₀ := D.erase 0
  by_cases hD₀ : D₀.Nonempty
  · let U : Finset (ZMod q) := D₀.biUnion (badMultipliers q (2 * N))
    have hxcast : ∀ x ∈ D₀, (x : ZMod q) ≠ 0 := by
      intro x hxD
      have hxD' := Finset.mem_erase.mp hxD
      exact intCast_zmod_ne_zero_of_natAbs_lt hxD'.1 (habs x hxD'.2)
    have hUcard : U.card < q := by
      calc
        U.card ≤ D₀.card * (q / (2 * N) + 1) :=
          card_biUnion_badMultipliers_le (by omega) hxcast
        _ ≤ N * (q / (2 * N) + 1) := by
          gcongr
          exact Finset.card_erase_le.trans hcard
        _ < q := multiplier_union_card_lt hN hq
    have hUne : U ≠ Finset.univ := by
      intro hEq
      have : U.card = q := by simp [hEq]
      omega
    have hex : ∃ lam : ZMod q, lam ∉ U := by
      by_contra h
      push Not at h
      apply hUne
      ext lam
      simp [h lam]
    obtain ⟨lam, hlamU⟩ := hex
    refine ⟨lam, ?_, ?_⟩
    · intro hlam0
      have hxU : (0 : ZMod q) ∈ U := by
        obtain ⟨x, hxD₀⟩ := hD₀
        apply Finset.mem_biUnion.mpr
        refine ⟨x, hxD₀, ?_⟩
        simp
      exact hlamU (by simpa [hlam0] using hxU)
    · intro x hxD hx0 hbad
      apply hlamU
      apply Finset.mem_biUnion.mpr
      exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩,
        mem_badMultipliers.mpr hbad⟩
  · refine ⟨1, one_ne_zero, ?_⟩
    intro x hxD hx0
    exfalso
    apply hD₀
    exact ⟨x, Finset.mem_erase.mpr ⟨hx0, hxD⟩⟩

lemma multiset_sum_mem_nsmul (A : Finset ℤ) {T : Multiset ℤ}
    (hT : ∀ x ∈ T, x ∈ A) : T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

def ruzsaRepresentative (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  (lam * (a : ZMod q)).val

def ruzsaColor (q s : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ℕ :=
  ruzsaRepresentative q lam a / (q / (2 * s) + 1)

def ruzsaModelMap (q M : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) : ZMod M :=
  ruzsaRepresentative q lam a

lemma ruzsaRepresentative_lt (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    ruzsaRepresentative q lam a < q := by
  exact (lam * (a : ZMod q)).val_lt

lemma ruzsaRepresentative_cast (q : ℕ) [NeZero q] (lam : ZMod q) (a : ℤ) :
    (ruzsaRepresentative q lam a : ZMod q) = lam * (a : ZMod q) := by
  exact ZMod.natCast_zmod_val _

lemma ruzsaColor_lt {q s : ℕ} [NeZero q] (lam : ZMod q)
    (hs : 0 < s) (_hq : 2 * s < q) (a : ℤ) :
    ruzsaColor q s lam a < 2 * s := by
  let L := q / (2 * s) + 1
  have hden : 0 < 2 * s := by omega
  have hqL : q < (2 * s) * L := by
    simp only [L]
    exact Nat.lt_mul_div_succ q hden
  have hrep : ruzsaRepresentative q lam a < q := ruzsaRepresentative_lt q lam a
  dsimp [ruzsaColor]
  rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
  simpa only [L] using hrep.trans hqL

lemma ruzsaRepresentative_bounds_of_color_eq {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {a : ℤ} (hcolor : ruzsaColor q s lam a = c) :
    c * (q / (2 * s) + 1) ≤ ruzsaRepresentative q lam a ∧
      ruzsaRepresentative q lam a < (c + 1) * (q / (2 * s) + 1) := by
  have hL : 0 < q / (2 * s) + 1 := Nat.succ_pos _
  have hdiv : ruzsaRepresentative q lam a / (q / (2 * s) + 1) = c := by
    simpa [ruzsaColor] using hcolor
  constructor
  · rw [← hdiv]
    simpa [mul_comm] using Nat.div_mul_le_self
      (ruzsaRepresentative q lam a) (q / (2 * s) + 1)
  · rw [← hdiv]
    simpa [mul_comm] using Nat.lt_mul_div_succ (ruzsaRepresentative q lam a) hL

def ruzsaRepresentativeSum (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) : ℕ :=
  (T.map (ruzsaRepresentative q lam)).sum

lemma ruzsaRepresentativeSum_bounds {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T : Multiset ℤ} (hcard : T.card = s) (hs : 0 < s)
    (hcolor : ∀ x ∈ T, ruzsaColor q s lam x = c) :
    s * (c * (q / (2 * s) + 1)) ≤ ruzsaRepresentativeSum q lam T ∧
      ruzsaRepresentativeSum q lam T < s * ((c + 1) * (q / (2 * s) + 1)) := by
  let L := q / (2 * s) + 1
  have hlo : T.card • (c * L) ≤ ruzsaRepresentativeSum q lam T := by
    have hlo' := Multiset.card_nsmul_le_sum
      (s := T.map (ruzsaRepresentative q lam)) (a := c * L) (by
        intro y hy
        rw [Multiset.mem_map] at hy
        obtain ⟨x, hxT, rfl⟩ := hy
        simpa only [L] using
          (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).1)
    simpa only [ruzsaRepresentativeSum, Multiset.card_map] using hlo'
  have hTne : T ≠ 0 := by
    intro hT
    simp [hT] at hcard
    omega
  have hhi : ruzsaRepresentativeSum q lam T < T.card • ((c + 1) * L) := by
    have hhi' := Multiset.sum_lt_sum_of_nonempty hTne fun x hxT =>
      (ruzsaRepresentative_bounds_of_color_eq lam (hcolor x hxT)).2
    simpa only [ruzsaRepresentativeSum, Multiset.map_const',
      Multiset.sum_replicate, L] using hhi'
  simpa only [hcard, L, Nat.nsmul_eq_mul] using And.intro hlo hhi

lemma ruzsaRepresentativeSum_sub_abs_lt {q s c : ℕ} [NeZero q]
    (lam : ZMod q) {T U : Multiset ℤ}
    (hTcard : T.card = s) (hUcard : U.card = s) (hs : 0 < s)
    (hTcolor : ∀ x ∈ T, ruzsaColor q s lam x = c)
    (hUcolor : ∀ x ∈ U, ruzsaColor q s lam x = c) :
    (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U <
        s * (q / (2 * s) + 1) ∧
      -((s * (q / (2 * s) + 1) : ℕ) : ℤ) <
        (ruzsaRepresentativeSum q lam T : ℤ) - ruzsaRepresentativeSum q lam U := by
  obtain ⟨hTlo, hThi⟩ :=
    ruzsaRepresentativeSum_bounds lam hTcard hs hTcolor
  obtain ⟨hUlo, hUhi⟩ :=
    ruzsaRepresentativeSum_bounds lam hUcard hs hUcolor
  have hTU : ruzsaRepresentativeSum q lam T <
      ruzsaRepresentativeSum q lam U + s * (q / (2 * s) + 1) := by
    nlinarith
  have hUT : ruzsaRepresentativeSum q lam U <
      ruzsaRepresentativeSum q lam T + s * (q / (2 * s) + 1) := by
    nlinarith
  have hTU' : (ruzsaRepresentativeSum q lam T : ℤ) <
      (ruzsaRepresentativeSum q lam U : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hTU
  have hUT' : (ruzsaRepresentativeSum q lam U : ℤ) <
      (ruzsaRepresentativeSum q lam T : ℤ) + s * (q / (2 * s) + 1) := by
    exact_mod_cast hUT
  constructor <;> omega

lemma ruzsaRepresentativeSum_cast (q : ℕ) [NeZero q] (lam : ZMod q)
    (T : Multiset ℤ) :
    (ruzsaRepresentativeSum q lam T : ZMod q) = lam * (T.sum : ZMod q) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      rw [show ruzsaRepresentativeSum q lam (a ::ₘ T) =
        ruzsaRepresentative q lam a + ruzsaRepresentativeSum q lam T by
          simp [ruzsaRepresentativeSum]]
      rw [Nat.cast_add, ruzsaRepresentative_cast, ih, Multiset.sum_cons,
        Int.cast_add]
      ring

lemma ruzsaModelMap_sum (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
      (ruzsaRepresentativeSum q lam T : ZMod M) := by
  induction T using Multiset.induction_on with
  | empty => simp [ruzsaRepresentativeSum]
  | @cons a T ih =>
      simp only [ruzsaModelMap, ruzsaRepresentativeSum, Multiset.map_cons,
        Multiset.sum_cons, Nat.cast_add, ih]

lemma ruzsaBlockWidth_lt {q s : ℕ} (_hs : 0 < s) (hq : 2 * s < q) :
    s * (q / (2 * s) + 1) < q := by
  have hdiv := Nat.mul_div_le q (2 * s)
  have hhalf : 2 * (s * (q / (2 * s))) ≤ q := by
    simpa only [mul_assoc] using hdiv
  nlinarith

lemma ruzsaRepresentativeSum_sub_cast (q : ℕ) [NeZero q]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q) =
      lam * ((T.sum - U.sum : ℤ) : ZMod q) := by
  rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    ruzsaRepresentativeSum_cast, ruzsaRepresentativeSum_cast, Int.cast_sub]
  ring

lemma ruzsaModelMap_sum_eq_iff_dvd (q M : ℕ) [NeZero q] [NeZero M]
    (lam : ZMod q) (T U : Multiset ℤ) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔
      (M : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) := by
  rw [ruzsaModelMap_sum, ruzsaModelMap_sum]
  constructor
  · intro h
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp
    rw [Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h, sub_self]
  · intro h
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h
    simpa only [Int.cast_sub, Int.cast_natCast, sub_eq_zero] using hz

lemma zmod_val_eq_natAbs_of_nonneg {q : ℕ} [NeZero q]
    {y : ℤ} {z : ZMod q} (hy : 0 ≤ y) (hyq : y.natAbs < q)
    (hcast : (y : ZMod q) = z) : z.val = y.natAbs := by
  have hycoe : (y.natAbs : ℤ) = y := Int.natAbs_of_nonneg hy
  have hcastNat : (y.natAbs : ZMod q) = z := by
    rw [← hcast]
    simpa using congrArg (fun t : ℤ => (t : ZMod q)) hycoe
  rw [← hcastNat, ZMod.val_natCast_of_lt hyq]

lemma int_natAbs_lt_of_neg_lt_and_lt {y : ℤ} {B : ℕ}
    (hlo : -(B : ℤ) < y) (hhi : y < B) : y.natAbs < B := by
  by_cases hy : 0 ≤ y
  · have hcast : (y.natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hy]
      exact hhi
    exact_mod_cast hcast
  · have hyneg : 0 ≤ -y := by omega
    have hcast : ((-y).natAbs : ℤ) < B := by
      rw [Int.natAbs_of_nonneg hyneg]
      omega
    rw [Int.natAbs_neg] at hcast
    exact_mod_cast hcast

lemma ruzsaModelMap_multiset_sum_eq_iff
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val))
    {T U : Multiset ℤ}
    (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
    (hTcard : T.card = s) (hUcard : U.card = s) :
    (T.map (ruzsaModelMap q M lam)).sum =
        (U.map (ruzsaModelMap q M lam)).sum ↔ T.sum = U.sum := by
  have hTsum : T.sum ∈ s • A := by
    simpa only [hTcard] using multiset_sum_mem_nsmul A hTA
  have hUsum : U.sum ∈ s • A := by
    simpa only [hUcard] using multiset_sum_mem_nsmul A hUA
  have hTUmem : T.sum - U.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨T.sum, hTsum, U.sum, hUsum, rfl⟩
  have hUTmem : U.sum - T.sum ∈ s • A - s • A :=
    Finset.mem_sub.mpr ⟨U.sum, hUsum, T.sum, hTsum, rfl⟩
  have hshort := ruzsaRepresentativeSum_sub_abs_lt lam hTcard hUcard hs
    (fun x hx => hmono x (hTA x hx)) (fun x hx => hmono x (hUA x hx))
  have hwidth := ruzsaBlockWidth_lt hs hq
  have hsmall :
      (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs < q := by
    have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
      exact_mod_cast hwidth
    apply int_natAbs_lt_of_neg_lt_and_lt
    · exact (by omega : -(q : ℤ) <
        -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hshort.2
    · exact hshort.1.trans hwidthZ
  constructor
  · intro hmap
    by_contra hsum
    have hx : T.sum - U.sum ≠ 0 := sub_ne_zero.mpr hsum
    by_cases hy : 0 ≤ (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U
    · have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam T U).mp hmap
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam T : ℤ) -
          ruzsaRepresentativeSum q lam U : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((T.sum - U.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam T : ℤ) -
            ruzsaRepresentativeSum q lam U : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hy hsmall
        exact ruzsaRepresentativeSum_sub_cast q lam T U
      exact hgood (T.sum - U.sum) hTUmem hx (by rwa [hval])
    · have hswapNonneg : 0 ≤ (ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T := by omega
      have hswapShort := ruzsaRepresentativeSum_sub_abs_lt lam hUcard hTcard hs
        (fun x hx => hmono x (hUA x hx)) (fun x hx => hmono x (hTA x hx))
      have hswapSmall :
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs < q := by
        have hwidthZ : ((s * (q / (2 * s) + 1) : ℕ) : ℤ) < q := by
          exact_mod_cast hwidth
        apply int_natAbs_lt_of_neg_lt_and_lt
        · exact (by omega : -(q : ℤ) <
            -((s * (q / (2 * s) + 1) : ℕ) : ℤ)).trans hswapShort.2
        · exact hswapShort.1.trans hwidthZ
      have hdiv : (M : ℤ) ∣
          ((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T) :=
        (ruzsaModelMap_sum_eq_iff_dvd q M lam U T).mp hmap.symm
      have hdivNat : M ∣ (((ruzsaRepresentativeSum q lam U : ℤ) -
          ruzsaRepresentativeSum q lam T : ℤ)).natAbs :=
        Int.natCast_dvd.mp hdiv
      have hval : (lam * ((U.sum - T.sum : ℤ) : ZMod q)).val =
          (((ruzsaRepresentativeSum q lam U : ℤ) -
            ruzsaRepresentativeSum q lam T : ℤ)).natAbs := by
        apply zmod_val_eq_natAbs_of_nonneg hswapNonneg hswapSmall
        exact ruzsaRepresentativeSum_sub_cast q lam U T
      have hx' : U.sum - T.sum ≠ 0 := sub_ne_zero.mpr (Ne.symm hsum)
      exact hgood (U.sum - T.sum) hUTmem hx' (by rwa [hval])
  · intro hsum
    have hcast : ((((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U : ℤ) : ZMod q)) = 0 := by
      rw [ruzsaRepresentativeSum_sub_cast, hsum, sub_self, Int.cast_zero, mul_zero]
    have hdiv : (q : ℤ) ∣ ((ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U) :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcast
    have hzero : (ruzsaRepresentativeSum q lam T : ℤ) -
        ruzsaRepresentativeSum q lam U = 0 := by
      apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
      simpa only [Int.natAbs_natCast] using hsmall
    have hrepeq : ruzsaRepresentativeSum q lam T =
        ruzsaRepresentativeSum q lam U := by omega
    rw [ruzsaModelMap_sum, ruzsaModelMap_sum, hrepeq]

theorem isAddFreimanIso_ruzsaModelMap
    {A : Finset ℤ} {s M q c : ℕ} [NeZero q] [NeZero M]
    (lam : ZMod q) (hs : 0 < s) (hq : 2 * s < q)
    (hmono : ∀ a ∈ A, ruzsaColor q s lam a = c)
    (hgood : ∀ x ∈ s • A - s • A, x ≠ 0 →
      ¬ (M ∣ (lam * (x : ZMod q)).val)) :
    IsAddFreimanIso s (A : Set ℤ)
      (A.image (ruzsaModelMap q M lam) : Set (ZMod M))
      (ruzsaModelMap q M lam) := by
  let f := ruzsaModelMap q M lam
  have hrel {T U : Multiset ℤ}
      (hTA : ∀ x ∈ T, x ∈ A) (hUA : ∀ x ∈ U, x ∈ A)
      (hTcard : T.card = s) (hUcard : U.card = s) :
      (T.map f).sum = (U.map f).sum ↔ T.sum = U.sum :=
    ruzsaModelMap_multiset_sum_eq_iff lam hs hq hmono hgood
      hTA hUA hTcard hUcard
  have hinj : Set.InjOn f (A : Set ℤ) := by
    intro a ha b hb hab
    have hrepl := hrel
      (T := Multiset.replicate s a) (U := Multiset.replicate s b)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
      (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using hb)
      (by simp) (by simp)
    have hsum := hrepl.mp (by simp [f, hab])
    simp only [Multiset.sum_replicate, nsmul_eq_mul] at hsum
    have hsZ : (0 : ℤ) < s := by exact_mod_cast hs
    nlinarith
  refine ⟨⟨?_, hinj, ?_⟩, ?_⟩
  · intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩)
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_image] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    exact ⟨a, Finset.mem_coe.mpr ha, rfl⟩
  · intro T U hTA hUA hTcard hUcard
    apply hrel
    · intro x hx
      exact Finset.mem_coe.mp (hTA hx)
    · intro x hx
      exact Finset.mem_coe.mp (hUA hx)
    · exact hTcard
    · exact hUcard

lemma exists_nonempty_large_color_fiber_mul {A : Finset ℤ} {k : ℕ}
    (hA : A.Nonempty) (hk : 0 < k) (f : ℤ → ℕ)
    (hf : ∀ a ∈ A, f a < k) :
    ∃ c < k, let B := A.filter fun a => f a = c
      B.Nonempty ∧ A.card ≤ k * B.card := by
  classical
  let n := (A.card - 1) / k
  have hApos : 0 < A.card := Finset.card_pos.mpr hA
  have hkn : k * n < A.card := by
    have hle : k * n ≤ A.card - 1 := by
      simpa only [n] using Nat.mul_div_le (A.card - 1) k
    omega
  obtain ⟨c, hc, hcard⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := A) (t := Finset.range k) (f := f)
      (fun a ha => Finset.mem_range.mpr (hf a ha)) (by simpa using hkn)
  refine ⟨c, Finset.mem_range.mp hc, ?_⟩
  dsimp
  have hceil : A.card - 1 < k * (n + 1) := by
    simpa only [n] using Nat.lt_mul_div_succ (A.card - 1) hk
  have hmul : k * (n + 1) ≤
      k * (A.filter fun a => f a = c).card := by
    exact Nat.mul_le_mul_left k (by omega)
  constructor
  · exact Finset.card_pos.mp ((Nat.zero_le n).trans_lt hcard)
  · have hpred : A.card - 1 + 1 = A.card :=
      Nat.sub_one_add_one hApos.ne'
    have hlt : A.card - 1 <
        k * (A.filter fun a => f a = c).card := hceil.trans_le hmul
    omega

theorem exists_large_cyclic_freiman_model (A : Finset ℤ) (s : ℕ)
    (hA : A.Nonempty) (hs : 0 < s) :
    let D := s • A - s • A
    ∃ (A' : Finset ℤ) (B : Finset (ZMod (2 * D.card)))
      (f : ℤ → ZMod (2 * D.card)),
      A'.Nonempty ∧ A' ⊆ A ∧ A.card ≤ (2 * s) * A'.card ∧
        B = A'.image f ∧ IsAddFreimanIso s (A' : Set ℤ) (B : Set _) f := by
  classical
  let D := s • A - s • A
  have hD : D.Nonempty := by
    obtain ⟨a, ha⟩ := hA
    have hsum : (Multiset.replicate s a).sum ∈ s • A := by
      simpa using multiset_sum_mem_nsmul A (T := Multiset.replicate s a)
        (by intro x hx; simpa [Multiset.eq_of_mem_replicate hx] using ha)
    exact ⟨0, Finset.mem_sub.mpr ⟨_, hsum, _, hsum, sub_self _⟩⟩
  have hDcard : 0 < D.card := Finset.card_pos.mpr hD
  let R := D.sup Int.natAbs
  let K := max (max (4 * D.card) (2 * s)) R + 1
  obtain ⟨q, hKq, hqPrime⟩ := Nat.exists_infinite_primes K
  have h4q : 4 * D.card < q := by
    dsimp [K] at hKq
    omega
  have h2sq : 2 * s < q := by
    dsimp [K] at hKq
    omega
  have hRq : R < q := by
    dsimp [K] at hKq
    omega
  let : Fact q.Prime := ⟨hqPrime⟩
  let : NeZero q := ⟨hqPrime.ne_zero⟩
  obtain ⟨lam, hlam, hgood⟩ := exists_good_multiplier
    (D := D) (N := D.card) (q := q) hDcard le_rfl
    (fun x hx => (Finset.le_sup hx).trans_lt hRq) h4q
  obtain ⟨c, hc, hfiber⟩ :=
    exists_nonempty_large_color_fiber_mul hA (by omega)
      (ruzsaColor q s lam) (fun a _ha => ruzsaColor_lt lam hs h2sq a)
  let A' := A.filter fun a => ruzsaColor q s lam a = c
  have hA'ne : A'.Nonempty := hfiber.1
  have hA'card : A.card ≤ (2 * s) * A'.card := hfiber.2
  have hA'sub : A' ⊆ A := by
    intro a ha
    exact (Finset.mem_filter.mp ha).1
  have hmono : ∀ a ∈ A', ruzsaColor q s lam a = c := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hsumSub : s • A' ⊆ s • A := by
    exact nsmul_le_nsmul_right hA'sub s
  have hdiffSub : s • A' - s • A' ⊆ D := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_sub.mp hx
    exact Finset.mem_sub.mpr ⟨u, hsumSub hu, v, hsumSub hv, rfl⟩
  have hgood' : ∀ x ∈ s • A' - s • A', x ≠ 0 →
      ¬ (2 * D.card ∣ (lam * (x : ZMod q)).val) := by
    intro x hx hx0
    exact hgood x (hdiffSub hx) hx0
  have hM : 0 < 2 * D.card := by omega
  let : NeZero (2 * D.card) := ⟨hM.ne'⟩
  let f : ℤ → ZMod (2 * D.card) := ruzsaModelMap q (2 * D.card) lam
  let B := A'.image f
  refine ⟨A', B, f, hA'ne, hA'sub, hA'card, rfl, ?_⟩
  exact isAddFreimanIso_ruzsaModelMap lam hs h2sq hmono hgood'

end Erdos3.FreimanModel

end

section

open scoped BigOperators Pointwise

namespace Erdos3.FreimanModel

noncomputable section

structure FourfoldPresentation (β : Type*) where
  pos₁ : β
  pos₂ : β
  neg₁ : β
  neg₂ : β

namespace FourfoldPresentation

variable {β : Type*} [AddCommGroup β]

def eval (p : FourfoldPresentation β) : β :=
  p.pos₁ + p.pos₂ - p.neg₁ - p.neg₂

def Mem (B : Finset β) (p : FourfoldPresentation β) : Prop :=
  p.pos₁ ∈ B ∧ p.pos₂ ∈ B ∧ p.neg₁ ∈ B ∧ p.neg₂ ∈ B

end FourfoldPresentation

variable {α β : Type*} [AddCommGroup α] [AddCommGroup β]
  [DecidableEq β]

lemma mem_two_nsmul_sub_two_nsmul_iff
    {B : Finset β} {x : β} :
    x ∈ 2 • B - 2 • B ↔
      ∃ p : FourfoldPresentation β,
        p.Mem B ∧ p.eval = x := by
  constructor
  · intro hx
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_sub.mp hx
    rw [show 2 • B = B + B by simp [two_nsmul]] at hu hv
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.mem_add.mp hu
    obtain ⟨c, hc, d, hd, hcd⟩ := Finset.mem_add.mp hv
    refine ⟨⟨a, b, c, d⟩, ⟨ha, hb, hc, hd⟩, ?_⟩
    dsimp only [FourfoldPresentation.eval]
    rw [← huv, ← hab, ← hcd]
    abel
  · rintro ⟨p, hp, rfl⟩
    apply Finset.mem_sub.mpr
    refine ⟨p.pos₁ + p.pos₂, ?_, p.neg₁ + p.neg₂, ?_, ?_⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.pos₁, hp.1, p.pos₂, hp.2.1, rfl⟩
    · rw [show 2 • B = B + B by simp [two_nsmul]]
      exact Finset.mem_add.mpr ⟨p.neg₁, hp.2.2.1, p.neg₂, hp.2.2.2, rfl⟩
    · dsimp only [FourfoldPresentation.eval]
      abel

noncomputable def defaultFourfoldPresentation (B : Finset β)
    (hB : B.Nonempty) : FourfoldPresentation β :=
  let b := Classical.choose hB
  ⟨b, b, b, b⟩

noncomputable def selectedFourfoldPresentation (B : Finset β)
    (hB : B.Nonempty) (x : β) : FourfoldPresentation β := by
  classical
  exact if hx : ∃ p : FourfoldPresentation β, p.Mem B ∧ p.eval = x then
      Classical.choose hx
    else defaultFourfoldPresentation B hB

lemma selectedFourfoldPresentation_spec (B : Finset β)
    (hB : B.Nonempty) {x : β} (hx : x ∈ 2 • B - 2 • B) :
    (selectedFourfoldPresentation B hB x).Mem B ∧
      (selectedFourfoldPresentation B hB x).eval = x := by
  have hex := mem_two_nsmul_sub_two_nsmul_iff.mp hx
  simp only [selectedFourfoldPresentation, dif_pos hex]
  exact Classical.choose_spec hex

def fourfoldMapValue (g : β → α) (p : FourfoldPresentation β) : α :=
  g p.pos₁ + g p.pos₂ - g p.neg₁ - g p.neg₂

lemma fourfold_sub_eq_iff_cross_add {G : Type*} [AddCommGroup G]
    (a b c d e f g h : G) :
    a + b - c - d = e + f - g - h ↔
      a + b + g + h = e + f + c + d := by
  constructor
  · intro heq
    calc
      a + b + g + h = (a + b - c - d) + (c + d + g + h) := by abel
      _ = (e + f - g - h) + (c + d + g + h) := by rw [heq]
      _ = e + f + c + d := by abel
  · intro heq
    calc
      a + b - c - d =
          (a + b + g + h) - (c + d + g + h) := by abel
      _ = (e + f + c + d) - (c + d + g + h) := by rw [heq]
      _ = e + f - g - h := by abel

lemma add_fourfold_sub_eq_iff_cross_add {G : Type*} [AddCommGroup G]
    (a₁ a₂ c₁ c₂ b₁ b₂ d₁ d₂
      e₁ e₂ g₁ g₂ f₁ f₂ h₁ h₂ : G) :
    (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
        (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) ↔
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
        e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by
  constructor
  · intro heq
    calc
      a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂ =
          ((a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = ((e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂)) +
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂ := by abel
  · intro heq
    calc
      (a₁ + a₂ - c₁ - c₂) + (b₁ + b₂ - d₁ - d₂) =
          (a₁ + a₂ + b₁ + b₂ + g₁ + g₂ + h₁ + h₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by abel
      _ = (e₁ + e₂ + f₁ + f₂ + c₁ + c₂ + d₁ + d₂) -
            (c₁ + c₂ + d₁ + d₂ + g₁ + g₂ + h₁ + h₂) := by rw [heq]
      _ = (e₁ + e₂ - g₁ - g₂) + (f₁ + f₂ - h₁ - h₂) := by abel

omit [DecidableEq β] in
lemma fourfoldMapValue_eq_iff_eval_eq
    {A : Set α} {B : Finset β} {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {p r : FourfoldPresentation β} (hp : p.Mem B) (hr : r.Mem B) :
    fourfoldMapValue g p = fourfoldMapValue g r ↔ p.eval = r.eval := by
  let s : Multiset β :=
    p.pos₁ ::ₘ p.pos₂ ::ₘ r.neg₁ ::ₘ r.neg₂ ::ₘ 0
  let t : Multiset β :=
    r.pos₁ ::ₘ r.pos₂ ::ₘ p.neg₁ ::ₘ p.neg₂ ::ₘ 0
  have hsB : ∀ ⦃x⦄, x ∈ s → x ∈ (B : Set β) := by
    intro x hx
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hp.1, hp.2.1, hr.2.2.1, hr.2.2.2]
  have htB : ∀ ⦃x⦄, x ∈ t → x ∈ (B : Set β) := by
    intro x hx
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl
    exacts [hr.1, hr.2.1, hp.2.2.1, hp.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = p.pos₁ + p.pos₂ + r.neg₁ + r.neg₂ := by
    simp [s]
    abel
  have ht : t.sum = r.pos₁ + r.pos₂ + p.neg₁ + p.neg₂ := by
    simp [t]
    abel
  have hgs : (s.map g).sum =
      g p.pos₁ + g p.pos₂ + g r.neg₁ + g r.neg₂ := by
    simp [s]
    abel
  have hgt : (t.map g).sum =
      g r.pos₁ + g r.pos₂ + g p.neg₁ + g p.neg₂ := by
    simp [t]
    abel
  rw [hs, ht, hgs, hgt] at hrel
  exact (fourfold_sub_eq_iff_cross_add
    (g p.pos₁) (g p.pos₂) (g p.neg₁) (g p.neg₂)
    (g r.pos₁) (g r.pos₂) (g r.neg₁) (g r.neg₂)).trans
      (hrel.trans (fourfold_sub_eq_iff_cross_add
        p.pos₁ p.pos₂ p.neg₁ p.neg₂ r.pos₁ r.pos₂ r.neg₁ r.neg₂).symm)

noncomputable def freimanFourfoldLift (B : Finset β) (hB : B.Nonempty)
    (g : β → α) (x : β) : α :=
  fourfoldMapValue g (selectedFourfoldPresentation B hB x)

lemma freimanFourfoldLift_eq_of_presentation
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g)
    {x : β} (hx : x ∈ 2 • B - 2 • B)
    {p : FourfoldPresentation β} (hp : p.Mem B) (hpx : p.eval = x) :
    freimanFourfoldLift B hB g x = fourfoldMapValue g p := by
  have hs := selectedFourfoldPresentation_spec B hB hx
  apply (fourfoldMapValue_eq_iff_eval_eq hg hs.1 hp).mpr
  exact hs.2.trans hpx.symm

lemma freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul [DecidableEq α]
    {A : Finset α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : Set.MapsTo g (B : Set β) (A : Set α))
    {x : β} (hx : x ∈ 2 • B - 2 • B) :
    freimanFourfoldLift B hB g x ∈ 2 • A - 2 • A := by
  let p := selectedFourfoldPresentation B hB x
  have hp := selectedFourfoldPresentation_spec B hB hx
  rw [mem_two_nsmul_sub_two_nsmul_iff]
  refine ⟨⟨g p.pos₁, g p.pos₂, g p.neg₁, g p.neg₂⟩, ?_, rfl⟩
  exact ⟨hg hp.1.1, hg hp.1.2.1, hg hp.1.2.2.1, hg hp.1.2.2.2⟩

theorem freimanFourfoldLift_injOn
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 4 (B : Set β) A g) :
    Set.InjOn (freimanFourfoldLift B hB g) (2 • B - 2 • B : Finset β) := by
  intro x hx y hy hxy
  have hsx := selectedFourfoldPresentation_spec B hB hx
  have hsy := selectedFourfoldPresentation_spec B hB hy
  have heval := (fourfoldMapValue_eq_iff_eval_eq hg hsx.1 hsy.1).mp hxy
  rw [hsx.2, hsy.2] at heval
  exact heval

lemma freimanFourfoldLift_add_eq_add
    {A : Set α} {B : Finset β} (hB : B.Nonempty) {g : β → α}
    (hg : IsAddFreimanIso 8 (B : Set β) A g)
    {x y z w : β}
    (hx : x ∈ 2 • B - 2 • B) (hy : y ∈ 2 • B - 2 • B)
    (hz : z ∈ 2 • B - 2 • B) (hw : w ∈ 2 • B - 2 • B) :
    freimanFourfoldLift B hB g x + freimanFourfoldLift B hB g y =
        freimanFourfoldLift B hB g z + freimanFourfoldLift B hB g w ↔
      x + y = z + w := by
  let px := selectedFourfoldPresentation B hB x
  let py := selectedFourfoldPresentation B hB y
  let pz := selectedFourfoldPresentation B hB z
  let pw := selectedFourfoldPresentation B hB w
  have hpx := selectedFourfoldPresentation_spec B hB hx
  have hpy := selectedFourfoldPresentation_spec B hB hy
  have hpz := selectedFourfoldPresentation_spec B hB hz
  have hpw := selectedFourfoldPresentation_spec B hB hw
  let s : Multiset β := px.pos₁ ::ₘ px.pos₂ ::ₘ py.pos₁ ::ₘ py.pos₂ ::ₘ
    pz.neg₁ ::ₘ pz.neg₂ ::ₘ pw.neg₁ ::ₘ pw.neg₂ ::ₘ 0
  let t : Multiset β := pz.pos₁ ::ₘ pz.pos₂ ::ₘ pw.pos₁ ::ₘ pw.pos₂ ::ₘ
    px.neg₁ ::ₘ px.neg₂ ::ₘ py.neg₁ ::ₘ py.neg₂ ::ₘ 0
  have hsB : ∀ ⦃a⦄, a ∈ s → a ∈ (B : Set β) := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpx.1.1, hpx.1.2.1, hpy.1.1, hpy.1.2.1,
      hpz.1.2.2.1, hpz.1.2.2.2, hpw.1.2.2.1, hpw.1.2.2.2]
  have htB : ∀ ⦃a⦄, a ∈ t → a ∈ (B : Set β) := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [hpz.1.1, hpz.1.2.1, hpw.1.1, hpw.1.2.1,
      hpx.1.2.2.1, hpx.1.2.2.2, hpy.1.2.2.1, hpy.1.2.2.2]
  have hrel := hg.map_sum_eq_map_sum hsB htB (by simp [s]) (by simp [t])
  have hs : s.sum = px.pos₁ + px.pos₂ + py.pos₁ + py.pos₂ +
      pz.neg₁ + pz.neg₂ + pw.neg₁ + pw.neg₂ := by
    simp [s]
    abel
  have ht : t.sum = pz.pos₁ + pz.pos₂ + pw.pos₁ + pw.pos₂ +
      px.neg₁ + px.neg₂ + py.neg₁ + py.neg₂ := by
    simp [t]
    abel
  have hgs : (s.map g).sum =
      g px.pos₁ + g px.pos₂ + g py.pos₁ + g py.pos₂ +
        g pz.neg₁ + g pz.neg₂ + g pw.neg₁ + g pw.neg₂ := by
    simp [s]
    abel
  have hgt : (t.map g).sum =
      g pz.pos₁ + g pz.pos₂ + g pw.pos₁ + g pw.pos₂ +
        g px.neg₁ + g px.neg₂ + g py.neg₁ + g py.neg₂ := by
    simp [t]
    abel
  rw [hs, ht, hgs, hgt] at hrel
  have hmapCross := add_fourfold_sub_eq_iff_cross_add
    (g px.pos₁) (g px.pos₂) (g px.neg₁) (g px.neg₂)
    (g py.pos₁) (g py.pos₂) (g py.neg₁) (g py.neg₂)
    (g pz.pos₁) (g pz.pos₂) (g pz.neg₁) (g pz.neg₂)
    (g pw.pos₁) (g pw.pos₂) (g pw.neg₁) (g pw.neg₂)
  have horiginalCross := add_fourfold_sub_eq_iff_cross_add
    px.pos₁ px.pos₂ px.neg₁ px.neg₂ py.pos₁ py.pos₂ py.neg₁ py.neg₂
    pz.pos₁ pz.pos₂ pz.neg₁ pz.neg₂ pw.pos₁ pw.pos₂ pw.neg₁ pw.neg₂
  have hvalues :
      px.eval + py.eval = pz.eval + pw.eval ↔ x + y = z + w := by
    rw [hpx.2, hpy.2, hpz.2, hpw.2]
  exact hmapCross.trans (hrel.trans (horiginalCross.symm.trans hvalues))

end

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

theorem exists_fourfold_lift_of_eight_iso {G H : Type*}
    [AddCommGroup G] [AddCommGroup H] [DecidableEq G] [DecidableEq H]
    (A : Finset G) (B : Finset H) (hB : B.Nonempty) (f : G → H)
    (hf : IsAddFreimanIso 8 (A : Set G) (B : Set H) f) :
    ∃ L : H → G,
      Set.MapsTo L (2 • B - 2 • B : Finset H) (2 • A - 2 • A : Finset G) ∧
      Set.InjOn L (2 • B - 2 • B : Finset H) ∧ L 0 = 0 ∧
      ∀ x ∈ 2 • B - 2 • B, ∀ y ∈ 2 • B - 2 • B,
        ∀ z ∈ 2 • B - 2 • B, ∀ w ∈ 2 • B - 2 • B,
          L x + L y = L z + L w ↔ x + y = z + w := by
  classical
  let g := Function.invFunOn f (A : Set G)
  have hg : IsAddFreimanIso 8 (B : Set H) (A : Set G) g := hf.invFunOn
  have hg4 : IsAddFreimanIso 4 (B : Set H) (A : Set G) g := hg.mono (hmn := by decide)
  let L := freimanFourfoldLift B hB g
  refine ⟨L, ?_, freimanFourfoldLift_injOn hB hg4, ?_, ?_⟩
  · intro x hx
    exact freimanFourfoldLift_mem_two_nsmul_sub_two_nsmul hB hg.bijOn.mapsTo hx
  · obtain ⟨b, hb⟩ := hB.exists_mem
    let p : FourfoldPresentation H := ⟨b, b, b, b⟩
    have hp : p.Mem B := ⟨hb, hb, hb, hb⟩
    have hpx : p.eval = 0 := by simp [p, FourfoldPresentation.eval]
    have hz : (0 : H) ∈ 2 • B - 2 • B :=
      mem_two_nsmul_sub_two_nsmul_iff.mpr ⟨p, hp, hpx⟩
    change freimanFourfoldLift B hB g 0 = 0
    rw [freimanFourfoldLift_eq_of_presentation hB hg4 hz hp hpx]
    simp [fourfoldMapValue, p]
  · intro x hx y hy z hz w hw
    exact freimanFourfoldLift_add_eq_add hB hg hx hy hz hw

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreimanFivefoldCardinality
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

def fiveTermValue (x : Fin 5 → G) : G := x 0 + x 1 + x 2 - x 3 - x 4

theorem fiveTermValue_eq_iff {A : Set G} {B : Set H} {f : G → H}
    (hf : IsAddFreimanIso 5 A B f) {x y : Fin 5 → G}
    (hx : ∀ i, x i ∈ A) (hy : ∀ i, y i ∈ A) :
    fiveTermValue (f ∘ x) = fiveTermValue (f ∘ y) ↔ fiveTermValue x = fiveTermValue y := by
  let s : Multiset G := x 0 ::ₘ x 1 ::ₘ x 2 ::ₘ y 3 ::ₘ y 4 ::ₘ 0
  let t : Multiset G := y 0 ::ₘ y 1 ::ₘ y 2 ::ₘ x 3 ::ₘ x 4 ::ₘ 0
  have hsA : ∀ ⦃a⦄, a ∈ s → a ∈ A := by
    intro a ha
    simp only [s, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    exacts [hx 0, hx 1, hx 2, hy 3, hy 4]
  have htA : ∀ ⦃a⦄, a ∈ t → a ∈ A := by
    intro a ha
    simp only [t, Multiset.mem_cons, Multiset.notMem_zero, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl
    exacts [hy 0, hy 1, hy 2, hx 3, hx 4]
  have hrel := hf.map_sum_eq_map_sum hsA htA (by simp [s]) (by simp [t])
  simp only [fiveTermValue, Function.comp_apply, sub_sub, sub_eq_sub_iff_add_eq_add, add_assoc]
  simpa [s, t, add_assoc] using hrel

theorem card_fiveTermValues_le [DecidableEq G] [DecidableEq H] [Fintype H]
    (A : Finset G) {B : Set H} (f : G → H)
    (hf : IsAddFreimanIso 5 (A : Set G) B f) :
    ((Fintype.piFinset fun _ : Fin 5 => A).image fiveTermValue).card ≤ Fintype.card H := by
  classical
  let U := Fintype.piFinset fun _ : Fin 5 => A
  have hrel : ∀ x ∈ U, ∀ y ∈ U,
      fiveTermValue x = fiveTermValue y ↔
        fiveTermValue (f ∘ x) = fiveTermValue (f ∘ y) := by
    intro x hx y hy
    exact (fiveTermValue_eq_iff hf (Fintype.mem_piFinset.mp hx)
      (Fintype.mem_piFinset.mp hy)).symm
  have hcard := card_image_eq_of_same_fibers U fiveTermValue (fun x => fiveTermValue (f ∘ x)) hrel
  change (U.image fiveTermValue).card ≤ _
  rw [hcard]
  exact Finset.card_le_univ _

theorem sub_subset_fiveTermValues [DecidableEq G] (A P : Finset G)
    (hP : P ⊆ 2 • A - 2 • A) :
    A - P ⊆ (Fintype.piFinset fun _ : Fin 5 => A).image fiveTermValue := by
  classical
  intro z hz
  obtain ⟨a, ha, p, hp, rfl⟩ := Finset.mem_sub.mp hz
  obtain ⟨q, hq, hval⟩ := mem_two_nsmul_sub_two_nsmul_iff.mp (hP hp)
  let x : Fin 5 → G := ![a, q.neg₁, q.neg₂, q.pos₁, q.pos₂]
  have hx : x ∈ Fintype.piFinset (fun _ : Fin 5 => A) := by
    apply Fintype.mem_piFinset.mpr
    intro i
    fin_cases i
    · exact ha
    · exact hq.2.2.1
    · exact hq.2.2.2
    · exact hq.1
    · exact hq.2.1
  refine Finset.mem_image.mpr ⟨x, hx, ?_⟩
  rw [← hval]
  change a + q.neg₁ + q.neg₂ - q.pos₁ - q.pos₂ = a - (q.pos₁ + q.pos₂ - q.neg₁ - q.neg₂)
  abel

theorem card_sub_le_of_fourfold_subset [DecidableEq G] [DecidableEq H] [Fintype H]
    (A P : Finset G) {B : Set H} (f : G → H)
    (hf : IsAddFreimanIso 5 (A : Set G) B f) (hP : P ⊆ 2 • A - 2 • A) :
    (A - P).card ≤ Fintype.card H :=
  (Finset.card_le_card (sub_subset_fiveTermValues A P hP)).trans (card_fiveTermValues_le A f hf)

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmallDifferenceGrowth
namespace OAI

section

namespace Erdos3

open scoped Pointwise

theorem higher_difference_card_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A : Finset G) (hA : A.Nonempty) {K : ℝ}
    (hsmall : ((A - A).card : ℝ) ≤ K * A.card) (m n : ℕ) :
    ((m • A - n • A).card : ℝ) ≤ K ^ (m + n) * A.card := by
  have h := Finset.pluennecke_ruzsa_inequality_nsmul_sub_nsmul_sub hA A m n
  have hreal : ((m • A - n • A).card : ℝ) ≤
      (((A - A).card : ℝ) / A.card) ^ (m + n) * A.card := by
    have hc := (NNRat.cast_le (K := ℝ)).mpr h
    simpa only [NNRat.cast_natCast, NNRat.cast_mul, NNRat.cast_pow,
      NNRat.cast_div] using hc
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hratio : ((A - A).card : ℝ) / A.card ≤ K :=
    (div_le_iff₀ hcard).mpr hsmall
  exact hreal.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) hratio _) hcard.le)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerVectorFreimanEmbedding
namespace OAI

section

namespace Erdos3.FreimanModel

open scoped BigOperators Pointwise

noncomputable def coordinatePolynomial (n : ℕ) : (Fin n → ℤ) →+ Polynomial ℤ where
  toFun x := ∑ i : Fin n, Polynomial.monomial (i : ℕ) (x i)
  map_zero' := by simp
  map_add' x y := by simp [Finset.sum_add_distrib]

theorem coordinatePolynomial_coeff {n : ℕ} (x : Fin n → ℤ) (i : Fin n) :
    (coordinatePolynomial n x).coeff (i : ℕ) = x i := by
  change (∑ j : Fin n, Polynomial.monomial (j : ℕ) (x j)).coeff (i : ℕ) = x i
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [Polynomial.coeff_monomial, Fin.val_inj.ne.mpr hji]
  · simp

theorem coordinatePolynomial_injective (n : ℕ) :
    Function.Injective (coordinatePolynomial n) := by
  intro x y h
  funext i
  simpa only [coordinatePolynomial_coeff] using
    congrArg (fun p : Polynomial ℤ => p.coeff (i : ℕ)) h

theorem exists_fin_integer_embedding {n : ℕ} (A : Finset (Fin n → ℤ)) :
    ∃ f : (Fin n → ℤ) →+ ℤ, Set.InjOn f (A : Set _) := by
  classical
  let P := coordinatePolynomial n
  let R := (A ×ˢ A).biUnion fun xy => (P xy.1 - P xy.2).roots.toFinset
  obtain ⟨t, ht⟩ := R.exists_notMem
  let f := (Polynomial.evalRingHom t).toAddMonoidHom.comp P
  refine ⟨f, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have hP : P x - P y ≠ 0 :=
    sub_ne_zero.mpr (fun h => hne (coordinatePolynomial_injective n h))
  apply ht
  apply Finset.mem_biUnion.mpr
  refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
  change (P x - P y).eval t = 0
  rw [Polynomial.eval_sub, sub_eq_zero]
  exact hxy

theorem multiset_sum_mem_iterated_sumset {G : Type*} [AddCommMonoid G] [DecidableEq G]
    (A : Finset G) {T : Multiset G} (hT : ∀ x ∈ T, x ∈ A) :
    T.sum ∈ T.card • A := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons a T ih =>
      rw [Multiset.card_cons, succ_nsmul, Finset.mem_add]
      refine ⟨T.sum, ih ?_, a, hT a (by simp), ?_⟩
      · intro x hx
        exact hT x (by simp [hx])
      · simp [add_comm]

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeProperAffineRecovery
namespace OAI

section

namespace Erdos3.FreimanModel

def residueBlock {q : ℕ} [NeZero q] (x : ZMod q) : Fin 16 := by
  refine ⟨x.val / (q / 16 + 1), ?_⟩
  apply (Nat.div_lt_iff_lt_mul (Nat.succ_pos _)).mpr
  exact x.val_lt.trans (Nat.lt_mul_div_succ q (by decide))

def residueLift {q : ℕ} (x : ZMod q) : ℤ := x.val

theorem residueBlock_bounds {q : ℕ} [NeZero q] {x : ZMod q} {c : Fin 16}
    (hc : residueBlock x = c) :
    c.val * (q / 16 + 1) ≤ x.val ∧
      x.val ≤ c.val * (q / 16 + 1) + q / 16 := by
  have hdiv : x.val / (q / 16 + 1) = c.val := congrArg Fin.val hc
  have hmod := Nat.mod_lt x.val (Nat.succ_pos (q / 16))
  have hrem : x.val % (q / 16 + 1) ≤ q / 16 := Nat.le_of_lt_succ hmod
  have hid := Nat.mod_add_div x.val (q / 16 + 1)
  rw [hdiv, Nat.mul_comm (q / 16 + 1)] at hid
  omega

theorem residueLift_sum_bounds {q : ℕ} [NeZero q] {c : Fin 16}
    (T : Multiset (ZMod q)) (hT : T.card = 8)
    (hc : ∀ x ∈ T, residueBlock x = c) :
    (8 : ℤ) * (c.val * (q / 16 + 1) : ℕ) ≤ (T.map residueLift).sum ∧
      (T.map residueLift).sum ≤
        (8 : ℤ) * ((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) := by
  have hlo := Multiset.card_nsmul_le_sum
    (s := T.map residueLift) (a := ((c.val * (q / 16 + 1) : ℕ) : ℤ)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      change ((c.val * (q / 16 + 1) : ℕ) : ℤ) ≤ (x.val : ℤ)
      exact_mod_cast (residueBlock_bounds (hc x hx)).1)
  have hhi := Multiset.sum_le_card_nsmul
    (s := T.map residueLift) (n := (((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) : ℤ)) (by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
      change (x.val : ℤ) ≤ (((c.val * (q / 16 + 1) : ℕ) + (q / 16 : ℕ)) : ℤ)
      exact_mod_cast (residueBlock_bounds (hc x hx)).2)
  simpa only [Multiset.card_map, hT, nsmul_eq_mul, Nat.cast_add, Nat.cast_ofNat]
    using And.intro hlo hhi

theorem residueLift_sum_sub_abs_lt {q : ℕ} [NeZero q] {c : Fin 16}
    (T U : Multiset (ZMod q)) (hT : T.card = 8) (hU : U.card = 8)
    (hcT : ∀ x ∈ T, residueBlock x = c) (hcU : ∀ x ∈ U, residueBlock x = c) :
    |(T.map residueLift).sum - (U.map residueLift).sum| < (q : ℤ) := by
  obtain ⟨hTlo, hThi⟩ := residueLift_sum_bounds T hT hcT
  obtain ⟨hUlo, hUhi⟩ := residueLift_sum_bounds U hU hcU
  have hdiv : (16 : ℤ) * (q / 16 : ℕ) ≤ q := by
    exact_mod_cast Nat.mul_div_le q 16
  have hq : (0 : ℤ) < q := by exact_mod_cast NeZero.pos q
  rw [abs_lt]
  constructor <;> omega

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

variable {I : Type*} (q : I → ℕ) [∀ i, NeZero (q i)]

def cyclicProductLift (x : ∀ i, ZMod (q i)) : I → ℤ := fun i => residueLift (x i)

def cyclicProductBlock (x : ∀ i, ZMod (q i)) : I → Fin 16 := fun i => residueBlock (x i)

theorem cyclicProductLift_injective : Function.Injective (cyclicProductLift q) := by
  intro x y h
  funext i
  have hi := congrArg (fun z : ℤ => (z : ZMod (q i))) (congrFun h i)
  simpa [cyclicProductLift, residueLift] using hi

omit [∀ i, NeZero (q i)] in
theorem cyclicProductLift_sum_apply (T : Multiset (∀ i, ZMod (q i))) (i : I) :
    ((T.map (cyclicProductLift q)).sum) i = (T.map fun x => residueLift (x i)).sum := by
  induction T using Multiset.induction_on with
  | empty => simp
  | @cons x T ih => simp [ih, cyclicProductLift]

end Erdos3.FreimanModel

end

section

namespace Erdos3.FreimanModel

open scoped Pointwise

variable {I : Type*}

def variableIntegerGraphReduction (N : ℕ) (M : I → ℕ) :
    (Option I → ℤ) →+ (ZMod N × (∀ i, ZMod (M i))) where
  toFun z := ((z none : ZMod N), fun i => (z (some i) : ZMod (M i)))
  map_zero' := by ext <;> simp
  map_add' x y := by ext <;> simp

end Erdos3.FreimanModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPrimitiveGowers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def HasCyclicMixedTargetCorrelation {J : Type*} {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (η : J → (Fin (d + 3) → ℤ) → ℂ) (q : ℝ) : Prop :=
  ∃ (j : J) (A : Fin (d + 3) → (Fin (d + 3) → ZMod N) → ℂ),
    (∀ i x, ‖A i x‖ ≤ 1) ∧
    (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
    Real.exp (-q) ≤ ‖𝔼 x : Fin (d + 3) → ZMod N,
      star (f (∑ k, x k)) * star (η j (fun k => ((x k).val : ℤ))) * ∏ i, A i x‖

theorem HasCyclicMixedTargetCorrelation.mono {J : Type*} {d N : ℕ} [NeZero N] {q q' : ℝ}
    {f : ZMod N → ℂ} {η : J → (Fin (d + 3) → ℤ) → ℂ}
    (H : HasCyclicMixedTargetCorrelation f η q) (hqq' : q ≤ q') :
    HasCyclicMixedTargetCorrelation f η q' := by
  obtain ⟨j, A, hA, hAi, hc⟩ := H
  exact ⟨j, A, hA, hAi, (Real.exp_le_exp.mpr (neg_le_neg hqq')).trans hc⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.Energy
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def cyclicAPTerm {k N : ℕ} (a d : ZMod N) (j : Fin k) : ZMod N :=
  a + (j : ZMod N) * d

def cyclicAPProduct (k N : ℕ) (f : ZMod N → ℝ)
    (a d : ZMod N) : ℝ :=
  ∏ j : Fin k, f (cyclicAPTerm a d j)

@[simp]
theorem cyclicAPProduct_const (k N : ℕ) (c : ℝ) (a d : ZMod N) :
    cyclicAPProduct k N (fun _ => c) a d = c ^ k := by
  simp [cyclicAPProduct]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.PolynomialApproximation
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped Pointwise

def IsUnitBounded {Ω : Type*} (g : Ω → ℝ) : Prop :=
  (∀ x, 0 ≤ g x) ∧ ∀ x, g x ≤ 1

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BooleanCutReduction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

def bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

def booleanValue {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.BundleCountingRecurrence
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure HypergraphBundle
    (J K : Type*) [DecidableEq J] [DecidableEq K]
    (H : Finset (Finset J)) where
  edges : Finset (Finset K)
  projection : K → J
  projection_injective_on_edge :
    ∀ g ∈ edges, Set.InjOn projection (g : Set K)
  projection_mem_base :
    ∀ g ∈ edges, g.image projection ∈ H

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def IsClosedUnderInclusion
    (B : HypergraphBundle J K H) : Prop :=
  ∀ ⦃g⦄, g ∈ B.edges →
    ∀ ⦃f⦄, f ⊆ g → f ∈ B.edges

def order (B : HypergraphBundle J K H) : ℕ :=
  B.edges.sup Finset.card

def eraseEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H where
  edges := B.edges.erase g₀
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg)
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem eraseEdge_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.eraseEdge g₀).edges = B.edges.erase g₀ :=
  rfl

def edgeTuple
    (g : Finset K) (x : K → G) :
    ({v : K // v ∈ g} → G) :=
  fun v => x v.1

noncomputable def projectionEquiv
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges) :
    {v : K // v ∈ g} ≃
      {j : J // j ∈ g.image B.projection} := by
  classical
  apply Equiv.ofBijective
    (fun v : {v : K // v ∈ g} =>
      (⟨B.projection v.1,
        Finset.mem_image.mpr ⟨v.1, v.2, rfl⟩⟩ :
        {j : J // j ∈ g.image B.projection}))
  constructor
  · intro v w hvw
    apply Subtype.ext
    apply B.projection_injective_on_edge g hg v.2 w.2
    exact congrArg Subtype.val hvw
  · intro j
    obtain ⟨v, hv, hvj⟩ :=
      Finset.mem_image.mp j.2
    refine ⟨⟨v, hv⟩, ?_⟩
    apply Subtype.ext
    exact hvj

noncomputable def projectedEdgeTuple
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    ({j : J // j ∈ g.image B.projection} → G) :=
  fun j => y ((B.projectionEquiv hg).symm j)

abbrev BaseEdgeWeight
    (J G : Type*) :=
  (e : Finset J) → ({j : J // j ∈ e} → G) → ℝ

def BaseWeightsInUnitInterval
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, 0 ≤ A e y ∧ A e y ≤ 1

noncomputable def pullbackBaseEdgeWeight
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G) :
    (g : Finset K) → ({v : K // v ∈ g} → G) → ℝ := by
  classical
  intro g y
  by_cases hg : g ∈ B.edges
  · exact A (g.image B.projection)
      (B.projectedEdgeTuple hg y)
  · exact 1

@[simp]
theorem pullbackBaseEdgeWeight_of_mem
    (B : HypergraphBundle J K H)
    (A : BaseEdgeWeight J G)
    {g : Finset K} (hg : g ∈ B.edges)
    (y : {v : K // v ∈ g} → G) :
    B.pullbackBaseEdgeWeight A g y =
      A (g.image B.projection)
        (B.projectedEdgeTuple hg y) := by
  classical
  simp [pullbackBaseEdgeWeight, hg]

def WeightsInUnitInterval
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y, 0 ≤ A g y ∧ A g y ≤ 1

noncomputable def bundleProduct
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  ∏ g ∈ B.edges, A g (edgeTuple g x)

theorem WeightsInUnitInterval.eraseEdge
    (B : HypergraphBundle J K H)
    {A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ}
    (hA : B.WeightsInUnitInterval A)
    (g₀ : Finset K) :
    (B.eraseEdge g₀).WeightsInUnitInterval A := by
  intro g hg y
  exact hA g (Finset.mem_of_mem_erase hg) y

noncomputable def edgeRemainder
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : K → G) : ℝ :=
  (B.eraseEdge g₀).bundleProduct A x

abbrev EdgeComplement (g : Finset K) :=
  {v : K // v ∉ g}

noncomputable def edgeSumEquiv (g : Finset K) :
    {v : K // v ∈ g} ⊕ EdgeComplement g ≃ K :=
  Equiv.sumCompl fun v : K => v ∈ g

noncomputable def splitEdgeEquiv
    (g : Finset K) :
    (K → G) ≃
      (({v : K // v ∈ g} → G) ×
        (EdgeComplement g → G)) :=
  (Equiv.piCongrLeft (fun _ : K => G)
      (edgeSumEquiv g)).symm.trans
    (Equiv.sumPiEquivProdPi
      (fun _ : {v : K // v ∈ g} ⊕
        EdgeComplement g => G))

@[simp]
theorem splitEdgeEquiv_fst
    (g : Finset K) (x : K → G) :
    (splitEdgeEquiv g x).1 = edgeTuple g x := by
  funext v
  simp [splitEdgeEquiv, edgeSumEquiv, edgeTuple]

@[simp]
theorem edgeTuple_splitEdgeEquiv_symm
    (g : Finset K)
    (y : {v : K // v ∈ g} → G)
    (z : EdgeComplement g → G) :
    edgeTuple g ((splitEdgeEquiv g).symm (y, z)) = y := by
  rw [← splitEdgeEquiv_fst]
  simp

noncomputable def edgeRemainderFiber
    (B : HypergraphBundle J K H)
    (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G)
    (z : EdgeComplement g₀ → G) : ℝ :=
  B.edgeRemainder g₀ A
    ((splitEdgeEquiv g₀).symm (y, z))

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.CountExtraction
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def cyclicAPMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, ∑ d : ZMod N, cyclicAPProduct k N f a d

noncomputable def cyclicAPDiagonalMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N, cyclicAPProduct k N f a 0

noncomputable def cyclicAPOffDiagMass (k N : ℕ) [NeZero N]
    (f : ZMod N → ℝ) : ℝ :=
  ∑ a : ZMod N,
    ∑ d ∈ (Finset.univ.filter fun d : ZMod N => d ≠ 0),
      cyclicAPProduct k N f a d

@[simp]
theorem cyclicAPProduct_zero_difference
    (k N : ℕ) (f : ZMod N → ℝ) (a : ZMod N) :
    cyclicAPProduct k N f a 0 = f a ^ k := by
  simp [cyclicAPProduct, cyclicAPTerm]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleFiltration
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

abbrev DoubledOccurrenceVertex (g₀ : Finset K) :=
  {v : K // v ∈ g₀} ⊕ (Bool × EdgeComplement g₀)

def doubledVertexForget
    (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → K
  | Sum.inl v => v.1
  | Sum.inr v => v.2.1

def doubledVertexLift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    DoubledOccurrenceVertex g₀ :=
  if hv : v ∈ g₀ then
    Sum.inl ⟨v, hv⟩
  else
    Sum.inr ⟨copy, ⟨v, hv⟩⟩

@[simp]
theorem doubledVertexForget_lift
    (g₀ : Finset K) (copy : Bool) (v : K) :
    doubledVertexForget g₀
        (doubledVertexLift g₀ copy v) = v := by
  by_cases hv : v ∈ g₀ <;>
    simp [doubledVertexLift, doubledVertexForget, hv]

def doubledAssignment
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    DoubledOccurrenceVertex g₀ → G
  | Sum.inl v => y v
  | Sum.inr (false, v) => z.1 v
  | Sum.inr (true, v) => z.2 v

def splitDoubledAssignmentEquiv
    (g₀ : Finset K) :
    (DoubledOccurrenceVertex g₀ → G) ≃
      (({v : K // v ∈ g₀} → G) ×
        ((EdgeComplement g₀ → G) ×
          (EdgeComplement g₀ → G))) where
  toFun x :=
    (fun v => x (Sum.inl v),
      (fun v => x (Sum.inr (false, v)),
        fun v => x (Sum.inr (true, v))))
  invFun p := doubledAssignment g₀ p.1 p.2
  left_inv x := by
    funext v
    rcases v with v | ⟨copy, v⟩
    · rfl
    · cases copy <;> rfl
  right_inv p := by
    rcases p with ⟨y, zfalse, ztrue⟩
    rfl

omit [DecidableEq K] in
@[simp]
theorem splitDoubledAssignmentEquiv_symm_apply
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G)) :
    (splitDoubledAssignmentEquiv g₀).symm (y, z) =
      doubledAssignment g₀ y z :=
  rfl

@[simp]
theorem doubledAssignment_lift_false
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ false v) =
      (splitEdgeEquiv g₀).symm (y, z.1) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.1 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

@[simp]
theorem doubledAssignment_lift_true
    (g₀ : Finset K)
    (y : {v : K // v ∈ g₀} → G)
    (z : (EdgeComplement g₀ → G) ×
      (EdgeComplement g₀ → G))
    (v : K) :
    doubledAssignment g₀ y z
        (doubledVertexLift g₀ true v) =
      (splitEdgeEquiv g₀).symm (y, z.2) v := by
  classical
  by_cases hv : v ∈ g₀
  · simp only [doubledVertexLift, dif_pos hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInl
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]
  · simp only [doubledVertexLift, dif_neg hv,
      doubledAssignment]
    unfold splitEdgeEquiv
    convert
      (Equiv.piCongrLeft_sumInr
        (fun _ : K => G) (edgeSumEquiv g₀)
        y z.2 ⟨v, hv⟩).symm using 1 ;
      simp [edgeSumEquiv]

def doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    Finset (DoubledOccurrenceVertex g₀) :=
  g.image (doubledVertexLift g₀ copy)

theorem mem_doubledEdge
    (g₀ : Finset K) (copy : Bool)
    (g : Finset K) (v : K) (hv : v ∈ g) :
    doubledVertexLift g₀ copy v ∈
      doubledEdge g₀ copy g :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

@[simp]
theorem image_forget_doubledEdge
    (g₀ : Finset K) (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (doubledVertexForget g₀) = g := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    have huv : u = v := by
      simpa using hwv
    exact huv ▸ hu
  · intro hv
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv, by simp⟩

abbrev DoubledEdgeSource
    (B : HypergraphBundle J K H) (g₀ : Finset K) :=
  Bool × {g : Finset K // g ∈ (B.edges.erase g₀)}

def doubledEdgeOfSource
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (s : B.DoubledEdgeSource g₀) :
    Finset (DoubledOccurrenceVertex g₀) :=
  doubledEdge g₀ s.1 s.2.1

noncomputable def doubledSourceProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (x : DoubledOccurrenceVertex g₀ → G) : ℝ :=
  ∏ s : B.DoubledEdgeSource g₀,
    A s.2.1 (fun v =>
      x (doubledVertexLift g₀ s.1 v.1))

def doubledEdges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    Finset (Finset (DoubledOccurrenceVertex g₀)) :=
  Finset.univ.image (B.doubledEdgeOfSource g₀)

theorem mem_doubledEdges_iff
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (d : Finset (DoubledOccurrenceVertex g₀)) :
    d ∈ B.doubledEdges g₀ ↔
      ∃ (copy : Bool) (g : Finset K),
        g ∈ B.edges.erase g₀ ∧
          doubledEdge g₀ copy g = d := by
  classical
  constructor
  · intro hd
    obtain ⟨s, _hs, hsd⟩ :=
      Finset.mem_image.mp hd
    exact ⟨s.1, s.2.1, s.2.2, hsd⟩
  · rintro ⟨copy, g, hg, rfl⟩
    exact
      Finset.mem_image.mpr
        ⟨(copy, ⟨g, hg⟩), Finset.mem_univ _, rfl⟩

def doubledProjection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    DoubledOccurrenceVertex g₀ → J :=
  fun v => B.projection (doubledVertexForget g₀ v)

@[simp]
theorem doubledProjection_lift
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (v : K) :
    B.doubledProjection g₀
        (doubledVertexLift g₀ copy v) =
      B.projection v := by
  simp [doubledProjection]

@[simp]
theorem image_doubledProjection_doubledEdge
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (copy : Bool) (g : Finset K) :
    (doubledEdge g₀ copy g).image
        (B.doubledProjection g₀) =
      g.image B.projection := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_image.mpr
      ⟨w, hw, by simpa using hvj⟩
  · intro hj
    obtain ⟨v, hv, hvj⟩ := Finset.mem_image.mp hj
    exact
      Finset.mem_image.mpr
        ⟨doubledVertexLift g₀ copy v,
          mem_doubledEdge g₀ copy g v hv,
          by simpa using hvj⟩

def duplicateOutside
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J (DoubledOccurrenceVertex g₀) H where
  edges := B.doubledEdges g₀
  projection := B.doubledProjection g₀
  projection_injective_on_edge := by
    intro d hd v hv w hw hvw
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    obtain ⟨v₀, hv₀, rfl⟩ :=
      Finset.mem_image.mp hv
    obtain ⟨w₀, hw₀, rfl⟩ :=
      Finset.mem_image.mp hw
    apply congrArg (doubledVertexLift g₀ copy)
    apply B.projection_injective_on_edge g
      (Finset.mem_of_mem_erase hg) hv₀ hw₀
    simpa using hvw
  projection_mem_base := by
    intro d hd
    obtain ⟨copy, g, hg, rfl⟩ :=
      (B.mem_doubledEdges_iff g₀ d).1 hd
    rw [image_doubledProjection_doubledEdge]
    exact B.projection_mem_base g
      (Finset.mem_of_mem_erase hg)

@[simp]
theorem duplicateOutside_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).edges =
      B.doubledEdges g₀ :=
  rfl

@[simp]
theorem duplicateOutside_projection
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.duplicateOutside g₀).projection =
      B.doubledProjection g₀ :=
  rfl

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    HypergraphBundle J K H where
  edges := B.edges.filter P
  projection := B.projection
  projection_injective_on_edge := by
    intro g hg
    exact B.projection_injective_on_edge g
      (Finset.mem_filter.mp hg).1
  projection_mem_base := by
    intro g hg
    exact B.projection_mem_base g
      (Finset.mem_filter.mp hg).1

@[simp]
theorem filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).edges = B.edges.filter P :=
  rfl

@[simp]
theorem mem_filterEdges_edges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (g : Finset K) :
    g ∈ (B.filterEdges P).edges ↔
      g ∈ B.edges ∧ P g := by
  simp [filterEdges]

@[simp]
theorem filterEdges_projection
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P] :
    (B.filterEdges P).projection = B.projection :=
  rfl

def lowerOrder
    (B : HypergraphBundle J K H) (d : ℕ) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g.card < d

@[simp]
theorem lowerOrder_edges
    (B : HypergraphBundle J K H) (d : ℕ) :
    (B.lowerOrder d).edges =
      B.edges.filter fun g => g.card < d :=
  rfl

@[simp]
theorem mem_lowerOrder_edges
    (B : HypergraphBundle J K H)
    (d : ℕ) (g : Finset K) :
    g ∈ (B.lowerOrder d).edges ↔
      g ∈ B.edges ∧ g.card < d := by
  simp [lowerOrder]

def strictBoundary
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    HypergraphBundle J K H :=
  B.filterEdges fun g => g ⊂ g₀

@[simp]
theorem strictBoundary_edges
    (B : HypergraphBundle J K H) (g₀ : Finset K) :
    (B.strictBoundary g₀).edges =
      B.edges.filter fun g => g ⊂ g₀ :=
  rfl

@[simp]
theorem mem_strictBoundary_edges
    (B : HypergraphBundle J K H)
    (g₀ g : Finset K) :
    g ∈ (B.strictBoundary g₀).edges ↔
      g ∈ B.edges ∧ g ⊂ g₀ := by
  simp [strictBoundary]

noncomputable def bundleMainProduct
    (B : HypergraphBundle J K H)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges, p (g.image B.projection)

@[simp]
theorem bundleMainProduct_filterEdges
    (B : HypergraphBundle J K H)
    (P : Finset K → Prop) [DecidablePred P]
    (p : Finset J → ℝ) :
    (B.filterEdges P).bundleMainProduct p =
      ∏ g ∈ B.edges.filter P,
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_lowerOrder
    (B : HypergraphBundle J K H)
    (d : ℕ) (p : Finset J → ℝ) :
    (B.lowerOrder d).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g.card < d),
        p (g.image B.projection) :=
  rfl

@[simp]
theorem bundleMainProduct_strictBoundary
    (B : HypergraphBundle J K H)
    (g₀ : Finset K) (p : Finset J → ℝ) :
    (B.strictBoundary g₀).bundleMainProduct p =
      ∏ g ∈ B.edges.filter (fun g => g ⊂ g₀),
        p (g.image B.projection) :=
  rfl

end HypergraphBundle

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.HypergraphBundleEnvelopeSelection
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def BaseWeightsIdempotent
    (H : Finset (Finset J))
    (A : BaseEdgeWeight J G) : Prop :=
  ∀ e ∈ H, ∀ y, A e y * A e y = A e y

def finsetMembershipEquivOfEq
    {α : Type*} {s t : Finset α} (h : s = t) :
    {a : α // a ∈ s} ≃ {a : α // a ∈ t} :=
  Equiv.cast
    (congrArg (fun u : Finset α => {a : α // a ∈ u}) h)

@[simp]
theorem finsetMembershipEquivOfEq_symm_val
    {α : Type*} {s t : Finset α} (h : s = t)
    (a : {a : α // a ∈ t}) :
    ((finsetMembershipEquivOfEq h).symm a).1 = a.1 := by
  subst t
  rfl

@[simp]
theorem projectionEquiv_apply_val
    (B : HypergraphBundle J K H)
    {g : Finset K} (hg : g ∈ B.edges)
    (v : {v : K // v ∈ g}) :
    ((B.projectionEquiv hg) v).1 =
      B.projection v.1 := by
  rfl

noncomputable def doubledBundleEdgeFactor
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : BaseEdgeWeight J G)
    (x : DoubledOccurrenceVertex g₀ → G)
    (d : Finset (DoubledOccurrenceVertex g₀)) : ℝ :=
  (B.duplicateOutside g₀).pullbackBaseEdgeWeight A d
    (edgeTuple d x)

end HypergraphBundle

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

namespace HypergraphBundle

variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

def restrictEdgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (y : {v : K // v ∈ g} → G) :
    {v : K // v ∈ f} → G :=
  fun v => y ⟨v.1, hfg v.2⟩

omit [DecidableEq K] in
@[simp]
theorem restrictEdgeTuple_edgeTuple
    {f g : Finset K} (hfg : f ⊆ g)
    (x : K → G) :
    restrictEdgeTuple hfg (edgeTuple g x) =
      edgeTuple f x := by
  rfl

noncomputable def strictBoundaryLocalProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ)
    (y : {v : K // v ∈ g₀} → G) : ℝ :=
  ∏ g :
      {g : Finset K //
        g ∈ (B.strictBoundary g₀).edges},
    A g.1
      (restrictEdgeTuple
        (((B.mem_strictBoundary_edges g₀ g.1).1
          g.2).2.1)
        y)

def WeightsIdempotent
    (B : HypergraphBundle J K H)
    (A : (g : Finset K) →
      ({v : K // v ∈ g} → G) → ℝ) : Prop :=
  ∀ g ∈ B.edges, ∀ y,
    A g y * A g y = A g y

noncomputable def lowerExteriorMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ B.edges.filter
      (fun g =>
        g.card < g₀.card ∧ ¬ g ⊆ g₀),
    p (g.image B.projection)

noncomputable def maximalRemainderMainProduct
    (B : HypergraphBundle J K H) (g₀ : Finset K)
    (p : Finset J → ℝ) : ℝ :=
  ∏ g ∈ (B.edges.erase g₀).filter
      (fun g => ¬ g.card < g₀.card),
    p (g.image B.projection)

end HypergraphBundle

structure IsBundleCountingEnvelope
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ) : Prop where
  density_pos : ∀ d, 0 < α d
  density_le_one : ∀ d, α d ≤ 1
  defect_nonneg : ∀ d, 0 ≤ β d
  uniform_nonneg : 0 ≤ τ
  floor_pos : ∀ d, 0 < μ d
  rankFloor :
    ∀ ⦃i d : ℕ⦄, i ≤ d → μ d ≤ α i
  error_nonneg :
    ∀ d n, 0 ≤ E d n
  error_mono_order :
    ∀ ⦃d d' n : ℕ⦄, d ≤ d' →
      E d n ≤ E d' n
  error_mono_card :
    ∀ ⦃d n n' : ℕ⦄, n ≤ n' →
      E d n ≤ E d n'
  step :
    ∀ d n,
      E (d + 1) n +
            Real.sqrt
                (β (d + 1) *
                  (1 + E d (n + 1)) *
                  (1 + E d (2 * (n + 1)))) /
              (α (d + 1)) ^ (n + 1) +
          τ / (μ (d + 1)) ^ (n + 1) ≤
        E (d + 1) (n + 1)

noncomputable def bundleCountingStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (E : ℕ → ℕ → ℝ)
    (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + E d (n + 1)) *
          (1 + E d (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.StrongOrderedComplexRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem exists_adjacent_real_sub_le_div
    (E : ℕ → ℝ) {length : ℕ}
    (hlength : 0 < length)
    {B : ℝ}
    (hE0 : 0 ≤ E 0)
    (hElast : E length ≤ B) :
    ∃ i : ℕ, i < length ∧
      E (i + 1) - E i ≤ B / length := by
  have htel :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) =
        E length - E 0 :=
    Finset.sum_range_sub E length
  have hsum :
      ∑ i ∈ Finset.range length,
          (E (i + 1) - E i) ≤
        ∑ _i ∈ Finset.range length,
          B / (length : ℝ) := by
    rw [htel]
    calc
      E length - E 0 ≤ B := by linarith
      _ =
          ∑ _i ∈ Finset.range length,
            B / (length : ℝ) := by
        simp only [Finset.sum_const,
          Finset.card_range, nsmul_eq_mul]
        field_simp
  obtain ⟨i, hi, hsmall⟩ :=
    Finset.exists_le_of_sum_le
      ⟨0, Finset.mem_range.mpr hlength⟩ hsum
  exact ⟨i, Finset.mem_range.mp hi, hsmall⟩

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemovalAssembly
namespace OAI

section

namespace Erdos3.FixedDensity

structure NatGrowthFunction where
  toFun : ℕ → ℕ
  monotone' : Monotone toFun
  above_diagonal : ∀ n, n + 1 ≤ toFun n

namespace NatGrowthFunction

instance instCoeFunForallNat : CoeFun NatGrowthFunction (fun _ => ℕ → ℕ) :=
  ⟨NatGrowthFunction.toFun⟩

end NatGrowthFunction

noncomputable def growthRegularityStepTolerance
    (F : NatGrowthFunction) (M : ℕ) : ℝ :=
  1 / (F M : ℝ)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.RankwiseBundleEnvelopeSelection
namespace OAI

section

namespace Erdos3.FixedDensity

open Filter Topology

def bundleRankwiseDensityFloor (α : ℕ → ℝ) : ℕ → ℝ
  | 0 => α 0
  | d + 1 => min (bundleRankwiseDensityFloor α d) (α (d + 1))

@[simp]
theorem bundleRankwiseDensityFloor_zero (α : ℕ → ℝ) :
    bundleRankwiseDensityFloor α 0 = α 0 :=
  rfl

@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl

noncomputable def bundleRankwiseStepIncrement
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (lower : ℕ → ℝ) (d n : ℕ) : ℝ :=
  Real.sqrt
        (β (d + 1) *
          (1 + lower (n + 1)) *
          (1 + lower (2 * (n + 1)))) /
      (α (d + 1)) ^ (n + 1) +
    τ / (μ (d + 1)) ^ (n + 1)

noncomputable def bundleRankwiseNextRow
    (α β μ : ℕ → ℝ) (τ : ℝ)
    (d : ℕ) (lower : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 =>
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n)

noncomputable def bundleRankwiseEnvelopeError
    (α β μ : ℕ → ℝ) (τ : ℝ) : ℕ → ℕ → ℝ
  | 0 => fun _ => 0
  | d + 1 =>
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d)

@[simp]
theorem bundleRankwiseNextRow_zero
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower 0 = 0 :=
  rfl

@[simp]
theorem bundleRankwiseNextRow_succ
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower (n + 1) =
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n) :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_zero_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ 0 n = 0 :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ (d + 1) n =
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d) n :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_zero_card
    (α β μ : ℕ → ℝ) (τ : ℝ) :
    ∀ d, bundleRankwiseEnvelopeError α β μ τ d 0 = 0 := by
  intro d
  cases d <;> simp

@[simp]
theorem bundleRankwiseNextRow_zero_parameters
    (α μ : ℕ → ℝ) (d : ℕ) (lower : ℕ → ℝ)
    (hlower : ∀ n, lower n = 0) :
    ∀ n,
      bundleRankwiseNextRow α (fun _ => 0) μ 0 d lower n = 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ, ih]
      simp [bundleRankwiseStepIncrement, hlower]

@[simp]
theorem bundleRankwiseEnvelopeError_zero_parameters
    (α μ : ℕ → ℝ) :
    ∀ d n,
      bundleRankwiseEnvelopeError α (fun _ => 0) μ 0 d n = 0 := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_zero_parameters α μ d _ ih n

def bundleReverseDoublingHorizon
    (rankBound edgeBound d : ℕ) : ℕ :=
  (edgeBound + 1) * 2 ^ (rankBound - d)

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.ShortInterval
namespace OAI

section

namespace Erdos3.FixedDensity

def cyclicAPVal {N : ℕ} [NeZero N] (a d : ZMod N) (j : ℕ) : ℕ :=
  (a + (j : ZMod N) * d).val

@[simp]
theorem cyclicAPVal_cast {N : ℕ} [NeZero N]
    (a d : ZMod N) (j : ℕ) :
    (cyclicAPVal a d j : ZMod N) = a + (j : ZMod N) * d :=
  ZMod.natCast_zmod_val _

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.TowerDominatingGrowth
namespace OAI

section

namespace Erdos3.FixedDensity

def finiteMaximum : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0, _ => 0
  | n + 1, value =>
      max
        (finiteMaximum n (fun i => value i.castSucc))
        (value (Fin.last n))

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullCoarseTargetRegularity
namespace OAI

section

namespace Erdos3.FixedDensity

noncomputable def sourceFullCommonTolerance
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ) : ℝ :=
  1 / (F (scale 0) : ℝ)

noncomputable def sourceFullRankGap
    {r : ℕ} (F : NatGrowthFunction)
    (scale : Fin (r + 1) → ℕ)
    (j : Fin r) : ℝ :=
  1 / (F (scale j.succ) : ℝ) ^ 2

namespace SourceFullCoarseTargetSchedule

def factorLowerInitialBound
    {r : ℕ}
    (initialBound : Fin (r + 2) → ℕ)
    (factor : ℕ) :
    Fin (r + 1) → ℕ :=
  Fin.lastCases
    (factor * initialBound (Fin.last r).castSucc)
    (fun q => initialBound q.castSucc.castSucc)

end SourceFullCoarseTargetSchedule

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.SourceFullBundleRemovalParameters
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def sourceBundleDensity (δ : ℝ) (m : ℕ) : ℝ :=
  δ / (m + 1 : ℕ)

noncomputable def sourceBundleDefectScale
    (δ η : ℝ) (N m : ℕ) : ℝ :=
  η * sourceBundleDensity δ m ^ N

def sourceBundleSelectedScale
    {r : ℕ} (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℕ :=
  scale ⟨min d r, Nat.lt_succ_iff.mpr (Nat.min_le_right d r)⟩

@[simp]
theorem sourceBundleSelectedScale_zero
    {r : ℕ} (scale : Fin (r + 1) → ℕ) :
    sourceBundleSelectedScale scale 0 = scale 0 := by
  simp [sourceBundleSelectedScale]

noncomputable def sourceBundleRankwiseDensity
    {r : ℕ} (δ : ℝ) (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDensity δ (sourceBundleSelectedScale scale d)

noncomputable def sourceBundleRankwiseDefect
    {r : ℕ} (δ κ : ℝ) (N : ℕ)
    (scale : Fin (r + 1) → ℕ) (d : ℕ) : ℝ :=
  sourceBundleDefectScale δ κ N
      (sourceBundleSelectedScale scale d) ^ 2

structure SourceBundleRemovalGrowthConditions
    (δ η : ℝ) (N Q : ℕ) : Prop where
  uniform :
    1 ≤ (Q : ℝ) * η ^ 2 * δ ^ N
  gap :
    1 ≤ δ * (Q : ℝ) ^ 2 * η ^ 2 * δ ^ (2 * N)

end Erdos3.FixedDensity

end

end OAI
end


