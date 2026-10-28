-- Prove2me | Definitions.Def_OAIQ033D009
-- name    : OAIQ033D009
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T01:47:40.312995+00:00
-- url     : https://prove2.me/theorems/20d57a6c-d282-4210-97bc-ce4faa883bc5
-- title:
--   Definitions bundle OAIQ033D009 of the split of OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.DimensionTen.main_pair`, carved from OpenAI's openai/math development (OpenAI, *Entanglement without distillable secret key in local dimension ten (result family 272)*, OpenAI Math Release, September 27, 2026, result family 272, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 143 declarations of OpenAI's Lean: 131 definitions, 4 instances and 8 theorems. The definitions and types are `OAI.DimensionTen.Mod139.pow6_17_mul_t`, `OAI.DimensionTen.Mod139.pow6_2`, `OAI.DimensionTen.Mod139.pow6_2_mul_t`, `OAI.DimensionTen.Mod139.pow6_2_q`, `OAI.DimensionTen.Mod139.pow6_34`, `OAI.DimensionTen.Mod139.pow6_34_mul_t`, `OAI.DimensionTen.Mod139.pow6_34_q`, `OAI.DimensionTen.Mod139.pow6_4`, `OAI.DimensionTen.Mod139.pow6_4_mul_t`, `OAI.DimensionTen.Mod139.pow6_4_q`, `OAI.DimensionTen.Mod139.pow6_68`, `OAI.DimensionTen.Mod139.pow6_68_mul_t`, `OAI.DimensionTen.Mod139.pow6_68_q`, `OAI.DimensionTen.Mod139.pow6_69`, `OAI.DimensionTen.Mod139.pow6_69_mul_t`, `OAI.DimensionTen.Mod139.pow6_69_q`, `OAI.DimensionTen.Mod139.pow6_8`, `OAI.DimensionTen.Mod139.pow6_8_mul_t`, `OAI.DimensionTen.Mod139.pow6_8_q`, `OAI.DimensionTen.Mod139.pow7_138`, `OAI.DimensionTen.Mod139.pow7_138_mul_t`, `OAI.DimensionTen.Mod139.pow7_138_q`, `OAI.DimensionTen.Mod139.pow7_139`, `OAI.DimensionTen.Mod139.pow7_139_mul_t`, `OAI.DimensionTen.Mod139.pow7_139_q`, `OAI.DimensionTen.Mod139.pow7_16`, `OAI.DimensionTen.Mod139.pow7_16_mul_t`, `OAI.DimensionTen.Mod139.pow7_16_q`, `OAI.DimensionTen.Mod139.pow7_17`, `OAI.DimensionTen.Mod139.pow7_17_mul_t`, `OAI.DimensionTen.Mod139.pow7_17_q`, `OAI.DimensionTen.Mod139.pow7_2`, `OAI.DimensionTen.Mod139.pow7_2_mul_t`, `OAI.DimensionTen.Mod139.pow7_2_q`, `OAI.DimensionTen.Mod139.pow7_34`, `OAI.DimensionTen.Mod139.pow7_34_mul_t`, `OAI.DimensionTen.Mod139.pow7_34_q`, `OAI.DimensionTen.Mod139.pow7_4`, `OAI.DimensionTen.Mod139.pow7_4_mul_t`, `OAI.DimensionTen.Mod139.pow7_4_q` and 91 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/Quantum/DimensionTen, in whole or in part: `Quantum_DimensionTen_ChoiPairing`, `Quantum_DimensionTen_CompoundTrace`, `Quantum_DimensionTen_ExteriorMaps`, `Quantum_DimensionTen_Kraus`, `Quantum_DimensionTen_Mod139Powers03`, `Quantum_DimensionTen_Mod139Powers04`, `Quantum_DimensionTen_Mod139Powers05`, `Quantum_DimensionTen_Mod139Result`, `Quantum_DimensionTen_PencilKraus`, `Quantum_DimensionTen_PencilModel`, `Quantum_DimensionTen_PureMatrices`, `Quantum_DimensionTen_RootReduction`, `Quantum_DimensionTen_Veronese`, `Quantum_PPTSquare_Mod131Data`, `Quantum_PPTSquare_Mod139Data`, `Quantum_PPTSquare_Mod41Data`, `Quantum_PPTSquare_TensorModel`.
--
--   **Imports.** It imports the published bundle `Def_DimensionTenPair`.
--
--   **Imported by** (directly, in this split): the statements `OAI.DimensionTen.Border.quadratic_zero_bound` and `OAI.DimensionTen.compositeChoi_kernel_rank`; the proofs of `OAI.DimensionTen.Border.quadratic_zero_bound`, `OAI.DimensionTen.Mod139.iterate12`, `OAI.DimensionTen.Mod139.iterate6`, `OAI.DimensionTen.compositeChoi_kernel_rank`, `OAI.DimensionTen.compositeChoi_ne`, `OAI.DimensionTen.exists_swap_of_mod131` and `OAI.DimensionTen.main_pair`.
-- source:
--   OpenAI, Entanglement without distillable secret key in local dimension ten (result family 272), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 272; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Entanglement-with-zero-distillable-secret-key-in-local-dimension-ten-September-27-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/Quantum/DimensionTen at commit adc7f12

import Mathlib
import Definitions.Def_DimensionTenPair

section
-- module Solutions.OAIQ033_DT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_PPTSquare_Mod131Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
namespace P131
local instance primeFact : Fact (Nat.Prime 131) := ⟨by decide +kernel⟩
end P131
end ModularPencil

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_PPTSquare_Mod139Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
namespace P139
local instance primeFact : Fact (Nat.Prime 139) := ⟨by decide +kernel⟩
end P139
end ModularPencil

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_PPTSquare_Mod41Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Matrix
namespace ModularPencil
namespace P41
local instance primeFact : Fact (Nat.Prime 41) := ⟨by decide +kernel⟩
end P41
end ModularPencil

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_PPTSquare_TensorModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
open scoped MatrixOrder
namespace TensorCriterion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix

def altPair : Fin 6 → Fin 4 × Fin 4 := ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]

end TensorCriterion

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder
open Matrix Complex

namespace DimensionTen

def pencil (x : Fin 4 → ℂ) : Matrix (Fin 6) (Fin 4) ℂ :=
  ∑ i : Fin 4, x i • blocks i


def projector (x : Fin 4 → ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.vecMulVec x (star x)


def chart (t : Fin 3 → ℂ) : Fin 4 → ℂ := Fin.cons 1 t


end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PureMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def pure {n : Type*} (x : n → ℂ) : Matrix n n ℂ := Matrix.vecMulVec x (star x)

def omega (a : ℕ) : Fin a × Fin a → ℂ := fun ij => if ij.1 = ij.2 then 1 else 0

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Kraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open Matrix
namespace DimensionTen

def krausMap {r a b : Type*} [Fintype r] [Fintype a]
    (Q : r → Matrix b a ℂ) (A : Matrix a a ℂ) : Matrix b b ℂ :=
  ∑ k, Q k * A * (Q k)ᴴ

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ChoiPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def asLinearMap {a b : ℕ} (F : Mat a → Mat b) (hF : IsComplexLinear F) :
    Mat a →ₗ[ℂ] Mat b where
  toFun := F
  map_add' := hF.1
  map_smul' := hF.2

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Veronese
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def veronese (x : Fin 4 → ℂ) (i : Fin 10) : ℂ :=
  let p := (symmetricPairs i).1
  let q := (symmetricPairs i).2
  (if p = q then 1 else (Real.sqrt 2 : ℂ)) * x p * x q

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_CompoundTrace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def compound (B : Mat 4) : Mat 6 := fun i j =>
  B (exteriorPairs i).1 (exteriorPairs j).1 * B (exteriorPairs i).2 (exteriorPairs j).2 -
  B (exteriorPairs i).1 (exteriorPairs j).2 * B (exteriorPairs i).2 (exteriorPairs j).1

end DimensionTen

end
end

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def complementaryIndex : Fin 6 → Fin 6 := ![5,4,3,2,1,0]
def complementarySign : Fin 6 → ℂ := ![1,-1,1,1,-1,1]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_PencilKraus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def pencilKraus (r : Fin 6) : Mat 4 := fun i j => blocks j r i

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_ExteriorMaps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

def exteriorKraus (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 10) ℂ :=
  exteriorIsometryᴴ * (pencilKraus p.1 ⊗ₖ pencilKraus p.2) * symmetricIsometry

def complementaryKraus (p : Fin 6 × Fin 6) : Matrix (Fin 6) (Fin 10) ℂ :=
  hodgeComplement * exteriorKraus p

def phiOneKraus (p : Fin 6 × Fin 6) : Mat 10 := firstSix * exteriorKraus p

def phiTwoKraus (p : Fin 6 × Fin 6) : Mat 10 := (complementaryKraus p)ᴴ * firstSixᴴ

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers03
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139


def pow6_2 {R : Type*} [CommRing R] (z : R) : R := (44 + z * (137 + z * (3 + z * (84 + z * (61 + z * (97 + z * (44 + z * (118 + z * (76 + z * (88 + z * (118 + z * (131 + z * (132 + z * (91 + z * (110 + z * (28 + z * (51 + z * (101 + z * (71 + z * 14)))))))))))))))))))

def pow6_2_q {R : Type*} [CommRing R] (z : R) : R := (34 + z * (32 + z * (108 + z * (50 + z * (80 + z * (62 + z * (1 + z * (26 + z * (6 + z * (16 + z * (77 + z * (56 + z * (121 + z * (60 + z * (76 + z * (24 + z * (59 + z * (63 + z * 69))))))))))))))))))

def pow6_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-26) + z * ((-55) + z * ((-104) + z * ((-136) + z * ((-162) + z * ((-119) + z * ((-131) + z * ((-118) + z * (7 + z * ((-86) + z * ((-46) + z * (61 + z * ((-103) + z * ((-88) + z * ((-13) + z * ((-141) + z * ((-36) + z * (72 + z * (61 + z * (157 + z * (247 + z * (110 + z * (301 + z * (292 + z * (155 + z * (319 + z * (367 + z * (253 + z * (284 + z * (327 + z * (178 + z * (121 + z * (197 + z * (181 + z * (278 + z * (206 + z * (73 + z * (123 + z * 93))))))))))))))))))))))))))))))))))))))


def pow6_4 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (34 + z * (133 + z * (87 + z * (28 + z * (74 + z * (52 + z * (45 + z * (130 + z * (120 + z * (2 + z * (36 + z * (109 + z * (21 + z * (88 + z * (8 + z * (4 + z * (124 + z * (71 + z * 20)))))))))))))))))))

def pow6_4_q {R : Type*} [CommRing R] (z : R) : R := (85 + z * (25 + z * (63 + z * (41 + z * (98 + z * (46 + z * (109 + z * (4 + z * (127 + z * (131 + z * (6 + z * (71 + z * (75 + z * (134 + z * (31 + z * (73 + z * (101 + z * (113 + z * 57))))))))))))))))))

def pow6_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-51) + z * ((-7) + z * ((-10) + z * ((-131) + z * ((-53) + z * ((-78) + z * ((-64) + z * ((-101) + z * (12 + z * ((-171) + z * ((-33) + z * (52 + z * (107 + z * (35 + z * (141 + z * (119 + z * ((-51) + z * (125 + z * (69 + z * (48 + z * (127 + z * (165 + z * (127 + z * (221 + z * (149 + z * (123 + z * (81 + z * ((-35) + z * (88 + z * (105 + z * (25 + z * ((-94) + z * ((-137) + z * ((-89) + z * ((-58) + z * ((-63) + z * ((-90) + z * ((-39) + z * 1))))))))))))))))))))))))))))))))))))))


def pow6_8 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (129 + z * (60 + z * (82 + z * (72 + z * (20 + z * (40 + z * (8 + z * (137 + z * (85 + z * (123 + z * (128 + z * (63 + z * (111 + z * (18 + z * (50 + z * (106 + z * (52 + z * (108 + z * 64)))))))))))))))))))

def pow6_8_q {R : Type*} [CommRing R] (z : R) : R := (84 + z * (3 + z * (61 + z * (120 + z * (128 + z * (18 + z * (122 + z * (115 + z * (116 + z * (86 + z * (23 + z * (120 + z * (107 + z * (69 + z * (75 + z * (19 + z * (52 + z * (12 + z * 122))))))))))))))))))

def pow6_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (8 + z * ((-28) + z * (75 + z * ((-37) + z * ((-116) + z * ((-33) + z * ((-196) + z * ((-225) + z * ((-116) + z * ((-171) + z * ((-211) + z * ((-126) + z * ((-274) + z * ((-441) + z * ((-133) + z * ((-374) + z * ((-406) + z * ((-104) + z * ((-416) + z * ((-337) + z * ((-133) + z * ((-384) + z * ((-468) + z * ((-222) + z * ((-315) + z * ((-226) + z * ((-44) + z * ((-366) + z * ((-249) + z * ((-59) + z * ((-162) + z * ((-108) + z * ((-111) + z * ((-131) + z * ((-41) + z * (71 + z * ((-29) + z * ((-92) + z * 2))))))))))))))))))))))))))))))))))))))

def pow6_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-20) + z * ((-4) + z * ((-36) + z * ((-55) + z * (10 + z * ((-97) + z * ((-205) + z * ((-125) + z * ((-204) + z * ((-209) + z * ((-82) + z * ((-67) + z * ((-131) + z * ((-75) + z * ((-192) + z * ((-137) + z * (5 + z * ((-47) + z * ((-34) + z * (77 + z * ((-106) + z * ((-135) + z * (155 + z * (84 + z * ((-20) + z * (17 + z * (49 + z * (142 + z * (120 + z * (133 + z * (34 + z * ((-6) + z * (49 + z * ((-11) + z * (76 + z * (75 + z * ((-27) + z * (21 + z * 46))))))))))))))))))))))))))))))))))))))


def pow6_34 {R : Type*} [CommRing R] (z : R) : R := (100 + z * (20 + z * (85 + z * (129 + z * (56 + z * (73 + z * (116 + z * (88 + z * (86 + z * (85 + z * (72 + z * (25 + z * (41 + z * (133 + z * (128 + z * (74 + z * (132 + z * (45 + z * (67 + z * 138)))))))))))))))))))

def pow6_34_q {R : Type*} [CommRing R] (z : R) : R := (3 + z * (110 + z * (11 + z * (65 + z * (92 + z * (72 + z * (97 + z * (94 + z * (134 + z * (101 + z * (136 + z * (14 + z * (66 + z * (50 + z * (69 + z * (37 + z * (62 + z * (12 + z * 35))))))))))))))))))

def pow6_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (15 + z * ((-24) + z * ((-1) + z * (22 + z * (11 + z * (38 + z * (122 + z * (78 + z * (16 + z * (16 + z * ((-98) + z * ((-90) + z * (109 + z * ((-26) + z * (90 + z * (149 + z * (71 + z * (200 + z * (308 + z * (215 + z * (361 + z * (388 + z * (278 + z * (334 + z * (98 + z * (258 + z * (44 + z * (185 + z * (262 + z * (167 + z * (389 + z * (178 + z * (202 + z * (231 + z * (181 + z * (213 + z * (131 + z * (62 + z * 34))))))))))))))))))))))))))))))))))))))


def pow6_68 {R : Type*} [CommRing R] (z : R) : R := (54 + z * (46 + z * (120 + z * (15 + z * (55 + z * (69 + z * (105 + z * (89 + z * (112 + z * (74 + z * (103 + z * (100 + z * (126 + z * (107 + z * (75 + z * (115 + z * (109 + z * (45 + z * (27 + z * 21)))))))))))))))))))

def pow6_68_q {R : Type*} [CommRing R] (z : R) : R := (10 + z * (124 + z * (137 + z * (132 + z * (116 + z * (55 + z * (106 + z * (30 + z * (17 + z * (123 + z * (77 + z * (138 + z * (1 + z * (135 + z * (68 + z * (100 + z * (25 + z * (16 + z * 1))))))))))))))))))

def pow6_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (64 + z * ((-74) + z * ((-97) + z * ((-131) + z * ((-283) + z * ((-214) + z * ((-131) + z * ((-116) + z * (9 + z * (15 + z * ((-88) + z * ((-240) + z * ((-170) + z * ((-128) + z * ((-160) + z * ((-119) + z * (73 + z * ((-71) + z * (85 + z * (238 + z * (81 + z * (276 + z * (328 + z * (217 + z * (171 + z * (226 + z * (281 + z * (247 + z * (202 + z * (184 + z * (183 + z * (225 + z * (355 + z * (260 + z * (177 + z * (270 + z * (106 + z * (132 + z * 137))))))))))))))))))))))))))))))))))))))


def pow6_69 {R : Type*} [CommRing R] (z : R) : R := (68 + z * (85 + z * (124 + z * (43 + z * (78 + z * (5 + z * (97 + z * (73 + z * (36 + z * (115 + z * (93 + z * (35 + z * (75 + z * (102 + z * (116 + z * (49 + z * (56 + z * (14 + z * (52 + z * 64)))))))))))))))))))

def pow6_69_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (40 + z * (17 + z * (98 + z * (74 + z * (60 + z * (20 + z * (24 + z * (114 + z * (52 + z * (85 + z * (91 + z * (29 + z * (35 + z * (112 + z * (74 + z * (67 + z * (114 + z * 31))))))))))))))))))

def pow6_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-2) + z * ((-5) + z * ((-5) + z * ((-19) + z * ((-70) + z * ((-105) + z * ((-80) + z * ((-73) + z * ((-74) + z * (50 + z * ((-56) + z * ((-47) + z * ((-45) + z * (15 + z * ((-20) + z * (109 + z * (97 + z * (41 + z * (15 + z * (123 + z * (189 + z * (149 + z * (225 + z * (214 + z * (146 + z * (310 + z * (232 + z * (119 + z * (235 + z * (158 + z * (89 + z * (214 + z * (97 + z * ((-3) + z * (98 + z * (11 + z * ((-61) + z * (10 + z * 17))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers04
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow7_2 {R : Type*} [CommRing R] (z : R) : R := (26 + z * (98 + z * (47 + z * (78 + z * (15 + z * (135 + z * (52 + z * (87 + z * (82 + z * (19 + z * (8 + z * (41 + z * (82 + z * (109 + z * (41 + z * (89 + z * (65 + z * (123 + z * (87 + z * 45)))))))))))))))))))

def pow7_2_q {R : Type*} [CommRing R] (z : R) : R := (60 + z * (95 + z * (79 + z * (103 + z * (57 + z * (132 + z * (134 + z * (35 + z * (135 + z * (119 + z * (81 + z * (37 + z * (99 + z * (111 + z * (31 + z * (77 + z * (50 + z * (5 + z * 89))))))))))))))))))

def pow7_2_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-34) + z * ((-67) + z * ((-109) + z * ((-246) + z * ((-317) + z * ((-319) + z * ((-227) + z * ((-233) + z * ((-318) + z * ((-498) + z * ((-357) + z * ((-424) + z * ((-340) + z * ((-540) + z * ((-307) + z * ((-564) + z * ((-416) + z * ((-453) + z * ((-426) + z * ((-597) + z * ((-389) + z * ((-435) + z * ((-336) + z * ((-138) + z * ((-268) + z * ((-187) + z * ((-228) + z * ((-227) + z * ((-321) + z * ((-147) + z * ((-70) + z * ((-193) + z * ((-29) + z * (10 + z * ((-35) + z * (51 + z * ((-13) + z * ((-55) + z * 5))))))))))))))))))))))))))))))))))))))


def pow7_4 {R : Type*} [CommRing R] (z : R) : R := (131 + z * (67 + z * (3 + z * (11 + z * (5 + z * (0 + z * (86 + z * (81 + z * (99 + z * (136 + z * (105 + z * (107 + z * (127 + z * (86 + z * (38 + z * (54 + z * (13 + z * (107 + z * (131 + z * 77)))))))))))))))))))

def pow7_4_q {R : Type*} [CommRing R] (z : R) : R := (78 + z * (87 + z * (28 + z * (137 + z * (138 + z * (83 + z * (70 + z * (73 + z * (111 + z * (109 + z * (22 + z * (74 + z * (19 + z * (67 + z * (115 + z * (66 + z * (74 + z * (81 + z * 79))))))))))))))))))

def pow7_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-55) + z * ((-98) + z * ((-81) + z * ((-185) + z * ((-262) + z * ((-301) + z * ((-192) + z * ((-298) + z * ((-200) + z * ((-329) + z * ((-327) + z * ((-415) + z * ((-322) + z * ((-316) + z * ((-334) + z * ((-354) + z * ((-417) + z * ((-442) + z * ((-275) + z * ((-352) + z * ((-94) + z * ((-226) + z * ((-224) + z * ((-174) + z * ((-147) + z * ((-63) + z * ((-128) + z * ((-273) + z * ((-76) + z * (17 + z * (71 + z * (68 + z * (17 + z * ((-20) + z * (66 + z * (68 + z * (1 + z * ((-17) + z * 14))))))))))))))))))))))))))))))))))))))


def pow7_8 {R : Type*} [CommRing R] (z : R) : R := (116 + z * (41 + z * (114 + z * (46 + z * (104 + z * (68 + z * (75 + z * (42 + z * (25 + z * (104 + z * (36 + z * (97 + z * (10 + z * (135 + z * (17 + z * (18 + z * (86 + z * (93 + z * (55 + z * 65)))))))))))))))))))

def pow7_8_q {R : Type*} [CommRing R] (z : R) : R := (116 + z * (126 + z * (134 + z * (40 + z * (114 + z * (124 + z * (65 + z * (116 + z * (136 + z * (45 + z * (104 + z * (99 + z * (12 + z * (6 + z * (51 + z * (6 + z * (132 + z * (47 + z * 91))))))))))))))))))

def pow7_8_mul_t {R : Type*} [CommRing R] (z : R) : R := (35 + z * ((-71) + z * ((-279) + z * ((-348) + z * ((-433) + z * ((-486) + z * ((-319) + z * ((-308) + z * ((-395) + z * ((-341) + z * ((-445) + z * ((-509) + z * ((-322) + z * ((-316) + z * ((-463) + z * ((-342) + z * ((-363) + z * ((-243) + z * ((-67) + z * ((-48) + z * ((-300) + z * ((-137) + z * (21 + z * ((-63) + z * (85 + z * (212 + z * (109 + z * (239 + z * (323 + z * (195 + z * (250 + z * (161 + z * (30 + z * (15 + z * ((-12) + z * (60 + z * (131 + z * (61 + z * 42))))))))))))))))))))))))))))))))))))))


def pow7_16 {R : Type*} [CommRing R] (z : R) : R := (0 + z * (3 + z * (106 + z * (95 + z * (136 + z * (6 + z * (95 + z * (130 + z * (13 + z * (63 + z * (21 + z * (89 + z * (120 + z * (66 + z * (8 + z * (107 + z * (95 + z * (73 + z * (35 + z * 55)))))))))))))))))))

def pow7_16_q {R : Type*} [CommRing R] (z : R) : R := (103 + z * (94 + z * (88 + z * (95 + z * (34 + z * (108 + z * (21 + z * (109 + z * (2 + z * (0 + z * (126 + z * (62 + z * (33 + z * (89 + z * (36 + z * (36 + z * (12 + z * (110 + z * 55))))))))))))))))))

def pow7_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (19 + z * ((-93) + z * ((-40) + z * ((-188) + z * ((-65) + z * ((-135) + z * ((-14) + z * ((-127) + z * ((-102) + z * ((-29) + z * ((-209) + z * ((-45) + z * ((-207) + z * ((-4) + z * ((-281) + z * ((-86) + z * ((-178) + z * ((-55) + z * ((-94) + z * ((-112) + z * ((-197) + z * ((-134) + z * (126 + z * ((-124) + z * (27 + z * ((-87) + z * ((-96) + z * ((-3) + z * ((-2) + z * ((-29) + z * (46 + z * ((-70) + z * (5 + z * ((-42) + z * (59 + z * (62 + z * ((-33) + z * (0 + z * 30))))))))))))))))))))))))))))))))))))))


def pow7_17 {R : Type*} [CommRing R] (z : R) : R := (5 + z * (92 + z * (3 + z * (136 + z * (57 + z * (82 + z * (71 + z * (34 + z * (85 + z * (46 + z * (36 + z * (102 + z * (33 + z * (132 + z * (96 + z * (69 + z * (8 + z * (75 + z * (1 + z * 5)))))))))))))))))))

def pow7_17_q {R : Type*} [CommRing R] (z : R) : R := (86 + z * (87 + z * (86 + z * (10 + z * (120 + z * (106 + z * (51 + z * (126 + z * (40 + z * (130 + z * (114 + z * (62 + z * (55 + z * (39 + z * (87 + z * (40 + z * (109 + z * (60 + z * 11))))))))))))))))))

def pow7_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-65) + z * ((-141) + z * ((-186) + z * ((-139) + z * ((-199) + z * ((-244) + z * ((-300) + z * ((-233) + z * ((-225) + z * ((-237) + z * ((-418) + z * ((-308) + z * ((-250) + z * ((-228) + z * ((-447) + z * ((-423) + z * ((-314) + z * ((-418) + z * ((-278) + z * ((-400) + z * ((-282) + z * ((-94) + z * ((-46) + z * ((-273) + z * ((-126) + z * ((-204) + z * ((-194) + z * ((-148) + z * ((-90) + z * ((-132) + z * ((-74) + z * ((-4) + z * ((-45) + z * (12 + z * (19 + z * ((-34) + z * ((-8) + z * (23 + z * 11))))))))))))))))))))))))))))))))))))))


def pow7_34 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (107 + z * (40 + z * (56 + z * (34 + z * (22 + z * (135 + z * (0 + z * (20 + z * (34 + z * (120 + z * (13 + z * (119 + z * (66 + z * (3 + z * (44 + z * (115 + z * (33 + z * (76 + z * 2)))))))))))))))))))

def pow7_34_q {R : Type*} [CommRing R] (z : R) : R := (99 + z * (131 + z * (58 + z * (116 + z * (82 + z * (57 + z * (98 + z * (9 + z * (40 + z * (8 + z * (79 + z * (14 + z * (3 + z * (102 + z * (0 + z * (34 + z * (85 + z * (7 + z * 25))))))))))))))))))

def pow7_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-75) + z * ((-180) + z * ((-187) + z * ((-337) + z * ((-234) + z * ((-320) + z * ((-179) + z * ((-219) + z * ((-190) + z * ((-119) + z * ((-300) + z * ((-157) + z * ((-74) + z * ((-296) + z * ((-15) + z * ((-127) + z * ((-75) + z * ((-63) + z * (39 + z * ((-229) + z * ((-62) + z * ((-24) + z * ((-24) + z * ((-58) + z * (28 + z * (30 + z * (9 + z * (118 + z * (103 + z * ((-119) + z * (110 + z * ((-71) + z * ((-94) + z * ((-31) + z * ((-69) + z * ((-82) + z * ((-20) + z * ((-23) + z * 0))))))))))))))))))))))))))))))))))))))


def pow7_68 {R : Type*} [CommRing R] (z : R) : R := (124 + z * (89 + z * (12 + z * (60 + z * (68 + z * (22 + z * (61 + z * (89 + z * (122 + z * (32 + z * (81 + z * (90 + z * (12 + z * (87 + z * (25 + z * (92 + z * (73 + z * (135 + z * (19 + z * 66)))))))))))))))))))

def pow7_68_q {R : Type*} [CommRing R] (z : R) : R := (115 + z * (65 + z * (133 + z * (106 + z * (18 + z * (34 + z * (57 + z * (65 + z * (43 + z * (23 + z * (88 + z * (10 + z * (134 + z * (76 + z * (123 + z * (30 + z * (15 + z * (70 + z * 4))))))))))))))))))

def pow7_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-66) + z * ((-66) + z * ((-147) + z * ((-259) + z * ((-254) + z * ((-247) + z * ((-171) + z * ((-109) + z * ((-247) + z * ((-268) + z * ((-322) + z * ((-226) + z * ((-225) + z * ((-282) + z * ((-369) + z * ((-483) + z * ((-300) + z * ((-362) + z * ((-211) + z * ((-249) + z * ((-347) + z * ((-367) + z * ((-63) + z * ((-239) + z * ((-92) + z * ((-176) + z * ((-131) + z * ((-186) + z * (28 + z * ((-90) + z * ((-122) + z * ((-97) + z * ((-99) + z * ((-94) + z * (92 + z * ((-26) + z * ((-25) + z * ((-2) + z * 0))))))))))))))))))))))))))))))))))))))


def pow7_69 {R : Type*} [CommRing R] (z : R) : R := (107 + z * (90 + z * (125 + z * (80 + z * (53 + z * (20 + z * (54 + z * (40 + z * (43 + z * (47 + z * (134 + z * (69 + z * (110 + z * (103 + z * (135 + z * (43 + z * (62 + z * (71 + z * (55 + z * 74)))))))))))))))))))

def pow7_69_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (20 + z * (93 + z * (84 + z * (2 + z * (134 + z * (80 + z * (93 + z * (65 + z * (38 + z * (73 + z * (4 + z * (60 + z * (29 + z * (107 + z * (101 + z * (61 + z * (123 + z * 41))))))))))))))))))

def pow7_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-58) + z * ((-8) + z * ((-108) + z * ((-228) + z * ((-196) + z * ((-127) + z * ((-164) + z * ((-166) + z * ((-192) + z * ((-183) + z * ((-277) + z * ((-168) + z * ((-174) + z * ((-153) + z * ((-182) + z * ((-316) + z * ((-273) + z * ((-173) + z * ((-379) + z * ((-352) + z * ((-180) + z * ((-353) + z * (5 + z * ((-152) + z * ((-61) + z * ((-184) + z * ((-33) + z * ((-176) + z * ((-90) + z * ((-79) + z * ((-147) + z * ((-83) + z * ((-53) + z * ((-93) + z * ((-21) + z * ((-10) + z * ((-78) + z * ((-3) + z * 13))))))))))))))))))))))))))))))))))))))


def pow7_138 {R : Type*} [CommRing R] (z : R) : R := (50 + z * (102 + z * (112 + z * (11 + z * (42 + z * (65 + z * (49 + z * (48 + z * (115 + z * (33 + z * (65 + z * (95 + z * (37 + z * (64 + z * (31 + z * (77 + z * (28 + z * (116 + z * (133 + z * 8)))))))))))))))))))

def pow7_138_q {R : Type*} [CommRing R] (z : R) : R := (94 + z * (60 + z * (87 + z * (23 + z * (81 + z * (45 + z * (57 + z * (67 + z * (89 + z * (22 + z * (0 + z * (67 + z * (17 + z * (61 + z * (35 + z * (78 + z * (7 + z * (127 + z * 55))))))))))))))))))

def pow7_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (11 + z * (10 + z * (47 + z * (48 + z * (7 + z * ((-41) + z * ((-46) + z * ((-107) + z * ((-149) + z * ((-162) + z * ((-20) + z * (7 + z * (205 + z * (199 + z * (274 + z * (114 + z * (184 + z * (41 + z * (4 + z * (92 + z * (103 + z * (48 + z * (160 + z * (141 + z * (175 + z * (184 + z * (170 + z * (134 + z * (274 + z * (280 + z * (111 + z * (140 + z * (96 + z * (10 + z * (8 + z * (22 + z * ((-60) + z * (7 + z * 39))))))))))))))))))))))))))))))))))))))


def pow7_139 {R : Type*} [CommRing R] (z : R) : R := (121 + z * (104 + z * (88 + z * (36 + z * (41 + z * (102 + z * (131 + z * (65 + z * (132 + z * (82 + z * (40 + z * (63 + z * (28 + z * (122 + z * (71 + z * (6 + z * (113 + z * (125 + z * (130 + z * 57)))))))))))))))))))

def pow7_139_q {R : Type*} [CommRing R] (z : R) : R := (96 + z * (79 + z * (27 + z * (31 + z * (6 + z * (68 + z * (69 + z * (118 + z * (105 + z * (110 + z * (99 + z * (36 + z * (84 + z * (40 + z * (37 + z * (38 + z * (109 + z * (52 + z * 85))))))))))))))))))

def pow7_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-59) + z * ((-79) + z * ((-61) + z * ((-102) + z * ((-155) + z * ((-88) + z * ((-19) + z * ((-44) + z * ((-165) + z * ((-235) + z * ((-363) + z * ((-234) + z * ((-256) + z * ((-238) + z * ((-253) + z * ((-237) + z * ((-329) + z * ((-197) + z * ((-236) + z * ((-335) + z * ((-273) + z * ((-297) + z * ((-150) + z * ((-113) + z * ((-49) + z * ((-256) + z * ((-218) + z * ((-127) + z * ((-211) + z * ((-91) + z * ((-82) + z * ((-113) + z * ((-57) + z * (32 + z * ((-4) + z * ((-12) + z * ((-20) + z * ((-48) + z * 1))))))))))))))))))))))))))))))))))))))


abbrev u7 {R : Type*} [CommRing R] (z : R) : R := pow7_139 z


def pow8_2 {R : Type*} [CommRing R] (z : R) : R := (49 + z * (22 + z * (135 + z * (107 + z * (117 + z * (129 + z * (71 + z * (42 + z * (102 + z * (136 + z * (79 + z * (21 + z * (98 + z * (126 + z * (111 + z * (104 + z * (41 + z * (62 + z * (47 + z * 10)))))))))))))))))))

def pow8_2_q {R : Type*} [CommRing R] (z : R) : R := (135 + z * (31 + z * (35 + z * (54 + z * (37 + z * (40 + z * (109 + z * (110 + z * (138 + z * (6 + z * (68 + z * (66 + z * (86 + z * (87 + z * (86 + z * (111 + z * (2 + z * (102 + z * 52))))))))))))))))))

def pow8_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (3 + z * (39 + z * (55 + z * ((-34) + z * ((-62) + z * (74 + z * (156 + z * (71 + z * (70 + z * (8 + z * ((-59) + z * (52 + z * (0 + z * (60 + z * (114 + z * ((-159) + z * ((-122) + z * (72 + z * (175 + z * (218 + z * (54 + z * ((-12) + z * (158 + z * (138 + z * (203 + z * (142 + z * (70 + z * (32 + z * ((-50) + z * (82 + z * (63 + z * (60 + z * (103 + z * ((-7) + z * (181 + z * (249 + z * (92 + z * (58 + z * 23))))))))))))))))))))))))))))))))))))))


def pow8_4 {R : Type*} [CommRing R] (z : R) : R := (55 + z * (17 + z * (61 + z * (92 + z * (21 + z * (62 + z * (24 + z * (133 + z * (87 + z * (87 + z * (14 + z * (6 + z * (80 + z * (91 + z * (119 + z * (117 + z * (16 + z * (119 + z * (118 + z * 19)))))))))))))))))))

def pow8_4_q {R : Type*} [CommRing R] (z : R) : R := (70 + z * (37 + z * (9 + z * (21 + z * (50 + z * (74 + z * (16 + z * (4 + z * (41 + z * (95 + z * (67 + z * (50 + z * (137 + z * (80 + z * (107 + z * (59 + z * (121 + z * (94 + z * 100))))))))))))))))))

def pow8_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-36) + z * ((-74) + z * ((-4) + z * ((-6) + z * (93 + z * (158 + z * (216 + z * (280 + z * (292 + z * (243 + z * (257 + z * (310 + z * (266 + z * (175 + z * (231 + z * (257 + z * (223 + z * (395 + z * (242 + z * (115 + z * (141 + z * (176 + z * (189 + z * (127 + z * ((-10) + z * ((-63) + z * ((-3) + z * ((-52) + z * ((-124) + z * ((-64) + z * ((-112) + z * ((-185) + z * ((-158) + z * ((-162) + z * ((-157) + z * ((-133) + z * ((-136) + z * ((-86) + z * 0))))))))))))))))))))))))))))))))))))))


def pow8_8 {R : Type*} [CommRing R] (z : R) : R := (114 + z * (31 + z * (127 + z * (92 + z * (92 + z * (14 + z * (94 + z * (54 + z * (18 + z * (80 + z * (18 + z * (83 + z * (131 + z * (123 + z * (122 + z * (65 + z * (54 + z * (47 + z * (109 + z * 94)))))))))))))))))))

def pow8_8_q {R : Type*} [CommRing R] (z : R) : R := (82 + z * (48 + z * (59 + z * (138 + z * (77 + z * (87 + z * (12 + z * (49 + z * (16 + z * (60 + z * (103 + z * (36 + z * (71 + z * (49 + z * (23 + z * (128 + z * (125 + z * (115 + z * 83))))))))))))))))))

def pow8_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-41) + z * ((-95) + z * ((-111) + z * ((-190) + z * ((-277) + z * ((-241) + z * ((-262) + z * ((-194) + z * ((-136) + z * ((-127) + z * ((-165) + z * ((-234) + z * ((-224) + z * ((-392) + z * ((-138) + z * ((-101) + z * ((-242) + z * ((-195) + z * ((-406) + z * ((-444) + z * ((-104) + z * (10 + z * (16 + z * ((-103) + z * ((-11) + z * ((-65) + z * (0 + z * (68 + z * ((-157) + z * ((-22) + z * (52 + z * ((-7) + z * (154 + z * ((-6) + z * ((-118) + z * (6 + z * ((-35) + z * ((-45) + z * 2))))))))))))))))))))))))))))))))))))))


def pow8_16 {R : Type*} [CommRing R] (z : R) : R := (104 + z * (88 + z * (123 + z * (69 + z * (24 + z * (29 + z * (86 + z * (65 + z * (53 + z * (103 + z * (68 + z * (79 + z * (3 + z * (133 + z * (1 + z * (38 + z * (68 + z * (118 + z * (119 + z * 133)))))))))))))))))))

def pow8_16_q {R : Type*} [CommRing R] (z : R) : R := (46 + z * (17 + z * (57 + z * (57 + z * (56 + z * (118 + z * (8 + z * (58 + z * (40 + z * (75 + z * (124 + z * (125 + z * (35 + z * (134 + z * (103 + z * (54 + z * (71 + z * (94 + z * 79))))))))))))))))))

def pow8_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (58 + z * ((-3) + z * (115 + z * (55 + z * (112 + z * ((-39) + z * (109 + z * ((-26) + z * ((-12) + z * (19 + z * ((-140) + z * ((-132) + z * ((-98) + z * ((-70) + z * ((-44) + z * (55 + z * (65 + z * ((-81) + z * ((-37) + z * ((-48) + z * ((-74) + z * ((-3) + z * (24 + z * ((-146) + z * ((-76) + z * (137 + z * ((-52) + z * (5 + z * (32 + z * ((-61) + z * (127 + z * (168 + z * (71 + z * (39 + z * (20 + z * (12 + z * (4 + z * (74 + z * 63))))))))))))))))))))))))))))))))))))))


def pow8_17 {R : Type*} [CommRing R] (z : R) : R := (39 + z * (119 + z * (26 + z * (19 + z * (100 + z * (69 + z * (70 + z * (121 + z * (10 + z * (12 + z * (11 + z * (18 + z * (114 + z * (12 + z * (42 + z * (2 + z * (27 + z * (119 + z * (106 + z * 43)))))))))))))))))))

def pow8_17_q {R : Type*} [CommRing R] (z : R) : R := (93 + z * (127 + z * (133 + z * (64 + z * (107 + z * (57 + z * (126 + z * (112 + z * (46 + z * (111 + z * (58 + z * (54 + z * (101 + z * (0 + z * (70 + z * (66 + z * (83 + z * (17 + z * 75))))))))))))))))))

def pow8_17_mul_t {R : Type*} [CommRing R] (z : R) : R := (20 + z * ((-24) + z * ((-57) + z * ((-133) + z * ((-247) + z * ((-228) + z * ((-149) + z * ((-147) + z * ((-102) + z * ((-182) + z * ((-265) + z * ((-205) + z * ((-274) + z * ((-153) + z * ((-190) + z * ((-217) + z * ((-282) + z * ((-120) + z * (11 + z * (43 + z * ((-109) + z * ((-57) + z * ((-97) + z * (72 + z * (154 + z * ((-3) + z * (195 + z * (166 + z * ((-19) + z * (143 + z * (86 + z * (73 + z * (164 + z * (91 + z * (103 + z * (264 + z * (208 + z * (104 + z * 54))))))))))))))))))))))))))))))))))))))


def pow8_34 {R : Type*} [CommRing R] (z : R) : R := (72 + z * (98 + z * (89 + z * (122 + z * (26 + z * (43 + z * (35 + z * (76 + z * (54 + z * (31 + z * (86 + z * (70 + z * (128 + z * (5 + z * (117 + z * (109 + z * (123 + z * (116 + z * (103 + z * 32)))))))))))))))))))

def pow8_34_q {R : Type*} [CommRing R] (z : R) : R := (125 + z * (113 + z * (44 + z * (113 + z * (138 + z * (62 + z * (100 + z * (67 + z * (137 + z * (87 + z * (59 + z * (0 + z * (9 + z * (95 + z * (2 + z * (65 + z * (85 + z * (126 + z * 42))))))))))))))))))

def pow8_34_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-84) + z * ((-129) + z * ((-129) + z * ((-290) + z * ((-355) + z * ((-221) + z * ((-276) + z * ((-295) + z * ((-272) + z * ((-478) + z * ((-561) + z * ((-401) + z * ((-341) + z * ((-381) + z * ((-454) + z * ((-505) + z * ((-618) + z * ((-614) + z * ((-417) + z * ((-486) + z * ((-539) + z * ((-337) + z * ((-371) + z * ((-272) + z * ((-75) + z * ((-234) + z * ((-349) + z * ((-371) + z * ((-232) + z * ((-47) + z * (8 + z * ((-117) + z * ((-178) + z * ((-107) + z * ((-13) + z * (27 + z * (7 + z * (26 + z * 13))))))))))))))))))))))))))))))))))))))


def pow8_68 {R : Type*} [CommRing R] (z : R) : R := (53 + z * (93 + z * (37 + z * (136 + z * (101 + z * (45 + z * (94 + z * (86 + z * (9 + z * (89 + z * (54 + z * (98 + z * (11 + z * (102 + z * (70 + z * (60 + z * (124 + z * (56 + z * (135 + z * 137)))))))))))))))))))

def pow8_68_q {R : Type*} [CommRing R] (z : R) : R := (123 + z * (74 + z * (133 + z * (13 + z * (43 + z * (81 + z * (19 + z * (46 + z * (44 + z * (127 + z * (74 + z * (114 + z * (54 + z * (10 + z * (33 + z * (97 + z * (52 + z * (64 + z * 51))))))))))))))))))

def pow8_68_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-56) + z * ((-63) + z * ((-115) + z * ((-59) + z * ((-75) + z * ((-95) + z * ((-69) + z * ((-81) + z * ((-73) + z * ((-213) + z * ((-209) + z * ((-244) + z * ((-168) + z * ((-116) + z * ((-71) + z * ((-48) + z * ((-37) + z * (185 + z * (24 + z * (89 + z * (4 + z * (22 + z * (153 + z * (54 + z * (53 + z * (19 + z * (239 + z * (107 + z * (187 + z * (251 + z * (194 + z * (208 + z * (327 + z * (233 + z * (159 + z * (133 + z * (33 + z * (0 + z * 7))))))))))))))))))))))))))))))))))))))


def pow8_69 {R : Type*} [CommRing R] (z : R) : R := (130 + z * (76 + z * (3 + z * (88 + z * (8 + z * (46 + z * (131 + z * (17 + z * (90 + z * (13 + z * (42 + z * (30 + z * (106 + z * (87 + z * (104 + z * (120 + z * (45 + z * (5 + z * (136 + z * 63)))))))))))))))))))

def pow8_69_q {R : Type*} [CommRing R] (z : R) : R := (130 + z * (86 + z * (127 + z * (99 + z * (102 + z * (100 + z * (111 + z * (43 + z * (20 + z * (72 + z * (116 + z * (75 + z * (44 + z * (84 + z * (41 + z * (105 + z * (31 + z * (65 + z * 25))))))))))))))))))

def pow8_69_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-53) + z * ((-59) + z * ((-153) + z * ((-169) + z * ((-209) + z * ((-205) + z * ((-185) + z * ((-155) + z * ((-121) + z * ((-74) + z * ((-223) + z * ((-108) + z * ((-157) + z * ((-276) + z * ((-173) + z * ((-231) + z * ((-179) + z * ((-15) + z * ((-73) + z * (31 + z * (92 + z * (92 + z * (146 + z * (127 + z * (207 + z * (99 + z * (139 + z * (270 + z * (43 + z * (108 + z * (120 + z * (131 + z * (268 + z * (132 + z * (166 + z * (259 + z * (194 + z * (160 + z * 56))))))))))))))))))))))))))))))))))))))


def pow8_138 {R : Type*} [CommRing R] (z : R) : R := (137 + z * (27 + z * (75 + z * (37 + z * (65 + z * (16 + z * (138 + z * (73 + z * (134 + z * (128 + z * (80 + z * (59 + z * (1 + z * (34 + z * (49 + z * (58 + z * (117 + z * (133 + z * (79 + z * 60)))))))))))))))))))

def pow8_138_q {R : Type*} [CommRing R] (z : R) : R := (18 + z * (77 + z * (66 + z * (19 + z * (51 + z * (24 + z * (36 + z * (116 + z * (106 + z * (130 + z * (73 + z * (48 + z * (93 + z * (54 + z * (43 + z * (99 + z * (29 + z * (52 + z * 77))))))))))))))))))

def pow8_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (107 + z * (68 + z * ((-87) + z * (9 + z * ((-91) + z * ((-110) + z * (157 + z * ((-74) + z * ((-108) + z * ((-172) + z * ((-411) + z * ((-298) + z * ((-182) + z * ((-129) + z * ((-80) + z * ((-100) + z * ((-203) + z * ((-417) + z * ((-2) + z * ((-94) + z * ((-198) + z * ((-44) + z * ((-222) + z * ((-196) + z * (32 + z * ((-180) + z * ((-30) + z * ((-61) + z * ((-98) + z * (66 + z * (120 + z * (31 + z * (134 + z * (127 + z * (20 + z * ((-15) + z * (33 + z * (52 + z * 28))))))))))))))))))))))))))))))))))))))


def pow8_139 {R : Type*} [CommRing R] (z : R) : R := (123 + z * (122 + z * (58 + z * (6 + z * (73 + z * (55 + z * (45 + z * (68 + z * (87 + z * (137 + z * (102 + z * (39 + z * (90 + z * (70 + z * (61 + z * (46 + z * (83 + z * (124 + z * (34 + z * 84)))))))))))))))))))

def pow8_139_q {R : Type*} [CommRing R] (z : R) : R := (23 + z * (82 + z * (28 + z * (83 + z * (128 + z * (34 + z * (114 + z * (82 + z * (75 + z * (80 + z * (130 + z * (116 + z * (110 + z * (15 + z * (22 + z * (48 + z * (67 + z * (22 + z * 84))))))))))))))))))

def pow8_139_mul_t {R : Type*} [CommRing R] (z : R) : R := (101 + z * (43 + z * (58 + z * ((-42) + z * ((-112) + z * ((-97) + z * ((-11) + z * ((-80) + z * (65 + z * (38 + z * ((-86) + z * ((-138) + z * ((-210) + z * ((-189) + z * ((-120) + z * ((-28) + z * (16 + z * (107 + z * (86 + z * ((-75) + z * ((-138) + z * ((-33) + z * (33 + z * (130 + z * (200 + z * (80 + z * (98 + z * (119 + z * ((-28) + z * ((-8) + z * (11 + z * ((-6) + z * (170 + z * (194 + z * (156 + z * (214 + z * (100 + z * (11 + z * 24))))))))))))))))))))))))))))))))))))))


abbrev u8 {R : Type*} [CommRing R] (z : R) : R := pow8_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Powers05
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139
def pow9_2 {R : Type*} [CommRing R] (z : R) : R := (73 + z * (45 + z * (77 + z * (120 + z * (43 + z * (71 + z * (112 + z * (119 + z * (118 + z * (35 + z * (137 + z * (58 + z * (86 + z * (110 + z * (56 + z * (137 + z * (97 + z * (6 + z * (76 + z * 50)))))))))))))))))))

def pow9_2_q {R : Type*} [CommRing R] (z : R) : R := (105 + z * (80 + z * (6 + z * (120 + z * (63 + z * (67 + z * (94 + z * (27 + z * (56 + z * (2 + z * (45 + z * (52 + z * (83 + z * (33 + z * (97 + z * (79 + z * (98 + z * (67 + z * 106))))))))))))))))))

def pow9_2_mul_t {R : Type*} [CommRing R] (z : R) : R := (29 + z * (63 + z * (40 + z * ((-156) + z * ((-153) + z * ((-84) + z * ((-129) + z * ((-154) + z * ((-52) + z * (98 + z * (99 + z * (61 + z * (24 + z * ((-16) + z * ((-1) + z * ((-101) + z * ((-126) + z * (164 + z * (25 + z * ((-97) + z * ((-17) + z * ((-8) + z * ((-48) + z * (98 + z * (26 + z * (75 + z * (174 + z * (70 + z * (83 + z * (93 + z * ((-66) + z * ((-50) + z * ((-25) + z * ((-27) + z * ((-27) + z * (21 + z * (18 + z * ((-57) + z * 50))))))))))))))))))))))))))))))))))))))


def pow9_4 {R : Type*} [CommRing R] (z : R) : R := (87 + z * (104 + z * (2 + z * (138 + z * (117 + z * (20 + z * (2 + z * (120 + z * (57 + z * (10 + z * (38 + z * (10 + z * (59 + z * (73 + z * (44 + z * (101 + z * (117 + z * (92 + z * (81 + z * 38)))))))))))))))))))

def pow9_4_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (30 + z * (27 + z * (70 + z * (131 + z * (138 + z * (67 + z * (132 + z * (2 + z * (72 + z * (133 + z * (59 + z * (21 + z * (98 + z * (120 + z * (126 + z * (5 + z * (72 + z * 137))))))))))))))))))

def pow9_4_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-62) + z * ((-92) + z * ((-70) + z * ((-54) + z * ((-152) + z * ((-136) + z * ((-117) + z * ((-204) + z * ((-72) + z * ((-73) + z * ((-31) + z * ((-13) + z * (29 + z * ((-1) + z * ((-103) + z * (28 + z * (51 + z * ((-17) + z * (67 + z * ((-117) + z * ((-20) + z * (183 + z * (87 + z * ((-12) + z * ((-5) + z * (79 + z * (106 + z * ((-17) + z * ((-24) + z * (3 + z * (4 + z * (20 + z * ((-66) + z * ((-153) + z * ((-30) + z * (18 + z * ((-121) + z * ((-72) + z * 17))))))))))))))))))))))))))))))))))))))


def pow9_8 {R : Type*} [CommRing R] (z : R) : R := (118 + z * (38 + z * (115 + z * (109 + z * (64 + z * (70 + z * (13 + z * (6 + z * (72 + z * (55 + z * (135 + z * (85 + z * (87 + z * (60 + z * (123 + z * (30 + z * (125 + z * (37 + z * (123 + z * 4)))))))))))))))))))

def pow9_8_q {R : Type*} [CommRing R] (z : R) : R := (112 + z * (67 + z * (86 + z * (21 + z * (11 + z * (45 + z * (4 + z * (0 + z * (128 + z * (117 + z * (10 + z * (92 + z * (92 + z * (96 + z * (124 + z * (71 + z * (7 + z * (78 + z * 54))))))))))))))))))

def pow9_8_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-31) + z * ((-19) + z * ((-145) + z * ((-83) + z * (97 + z * ((-27) + z * ((-26) + z * (204 + z * (101 + z * ((-293) + z * ((-165) + z * ((-119) + z * ((-308) + z * ((-282) + z * ((-265) + z * ((-320) + z * ((-132) + z * ((-110) + z * ((-250) + z * (0 + z * (47 + z * ((-213) + z * ((-71) + z * ((-84) + z * ((-266) + z * ((-76) + z * ((-140) + z * ((-395) + z * ((-162) + z * ((-7) + z * ((-72) + z * (43 + z * (65 + z * (30 + z * (136 + z * (107 + z * ((-14) + z * ((-6) + z * 10))))))))))))))))))))))))))))))))))))))


def pow9_16 {R : Type*} [CommRing R] (z : R) : R := (37 + z * (89 + z * (42 + z * (101 + z * (79 + z * (11 + z * (91 + z * (58 + z * (137 + z * (115 + z * (48 + z * (120 + z * (93 + z * (90 + z * (107 + z * (61 + z * (29 + z * (20 + z * (100 + z * 47)))))))))))))))))))

def pow9_16_q {R : Type*} [CommRing R] (z : R) : R := (29 + z * (125 + z * (55 + z * (45 + z * (80 + z * (125 + z * (95 + z * (126 + z * (136 + z * (71 + z * (113 + z * (6 + z * (35 + z * (92 + z * (136 + z * (107 + z * (4 + z * (48 + z * 16))))))))))))))))))

def pow9_16_mul_t {R : Type*} [CommRing R] (z : R) : R := (78 + z * ((-56) + z * (28 + z * (25 + z * ((-28) + z * ((-30) + z * ((-136) + z * ((-245) + z * ((-313) + z * ((-413) + z * ((-286) + z * ((-273) + z * ((-43) + z * ((-33) + z * ((-127) + z * ((-296) + z * ((-149) + z * ((-376) + z * ((-23) + z * ((-120) + z * ((-112) + z * ((-54) + z * ((-111) + z * ((-296) + z * ((-135) + z * ((-112) + z * (90 + z * (11 + z * (157 + z * (29 + z * (154 + z * (4 + z * (124 + z * ((-128) + z * (117 + z * (33 + z * (55 + z * ((-8) + z * 0))))))))))))))))))))))))))))))))))))))


def pow9_17 {R : Type*} [CommRing R] (z : R) : R := (81 + z * (56 + z * (36 + z * (60 + z * (15 + z * (77 + z * (75 + z * (21 + z * (33 + z * (95 + z * (113 + z * (45 + z * (76 + z * (98 + z * (0 + z * (104 + z * (131 + z * (39 + z * (72 + z * 120)))))))))))))))))))

def pow9_17_q {R : Type*} [CommRing R] (z : R) : R := (122 + z * (46 + z * (23 + z * (24 + z * (73 + z * (125 + z * (0 + z * (120 + z * (34 + z * (99 + z * (130 + z * (23 + z * (122 + z * (64 + z * (105 + z * (100 + z * (47 + z * (50 + z * 56))))))))))))))))))

def pow9_17_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-60) + z * ((-31) + z * ((-37) + z * ((-31) + z * ((-37) + z * ((-91) + z * ((-76) + z * ((-126) + z * ((-44) + z * ((-52) + z * ((-107) + z * ((-45) + z * ((-9) + z * ((-78) + z * ((-157) + z * ((-113) + z * ((-132) + z * ((-114) + z * ((-62) + z * ((-73) + z * (13 + z * (53 + z * (12 + z * ((-61) + z * ((-4) + z * ((-1) + z * (1 + z * (81 + z * ((-49) + z * ((-21) + z * (17 + z * ((-37) + z * ((-5) + z * ((-77) + z * ((-37) + z * (59 + z * ((-9) + z * (20 + z * 28))))))))))))))))))))))))))))))))))))))


def pow9_34 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (102 + z * (62 + z * (20 + z * (37 + z * (26 + z * (51 + z * (71 + z * (124 + z * (4 + z * (113 + z * (89 + z * (34 + z * (60 + z * (138 + z * (113 + z * (54 + z * (118 + z * (69 + z * 124)))))))))))))))))))

def pow9_34_q {R : Type*} [CommRing R] (z : R) : R := (56 + z * (117 + z * (4 + z * (25 + z * (60 + z * (20 + z * (79 + z * (128 + z * (107 + z * (134 + z * (64 + z * (16 + z * (125 + z * (125 + z * (48 + z * (55 + z * (64 + z * (123 + z * 83))))))))))))))))))

def pow9_34_mul_t {R : Type*} [CommRing R] (z : R) : R := (4 + z * ((-73) + z * ((-92) + z * ((-82) + z * ((-151) + z * ((-70) + z * ((-30) + z * ((-196) + z * ((-274) + z * ((-314) + z * ((-342) + z * ((-291) + z * ((-217) + z * ((-298) + z * ((-407) + z * ((-235) + z * ((-325) + z * ((-465) + z * ((-220) + z * ((-286) + z * ((-343) + z * ((-110) + z * ((-208) + z * ((-245) + z * ((-47) + z * ((-83) + z * ((-195) + z * ((-190) + z * (45 + z * (131 + z * ((-55) + z * (6 + z * (33 + z * ((-60) + z * (159 + z * (117 + z * ((-70) + z * (47 + z * 103))))))))))))))))))))))))))))))))))))))


def pow9_68 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (128 + z * (101 + z * (7 + z * (104 + z * (29 + z * (95 + z * (37 + z * (71 + z * (20 + z * (0 + z * (44 + z * (16 + z * (123 + z * (92 + z * (65 + z * (133 + z * (55 + z * (30 + z * 8)))))))))))))))))))

def pow9_68_q {R : Type*} [CommRing R] (z : R) : R := (2 + z * (5 + z * (129 + z * (101 + z * (62 + z * (125 + z * (64 + z * (120 + z * (117 + z * (74 + z * (20 + z * (114 + z * (28 + z * (36 + z * (105 + z * (41 + z * (101 + z * (127 + z * 86))))))))))))))))))

def pow9_68_mul_t {R : Type*} [CommRing R] (z : R) : R := (110 + z * (177 + z * (82 + z * ((-69) + z * ((-135) + z * ((-248) + z * ((-248) + z * ((-203) + z * ((-108) + z * ((-274) + z * ((-171) + z * ((-223) + z * ((-273) + z * ((-228) + z * ((-72) + z * ((-87) + z * ((-121) + z * ((-235) + z * ((-229) + z * ((-27) + z * ((-225) + z * ((-269) + z * ((-65) + z * ((-98) + z * ((-102) + z * (191 + z * ((-40) + z * (41 + z * (182 + z * (257 + z * (72 + z * (157 + z * (145 + z * (162 + z * (171 + z * (27 + z * (64 + z * (43 + z * 110))))))))))))))))))))))))))))))))))))))


def pow9_69 {R : Type*} [CommRing R] (z : R) : R := (125 + z * (64 + z * (125 + z * (82 + z * (16 + z * (100 + z * (42 + z * (46 + z * (76 + z * (58 + z * (18 + z * (81 + z * (57 + z * (127 + z * (130 + z * (132 + z * (22 + z * (121 + z * (96 + z * 22)))))))))))))))))))

def pow9_69_q {R : Type*} [CommRing R] (z : R) : R := (132 + z * (30 + z * (82 + z * (1 + z * (1 + z * (24 + z * (85 + z * (80 + z * (102 + z * (63 + z * (104 + z * (68 + z * (63 + z * (58 + z * (118 + z * (127 + z * (72 + z * (37 + z * 116))))))))))))))))))

def pow9_69_mul_t {R : Type*} [CommRing R] (z : R) : R := (10 + z * (84 + z * (46 + z * ((-72) + z * (4 + z * (79 + z * (91 + z * (12 + z * (0 + z * ((-74) + z * ((-149) + z * ((-123) + z * ((-115) + z * ((-41) + z * ((-17) + z * ((-216) + z * ((-202) + z * ((-55) + z * ((-247) + z * ((-297) + z * ((-204) + z * ((-195) + z * ((-160) + z * ((-59) + z * ((-226) + z * ((-150) + z * ((-191) + z * ((-221) + z * ((-226) + z * ((-151) + z * ((-58) + z * ((-128) + z * ((-3) + z * ((-71) + z * ((-126) + z * (31 + z * ((-72) + z * ((-87) + z * 4))))))))))))))))))))))))))))))))))))))


def pow9_138 {R : Type*} [CommRing R] (z : R) : R := (2 + z * (18 + z * (82 + z * (3 + z * (30 + z * (87 + z * (72 + z * (18 + z * (114 + z * (78 + z * (68 + z * (73 + z * (117 + z * (20 + z * (51 + z * (16 + z * (18 + z * (0 + z * (44 + z * 102)))))))))))))))))))

def pow9_138_q {R : Type*} [CommRing R] (z : R) : R := (27 + z * (52 + z * (5 + z * (5 + z * (8 + z * (138 + z * (44 + z * (19 + z * (62 + z * (109 + z * (33 + z * (67 + z * (63 + z * (119 + z * (66 + z * (7 + z * (5 + z * (96 + z * 67))))))))))))))))))

def pow9_138_mul_t {R : Type*} [CommRing R] (z : R) : R := (92 + z * (52 + z * (180 + z * (182 + z * (131 + z * (172 + z * (49 + z * (97 + z * (86 + z * ((-34) + z * (8 + z * (46 + z * ((-44) + z * (98 + z * (119 + z * (188 + z * (252 + z * (332 + z * (184 + z * (193 + z * (232 + z * ((-32) + z * (135 + z * (79 + z * ((-40) + z * (117 + z * (189 + z * (8 + z * (189 + z * (236 + z * (216 + z * (204 + z * (201 + z * (72 + z * (111 + z * (99 + z * ((-33) + z * ((-32) + z * 3))))))))))))))))))))))))))))))))))))))


def pow9_139 {R : Type*} [CommRing R] (z : R) : R := (94 + z * (83 + z * (71 + z * (34 + z * (63 + z * (64 + z * (52 + z * (63 + z * (11 + z * (126 + z * (79 + z * (8 + z * (46 + z * (113 + z * (77 + z * (134 + z * (121 + z * (128 + z * (31 + z * 60)))))))))))))))))))

def pow9_139_q {R : Type*} [CommRing R] (z : R) : R := (110 + z * (100 + z * (45 + z * (110 + z * (6 + z * (105 + z * (79 + z * (11 + z * (33 + z * (129 + z * (17 + z * (41 + z * (33 + z * (48 + z * (92 + z * (2 + z * (119 + z * (81 + z * 89))))))))))))))))))

def pow9_139_mul_t {R : Type*} [CommRing R] (z : R) : R := ((-82) + z * ((-155) + z * ((-132) + z * ((-235) + z * ((-258) + z * ((-220) + z * ((-162) + z * ((-216) + z * ((-172) + z * ((-218) + z * ((-211) + z * ((-149) + z * ((-84) + z * ((-184) + z * ((-122) + z * ((-192) + z * ((-311) + z * ((-200) + z * ((-298) + z * ((-290) + z * ((-96) + z * ((-112) + z * ((-120) + z * (7 + z * ((-116) + z * ((-58) + z * ((-30) + z * ((-81) + z * (16 + z * ((-2) + z * ((-96) + z * ((-36) + z * ((-180) + z * ((-101) + z * ((-90) + z * ((-58) + z * ((-39) + z * ((-31) + z * 61))))))))))))))))))))))))))))))))))))))


abbrev u9 {R : Type*} [CommRing R] (z : R) : R := pow9_139 z

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_Mod139Result
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Polynomial
namespace DimensionTen.Mod139

def separable_bezout_t {R : Type*} [CommRing R] (z : R) : R := (126 + z * (163 + z * (282 + z * (341 + z * (498 + z * (474 + z * (548 + z * (570 + z * (721 + z * (835 + z * (915 + z * (1075 + z * (1033 + z * (1137 + z * (1325 + z * (1241 + z * (1352 + z * (1485 + z * (1571 + z * (1372 + z * (1481 + z * (1296 + z * (1184 + z * (1208 + z * (1034 + z * (914 + z * (902 + z * (984 + z * (703 + z * (675 + z * (539 + z * (476 + z * (493 + z * (354 + z * (269 + z * (155 + z * (178 + z * (149 + z * 13))))))))))))))))))))))))))))))))))))))

end DimensionTen.Mod139

end

end OAI
end

section
-- module Solutions.OAIQ033_DT.Quantum_DimensionTen_RootReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open NumberField Polynomial
namespace DimensionTen


def rootInteger {K : Type*} [Field K] [CharZero K] (f : ℤ[X]) (hm : f.Monic)
    (x : f.rootSet K) : 𝓞 K :=
  ⟨x, ⟨f, hm, (mem_rootSet.mp x.property).2⟩⟩

@[simp] lemma rootInteger_coe {K : Type*} [Field K] [CharZero K] (f : ℤ[X]) (hm : f.Monic)
    (x : f.rootSet K) : (rootInteger f hm x : K) = x := rfl

end DimensionTen

end
end

end OAI
end


