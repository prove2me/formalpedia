-- Prove2me | Definitions.Def_KnillLaflammeLean_QuantumInfo_Channel
-- name    : KnillLaflammeLean_QuantumInfo_Channel
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-20T23:46:35.097179+00:00
-- url     : https://prove2.me/theorems/5158de38-a0b9-4eae-be5a-058875034111
-- title:
--   Channel
-- statement:
--   Definitions and structural lemmas for Channel, from Zayn Blore's pinned Knill–Laflamme quantum error correction development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/zblore/knill-laflamme-lean/blob/f680e2d5f616bb423fb814f1471b07387729fffd/KnillLaflammeLean/QuantumInfo/Channel.lean

module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Matrix.PosDef
set_option autoImplicit false
@[expose] public section
@[expose] public section
open Matrix
open scoped ComplexOrder
namespace QuantumInfo
structure Channel (n m ι : Type*) [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n] where
  /-- The Kraus operators `Kᵢ : ℂⁿ → ℂᵐ`. -/
  kraus : ι → Matrix m n ℂ
  /-- Trace preservation: `∑ᵢ Kᵢᴴ Kᵢ = 1`. -/
  tp : (∑ i : ι, (kraus i)ᴴ * (kraus i) : Matrix n n ℂ) = 1
namespace Channel
variable {n m ι : Type*} [Fintype n] [Fintype m] [Fintype ι] [DecidableEq n]
noncomputable def apply (Φ : Channel n m ι) (ρ : Matrix n n ℂ) : Matrix m m ℂ :=
  ∑ i : ι, Φ.kraus i * ρ * (Φ.kraus i)ᴴ
noncomputable def adjoint (Φ : Channel n m ι) (P : Matrix m m ℂ) : Matrix n n ℂ :=
  ∑ i : ι, (Φ.kraus i)ᴴ * P * (Φ.kraus i)
@[simp] lemma adjoint_def (Φ : Channel n m ι) (P : Matrix m m ℂ) :
    Φ.adjoint P = ∑ i : ι, (Φ.kraus i)ᴴ * P * (Φ.kraus i) := rfl
def id (n : Type*) [Fintype n] [DecidableEq n] : Channel n n PUnit where
  kraus _ := 1
  tp := by simp
end Channel
end QuantumInfo


