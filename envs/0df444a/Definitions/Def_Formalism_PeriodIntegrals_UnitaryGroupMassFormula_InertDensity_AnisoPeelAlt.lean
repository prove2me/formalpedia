-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:12:46.579418+00:00
-- url     : https://prove2.me/theorems/96dabd32-aa97-464d-a2ec-facce0dab77c
-- title:
--   Aniso Peel Alt
-- statement:
--   Definitions and structural lemmas for Aniso Peel Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/AnisoPeelAlt.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_SiegelMassRatios_DensExact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
namespace DensInertW
def hf {L : Type} [Field L] {n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (x y : Fin n → L) : L :=
  ∑ k, ∑ l, x k * M k l * y l ^ q
def IsHerm {L : Type} [Field L] {n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L) : Prop :=
  ∀ k l, M l k = M k l ^ q
def NonDeg {L : Type} [Field L] {n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) : Prop :=
  ∀ w ∈ W, (∀ v ∈ W, hf q M w v = 0) → w = 0
def cntT {L : Type} [Field L] {n m : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) (B : Matrix (Fin m) (Fin m) L) : ℕ :=
  {X : Fin m → Fin n → L | (∀ i, X i ∈ W) ∧ LinearIndependent L X ∧
      ∀ i j, hf q M (X i) (X j) = B i j}.ncard
def valZ (q d : ℕ) : ℤ := (q : ℤ) ^ (2 * d - 1) + (-1) ^ d * ((q : ℤ) ^ d - (q : ℤ) ^ (d - 1))
def valN (q d : ℕ) : ℤ := (q : ℤ) ^ (d - 1) * ((q : ℤ) ^ d - (-1) ^ d)
def Fr (q : ℕ) : ℕ → ℕ → ℕ → ℤ
  | _, 0, 0 => 1
  | d, r + 1, c => valN q d * Fr q (d - 1) r c
  | d, 0, c + 1 => (valZ q d - 1) * (q : ℤ) ^ (2 * c) * Fr q (d - 2) 0 c
open Classical in

def ValCount : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L)),
      IsHerm (Fintype.card K) M → NonDeg (Fintype.card K) M W →
      ∀ a : L, a ^ Fintype.card K = a →
        (({v : Fin n → L | v ∈ W ∧ hf (Fintype.card K) M v v = a}.ncard : ℕ) : ℤ) =
          if a = 0 then valZ (Fintype.card K) (Module.finrank L W)
          else valN (Fintype.card K) (Module.finrank L W)
def Diag : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (m : ℕ) (B : Matrix (Fin m) (Fin m) L), IsHerm (Fintype.card K) B →
      ∃ P : Matrix (Fin m) (Fin m) L, IsUnit P.det ∧ ∃ (w : Fin m → L) (r : ℕ), r ≤ m ∧
        P * B * (P.map (fun y => y ^ Fintype.card K)).transpose = Matrix.diagonal w ∧
        (∀ i, w i ≠ 0 ↔ i.val < r) ∧ (∀ i, w i ^ Fintype.card K = w i)
def Congr : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L)) (m : ℕ)
      (B P : Matrix (Fin m) (Fin m) L), IsUnit P.det →
      cntT (Fintype.card K) M W (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose) =
        cntT (Fintype.card K) M W B
def AnisoPeel : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L)),
      IsHerm (Fintype.card K) M → NonDeg (Fintype.card K) M W →
      ∀ (m : ℕ) (b : L) (w : Fin m → L) (k : ℤ), b ^ Fintype.card K = b → b ≠ 0 →
        (∀ W' : Submodule L (Fin n → L), NonDeg (Fintype.card K) M W' →
          Module.finrank L W' + 1 = Module.finrank L W →
          (cntT (Fintype.card K) M W' (Matrix.diagonal w) : ℤ) = k) →
        (cntT (Fintype.card K) M W (Matrix.diagonal (Fin.cons b w : Fin (m + 1) → L)) : ℤ) =
          valN (Fintype.card K) (Module.finrank L W) * k
def IsoPeel : Prop :=
  ∀ (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L],
    Module.finrank K L = 2 →
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L)),
      IsHerm (Fintype.card K) M → NonDeg (Fintype.card K) M W →
      ∀ (c : ℕ) (k : ℤ),
        (∀ W' : Submodule L (Fin n → L), NonDeg (Fintype.card K) M W' →
          Module.finrank L W' + 2 = Module.finrank L W →
          (cntT (Fintype.card K) M W' (0 : Matrix (Fin c) (Fin c) L) : ℤ) = k) →
        (cntT (Fintype.card K) M W (0 : Matrix (Fin (c + 1)) (Fin (c + 1)) L) : ℤ) =
          (valZ (Fintype.card K) (Module.finrank L W) - 1) * (Fintype.card K : ℤ) ^ (2 * c) * k
def Arith : Prop :=
  ∀ (q n m r : ℕ), 1 < q → r ≤ m →
    ((Fr q n r (m - r) : ℤ) : ℝ) / ((q : ℝ) ^ (2 * n * m) / (q : ℝ) ^ (m ^ 2)) =
      Formalism.L2.SG.DensExact.densProd q (-1) n m (m - r)
end DensInertW


