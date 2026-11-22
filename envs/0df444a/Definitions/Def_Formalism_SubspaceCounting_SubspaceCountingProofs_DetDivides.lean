-- Prove2me | Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
-- name    : Formalism_SubspaceCounting_SubspaceCountingProofs_DetDivides
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:24:27.738733+00:00
-- url     : https://prove2.me/theorems/7f20f324-c628-4a9a-837b-84adc3d72480
-- title:
--   Det Divides
-- statement:
--   Definitions and structural lemmas for Det Divides, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/DetDivides.lean

import Definitions.Def_Formalism_SubspaceCounting_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Polynomial
namespace Formalism.G0.DetDividesP
open Formalism.G0
variable {L : Type} [Field L] {r : ℕ}
def nMat (g : GL (Fin r) L) : Matrix (Fin r) (Fin r) L[X] :=
  (g.1.map C) * Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then 1 else X) *
    ((g⁻¹ : GL (Fin r) L).1.map C)
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
open Polynomial
namespace Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
open Classical in

def ptA {L : Type} [Field L] (A : Fin r → ι) (g : GL (Fin r) L) (x : ι × Fin r → L) : ι × Fin r → L[X] :=
  fun p => if p.1 ∈ Set.range A then ∑ b, msMat g p.2 b * C (x (p.1, b)) else C (x p)
def Red (A : Fin r → ι) (G : MvPolynomial (ι × Fin r) K) (n : ℕ) : Prop :=
  ∀ (L : Type) [Field L] [Algebra K L] (g : GL (Fin r) L) (x : ι × Fin r → L),
    MvPolynomial.aeval x (detLetters (K := K) A) ≠ 0 →
      (X : L[X]) ^ n ∣ MvPolynomial.aeval (ptA A g x) G
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
open Polynomial
namespace Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
open Polynomial
namespace Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
def Tm (K : Type) [Field K] (A : Fin r → ι) : Matrix (Fin r) (Fin r) (MvPolynomial ((ι × Fin r) ⊕ ι) K) :=
  Matrix.of fun l b => X (Sum.inl (A l, b))
def Wv (K : Type) [Field K] (A : Fin r → ι) : Fin r → MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  fun l => X (Sum.inr (A l))
open Classical in

def evPerm (A : Fin r → ι) (τ : Equiv.Perm (Fin r)) : MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] K :=
  aeval (Sum.elim (fun q => if h : ∃ l, A l = q.1 then (if q.2 = τ (Classical.choose h) then 1 else 0) else 0)
    (fun _ => 0))
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
def rho (K : Type) [Field K] (A : Fin r → ι) (l : Fin r) :
    MvPolynomial ((ι × Fin r) ⊕ ι) K →ₐ[K] MvPolynomial ((ι × Fin r) ⊕ ι) K :=
  aeval (Sum.elim (fun q => X (Sum.inl q)) (fun i => if i = A l then 1 else 0))
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
def lst (hr : 0 < r) : Fin r := ⟨r - 1, by omega⟩
section matrices
variable {L : Type} [Field L]
lemma E_sq (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) :
    Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) *
      Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1) = 0 := by
  rw [Matrix.vecMulVec_mul_vecMulVec, dotProduct_single]; simp [hφ]
def gU (i : Fin r) (φ : Fin r → L) (hφ : φ i = 1) : GL (Fin r) L where
  val := 1 - Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  inv := 1 + Matrix.vecMulVec (Pi.single i (1 : L)) (φ - Pi.single i 1)
  val_inv := by
    rw [mul_add, mul_one, sub_mul, one_mul, E_sq i φ hφ]; abel
  inv_val := by
    rw [add_mul, one_mul, mul_sub, mul_one, E_sq i φ hφ]; abel
end matrices
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
namespace Formalism.G0.DetDividesP
open Formalism.G0 MvPolynomial
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
end Formalism.G0.DetDividesP
end
noncomputable section
open scoped BigOperators
namespace Formalism.G0.DetDividesP
open Formalism.G0
variable {K ι : Type} [Field K] [DecidableEq ι] {r : ℕ}
end Formalism.G0.DetDividesP
namespace Formalism.G0
end Formalism.G0
end


