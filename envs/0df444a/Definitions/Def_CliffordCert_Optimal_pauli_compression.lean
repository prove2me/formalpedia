-- Prove2me | Definitions.Def_CliffordCert_Optimal_pauli_compression
-- name    : CliffordCert_Optimal_pauli_compression
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:34:34.783614+00:00
-- url     : https://prove2.me/theorems/c9c679a7-ca0f-4b80-946c-5a9e02c16be9
-- title:
--   Signed Paulis and fixed input-only Clifford compression
-- statement:
--   A Pauli label is $v=(a,b)\in\mathbb F_2^n\oplus\mathbb F_2^n$, with commutation form $B(v,w)=a\cdot b'+b\cdot a'$. The actual matrices are
--   $$P_v=\bigotimes_{j=1}^n i^{a_jb_j}X^{a_j}Z^{b_j},\qquad Y=iXZ,$$
--   where each exponent uses the ordinary integers 0 and 1. A Clifford matrix is unitary and conjugates every $P_v$ to some $\pm P_w$.
--
--   For $q\le n$, the compression map is computed from $C$ by matrix-unit coefficients of
--   $$\Phi_C(X)=\operatorname{Tr}_{\text{last }n-q\text{ qubits}}(CXC^\dagger).$$
--   It introduces no ancillary register. The retained lift is $A\otimes I$ in exactly the same tensor order. An encoder family contains only a finite list and its Clifford witnesses. Density matrices, signed Pauli strings and the individual Clifford predicate reuse the checked published definitions. The local wrappers only convert ZMod 2 labels to Fin 2 labels and raw matrices to bundled unitaries; no ensemble is used. Compression inequalities and the maximally mixed image occur only as theorem conclusions.
--
--   This module fixes the normalization and physical operations used throughout the certification statement.
-- source:
--   Hyunho Cha, Jungwoo Lee, STOC 2027 submission #226 (October 2026), p. 5, §§2–3, Theorem 2; pp. 11–12, Eqs. (16), (18)–(20) (PDF pp. 12–13) (PDF p. 6); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/226.pdf

import Definitions.Def_ShallowShadows_ShadowNorm_IsClifford
import Definitions.Def_CliffordCert_Optimal_symplectic
import Definitions.Def_CliffordCert_Optimal_matrix_model
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace CliffordCert.Optimal
attribute [local instance] Classical.propDecidable Classical.decEq
abbrev Bits (n : ℕ) := Fin n → Fin 2
abbrev Label (n : ℕ) := Binary n × Binary n

def commutation {n : ℕ} (v w : Label n) : F₂ :=
  ∑ j, (v.1 j * w.2 j + v.2 j * w.1 j)

/-- Convert field-valued binary labels to the published computational bit labels. -/
def labelBits {n : ℕ} (v : Label n) : Bits n × Bits n :=
  (fun j => ⟨(v.1 j).val, ZMod.val_lt (v.1 j)⟩,
   fun j => ⟨(v.2 j).val, ZMod.val_lt (v.2 j)⟩)

/-- Eq. (18): reuse the identical signed Hermitian Pauli formula. -/
def pauli {n : ℕ} (v : Label n) : Mat (Bits n) :=
  ShallowShadows.ShadowNorm.pauli (labelBits v)

/-- Only the raw-matrix / bundled-unitary adapter is local. -/
def IsClifford {n : ℕ} (C : Mat (Bits n)) : Prop :=
  ∃ U : Matrix.unitaryGroup (Bits n) ℂ, (U : Mat (Bits n)) = C ∧
    ShallowShadows.ShadowNorm.IsClifford U

def joinBits {n q : ℕ} (hqn : q ≤ n) (a : Bits q) (b : Bits (n-q)) : Bits n :=
  fun j => if h : j.val < q then a ⟨j.val, h⟩ else b ⟨j.val-q, by omega⟩

/-- Partial trace of C X C† over the LAST n-q registers, written in matrix units. -/
def compression {n q : ℕ} (hqn : q ≤ n) (C : Mat (Bits n)) :
    Mat (Bits n) →ₗ[ℂ] Mat (Bits q) :=
  fromCoefficients fun u v a b =>
    ∑ y : Bits (n-q), C (joinBits hqn u y) a * star (C (joinBits hqn v y) b)

def retainedLift {n q : ℕ} (hqn : q ≤ n) (A : Mat (Bits q)) : Mat (Bits n) :=
  fun x y => A (fun j => x ⟨j.val, by omega⟩) (fun j => y ⟨j.val, by omega⟩) *
    if (fun j : Fin (n-q) => x ⟨q+j.val, by omega⟩) =
       (fun j : Fin (n-q) => y ⟨q+j.val, by omega⟩) then 1 else 0

def ActsOnlyOnRetained {n q : ℕ} (hqn : q ≤ n) (A : Mat (Bits n)) : Prop :=
  ∃ R : Mat (Bits q), A = retainedLift hqn R

/-- The explicit standard symplectic form on labels, with no characteristic-two ambiguity. -/
def LabelNondegenerate {n : ℕ} (S : Submodule F₂ (Label n)) : Prop :=
  ∀ v ∈ S, (∀ w ∈ S, commutation v w = 0) → v = 0

def maximallyMixed (n : ℕ) : Mat (Bits n) := ((2 : ℂ)^n)⁻¹ • 1

/-- Physical data only: no compression or testing guarantee is bundled here. -/
structure EncoderFamily (n q : ℕ) where
  length : ℕ
  unitary : Fin length → Mat (Bits n)
  clifford : ∀ i, IsClifford (unitary i)

end CliffordCert.Optimal


