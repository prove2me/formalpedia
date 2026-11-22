-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:05:47.398943+00:00
-- url     : https://prove2.me/theorems/e6fd7d24-2529-4159-aae2-7a486677a568
-- title:
--   Row Deg
-- statement:
--   Definitions and structural lemmas for Row Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/RowDeg.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.Pj
open MvPolynomial
abbrev Letter (T : Type) (r : T → ℕ) (n : ℕ) : Type := Σ σ : T, Fin (r σ) × Fin n
variable {T : Type} (r : T → ℕ) (n : ℕ)
def letMat (R : Type) [CommRing R] (σ : T) :
    Matrix (Fin (r σ)) (Fin n) (MvPolynomial (Letter T r n) R) :=
  fun a b => X ⟨σ, a, b⟩
variable (k : Type) [Field k]
def lap (hinv : Matrix (Fin n) (Fin n) k) (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) :
    MvPolynomial (Letter T r n) k →ₗ[k] MvPolynomial (Letter T r n) k :=
  ∑ b, ∑ b', hinv b b' •
    ((pderiv (⟨τ, a, b⟩ : Letter T r n)).toLinearMap ∘ₗ
      (pderiv (⟨τ', a', b'⟩ : Letter T r n)).toLinearMap)
def harmK (cc : T → T) (isX : T → Prop) (hinv : T → Matrix (Fin n) (Fin n) k) :
    Submodule k (MvPolynomial (Letter T r n) k) :=
  ⨅ (τ : T) (_ : isX τ) (a : Fin (r τ)) (a' : Fin (r (cc τ))),
    LinearMap.ker (lap r n k (hinv τ) τ (cc τ) a a')
def rowShift (σ : T) (i i' : Fin (r σ)) (t : k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => open Classical in
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X ℓ + C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ
def RowInv (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ (σ : T) (i i' : Fin (r σ)), i' < i → ∀ t : k, rowShift r n k σ i i' t P = P
def RowDeg (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ m ∈ P.support, ∀ (σ : T) (i : Fin (r σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a σ i
def HHa (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) : Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ harmK r n k cc isX (fun _ => 1) ∧ RowInv r n k P ∧ RowDeg r n k a P}
def HaO (O : Subring k) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ HHa r n k cc isX a ∧ ∀ m, P.coeff m ∈ O}
end Formalism.L2.Pj


