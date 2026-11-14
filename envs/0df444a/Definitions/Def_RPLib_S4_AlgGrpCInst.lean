-- Prove2me | Definitions.Def_RPLib_S4_AlgGrpCInst
-- name    : RPLib_S4_AlgGrpCInst
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T03:13:20.998052+00:00
-- url     : https://prove2.me/theorems/abc37138-851c-44fe-ad0c-bdc88df464a1
-- title:
--   Larsen's alternative library: the two instances used in Larsen's alternative
-- statement:
--   * `lieS_inf_sl_eq_bot_or_eq`: `G` irreducible, every `Ad(G)`-equivariant endomorphism of
--     `sl_n = slMat` scalar ⇒ `Lie (G ∩ SL) = 0` or `= sl_n`.
--   * `lieS_iso_eq_bot_or_eq`: `G ≤ O(B)` or `Sp(B)` (`isoSub B`) irreducible, every `Ad(G)`-equivariant
--     endomorphism of `isoLie B = {X | Xᵀ B + B X = 0}` scalar ⇒ `Lie G = 0` or `= isoLie B`.
--
--   **Formalization note.** Library module (namespace `RamanujanPetersson.AlgGrpA/B/C` or `RamanujanPetersson.Larsen`) of a formalization of Larsen's alternative, used in a formalization of the Ramanujan-Petersson conjecture. $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with the Zariski topology `RamanujanPetersson.AlgGrpA.zarTop` (induced from $\mathrm{Spec}\,K[x_{ij}, y_{ij}]$ via the entries of $g$ and $g^{-1}$; a local instance). The file contains definitions together with proved lemmas (no `sorry`), so that later solution files can import them.
-- source:
--   N. M. Katz, Larsen's alternative, moments, and the monodromy of Lefschetz pencils, in: Contributions to Automorphic Forms, Geometry, and Number Theory (Shalika volume), Johns Hopkins Univ. Press 2004, 521-560; A. Borel, Linear Algebraic Groups, 2nd ed., GTM 126, Springer 1991, doi:10.1007/978-1-4612-0941-6

import Mathlib
import Definitions.Def_RPLib_S4_AlgGrpCCor

/-!
# S4-AlgGrpC, file Inst: the two instances used in Larsen's alternative

* `lieS_inf_sl_eq_bot_or_eq`: `G` irreducible, every `Ad(G)`-equivariant endomorphism of
  `sl_n = slMat` scalar ⇒ `Lie (G ∩ SL) = 0` or `= sl_n`.
* `lieS_iso_eq_bot_or_eq`: `G ≤ O(B)` or `Sp(B)` (`isoSub B`) irreducible, every `Ad(G)`-equivariant
  endomorphism of `isoLie B = {X | Xᵀ B + B X = 0}` scalar ⇒ `Lie G = 0` or `= isoLie B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open MvPolynomial
open scoped Matrix

noncomputable section

namespace RamanujanPetersson.AlgGrpC

open RamanujanPetersson.AlgGrpA RamanujanPetersson.AlgGrpB

variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]

/-- `G ∩ SL` as a subgroup (`detOne` is `SL_n` from `Def_RP_AlgGrpB_SOBase`). -/
theorem coe_inf_detOne (G : Subgroup (Matrix.GeneralLinearGroup n K)) :
    ((G ⊓ detOne : Subgroup (Matrix.GeneralLinearGroup n K)) : Set (Matrix.GeneralLinearGroup n K)) =
      (G : Set (Matrix.GeneralLinearGroup n K)) ∩ slSet :=
  rfl

/-- The trace-zero matrices `sl_n`. -/
def slMat : Submodule K (Matrix n n K) := LinearMap.ker (Matrix.traceLinearMap n K K)

theorem mem_slMat {X : Matrix n n K} : X ∈ (slMat : Submodule K (Matrix n n K)) ↔ X.trace = 0 := by
  rw [slMat, LinearMap.mem_ker]
  rfl

/-- The Lie algebra `{X | Xᵀ B + B X = 0}` of the isometry group of `B`. -/
def isoLie (B : Matrix n n K) : Submodule K (Matrix n n K) where
  carrier := {X | Xᵀ * B + B * X = 0}
  add_mem' := fun {X Y} hX hY => by
    have hX' : Xᵀ * B + B * X = 0 := hX
    have hY' : Yᵀ * B + B * Y = 0 := hY
    show (X + Y)ᵀ * B + B * (X + Y) = 0
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX', hY', add_zero]
  zero_mem' := by
    show (0 : Matrix n n K)ᵀ * B + B * 0 = 0
    rw [Matrix.transpose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  smul_mem' := fun c X hX => by
    have hX' : Xᵀ * B + B * X = 0 := hX
    show (c • X)ᵀ * B + B * (c • X) = 0
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, hX', smul_zero]

theorem mem_isoLie {B X : Matrix n n K} : X ∈ isoLie B ↔ Xᵀ * B + B * X = 0 :=
  Iff.rfl

variable [IsAlgClosed K] [CharZero K]

/-- **Larsen's alternative, `SL` case.** -/
theorem lieS_inf_sl_eq_bot_or_eq {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hEnd : ∀ φ : Matrix n n K →ₗ[K] Matrix n n K, (∀ x ∈ (slMat : Submodule K (Matrix n n K)), φ x ∈ slMat) →
      (∀ g ∈ G, ∀ x ∈ (slMat : Submodule K (Matrix n n K)),
        φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
          (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
      ∃ c : K, ∀ x ∈ (slMat : Submodule K (Matrix n n K)), φ x = c • x) :
    lieS ((G : Set (Matrix.GeneralLinearGroup n K)) ∩ slSet) = ⊥ ∨
      lieS ((G : Set (Matrix.GeneralLinearGroup n K)) ∩ slSet) = slMat := by
  have e := coe_inf_detOne G
  have h := lieS_eq_bot_or_eq (H := G ⊓ detOne) (E := slMat) hG
    (fun g hg X hX => by
      rw [e] at hX ⊢
      exact conj_mem_lieS_inf_sl G hg hX)
    (fun X hX => by
      rw [e] at hX
      exact mem_slMat.2 (trace_eq_zero_of_mem_lieS Set.inter_subset_right hX))
    hEnd
  rwa [e] at h

/-- **Larsen's alternative, orthogonal / symplectic case.** -/
theorem lieS_iso_eq_bot_or_eq {B : Matrix n n K} {G : Subgroup (Matrix.GeneralLinearGroup n K)}
    (hGB : G ≤ isoSub B)
    (hG : ∀ W : Submodule K (n → K), (∀ g ∈ G, ∀ v ∈ W, (g : Matrix n n K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hEnd : ∀ φ : Matrix n n K →ₗ[K] Matrix n n K, (∀ x ∈ isoLie B, φ x ∈ isoLie B) →
      (∀ g ∈ G, ∀ x ∈ isoLie B,
        φ ((g : Matrix n n K) * x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) =
          (g : Matrix n n K) * φ x * ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K)) →
      ∃ c : K, ∀ x ∈ isoLie B, φ x = c • x) :
    lieS (G : Set (Matrix.GeneralLinearGroup n K)) = ⊥ ∨
      lieS (G : Set (Matrix.GeneralLinearGroup n K)) = isoLie B :=
  lieS_eq_bot_or_eq hG
    (fun g hg X hX => conj_mem_lieS (fun h hh => G.mul_mem (G.mul_mem hg hh) (G.inv_mem hg)) hX)
    (fun X hX => mem_isoLie.2 (lie_iso (Z := (G : Set (Matrix.GeneralLinearGroup n K)))
      (fun g hg => hGB hg) hX))
    hEnd

end RamanujanPetersson.AlgGrpC


