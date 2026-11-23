-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardPreimageHom
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:23:59.759012+00:00
-- url     : https://prove2.me/theorems/41eeba96-2ab5-4ae5-8dde-0e86f4a674db
-- title:
--   Card Preimage Hom
-- statement:
--   Definitions and structural lemmas for Card Preimage Hom, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardPreimageHom.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
namespace GlobalTheory.CompanionTheory.LocalDens
open PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
theorem cT_add (σ : R →+* R) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    cT σ (x + y) = cT σ x + cT σ y := by
  ext i j; simp [cT]
theorem red_add (ϖ : R) (k : ℕ) {a b : ℕ} (x y : Matrix (Fin a) (Fin b) R) :
    red ϖ k (x + y) = red ϖ k x + red ϖ k y := by
  ext i j; simp [red]
theorem red_surj (ϖ : R) (k : ℕ) {a b : ℕ} : Function.Surjective (red ϖ k (a := a) (b := b)) := by
  intro y
  refine ⟨Matrix.of fun i j => (Ideal.Quotient.mk_surjective (y i j)).choose, ?_⟩
  ext i j
  simp only [red, Matrix.map_apply, Matrix.of_apply]
  exact (Ideal.Quotient.mk_surjective (y i j)).choose_spec
def gr (σ : R →+* R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (x : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin n) (Fin n) R := cT σ x * S * x
def sol (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ) :
    Set (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) :=
  red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (gr σ S x) = red ϖ k T}
theorem lev_le (ϖ : R) (k : ℕ) : lev ϖ (k + 1) ≤ lev ϖ k :=
  Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ (Nat.le_succ k))
def piM (ϖ : R) (k a b : ℕ) :
    Matrix (Fin a) (Fin b) (R ⧸ lev ϖ (k + 1)) →+ Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) :=
  (Ideal.Quotient.factor (lev_le ϖ k)).toAddMonoidHom.mapMatrix
theorem piM_red (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) :
    piM ϖ k a b (red ϖ (k + 1) x) = red ϖ k x := by
  ext i j
  simp [piM, red]
theorem cT_neg (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) : cT σ (-x) = - cT σ x := by
  ext i j; simp [cT]
theorem red_neg (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) : red ϖ k (-x) = - red ϖ k x := by
  ext i j; simp [red]
def hermSub (σ : R →+* R) (ϖ : R) (n k : ℕ) : AddSubgroup (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) where
  carrier := hermMod σ ϖ n k
  add_mem' := by
    rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    have hx' : cT σ x = x := hx
    have hy' : cT σ y = y := hy
    exact ⟨x + y, by show cT σ (x + y) = x + y; rw [cT_add, hx', hy'], red_add _ _ _ _⟩
  zero_mem' := ⟨0, by show cT σ 0 = 0; ext i j; simp [cT], by ext i j; simp [red]⟩
  neg_mem' := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' : cT σ x = x := hx
    exact ⟨-x, by show cT σ (-x) = -x; rw [cT_neg, hx'], red_neg _ _ _⟩
def piH (σ : R →+* R) (ϖ : R) (n k : ℕ) : hermSub σ ϖ n (k + 1) →+ hermSub σ ϖ n k :=
  ((piM ϖ k n n).comp (hermSub σ ϖ n (k + 1)).subtype).codRestrict (hermSub σ ϖ n k) (by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨x, hx, (piM_red ϖ k x).symm⟩)
noncomputable def gb (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (k : ℕ)
    (y : Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k) :=
  red ϖ k (gr σ S (Function.surjInv (red_surj ϖ k) y))
end GlobalTheory.CompanionTheory.LocalDens


