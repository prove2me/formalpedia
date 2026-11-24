-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarScaling_MapEqSelfOfIterate
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:22:07.231525+00:00
-- url     : https://prove2.me/theorems/e4447466-c147-4494-b018-93fd5fd4a110
-- title:
--   Map Eq Self Of Iterate
-- statement:
--   Definitions and structural lemmas for Map Eq Self Of Iterate, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/HaarScaling/MapEqSelfOfIterate.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_CdHaarScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MeasureTheory.Measure Matrix
namespace PI.UnitaryGroupMassFormula.CdHaarScale.Main
instance instTGUpqT (P Q : ℕ) : IsTopologicalGroup (Formalism.BasicNotions.UpqT P Q) :=
  inferInstanceAs (IsTopologicalGroup (Formalism.UG.Upq P Q))
instance instBorelUpqT (P Q : ℕ) : BorelSpace (Formalism.BasicNotions.UpqT P Q) := ⟨rfl⟩
def rmap {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) :
    Matrix m m ℂ →* Matrix n n ℂ where
  toFun := reindex e e
  map_one' := map_one (reindexAlgEquiv ℂ ℂ e)
  map_mul' := map_mul (reindexAlgEquiv ℂ ℂ e)
theorem rmap_apply {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (M : Matrix m m ℂ) : rmap e M = reindex e e M := rfl
theorem reindex_conj {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (M J : Matrix m m ℂ) :
    reindex e e (Mᴴ * J * M) = (reindex e e M)ᴴ * reindex e e J * reindex e e M := by
  simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
def transp {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n)
    (H : Subgroup (Matrix m m ℂ)ˣ) (K : Subgroup (Matrix n n ℂ)ˣ)
    (hHK : ∀ x : (Matrix m m ℂ)ˣ, x ∈ H ↔ Units.map (rmap e) x ∈ K) : H ≃ₜ* K where
  toFun g := ⟨Units.map (rmap e) g.1, (hHK g.1).1 g.2⟩
  invFun a := ⟨Units.map (rmap e.symm) a.1, by
    rw [hHK]
    have : Units.map (rmap e) (Units.map (rmap e.symm) a.1) = a.1 := by
      ext1; simp [rmap_apply]
    rw [this]; exact a.2⟩
  left_inv g := by
    apply Subtype.ext; apply Units.ext
    simp [rmap_apply]
  right_inv a := by
    apply Subtype.ext; apply Units.ext
    simp [rmap_apply]
  map_mul' g h := Subtype.ext (map_mul (Units.map (rmap e)) g.1 h.1)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Units.continuous_map (f := rmap e) (continuous_id.matrix_reindex e e)).comp
      continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (Units.continuous_map (f := rmap e.symm) (continuous_id.matrix_reindex e.symm e.symm)).comp
      continuous_subtype_val
theorem cT_eq {m : Type} (M : Matrix m m ℂ) : Formalism.UG.cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
theorem reindex_Jpq {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    reindex e e (Formalism.UG.Jpq P Q) = Formalism.REAL.Jm ε := by
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Formalism.UG.Jpq, Formalism.REAL.Jm, Matrix.diagonal_apply, Matrix.one_apply, h1, h2] <;>
    (try split_ifs <;> simp)
theorem reindex_Jm {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    reindex π π (Formalism.REAL.Jm ε) = Formalism.REAL.Jm ε := by
  have hs : ∀ i, ε (π.symm i) = ε i := fun i => by simpa using (hπ (π.symm i)).symm
  ext i j
  simp [Formalism.REAL.Jm, Matrix.diagonal_apply, hs]
theorem memUpq_iff {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false)
    (x : (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)ˣ) :
    x ∈ Formalism.UG.Upq P Q ↔ Units.map (rmap e) x ∈ Formalism.REAL.UJ ε := by
  have key : (Formalism.UG.cT (starRingEnd ℂ) (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) *
      Formalism.UG.Jpq P Q * (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) = Formalism.UG.Jpq P Q) ↔
      Formalism.REAL.inUJ ε (reindex e e (x : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)) := by
    rw [cT_eq, Formalism.REAL.inUJ, ← reindex_Jpq e h1 h2, ← reindex_conj]
    exact (Matrix.reindex e e).injective.eq_iff.symm
  exact key
theorem memUJ_iff {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i)
    (x : (Matrix (Fin n) (Fin n) ℂ)ˣ) :
    x ∈ Formalism.REAL.UJ ε ↔ Units.map (rmap π) x ∈ Formalism.REAL.UJ ε := by
  have key : Formalism.REAL.inUJ ε (x : Matrix (Fin n) (Fin n) ℂ) ↔
      Formalism.REAL.inUJ ε (reindex π π (x : Matrix (Fin n) (Fin n) ℂ)) := by
    rw [Formalism.REAL.inUJ, Formalism.REAL.inUJ]
    conv_rhs => rw [← reindex_Jm π hπ, ← reindex_conj]
    exact (Matrix.reindex π π).injective.eq_iff.symm
  exact key
def phi {P Q n : ℕ} {ε : Fin n → Bool} (e : Fin P ⊕ Fin Q ≃ Fin n)
    (h1 : ∀ i, ε (e (Sum.inl i)) = true) (h2 : ∀ j, ε (e (Sum.inr j)) = false) :
    Formalism.BasicNotions.UpqT P Q ≃ₜ* Formalism.REAL.UJ ε :=
  transp e (Formalism.UG.Upq P Q) (Formalism.REAL.UJ ε) (memUpq_iff e h1 h2)
def rho {n : ℕ} {ε : Fin n → Bool} (π : Fin n ≃ Fin n) (hπ : ∀ i, ε (π i) = ε i) :
    Formalism.REAL.UJ ε ≃ₜ* Formalism.REAL.UJ ε :=
  transp π (Formalism.REAL.UJ ε) (Formalism.REAL.UJ ε) (memUJ_iff π hπ)
end PI.UnitaryGroupMassFormula.CdHaarScale.Main


