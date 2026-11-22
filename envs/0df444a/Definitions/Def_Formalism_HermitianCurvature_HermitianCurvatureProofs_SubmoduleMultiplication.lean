-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:39:10.105716+00:00
-- url     : https://prove2.me/theorems/db2a07d9-3170-4668-816b-671e8fe3768d
-- title:
--   Submodule Multiplication
-- statement:
--   Definitions and structural lemmas for Submodule Multiplication, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
section Top
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
def I (R : Subring K) (a : K) : Set K := {x | ∃ r ∈ R, x = a * r}
structure Adic (R : Subring K) (ϖ : Kˣ) : Prop where
  t2 : T2Space K
  isOpen : IsOpen (R : Set K)
  isCompact : IsCompact (R : Set K)
  mem : (ϖ : K) ∈ R
  absorb : ∀ x : K, ∃ m : ℕ, (ϖ : K) ^ m * x ∈ R
  basis : ∀ W ∈ 𝓝 (0 : K), ∃ n : ℕ, ∀ r ∈ R, (ϖ : K) ^ n * r ∈ W
variable {R : Subring K} {ϖ : Kˣ}
theorem mul_mem_sub (Λ : Submodule R K) {r x : K} (hr : r ∈ R) (hx : x ∈ Λ) : r * x ∈ Λ :=
  Λ.smul_mem (⟨r, hr⟩ : R) hx
end Top
section Mat
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ}
def Rs (R : Subring K) : Submodule R K where
  carrier := R
  add_mem' := R.add_mem
  zero_mem' := R.zero_mem
  smul_mem' := fun c _ hx => R.mul_mem c.2 hx
def sm (a : K) (Λ : Submodule R K) : Submodule R K where
  carrier := {x | ∃ l ∈ Λ, x = a * l}
  add_mem' := by
    rintro _ _ ⟨l, hl, rfl⟩ ⟨l', hl', rfl⟩
    exact ⟨l + l', Λ.add_mem hl hl', by ring⟩
  zero_mem' := ⟨0, Λ.zero_mem, by simp⟩
  smul_mem' := by
    rintro c _ ⟨l, hl, rfl⟩
    exact ⟨c • l, Λ.smul_mem c hl, by rw [Subring.smul_def, Subring.smul_def]; simp only [smul_eq_mul]; ring⟩
def MemM (Λ : Submodule R K) (X : Matrix (Fin m) (Fin m) K) : Prop := ∀ i j, X i j ∈ Λ
end Mat
section Alg
variable {K : Type} [CommRing K] {m : ℕ}
def piW (w : Fin m → K) (j : Fin m) : K := ∏ k ∈ Finset.univ.filter (· < j), w k
def uW (w : Fin m → K) (i j : Fin m) : K := w i * w j * piW w j
def MW (w : Fin m → K) : Matrix (Fin m) (Fin m) K := Matrix.of fun i j =>
  (if i = j then 2 * w i else 0) + (if j < i then uW w i j else 0) + (if i < j then uW w j i else 0)
def HH (K : Type) [CommRing K] (m : ℕ) : Matrix (Fin m) (Fin m) K := 1 + Matrix.of fun _ _ => (1 : K)
def HA (K : Type) [CommRing K] (m : ℕ) : Matrix (Fin m) (Fin m) K :=
  ((m + 1 : ℕ) : K) • (1 : Matrix (Fin m) (Fin m) K) - Matrix.of fun _ _ => (1 : K)
end Alg
section Lip
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ} {m : ℕ} {c : K}
def LW (R : Subring K) (c : K) (f : (Fin m → K) → K) : Prop :=
  (∀ v, (∀ k, v k ∈ R) → f v ∈ R) ∧
  ∀ (Λ : Submodule R K) (v v' : Fin m → K), (∀ k, v k ∈ R) → (∀ k, v' k ∈ R) →
    (∀ k, v k - v' k ∈ Λ) → f v - f v' ∈ sm c Λ
noncomputable def wv (c : K) (v : Fin m → K) (k : Fin m) : K := Ring.inverse (1 + c * v k)
theorem wv_spec (hc : ∀ r ∈ R, ∃ u ∈ R, (1 + c * r) * u = 1) (v : Fin m → K) (k : Fin m)
    (hv : v k ∈ R) : (1 + c * v k) * wv c v k = 1 ∧ wv c v k ∈ R := by
  obtain ⟨u, hu, e⟩ := hc _ hv
  have h1 : (1 + c * v k) * wv c v k = 1 := Ring.mul_inverse_cancel _ (IsUnit.of_mul_eq_one _ e)
  have : wv c v k = u := by linear_combination u * h1 - wv c v k * e
  exact ⟨h1, this ▸ hu⟩
theorem LW.wv (hc : ∀ r ∈ R, ∃ u ∈ R, (1 + c * r) * u = 1) (k : Fin m) :
    LW R c (fun v : Fin m → K => wv c v k) :=
  ⟨fun v hv => (wv_spec hc v k (hv k)).2, fun Λ v v' hv hv' hd => by
    obtain ⟨e, h1⟩ := wv_spec hc v k (hv k)
    obtain ⟨e', h1'⟩ := wv_spec hc v' k (hv' k)
    refine ⟨-(InverseBoundedFixedPoint.wv c v k * InverseBoundedFixedPoint.wv c v' k) * (v k - v' k),
      mul_mem_sub Λ (R.neg_mem (R.mul_mem h1 h1')) (hd k), ?_⟩
    linear_combination (InverseBoundedFixedPoint.wv c v' k) * e - (InverseBoundedFixedPoint.wv c v k) * e'⟩
def cm (a : K) (Λ : Submodule R K) : Submodule R K where
  carrier := {v | a * v ∈ Λ}
  add_mem' := by
    intro x y hx hy
    show a * (x + y) ∈ Λ
    rw [mul_add]; exact Λ.add_mem hx hy
  zero_mem' := by
    show a * 0 ∈ Λ
    simp
  smul_mem' := by
    intro r x hx
    show a * (r • x) ∈ Λ
    have : a * (r • x) = r • (a * x) := by
      rw [Subring.smul_def, Subring.smul_def]; simp only [smul_eq_mul]; ring
    rw [this]; exact Λ.smul_mem r hx
end Lip
section Main
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
end Main
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint


