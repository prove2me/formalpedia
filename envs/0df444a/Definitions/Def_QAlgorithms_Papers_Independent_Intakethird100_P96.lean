-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P96
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P96
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T09:29:49.0012+00:00
-- url     : https://prove2.me/theorems/3908f289-957d-4783-a8be-0a260959a880
-- title:
--   Definitions for Reversible quantum cellular automata
-- statement:
--   The objects the formalized statements of *Reversible quantum cellular automata* (arXiv:quant-ph/0405174) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `contractLeft`: Slice the second tensor factor by a linear functional; §IV.C, PDF p.10.
--   - `contractRight`: Slice the first tensor factor by a linear functional; §IV.C, PDF p.10.
--   - `coefficientLeft`: The first-factor coefficient support, computed from all slices, §IV.C p.10.
--   - `coefficientRight`: The second-factor coefficient support, computed from all slices, §IV.C p.10.
--   - `tensorSpan`: The embedded tensor product of two subspaces, equations (21)--(22), p.10.
--   - `supportLeft`: First-factor support, without an assumed ambient unit, §IV.C p.10.
--   - `supportRight`: Second-factor support, without an assumed ambient unit, §IV.C p.10.
--   - `coordinateProjection`: Rank-one projection onto standard basis vector `i`, §IV.E, PDF p.11.
--   - `jointBlockIndex`: Basis labels for joint blocks and their multiplicity copies, Proposition 13, p.18. A zero multiplicity contributes no labels.
--   - `jointAction`: The joint product representation, identity on each multiplicity space, p.18.
--   - `RingConfiguration`: Configurations on a cyclic chain of length `extra + 5`, §V.B pp.14--15.
--   - `IsWatrous`: Watrous' translation-invariant amplitude product (43), on a finite ring. Allowing the entire ring as neighborhood makes this the largest such class.
--   - `ringHadamard`: Sitewise Hadamard in the preferred basis, §V.B, PDF p.14.
--   - `ringPhase`: Product of nearest-neighbor phase gates at angle pi, §V.B pp.14--15.
-- source:
--   Reversible quantum cellular automata, arXiv:quant-ph/0405174v1, https://arxiv.org/abs/quant-ph/0405174v1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P26

/-!
Statements from Schumacher--Werner, arXiv:quant-ph/0405174v1.
Deferred lattice results and source ambiguities are recorded in the unit's HARD.md.
-/

noncomputable section

open scoped TensorProduct Kronecker BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P96

-- Accepted-library reuse: the full complex matrix algebra, Appendix A pp.17--18.
open QAlgorithms.Papers.Independent.Information100.P26 (Mat)

example : (1 : Mat 1) 0 0 = 1 := rfl

section Coefficients

variable {B1 B2 : Type*} [AddCommGroup B1] [Module ℂ B1]
  [AddCommGroup B2] [Module ℂ B2]

/-- Slice the second tensor factor by a linear functional; §IV.C, PDF p.10. -/
def contractLeft (f : B2 →ₗ[ℂ] ℂ) : B1 ⊗[ℂ] B2 →ₗ[ℂ] B1 :=
  (TensorProduct.rid ℂ B1).toLinearMap.comp
    (TensorProduct.map (LinearMap.id : B1 →ₗ[ℂ] B1) f)

/-- Slice the first tensor factor by a linear functional; §IV.C, PDF p.10. -/
def contractRight (f : B1 →ₗ[ℂ] ℂ) : B1 ⊗[ℂ] B2 →ₗ[ℂ] B2 :=
  (TensorProduct.lid ℂ B2).toLinearMap.comp
    (TensorProduct.map f (LinearMap.id : B2 →ₗ[ℂ] B2))

example (f : B2 →ₗ[ℂ] ℂ) (x : B1) (y : B2) :
    contractLeft f (x ⊗ₜ[ℂ] y) = f y • x := by
  simp [contractLeft]

example (f : B1 →ₗ[ℂ] ℂ) (x : B1) (y : B2) :
    contractRight f (x ⊗ₜ[ℂ] y) = f x • y := by
  simp [contractRight]

/-- The first-factor coefficient support, computed from all slices, §IV.C p.10. -/
def coefficientLeft (M : Set (B1 ⊗[ℂ] B2)) : Submodule ℂ B1 :=
  Submodule.span ℂ {x | ∃ a ∈ M, ∃ f : B2 →ₗ[ℂ] ℂ, contractLeft f a = x}

/-- The second-factor coefficient support, computed from all slices, §IV.C p.10. -/
def coefficientRight (M : Set (B1 ⊗[ℂ] B2)) : Submodule ℂ B2 :=
  Submodule.span ℂ {y | ∃ a ∈ M, ∃ f : B1 →ₗ[ℂ] ℂ, contractRight f a = y}

/-- The embedded tensor product of two subspaces, equations (21)--(22), p.10. -/
def tensorSpan (P : Submodule ℂ B1) (Q : Submodule ℂ B2) :
    Submodule ℂ (B1 ⊗[ℂ] B2) :=
  Submodule.span ℂ {z | ∃ x ∈ P, ∃ y ∈ Q, z = x ⊗ₜ[ℂ] y}

example : coefficientLeft (∅ : Set (B1 ⊗[ℂ] B2)) = ⊥ := by
  simp [coefficientLeft]

example : coefficientRight (∅ : Set (B1 ⊗[ℂ] B2)) = ⊥ := by
  simp [coefficientRight]

example (P : Submodule ℂ B1) (Q : Submodule ℂ B2) (x : P) (y : Q) :
    (x : B1) ⊗ₜ[ℂ] (y : B2) ∈ tensorSpan P Q :=
  Submodule.subset_span ⟨x, x.property, y, y.property, rfl⟩

end Coefficients

section SupportAlgebras

variable {B1 B2 B3 : Type*} [CStarAlgebra B1] [CStarAlgebra B2] [CStarAlgebra B3]

/-- First-factor support, without an assumed ambient unit, §IV.C p.10. -/
def supportLeft (M : Set (B1 ⊗[ℂ] B2)) : NonUnitalStarSubalgebra ℂ B1 :=
  NonUnitalStarAlgebra.adjoin ℂ (coefficientLeft M : Set B1)

/-- Second-factor support, without an assumed ambient unit, §IV.C p.10. -/
def supportRight (M : Set (B1 ⊗[ℂ] B2)) : NonUnitalStarSubalgebra ℂ B2 :=
  NonUnitalStarAlgebra.adjoin ℂ (coefficientRight M : Set B2)

example (M : Set (B1 ⊗[ℂ] B2)) (x : B1) (hx : x ∈ coefficientLeft M) :
    x ∈ supportLeft M :=
  NonUnitalStarAlgebra.subset_adjoin ℂ _ hx

example (M : Set (B1 ⊗[ℂ] B2)) (y : B2) (hy : y ∈ coefficientRight M) :
    y ∈ supportRight M :=
  NonUnitalStarAlgebra.subset_adjoin ℂ _ hy

end SupportAlgebras

/-- Rank-one projection onto standard basis vector `i`, §IV.E, PDF p.11. -/
def coordinateProjection {d : ℕ} (i : Fin d) : Mat d :=
  Matrix.diagonal (fun j => if j = i then 1 else 0)

example {d : ℕ} (i : Fin d) : coordinateProjection i i i = 1 := by
  simp [coordinateProjection]

/-- Basis labels for joint blocks and their multiplicity copies, Proposition 13, p.18.
A zero multiplicity contributes no labels. -/
abbrev jointBlockIndex {aCount bCount : ℕ} (n : Fin aCount → ℕ) (m : Fin bCount → ℕ)
    (r : Fin aCount → Fin bCount → ℕ) :=
  Σ i : Fin aCount, Σ j : Fin bCount, ((Fin (n i) × Fin (m j)) × Fin (r i j))

example : Fintype.card (jointBlockIndex (fun _ : Fin 1 => 2) (fun _ : Fin 1 => 3)
    (fun _ _ => 0)) = 0 := by
  simp [jointBlockIndex]

/-- The joint product representation, identity on each multiplicity space, p.18. -/
def jointAction {aCount bCount : ℕ} {n : Fin aCount → ℕ} {m : Fin bCount → ℕ}
    (r : Fin aCount → Fin bCount → ℕ)
    (a : (i : Fin aCount) → Mat (n i)) (b : (j : Fin bCount) → Mat (m j)) :
    Matrix (jointBlockIndex n m r) (jointBlockIndex n m r) ℂ :=
  Matrix.blockDiagonal' (fun i => Matrix.blockDiagonal' (fun j =>
    (a i ⊗ₖ b j) ⊗ₖ (1 : Mat (r i j))))

example {aCount bCount : ℕ} {n : Fin aCount → ℕ} {m : Fin bCount → ℕ}
    (r : Fin aCount → Fin bCount → ℕ)
    (a : (i : Fin aCount) → Mat (n i)) (b : (j : Fin bCount) → Mat (m j)) :
    jointAction r a b = Matrix.blockDiagonal' (fun i => Matrix.blockDiagonal' (fun j =>
      (a i ⊗ₖ b j) ⊗ₖ (1 : Mat (r i j)))) := rfl

/-- Configurations on a cyclic chain of length `extra + 5`, §V.B pp.14--15. -/
abbrev RingConfiguration (extra : ℕ) := Fin (extra + 5) → Bool

/-- Watrous' translation-invariant amplitude product (43), on a finite ring.
Allowing the entire ring as neighborhood makes this the largest such class. -/
def IsWatrous (extra : ℕ)
    (W : Matrix (RingConfiguration extra) (RingConfiguration extra) ℂ) : Prop :=
  ∃ u : Bool → RingConfiguration extra → ℂ,
    ∀ a b, W a b = ∏ x : Fin (extra + 5), u (a x) (fun k => b (x + k))

/-- Sitewise Hadamard in the preferred basis, §V.B, PDF p.14. -/
def ringHadamard (extra : ℕ) :
    Matrix (RingConfiguration extra) (RingConfiguration extra) ℂ :=
  fun a b => ∏ x : Fin (extra + 5),
    (if a x = true ∧ b x = true then (-1 : ℂ) else 1) / (Real.sqrt 2 : ℂ)

/-- Product of nearest-neighbor phase gates at angle pi, §V.B pp.14--15. -/
def ringPhase (extra : ℕ) :
    Matrix (RingConfiguration extra) (RingConfiguration extra) ℂ :=
  Matrix.diagonal (fun b => ∏ x : Fin (extra + 5),
    if b x = true ∧ b (x + 1) = true then (-1 : ℂ) else 1)

example (extra : ℕ) : ringPhase extra (fun _ => false) (fun _ => false) = 1 := by
  simp [ringPhase]

example (extra : ℕ) : IsWatrous extra (fun _ _ => 1) := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro a b
  simp

end QAlgorithms.Papers.Independent.Intakethird100.P96


