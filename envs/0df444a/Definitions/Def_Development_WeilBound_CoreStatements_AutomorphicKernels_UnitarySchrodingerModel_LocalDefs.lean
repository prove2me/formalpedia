-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_UnitarySchrodingerModel_LocalDefs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:52:11.677106+00:00
-- url     : https://prove2.me/theorems/00af3630-54a2-4a6d-bebf-ac52fa4a6104
-- title:
--   Local Defs
-- statement:
--   Definitions and structural lemmas for Local Defs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/UnitarySchrodingerModel/LocalDefs.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology
namespace PositivityTheory.PfSWUS.Loc
variable {R : Type} [CommRing R]
abbrev lev (ϖ : R) (k : ℕ) : Ideal R := Ideal.span {ϖ ^ k}
def cT (σ : R →+* R) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) : Matrix (Fin b) (Fin a) R := (x.map σ).transpose
structure IsUnrQuad (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ) : Prop where
  inv : ∀ a, σ (σ a) = a
  fix_ϖ : σ ϖ = ϖ
  reg : IsSMulRegular R ϖ
  notUnit : ¬ IsUnit ϖ
  sep : ∀ a : R, (∀ k, a ∈ lev ϖ k) → a = 0
  complete : ∀ f : ℕ → R, (∀ k, f (k + 1) - f k ∈ lev ϖ k) → ∃ a, ∀ k, a - f k ∈ lev ϖ k
  fixLocal : ∀ a, σ a = a → a ∉ lev ϖ 1 → IsUnit a
  basis : ∃ u : R, IsUnit (u - σ u) ∧ ∀ a, ∃ x y, σ x = x ∧ σ y = y ∧ a = x + y * u
  one_lt : 1 < q
  card : Nat.card (R ⧸ lev ϖ 1) = q ^ 2
  eps : (ε = -1 ∧ IsField (R ⧸ lev ϖ 1)) ∨ (ε = 1 ∧ ¬ IsField (R ⧸ lev ϖ 1))
def IsUnimod (σ : R →+* R) {m : ℕ} (S : Matrix (Fin m) (Fin m) R) : Prop := cT σ S = S ∧ IsUnit S.det
def IsHermND (σ : R →+* R) (ϖ : R) {n : ℕ} (T : Matrix (Fin n) (Fin n) R) : Prop :=
  cT σ T = T ∧ ∃ k, ϖ ^ k ∈ Ideal.span {T.det}
def red (ϖ : R) (k : ℕ) {a b : ℕ} (x : Matrix (Fin a) (Fin b) R) : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ k) :=
  x.map (Ideal.Quotient.mk (lev ϖ k))
def solCount (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ) : ℕ :=
  Nat.card (red ϖ k '' {x : Matrix (Fin m) (Fin n) R | red ϖ k (cT σ x * S * x) = red ϖ k T})
def hermMod (σ : R →+* R) (ϖ : R) (n k : ℕ) : Set (Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) :=
  red ϖ k '' {h : Matrix (Fin n) (Fin n) R | cT σ h = h}
def densAt (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (k : ℕ) : ℝ :=
  (solCount σ ϖ S T k : ℝ) * (Nat.card (hermMod σ ϖ n k) : ℝ) /
    (Nat.card (Matrix (Fin m) (Fin n) (R ⧸ lev ϖ k)) : ℝ)
def IsDens (σ : R →+* R) (ϖ : R) {m n : ℕ} (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) (α : ℝ) : Prop :=
  Tendsto (densAt σ ϖ S T) atTop (𝓝 α)
structure IsLevelChars (σ : R →+* R) (ϖ : R) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) : Prop where
  compat : ∀ k a, ψ (k + 1) (Ideal.Quotient.mk _ (ϖ * a)) = ψ k (Ideal.Quotient.mk _ a)
  prim : ∀ a, σ a = a → (∀ b, σ b = b → ψ 1 (Ideal.Quotient.mk _ (a * b)) = 1) → a ∈ lev ϖ 1
def nuAt (ϖ : R) {n k : ℕ} (B : Matrix (Fin n) (Fin n) (R ⧸ lev ϖ k)) : ℕ :=
  Nat.card (Set.range fun x : Fin n → R ⧸ lev ϖ k => Matrix.vecMul x B)
def siegAt (ϖ : R) (σ : R →+* R) (ψ : ∀ k, AddChar (R ⧸ lev ϖ k) ℂ) (q : ℕ) (ε : ℤ) (m : ℕ) {n : ℕ}
    (T : Matrix (Fin n) (Fin n) R) (k : ℕ) : ℂ :=
  ∑' B : hermMod σ ϖ n k, ψ k (Matrix.trace (red ϖ k T * B.1)) *
    (((ε : ℂ) ^ m * (q : ℂ) ^ (-(m : ℤ))) ^ Nat.log (q ^ 2) (nuAt ϖ B.1))
def OrthCount : Prop :=
  ∀ (M X : Type) [AddCommGroup M] [Fintype M] [Fintype X] [DecidableEq M] (Q : X → M) (t : M),
    ((Finset.univ.filter fun x => Q x = t).card : ℂ) * (Fintype.card M : ℂ) = ∑' χ : AddChar M ℂ, ∑ x, χ (Q x - t)
def DensStab : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε →
  ∀ (m n : ℕ) (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R), IsUnimod σ S → IsHermND σ ϖ T →
    ∃ k₀, ∀ k ≥ k₀, densAt σ ϖ S T k = densAt σ ϖ S T k₀
def SiegelSeriesConv : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε →
  ∀ ψ, IsLevelChars σ ϖ ψ → ∀ (m n : ℕ), n < m → ∀ T : Matrix (Fin n) (Fin n) R, IsHermND σ ϖ T →
    ∃ b : ℂ, Tendsto (siegAt ϖ σ ψ q ε m T) atTop (𝓝 b)
def SeriesEqDens : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε →
  ∀ ψ, IsLevelChars σ ϖ ψ → ∀ (m n : ℕ), n < m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R),
    IsUnimod σ S → IsHermND σ ϖ T → ∀ α : ℝ, IsDens σ ϖ S T α →
      Tendsto (siegAt ϖ σ ψ q ε m T) atTop (𝓝 (α : ℂ))
def UnrFormula : Prop :=
  ∀ (R : Type) [CommRing R] (σ : R →+* R) (ϖ : R) (q : ℕ) (ε : ℤ), IsUnrQuad R σ ϖ q ε →
  ∀ (m n : ℕ), n ≤ m → ∀ (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R),
    IsUnimod σ S → IsUnimod σ T →
      IsDens σ ϖ S T (∏ i : Fin n, (1 - ((ε : ℝ) / q) ^ (m - (i : ℕ))))
end PositivityTheory.PfSWUS.Loc
end


