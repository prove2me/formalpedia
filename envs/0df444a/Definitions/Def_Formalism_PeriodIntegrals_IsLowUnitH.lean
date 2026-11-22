-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
-- name    : Formalism_PeriodIntegrals_IsLowUnitH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:19:01.391118+00:00
-- url     : https://prove2.me/theorems/d67b736a-bcf4-431b-bac5-dff1c8417c7c
-- title:
--   Is Low Unit H
-- statement:
--   Definitions and structural lemmas for Is Low Unit H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/IsLowUnitH.lean

import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff ComplexOrder
noncomputable section
namespace PI.UpqRep
def rdM {m : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (X : Matrix (Fin m) (Fin m) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ → V) : Matrix (Fin m) (Fin m) ℂ → V :=
  fun g => deriv (fun t : ℝ => f (g * NormedSpace.exp ((t : ℂ) • X))) 0
section KF
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsKFin {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S
end KF
def thetaJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Xᴴ * Jm ε)
def reJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (1 / 2 : ℂ) • (X + thetaJ ε X)
def imJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (-(Complex.I / 2)) • (X - thetaJ ε X)
def rdC {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => rdM (reJ ε X) f g + Complex.I * rdM (imJ ε X) f g
def rdCWord {n : ℕ} (ε : Fin n → Bool) :
    List (Matrix (Fin n) (Fin n) ℂ) → (Matrix (Fin n) (Fin n) ℂ → ℂ) → Matrix (Fin n) (Fin n) ℂ → ℂ
  | [], f => f
  | X :: w, f => rdC ε X (rdCWord ε w f)
def gelfandOp {n : ℕ} (ε : Fin n → Bool) (k : ℕ) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Matrix (Fin n) (Fin n) ℂ → ℂ :=
  fun g => ∑ a : Fin (k + 1) → Fin n,
    rdCWord ε (List.ofFn fun i : Fin (k + 1) => Matrix.single (a i) (a (finRotate (k + 1) i)) (1 : ℂ)) f g
def IsDSCoef {n : ℕ} (ε : Fin n → Bool) (φ : UJ ε → ℂ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v w : H),
    Nontrivial H ∧ IsURepOn (UJset ε) σ ∧ IsIrredOn (UJset ε) σ ∧ IsSqIntOn ε σ ∧ φ = coefOn σ v w
def IsSq {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin n → Bool)
    (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Nontrivial H ∧ IsURepOn (UJset ε) σ' ∧ IsIrredOn (UJset ε) σ' ∧ IsSqIntOn ε σ'
def IsEquiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)
section Eig
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def HasInfChar (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (c : ℕ → ℂ) : Prop :=
  ∀ v w : H, IsKFin ε σ' v → ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪w, σ' g v⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g
def Sph (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ k₁ ∈ Kset ε, ∀ k₂ ∈ Kset ε, ∀ g ∈ UJset ε, Ψ (k₁ * g * k₂) = σ k₁ ∘L Ψ g ∘L σ k₂
def Compr (ε : Fin n → Bool) (E : H →L[ℂ] H) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ g ∈ UJset ε, E ∘L Ψ g ∘L E = Ψ g
def Eig (ε : Fin n → Bool) (c : ℕ → ℂ) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ F : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
    (∀ g ∈ UJset ε, F g = ⟪x, Ψ g y⟫_ℂ) ∧ ∀ (k : ℕ), ∀ g ∈ UJset ε, gelfandOp ε k F g = c k * F g
def DSSum (ε : Fin n → Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∀ x y : H, ∃ (N : ℕ) (φ : Fin N → UJ ε → ℂ), (∀ i, IsDSCoef ε (φ i)) ∧
    ∀ g : UJ ε, ⟪x, Ψ (umat g) y⟫_ℂ = ∑ i, φ i g
end Eig
def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩
def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩
def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩
def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1
def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)
def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0
def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re
def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}
def blockW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if hi : r ≤ i.val ∧ i.val < r + k then
      (if hj : r ≤ j.val ∧ j.val < r + k then h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
    else (if i = j then 1 else 0)
def IsFrameW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z
section Second
variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ g, IsFrameW k r z g ∧ IsHCTypeU k u (fun h => π (g * blockW k r h * g⁻¹))
def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0
def dsig (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0
def dsigW (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)
def IsLowUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w
end Second
end PI.UpqRep
end


