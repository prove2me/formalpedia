-- Prove2me | Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
-- name    : Formalism_FormalDegreeBessel_StatementBF
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:21:25.845211+00:00
-- url     : https://prove2.me/theorems/3ed05b97-0567-4143-84f7-7eef9524e80c
-- title:
--   Statement BF
-- statement:
--   Definitions and structural lemmas for Statement BF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalDegreeBessel/StatementBF.lean

import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory TensorProduct
noncomputable section
namespace Formalism.QuantumDeterminants
abbrev Mt (k r : ℕ) := Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ
def dualAct {Wp : Type*} [AddCommGroup Wp] [Module ℂ Wp] {m : ℕ}
    (π : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ Wp) (h : Matrix (Fin m) (Fin m) ℂ)
    (w : Module.Dual ℂ Wp) : Module.Dual ℂ Wp :=
  w ∘ₗ π h⁻¹
def IsBesselFunctional {Vs Wp : Type*} [AddCommGroup Vs] [Module ℂ Vs] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Vs)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Wp)
    (ℓ : Vs ⊗[ℂ] Module.Dual ℂ Wp →ₗ[ℂ] ℂ) : Prop :=
  ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ (v : Vs) (w : Module.Dual ℂ Wp),
    ℓ (σ (h * n) v ⊗ₜ dualAct π h w) = psi k r z c n * ℓ (v ⊗ₜ w)
def IsBesselMap {Vs Wp : Type*} [AddCommGroup Vs] [Module ℂ Vs] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Vs)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Wp)
    (L : Vs →ₗ[ℂ] Wp) : Prop :=
  ∀ h ∈ UWset k r z, ∀ n ∈ Nset k r, ∀ v : Vs,
    L (σ (h * n) v) = psi k r z c n • π h (L v)
def pairing {Vs Wp : Type*} [AddCommGroup Vs] [Module ℂ Vs] [AddCommGroup Wp] [Module ℂ Wp]
    (L : Vs →ₗ[ℂ] Wp) : Vs ⊗[ℂ] Module.Dual ℂ Wp →ₗ[ℂ] ℂ :=
  TensorProduct.lift ((LinearMap.applyₗ (R := ℂ)).compl₁₂ L LinearMap.id).flip.flip
def IsRepOn {Wp : Type*} [AddCommGroup Wp] [Module ℂ Wp] {m : ℕ}
    (U : Set (Matrix (Fin m) (Fin m) ℂ)) (π : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ Wp) : Prop :=
  π 1 = 1 ∧ ∀ a ∈ U, ∀ b ∈ U, π (a * b) = π a * π b
def IsCRepOn {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] {m : ℕ}
    (U : Set (Matrix (Fin m) (Fin m) ℂ)) (π : Matrix (Fin m) (Fin m) ℂ → (Wp →L[ℂ] Wp)) : Prop :=
  π 1 = 1 ∧ ∀ a ∈ U, ∀ b ∈ U, π (a * b) = (π a).comp (π b)
def lmulM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x
def conjM {k r : ℕ} (a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x : Mt k r) : Mt k r :=
  a * Matrix.of x * a⁻¹
def besselJ {Wp Wq : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq]
    [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r))
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Wq →L[ℂ] Wp :=
  ∫ p : (Mt k r × Mt k r) × (Mt k r × Mt k r),
    (psi k r z c (Matrix.of p.1.2) * star (psi k r z' c (Matrix.of p.2.2))) •
      ((π (Matrix.of p.1.1)).comp
        ((F ((Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ * g * Matrix.of p.2.2 * Matrix.of p.2.1)).comp
          (π' (Matrix.of p.2.1)⁻¹)))
    ∂((μW.prod μN).prod (μW'.prod μN))
def Hb (k : ℕ) : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ :=
  Matrix.diagonal fun j => if j = Fin.last k then -1 else 1
def bigCell (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := fun i j =>
  if hj : j.val < r then (if i = esI k r ⟨j.val, hj⟩ then c ⟨j.val, hj⟩ else 0)
  else if hj2 : j.val ≤ r + k then
    (if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
  else
    (if i.val = 2 * r + k - j.val then (star (c ⟨2 * r + k - j.val, by omega⟩))⁻¹ else 0)
def BesselSub : Prop :=
  ∀ (Vs Wp : Type) [AddCommGroup Vs] [Module ℂ Vs] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Vs)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Wp),
    IsBesselFunctional k r z c σ π 0 ∧
    (∀ ℓ₁ ℓ₂, IsBesselFunctional k r z c σ π ℓ₁ → IsBesselFunctional k r z c σ π ℓ₂ →
      IsBesselFunctional k r z c σ π (ℓ₁ + ℓ₂)) ∧
    (∀ (a : ℂ) ℓ, IsBesselFunctional k r z c σ π ℓ → IsBesselFunctional k r z c σ π (a • ℓ))
def BesselMapEquiv : Prop :=
  ∀ (Vs Wp : Type) [AddCommGroup Vs] [Module ℂ Vs] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Vs)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Module.End ℂ Wp),
    inWb k r z → IsRepOn (UWset k r z) π →
    (∀ L : Vs →ₗ[ℂ] Wp, IsBesselMap k r z c σ π L ↔ IsBesselFunctional k r z c σ π (pairing L)) ∧
    (FiniteDimensional ℂ Wp → Function.Bijective (pairing (Vs := Vs) (Wp := Wp)))
def BesselNEquiv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [CompleteSpace Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)),
    inWb k r z → inWb k r z' →
    μN (Nset k r)ᶜ = 0 → (∀ n₀ ∈ Nset k r, μN.map (lmulM n₀) = μN) →
    ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∀ n₀ ∈ Nset k r, ∀ n₀' ∈ Nset k r,
      besselJ k r z z' c π π' μW μN μW' F (n₀ * g * n₀') =
        (psi k r z c n₀ * psi k r z' c n₀') • besselJ k r z z' c π π' μW μN μW' F g
def BesselUEquiv : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [CompleteSpace Wq]
    (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : ℂ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp))
    (π' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wq))
    (μW μN μW' : Measure (Mt k r)) [SigmaFinite μW] [SigmaFinite μN] [SigmaFinite μW']
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wq →L[ℂ] Wp)),
    inWb k r z → inWb k r z' →
    μN (Nset k r)ᶜ = 0 → μW (UWset k r z)ᶜ = 0 → μW' (UWset k r z')ᶜ = 0 →
    (∀ h₀ ∈ UWset k r z, μW.map (lmulM h₀) = μW) →
    (∀ h₀ ∈ UWset k r z', μW'.map (lmulM h₀) = μW') →
    (∀ h₀ ∈ UWset k r z ∪ UWset k r z', μN.map (conjM h₀) = μN) →
    IsCRepOn (UWset k r z) π → IsCRepOn (UWset k r z') π' →
    ∀ (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), ∀ h₀ ∈ UWset k r z, ∀ h₀' ∈ UWset k r z',
      besselJ k r z z' c π π' μW μN μW' F (h₀ * g * h₀') =
        (π h₀).comp ((besselJ k r z z' c π π' μW μN μW' F g).comp (π' h₀'))
def BigCellMem : Prop :=
  ∀ (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    (∀ a, c a ≠ 0) → μᴴ * Hb k * μ = Hb k → bigCell k r c μ ∈ UH (Hpk k r)
def BigCellZhat : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    inWb k r z → inWb k r z' →
    Zhat k r z z' (bigCell k r c μ) = Matrix.diagonal fun a : Fin (r + 1) =>
      if h : a.val < r then c ⟨a.val, h⟩ else herm (Hpk k r) (bigCell k r c μ *ᵥ z') z
def BigCellMinors : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    inWb k r z → inWb k r z' →
    (∀ l : Fin (r + 1), Dmin k r z z' (bigCell k r c μ) ⟨l.val, by omega⟩ =
        ∏ a : Fin r with a.val < l.val, c a) ∧
    ((∀ a, c a ≠ 0) → ∀ a : Fin r, cmin k r z z' (bigCell k r c μ) a = c a) ∧
    ((∀ a, c a ≠ 0) → zeta k r z z' (bigCell k r c μ) = herm (Hpk k r) (bigCell k r c μ *ᵥ z') z)
def Mdim (k r : ℕ) (a : Fin r) : ℕ := 2 * (r - a.val) + k + 1
def bcWeight (k r : ℕ) (T T' : ℝ) (p : (Fin r → ℂ) × ℂ) : ℝ :=
  if T * T' ≤ Complex.normSq p.2 then
    (∏ a : Fin r, ‖p.1 a‖ ^ (2 * (Mdim k r a - 2))) * (Complex.normSq p.2 - T * T') ^ (k - 1)
  else 0
def jNormSq {E : Type*} [NormedAddCommGroup E] (k r : ℕ) (T T' : ℝ) (j : (Fin r → ℂ) × ℂ → E) :
    ENNReal :=
  ∫⁻ p : (Fin r → ℂ) × ℂ, ENNReal.ofReal (bcWeight k r T T' p * ‖j p‖ ^ 2)
def betaBig {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (k r : ℕ) (T T' : ℝ)
    (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (J J' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → E) : ℂ :=
  ∫ p : (Fin r → ℂ) × ℂ, (bcWeight k r T T' p : ℂ) *
    inner ℂ (J' (bigCell k r p.1 (μsec p.2))) (J (bigCell k r p.1 (μsec p.2)))
end Formalism.QuantumDeterminants


