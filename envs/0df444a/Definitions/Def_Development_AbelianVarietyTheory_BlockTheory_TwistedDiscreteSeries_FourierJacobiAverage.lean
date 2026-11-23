-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FourierJacobiAverage
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:03.867609+00:00
-- url     : https://prove2.me/theorems/562dc6c0-44c6-4ade-a1a1-65202269ee28
-- title:
--   Fourier Jacobi Average
-- statement:
--   Definitions and structural lemmas for Fourier Jacobi Average, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/FourierJacobiAverage.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage
open GlobalTheory.SplitWeil GlobalTheory.RootEx
section Algebra
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]
def cenM (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (t : k) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  fromBlocks 1 0 0 (1 + Matrix.of fun l i => if l.val + 1 = p ∧ i.val + 1 = p + 1 then t else 0)
def NFJ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  N k n c ρ ⊔ N k n c (ρ + 1)
def RFJ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  R k n c ρ ⊔ R k n c (ρ + 1)
def schT (β₀ : n → k) (Φ₀ : (n → k) → ℂ) : (n → k) → ℂ := fun β => Φ₀ (β + β₀)
def schM (ψ : AddChar k Circle) (u : n → k) (Φ₀ : (n → k) → ℂ) : (n → k) → ℂ :=
  fun β => (ψ (u ⬝ᵥ β) : ℂ) * Φ₀ β
def colM {n' : Type} (c p : ℕ) (ξ : n → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 (Matrix.of fun r i => if i.val + 1 = p then ξ r else 0) 0 0
def rowM (n : Type) {n' : Type} (c p : ℕ) (u' : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = p then u' s else 0) 0
def twist {P : Type} [AddCommGroup P] [Module ℂ P] (η : kˣ →* ℂˣ) (π : Representation ℂ (GL n k) P) :
    Representation ℂ (GL n k) P where
  toFun g := (η (Matrix.GeneralLinearGroup.det g) : ℂ) • π g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, Units.val_mul, smul_mul_smul_comm]
end Algebra
section Apply
variable {X Z : Type} [TopologicalSpace X] [TopologicalSpace Z] {V : Type} [AddCommGroup V] [Module ℂ V]
open Classical in

def app (l : SB X →ₗ[ℂ] V) (f : X → ℂ) : V := if h : f ∈ SB X then l ⟨f, h⟩ else 0
def HasTensorVal (l : SB X → SB Z → ℂ) (Θ : X → Z → ℂ) (z : ℂ) : Prop :=
  ∃ (m : ℕ) (Ψ : Fin m → SB X) (Φ₀ : Fin m → SB Z),
    (∀ x y, Θ x y = ∑ i, (Ψ i : X → ℂ) x * (Φ₀ i : Z → ℂ) y) ∧ z = ∑ i, l (Ψ i) (Φ₀ i)
end Apply
section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
variable {P A P' A' : Type} [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
  [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A'] [Module ℂ A']
def IsFJ (ψ : AddChar k Circle) (ρ : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ v (β₀ : n → k) (Φ₀ Φ₁ : SB (n → k)), (Φ₁ : (n → k) → ℂ) = schT β₀ Φ₀ →
      fj φ (σ (colE c (ρ + 1) β₀) v) Φ₁ = fj φ v Φ₀) ∧
  (∀ φ v (u : n → k) (Φ₀ Φ₁ : SB (n → k)), (Φ₁ : (n → k) → ℂ) = schM ψ (-u) Φ₀ →
      fj φ (σ (rowE c ρ u) v) Φ₀ = fj φ v Φ₁) ∧
  (∀ φ v (Φ₀ : SB (n → k)), ∀ g ∈ N k n c ρ ⊓ N k n c (ρ + 1),
      fj φ (σ g v) Φ₀ = (ψ (simpleSum g) : ℂ) * fj φ v Φ₀)
def IsFJInv (η : kˣ →* ℂˣ) (s : ℝ) (π : Representation ℂ (GL n k) P) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (g : GL n k) φ v (Φ₀ Φ₁ : SB (n → k)),
    ((Φ₁ : (n → k) → ℂ) = fun β => (η (Matrix.GeneralLinearGroup.det g) : ℂ) *
      ((nabs k (Matrix.GeneralLinearGroup.det g) ^ s : ℝ) : ℂ) * (Φ₀ : (n → k) → ℂ) ((g⁻¹ : GL n k).val *ᵥ β)) →
    fj (π g φ) (σ (embX c g) v) Φ₁ = fj φ v Φ₀
def IsLiftUp (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A')
    (ϑ : A →ₗ[ℂ] SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] A') : Prop :=
  ∀ g h F (Φ Φ₁ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)),
    (Φ₁ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) = om μ g h Φ → ϑ (σ h F) Φ₁ = σ' g (ϑ F Φ)
def IsLiftX (μ : kˣ →* ℂˣ) (π : Representation ℂ (GL n k) P) (π' : Representation ℂ (GL n' k) P')
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) : Prop :=
  ∀ g h φ (Ψ Ψ₁ : SB (Matrix n n' k)), (Ψ₁ : Matrix n n' k → ℂ) = om μ g h Ψ → θ (π' g φ) Ψ₁ = π h (θ φ Ψ)
variable [MeasurableSpace k] [BorelSpace k]
def hat (ψ : AddChar k Circle) (ν : Measure k) (Φ₀ : (n → k) → ℂ) (u : n → k) : ℂ :=
  ∫ β, Φ₀ β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν)
def Represents (ψ : AddChar k Circle) (ν : Measure k) (ρ : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ (ρ + 1) σ (b φ)) ∧ ∀ φ v (Φ₀ : SB (n → k)),
    Integrable (fun β => (Φ₀ : (n → k) → ℂ) β * b φ (σ (colE c (ρ + 1) β) v)) (Measure.pi fun _ => ν) ∧
    fj φ v Φ₀ = ∫ β, (Φ₀ : (n → k) → ℂ) β * b φ (σ (colE c (ρ + 1) β) v) ∂(Measure.pi fun _ => ν)
def ExchangesTo (ψ : AddChar k Circle) (ν : Measure k) (ρ : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (b₀ b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) : Prop :=
  (∀ φ, IsNEquiv ψ ρ σ (b₀ φ)) ∧ ∀ φ v,
    Integrable (fun u => b₀ φ (σ (rowE c ρ u) v)) (Measure.pi fun _ => ν) ∧ b φ v = exUp ν ρ σ (b₀ φ) v
def fl (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (ρ : ℕ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (β : n → k) : ℂ :=
  opE ψ ν (ρ + 1) (om μ 1 (colE c (ρ + 1) β) Φ) x₀
def IsQuotIntFJ (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)) (ρ : ℕ)
    (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ) : Prop :=
  ∃ F ∈ SB (GL (n ⊕ Fin c) k),
    (∀ h, f h = ∫ g, (∫ u : N k n c (ρ + 1), (∫ β : n → k,
      F (embX c g * (u : GL (n ⊕ Fin c) k) * colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν))
        ∂(volN ν n c (ρ + 1))) ∂μX) ∧ z = ∫ h, F h ∂μG
def rInt (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (φ : P') (F : A)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (h : GL (n ⊕ Fin c) k) : ℂ :=
  b (app (θ φ) (opE ψ ν p (om μ 1 h Φ))) (σ h F)
def IdPos (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (μ : kˣ →* ℂˣ) (p : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (ϑ : A →ₗ[ℂ] SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] A')
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (b' : P' →ₗ[ℂ] A' →ₗ[ℂ] ℂ)
    (φ : P') (F : A) : Prop :=
  ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
    IsQuotInt ν μX μG p (rInt ψ ν μ p σ θ b φ F Φ) (b' φ (ϑ F Φ))
def IsFJInt (ψ : AddChar k Circle) (ν : Measure k) (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k))
    (μ : kˣ →* ℂˣ) (ρ : ℕ) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P) (fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (φ : P') (F : A)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (z : ℂ) : Prop :=
  ∃ f : GL (n ⊕ Fin c) k → ℂ,
    (∀ h, HasTensorVal (fun Ψ Φ₀ => fj (θ φ Ψ) (σ h F) Φ₀) (fl ψ ν μ ρ (om μ 1 h Φ)) (f h)) ∧
    IsQuotIntFJ ν μX μG ρ f z
def avg (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (p : ℕ) (Φ₀ : (n' → k) → ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ℂ :=
  ∫ u' : n' → k, hat ψ ν Φ₀ u' * om μ (rowE (c + 1) p u') 1 Φ x ∂(Measure.pi fun _ => ν)
def opEFJ (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ₀ : (n' → k) → ℂ)
    (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) : ℂ :=
  ∫ u' : n' → k, hat ψ ν Φ₀ u' * opE ψ ν p (fun x => Φ (x + rowM n c p u')) x₀ ∂(Measure.pi fun _ => ν)
end Defs
section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
def Heisenberg : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → c = 2 * ρ →
    (∀ g, g ∈ NFJ k n c ρ ↔ ∃ x ∈ N k n c ρ, ∃ y ∈ N k n c (ρ + 1), g = x * y) ∧
    (∃ H : Subgroup (GL (n ⊕ Fin c) k), H ≤ NFJ k n c ρ ∧ ∀ g, g ∈ H ↔ ∃ (u β : n → k) (t : k),
      g.val = (rowE c ρ u).val * (colE c (ρ + 1) β).val * cenM n c ρ t) ∧
    (∀ u β₀ : n → k, (rowE c ρ u * colE c (ρ + 1) β₀).val =
      cenM n c ρ (u ⬝ᵥ β₀) * (colE c (ρ + 1) β₀ * rowE c ρ u).val) ∧
    ∀ ψ : AddChar k Circle, Continuous ψ → ψ ≠ 1 → ∀ (u β₀ : n → k) (Φ₀ : SB (n → k)),
      schT β₀ Φ₀ ∈ SB (n → k) ∧ schM ψ u Φ₀ ∈ SB (n → k) ∧
      schM ψ u (schT β₀ Φ₀) = (ψ (-(u ⬝ᵥ β₀)) : ℂ) • schT β₀ (schM ψ u Φ₀)
def UniqueBessel : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → c = 2 * ρ →
  ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
  ∀ (P A : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A), IsSmoothRep σ →
  ∀ fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ, IsFJ ψ ρ σ fj →
    (∃! b, Represents ψ ν ρ σ fj b) ∧
    ∀ b, Represents ψ ν ρ σ fj b → (∃! b₀, ExchangesTo ψ ν ρ σ b₀ b) ∧
      ∀ b₀, ExchangesTo ψ ν ρ σ b₀ b → ∀ φ v (Φ₀ : SB (n → k)),
        Integrable (fun u => hat ψ ν Φ₀ u * b₀ φ (σ (rowE c ρ u) v)) (Measure.pi fun _ => ν) ∧
        fj φ v Φ₀ = ∫ u, hat ψ ν Φ₀ u * b₀ φ (σ (rowE c ρ u) v) ∂(Measure.pi fun _ => ν)
def Exponents : Prop :=
  ∀ (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), 1 ≤ ρ → c = 2 * ρ →
  ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
  ∀ (P A : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
    (π : Representation ℂ (GL n k) P) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A),
    IsSmoothRep π → IsSmoothRep σ →
  ∀ η : kˣ →* ℂˣ, IsUnram η → (∀ x, ‖(η x : ℂ)‖ = 1) →
  ∀ (fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ),
    IsFJ ψ ρ σ fj → Represents ψ ν ρ σ fj b →
    (∀ s e : ℝ, s + e + 1 = 0 → IsFJInv η s π σ fj → ∀ (g : GL n k) φ v,
      b (twist η π g φ) (σ (embX c g) v) =
        ((nabs k (Matrix.GeneralLinearGroup.det g) ^ e : ℝ) : ℂ) * b φ v) ∧
    (IsFJInv η (-1 / 2) π σ fj → IsPos ψ (ρ + 1) (twist η π) σ b ∧
      ∀ b₀, ExchangesTo ψ ν ρ σ b₀ b → IsPos ψ ρ (twist η π) σ b₀)
def LocalSign : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), 1 ≤ ρ → c = 2 * ρ →
    (∀ g, g ∈ RFJ k n c ρ ↔ ∃ r ∈ R k n c (ρ + 1), ∃ β : n → k, g = r * colE c (ρ + 1) β) ∧
    (∀ m : Measure (RFJ k n c ρ), m.IsHaarMeasure → m.IsMulRightInvariant) ∧
    (∀ (x₀ : Matrix n n' k) (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free (ρ + 1) rs} → k) (β : n → k)
      (r : n) (i : Fin (c + 1)), i.val + 1 = ρ + 1 →
      ((1 - ((colE c (ρ + 1) β).val - 1)) * affPt (ρ + 1) x₀ e :
        Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (Sum.inl r) (Sum.inr i) = -β r) ∧
    ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
      (∀ μ : kˣ →* ℂˣ, Continuous μ → ∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (β : n → k),
        (∀ x, om μ 1 (colE c (ρ + 1) β) Φ.1 x = Φ.1 ((1 - ((colE c (ρ + 1) β).val - 1)) * x)) ∧
        ∀ x₀, fl ψ ν μ ρ Φ.1 x₀ β = opE ψ ν (ρ + 1) (fun x => Φ.1 (x + colM c (ρ + 1) (-β))) x₀) ∧
      ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)), μX.IsHaarMeasure → μG.IsHaarMeasure →
      ∀ (f : GL (n ⊕ Fin c) k → ℂ) (z : ℂ), IsQuotInt ν μX μG (ρ + 1) f z →
        (∀ h, Integrable (fun β : n → k => f (colE c (ρ + 1) β * h)) (Measure.pi fun _ => ν)) ∧
        IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k, f (colE c (ρ + 1) β * h) ∂(Measure.pi fun _ => ν)) z
def Target : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), 1 ≤ ρ → c = 2 * ρ →
  ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
  ∀ μ : kˣ →* ℂˣ, Continuous μ →
  ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)), μX.IsHaarMeasure → μG.IsHaarMeasure →
  ∀ (P A P' A' : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A'] [Module ℂ A']
    (π : Representation ℂ (GL n k) P) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (π' : Representation ℂ (GL n' k) P') (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A'),
    IsSmoothRep π → IsSmoothRep σ → IsSmoothRep π' → IsSmoothRep σ' →
  ∀ (ϑ : A →ₗ[ℂ] SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] A')
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P), IsLiftUp μ σ σ' ϑ → IsLiftX μ π π' θ →
  ∀ (fj : P →ₗ[ℂ] A →ₗ[ℂ] SB (n → k) →ₗ[ℂ] ℂ) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (b' : P' →ₗ[ℂ] A' →ₗ[ℂ] ℂ),
    IsFJ ψ ρ σ fj → Represents ψ ν ρ σ fj b → IsPos ψ (ρ + 1) π σ b → IsPos ψ (ρ + 1) π' σ' b' →
  ∀ (φ : P') (F : A),
    (∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k),
      (∀ h, opE ψ ν (ρ + 1) (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)) ∧
      (∀ h β, (fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) ∈ SB (Matrix n n' k)) ∧
      (∀ h, Integrable (fun β : n → k => b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β)
          (σ (colE c (ρ + 1) β) (σ h F))) (Measure.pi fun _ => ν)) ∧
      ∀ z : ℂ,
        (IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsQuotIntFJ ν μX μG ρ (fun h => ∫ β : n → k,
            b (app (θ φ) fun x₀ => fl ψ ν μ ρ (om μ 1 h Φ.1) x₀ β) (σ (colE c (ρ + 1) β) (σ h F))
              ∂(Measure.pi fun _ => ν)) z) ∧
        (IsQuotInt ν μX μG (ρ + 1) (rInt ψ ν μ (ρ + 1) σ θ b φ F Φ.1) z ↔
          IsFJInt ψ ν μX μG μ ρ σ θ fj φ F Φ.1 z)) ∧
    (IdPos ψ ν μX μG μ (ρ + 1) σ ϑ θ b b' φ F ↔
      ∀ Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k), IsFJInt ψ ν μX μG μ ρ σ θ fj φ F Φ.1 (b' φ (ϑ F Φ)))
def Source : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ), c + 1 = 2 * ρ →
  ∀ (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → IsSelfDual ψ ν →
  ∀ μ : kˣ →* ℂˣ, Continuous μ →
  ∀ (μX : Measure (GL n k)) (μG : Measure (GL (n ⊕ Fin c) k)), μX.IsHaarMeasure → μG.IsHaarMeasure →
  ∀ (P A P' A' : Type) [AddCommGroup P] [Module ℂ P] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup P'] [Module ℂ P'] [AddCommGroup A'] [Module ℂ A']
    (π : Representation ℂ (GL n k) P) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
    (π' : Representation ℂ (GL n' k) P') (σ' : Representation ℂ (GL (n' ⊕ Fin (c + 1)) k) A'),
    IsSmoothRep π → IsSmoothRep σ → IsSmoothRep π' → IsSmoothRep σ' →
  ∀ (ϑ : A →ₗ[ℂ] SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] A')
    (θ : P' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] P), IsLiftUp μ σ σ' ϑ → IsLiftX μ π π' θ →
  ∀ (fj' : P' →ₗ[ℂ] A' →ₗ[ℂ] SB (n' → k) →ₗ[ℂ] ℂ) (b : P →ₗ[ℂ] A →ₗ[ℂ] ℂ) (b' : P' →ₗ[ℂ] A' →ₗ[ℂ] ℂ),
    IsPos ψ ρ π σ b → IsPos ψ ρ π' σ' b' →
    (∀ φ v' (Φ₀ : SB (n' → k)),
      fj' φ v' Φ₀ = ∫ u', hat ψ ν Φ₀ u' * b' φ (σ' (rowE (c + 1) ρ u') v') ∂(Measure.pi fun _ => ν)) →
  ∀ (φ : P') (F : A),
    (∀ m : Measure (R k n c ρ), m.IsHaarMeasure → m.IsMulRightInvariant) ∧
    (∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Φ₀ : SB (n' → k)),
      avg ψ ν μ ρ Φ₀ Φ.1 ∈ SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) ∧
      (∀ h, opE ψ ν ρ (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)) ∧
      (∀ h, opEFJ ψ ν ρ Φ₀ (om μ 1 h Φ.1) ∈ SB (Matrix n n' k)) ∧
      (∀ h, opE ψ ν ρ (om μ 1 h (avg ψ ν μ ρ Φ₀ Φ.1)) = opEFJ ψ ν ρ Φ₀ (om μ 1 h Φ.1)) ∧
      fj' φ (ϑ F Φ) Φ₀ = b' φ (app (ϑ F) (avg ψ ν μ ρ Φ₀ Φ.1))) ∧
    ((∀ (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (Φ₀ : SB (n' → k)),
        IsQuotInt ν μX μG ρ (fun h => b (app (θ φ) (opEFJ ψ ν ρ Φ₀ (om μ 1 h Φ.1))) (σ h F)) (fj' φ (ϑ F Φ) Φ₀)) ↔
      IdPos ψ ν μX μG μ ρ σ ϑ θ b b' φ F)
end Statements
def FourierJacobiBessel : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k],
    Heisenberg k ∧ UniqueBessel k ∧ Exponents k ∧ LocalSign k ∧ Target k ∧ Source k
example {k n : Type} [Field k] [Fintype n] [DecidableEq n] (ψ : AddChar k Circle) (u β₀ : n → k)
    (Φ₀ : (n → k) → ℂ) : schM ψ u (schT β₀ Φ₀) = (ψ (-(u ⬝ᵥ β₀)) : ℂ) • schT β₀ (schM ψ u Φ₀) := by
  funext β
  simp only [schM, schT, Pi.smul_apply, smul_eq_mul, dotProduct_add, ← mul_assoc, ← Circle.coe_mul,
    ← AddChar.map_add_eq_mul]
  congr 3
  ring
example {k n n' : Type} [Field k] {c p : ℕ} (x : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) (ξ : n → k) (u' : n' → k) :
    ch (x + colM c p ξ) = ch x ∧ ch (x + rowM n c p u') = ch x := by
  simp [ch, colM, rowM]
end GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage


