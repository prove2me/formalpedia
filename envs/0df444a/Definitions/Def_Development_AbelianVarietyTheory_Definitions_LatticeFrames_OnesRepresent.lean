-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:00:01.427806+00:00
-- url     : https://prove2.me/theorems/e9c5c49a-5d57-4e6b-a7ce-1ff85a9126aa
-- title:
--   Ones Represent
-- statement:
--   Definitions and structural lemmas for Ones Represent, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/OnesRepresent.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.SymChain
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
structure SymData (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) where

  ψ : AddChar k Circle

  ϖ : kˣ

  ρ : ℕ

  P : TypeDatum k (Fin κ ⊕ Fin (s + 1))

  μ : ℕ → kˣ →* ℂˣ
  tame : ∀ j, IsTame (μ j)
  cond : HasConductor ψ 1
  unif : IsUnif ϖ
  odd : s + 1 = 2 * ρ + 1
  sym : IsSymLevel ψ ϖ ρ P
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
def FreeTop (ρ : ℕ) {κ l : ℕ} : Fin κ ⊕ Fin l → Fin κ ⊕ Fin l → Prop
  | .inl i, .inl j => i < j
  | .inr i, .inl _ => i.val < ρ
  | .inl _, .inr j => ρ < j.val
  | .inr i, .inr j => i < j
def FreeIx (ρ : ℕ) {κ l j : ℕ} {t : Type} : Ix (Fin κ ⊕ Fin l) t j → Ix (Fin κ ⊕ Fin l) t j → Prop
  | .inl a, .inl b => FreeTop ρ a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr p, .inr p' => p.1 ≤ p'.1
namespace SymData
def Pattern : Prop :=
  ∀ j (g : GL (Ix (Fin κ ⊕ Fin (s + 1)) t j) k), g ∈ (S.P.iter t S.μ S.tame j).J ↔
    g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx S.ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1
abbrev T : Chain k s (XIx (Fin κ) t) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) := typeChain t S.ϖ S.P S.μ S.tame
def y0 : XIx (Fin κ) t (s + 1) → k := Pi.single (Sum.inl (Sum.inr 0)) ((S.ϖ⁻¹ : kˣ) : k)
def PrLevel : Prop :=
  ∀ j c (h : j + c = s + 1), prX (Cgrp ((S.T t).lev j c h).J 1) = ((S.T t).lev j c h).J.comap (embX c)
def OneCoupling : Prop :=
  (∀ x₀ y, (S.T t).Psi 1 x₀ y ≠ 0 → y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)) ∧
  (∀ x₀ y, y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) → (S.T t).Psi 1 x₀ y = (S.T t).Psi 1 x₀ (S.y0 t)) ∧
  ∀ γ : GL (XIx (Fin κ) t (s + 1)) k, embX 0 γ ∈ ((S.T t).lev (s + 1) 0 rfl).J →
    γ.val *ᵥ S.y0 t - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)
def SupportOne : Prop :=
  ∀ j c (H : j + 1 + c = s) (h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k),
    h ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)) → ∀ x₀ e,
      (S.T t).Phi j (c + 1) (by omega) ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) 1, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
def OneClass : Prop :=
  ∀ j c (H : j + 1 + c = s) (h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k),
    flat S.ψ ν (S.μ (j + 1)) ((S.T t).Phi j (c + 1) (by omega)) 1 h ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) 1, ∃ u ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)), h = r * u
def OneIndex : Prop :=
  ∀ j c (h : j + 1 + c = s), ∀ β ∈ (S.T t).idx S.ψ ν j c h 1,
    β = DoubleCoset.mk (R k (XIx (Fin κ) t (j + 1)) (c + 1) 1) ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1
def NonZero : Prop :=
  (∀ j c (h : j + 1 + c = s), (S.T t).entry S.ψ ν j c h 1 1 ≠ 0) ∧ ∃ x₀, (S.T t).Psi 1 x₀ (S.y0 t) ≠ 0
def OnesRepresent : Prop := (S.T t).IsRepSystem (fun _ _ _ => {1}) S.ψ ν
open Classical in

def PureTransform : Prop :=
  ∀ ε : k, valuation k ε = 1 → ∀ x₀ η,
    hatCol S.ψ ν ε ((S.T t).Phi s 0 rfl) x₀ η =
      (S.T t).Psi 1 x₀ (S.y0 t) * (if ∀ i, η i ∈ 𝒪[k] then (S.ψ (ε * (η ⬝ᵥ S.y0 t)) : ℂ) else 0)
end SymData
def AtMostOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      S.OneIndex t ν ∧ S.PrLevel t ∧ S.OneCoupling t
def Collapse : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), HasConductor ψ 1 → IsUnitVol ν →
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ), 1 ≤ c →
  ∀ (μ : kˣ →* ℂˣ) (P : Level (GL (n ⊕ Fin c) k)) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ ∈ SB _ → IsCO P.J →
    (∀ h : P.J, om μ 1 (h : GL (n ⊕ Fin c) k) Φ = (((P.lam h)⁻¹ : ℂˣ) : ℂ) • Φ) →
    (∀ β ∈ idxAt ψ ν μ Φ P.J 1, β = DoubleCoset.mk (R k n c 1) P.J 1) →
  ∀ (bas : GL (n ⊕ Fin c) k) (m : Measure (GL n k)), m.IsHaarMeasure →
  ∀ (μG : Measure (GL (n ⊕ Fin c) k)), μG.IsHaarMeasure →
  ∃ C : ℝ, 0 < C ∧
    ∀ (V' V A : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
      (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
      (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) (b : V →ₗ[ℂ] A →ₗ[ℂ] ℂ),
      (∀ γ φ (Ψ Ψ' : SB (Matrix n n' k)), Ψ'.1 = om μ 1 γ Ψ.1 → θ φ Ψ' = π γ (θ φ Ψ)) → IsPos ψ 1 π σ b →
      ∀ (φ : V') (v : A), (∀ h : P.J, σ (h : GL (n ⊕ Fin c) k) v = (P.lam h : ℂ) • v) →
      ∀ f : GL (n ⊕ Fin c) k → ℂ, (∀ h (Ψ : SB (Matrix n n' k)), Ψ.1 = flat ψ ν μ Φ 1 h → f h = b (θ φ Ψ) (σ h v)) →
      ∀ Ξ : SB (Matrix n n' k), Ξ.1 = xi ψ ν μ Φ P.J bas 1 1 →
      ∀ z : ℂ, IsQuotInt ν m μG 1 f z ↔ z = (C : ℂ) * b (θ φ Ξ) v
def CollapseExact : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), HasConductor ψ 1 → IsUnitVol ν →
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ), 1 ≤ c →
  ∀ (μ : kˣ →* ℂˣ) (P : Level (GL (n ⊕ Fin c) k)) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ), Φ ∈ SB _ → IsCO P.J →
    (∀ h : P.J, om μ 1 (h : GL (n ⊕ Fin c) k) Φ = (((P.lam h)⁻¹ : ℂˣ) : ℂ) • Φ) →
    (∀ β ∈ idxAt ψ ν μ Φ P.J 1, β = DoubleCoset.mk (R k n c 1) P.J 1) →
  ∀ (bas : GL (n ⊕ Fin c) k) (m : Measure (GL n k)), m.IsHaarMeasure →
  ∀ (μG : Measure (GL (n ⊕ Fin c) k)), μG.IsHaarMeasure →
    0 < (μG P.J).toReal ∧ 0 < (m (prX (Cgrp P.J 1))).toReal ∧
    ∀ (V' V A : Type) [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V] [AddCommGroup A] [Module ℂ A]
      (π : Representation ℂ (GL n k) V) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A)
      (θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V) (b : V →ₗ[ℂ] A →ₗ[ℂ] ℂ),
      (∀ γ φ (Ψ Ψ' : SB (Matrix n n' k)), Ψ'.1 = om μ 1 γ Ψ.1 → θ φ Ψ' = π γ (θ φ Ψ)) → IsPos ψ 1 π σ b →
      ∀ (φ : V') (v : A), (∀ h : P.J, σ (h : GL (n ⊕ Fin c) k) v = (P.lam h : ℂ) • v) →
      ∀ f : GL (n ⊕ Fin c) k → ℂ, (∀ h (Ψ : SB (Matrix n n' k)), Ψ.1 = flat ψ ν μ Φ 1 h → f h = b (θ φ Ψ) (σ h v)) →
      ∀ Ξ : SB (Matrix n n' k), Ξ.1 = xi ψ ν μ Φ P.J bas 1 1 →
      ∀ z : ℂ, IsQuotInt ν (rescale ν bas m) μG 1 f z ↔
        z = (((μG P.J).toReal / (m (prX (Cgrp P.J 1))).toReal : ℝ) : ℂ) * b (θ φ Ξ) v
example : FreeTop 1 (κ := 1) (l := 3) (.inr 0) (.inl 0) ∧ ¬ FreeTop 1 (κ := 1) (l := 3) (.inr 1) (.inl 0) := by
  simp [FreeTop]
example : FreeTop 1 (κ := 1) (l := 3) (.inl 0) (.inr 2) ∧ ¬ FreeTop 1 (κ := 1) (l := 3) (.inl 0) (.inr 1) := by
  simp [FreeTop]
example (ρ : ℕ) {κ l : ℕ} (a : Fin κ ⊕ Fin (l + 1)) : ¬ FreeTop ρ a (.inr 0) := by
  rcases a with a | a <;> simp [FreeTop]
end GlobalTheory.SymChain


