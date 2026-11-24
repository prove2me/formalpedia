-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
-- name    : Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T22:08:59.095513+00:00
-- url     : https://prove2.me/theorems/f1189c53-5243-4ead-a902-687e71a70b7f
-- title:
--   Contr Factor
-- statement:
--   Definitions and structural lemmas for Contr Factor, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/LatticeFrames/ContrFactor.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
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
namespace GlobalTheory.LocFlat
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
section Ops
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
variable {n n' n'' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n''] {c : ℕ}
def colAt (n' : Type) (c p : ℕ) (y : n → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 (Matrix.of fun r i => if i.val + 1 = p then y r else 0) 0 0
def rowAt (n : Type) (c p : ℕ) (u : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = p then u s else 0) 0
def flCol (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix n (n' ⊕ Unit) k) : ℂ :=
  opE ψ ν p (fun z => Φ (z + colAt n' c p fun r => x r (Sum.inr ()))) x.toCols₁
def flRow (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ) (Φ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ)
    (x : Matrix (n ⊕ Unit) n' k) : ℂ :=
  opE ψ ν p (fun z => Φ (z + rowAt n c p (x (Sum.inr ())))) x.toRows₁
def contr (ψ : AddChar k Circle) (ν : Measure k) (Ψ₁ : Matrix n (n' ⊕ Unit) k → ℂ) (Ψ₂ : Matrix (n'' ⊕ Unit) n k → ℂ)
    (p : Matrix n n' k × Matrix n'' n k) : ℂ :=
  ∫ u : n → k, Ψ₂ (fromRows p.2 (Matrix.of fun _ => u)) *
    hat ψ ν (-1) (fun y => Ψ₁ (fromCols p.1 (Matrix.of fun r _ => y r))) u ∂(Measure.pi fun _ => ν)
end Ops
section Chain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
def SupportAt : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    h ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)) → ∀ x₀ e,
      (S.T t).Phi j (c + 1) (by omega) ((h⁻¹).val * affPt p x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) p, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u
variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
def ClassAt : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j (c + 1) (by omega))) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) p, ∃ u ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)), h = r * u
def CosetAt : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c + 1 → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    opE S.ψ ν p (om (S.μ (j + 1)) 1 h ((S.T t).Phi j (c + 1) (by omega))) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) p, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u
def SamePos : Prop :=
  ∀ j c (H : j + 1 + c = s) (p : ℕ), 1 ≤ p → p ≤ c → p ≤ S.ρ → ∃ C : ℝ, 0 < C ∧
    opE S.ψ ν (p + 1) ((S.T t).Phi j (c + 1) (by omega)) = (C : ℂ) • opE S.ψ ν p ((S.T t).Phi j (c + 1) (by omega))
open Classical in

def PureCol : Prop :=
  ∀ j c (H : j + 1 + c = s) (r : ℕ), c + 1 = 2 * r → ∃ C : ℝ, 0 < C ∧ ∀ x,
    flCol S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
      (C : ℂ) * (S.T t).entry S.ψ ν j c H 1 1 x.toCols₁ *
        (if (fun a => x a (Sum.inr ())) ∈ box (XIx (Fin κ) t (j + 1)) (S.ϖ ^ r)⁻¹ then 1 else 0)
open Classical in

def PureRow : Prop :=
  ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∃ C : ℝ, 0 < C ∧ ∀ x,
    flRow S.ψ ν (r + 1) ((S.T t).Phi j (c + 1) (by omega)) x =
      (C : ℂ) * (S.T t).entry S.ψ ν j c H 1 1 x.toRows₁ *
        (if x (Sum.inr ()) ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) then 1 else 0)
def SuppCol : Prop :=
  ∀ j c (H : j + 1 + c = s) (r : ℕ), c + 1 = 2 * r → ∀ h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k,
    flCol S.ψ ν (r + 1) (om (S.μ (j + 1)) 1 h ((S.T t).Phi j (c + 1) (by omega))) ≠ 0 →
      ∃ β, ∃ q ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) (r + 1), ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J,
        h = colE (c + 1) (r + 1) β * q * u
def DoubleStep : Prop :=
  ∀ j c (H : j + 1 + 1 + c = s) (r : ℕ), c = 2 * r →
    (∀ h : GL (XIx (Fin κ) t (j + 1 + 1) ⊕ Fin (c + 1)) k,
      contr S.ψ ν (flCol S.ψ ν (r + 1 + 1) ((S.T t).Phi j (c + 1 + 1) (by omega)))
        (flRow S.ψ ν (r + 1) (om (S.μ (j + 1 + 1)) 1 h ((S.T t).Phi (j + 1) (c + 1) (by omega)))) ≠ 0 →
      ∃ q ∈ R k (XIx (Fin κ) t (j + 1 + 1)) (c + 1) (r + 1),
        ∃ u ∈ ((S.T t).lev (j + 1 + 1) (c + 1) (by omega)).J, h = q * u) ∧
    ∃ C : ℝ, 0 < C ∧ ∀ p,
      contr S.ψ ν (flCol S.ψ ν (r + 1 + 1) ((S.T t).Phi j (c + 1 + 1) (by omega)))
        (flRow S.ψ ν (r + 1) ((S.T t).Phi (j + 1) (c + 1) (by omega))) p =
      (C : ℂ) * (S.T t).entry S.ψ ν j (c + 1) (by omega) 1 1 p.1 * (S.T t).entry S.ψ ν (j + 1) c H 1 1 p.2
end Chain
def SymCollapse : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      SuppCol S t ν ∧ PureCol S t ν ∧ PureRow S t ν ∧ DoubleStep S t ν
def ContrFactor : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k),
    Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure →
  ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (M : Type) [AddCommGroup M] [Module ℂ M]
    (B : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] M),
    (∀ (u₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂', (∀ x, Ψ₁'.1 x = (ψ (-(u₀ ⬝ᵥ fun r => x r (Sum.inr ()))) : ℂ) * Ψ₁.1 x) →
      (∀ x, Ψ₂'.1 x = Ψ₂.1 (x + fromRows 0 (Matrix.of fun _ => u₀))) → B Ψ₁' Ψ₂' = B Ψ₁ Ψ₂) →
    (∀ (y₀ : n → k) Ψ₁ Ψ₁' Ψ₂ Ψ₂', (∀ x, Ψ₁'.1 x = Ψ₁.1 (x + fromCols 0 (Matrix.of fun r _ => y₀ r))) →
      (∀ x, Ψ₂'.1 x = (ψ (-(x (Sum.inr ()) ⬝ᵥ y₀)) : ℂ) * Ψ₂.1 x) → B Ψ₁' Ψ₂' = B Ψ₁ Ψ₂) →
    ∃ Λ : SB (Matrix n n' k × Matrix n'' n k) →ₗ[ℂ] M, ∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix n n' k × Matrix n'' n k),
      Ξ.1 = contr ψ ν Ψ₁.1 Ψ₂.1 ∧ B Ψ₁ Ψ₂ = Λ Ξ
end GlobalTheory.LocFlat


