-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OmegaColumnSlices
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_OmegaColumnSlices
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T22:33:25.798607+00:00
-- url     : https://prove2.me/theorems/a65c7866-8934-4cef-9c42-3d673809c6f0
-- title:
--   Omega Column Slices
-- statement:
--   Definitions and structural lemmas for Omega Column Slices, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/OmegaColumnSlices.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_box_one
import Theorems.Thm_GlobalTheory_StepData_mem_latOf_typeFrame

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
section Lattices
variable {k : Type} [Field k] [ValuativeRel k] {a b : Type} [Fintype a]
def Maps (Λ' : Submodule 𝒪[k] (a → k)) (Λ : Submodule 𝒪[k] (b → k)) (x : Matrix b a k) : Prop :=
  ∀ v ∈ Λ', x *ᵥ v ∈ Λ
def InjMod (ϖ : kˣ) (Λ' : Submodule 𝒪[k] (a → k)) (Λ : Submodule 𝒪[k] (b → k)) (x : Matrix b a k) : Prop :=
  Maps Λ' Λ x ∧ ∀ v ∈ Λ', (∃ w ∈ Λ, x *ᵥ v = (ϖ : k) • w) → ∃ v' ∈ Λ', v = (ϖ : k) • v'
def Shaped (ϖ : kˣ) (Λ' : Submodule 𝒪[k] (a → k)) (Λ : Submodule 𝒪[k] (b → k)) (f : Matrix b a k → ℂ) : Prop :=
  (∀ x, f x ≠ 0 → Maps Λ' Λ x) ∧ (∀ x y, Maps Λ' Λ y → f (x + (ϖ : k) • y) = f x) ∧
    ∀ x, f x ≠ 0 → InjMod ϖ Λ' Λ x
def dualStd (k : Type) [Field k] [ValuativeRel k] (a : Type) [Fintype a] : Set (a → k) :=
  {η | ∀ y ∈ box a (1 : kˣ), η ⬝ᵥ y ∈ 𝒪[k]}
def addLine (Λ : Submodule 𝒪[k] (b → k)) : Submodule 𝒪[k] (b ⊕ Unit → k) :=
  Λ.comap (LinearMap.funLeft 𝒪[k] k Sum.inl) ⊓ (box Unit (1 : kˣ)).comap (LinearMap.funLeft 𝒪[k] k Sum.inr)
def srcLat (a : Type) (ϖ : kˣ) : Submodule 𝒪[k] (a ⊕ Fin (0 + 1) → k) :=
  (box a (1 : kˣ)).comap (LinearMap.funLeft 𝒪[k] k Sum.inl) ⊓
    (box (Fin (0 + 1)) ϖ).comap (LinearMap.funLeft 𝒪[k] k Sum.inr)
def cosets (S M : Submodule 𝒪[k] (b → k)) : Set ((b → k) ⧸ M) :=
  {yb | ∃ y ∈ S, Submodule.Quotient.mk y = yb}
end Lattices
section Line
variable {k : Type} [Field k] {n n' : Type}
def tens (Φ₀ : Matrix n n' k → ℂ) (φ : (n → k) → ℂ) : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ :=
  fun x => Φ₀ x.toBlocks₁₁ * φ fun r => x (.inl r) (.inr 0)
def asCol (φ : (n → k) → ℂ) : Matrix n Unit k → ℂ := fun x => φ fun r => x r ()
def asRow (φ : (n → k) → ℂ) : Matrix Unit n k → ℂ := fun x => φ (x ())
def slice [ValuativeRel k] (Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ) (M : Submodule 𝒪[k] (n → k))
    (yb : (n → k) ⧸ M) : Matrix n n' k → ℂ := fun x₀ => Ψ (withCol x₀ (Quotient.out yb))
variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n]
def omCol (μz : kˣ →* ℂˣ) (h : GL n k) (φ : (n → k) → ℂ) : (n → k) → ℂ := fun y =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * φ ((h⁻¹).val *ᵥ y)
def omRow (μz : kˣ →* ℂˣ) (h : GL n k) (φ' : (n → k) → ℂ) : (n → k) → ℂ := fun η =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ' (η ᵥ* h.val)
end Line
section Pen
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
def ResidueFun (ϖ : kˣ) (Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ) : Prop :=
  (∀ x₀ y', Ψ (withCol x₀ y') ≠ 0 → (∀ i j, x₀ i j ∈ 𝒪[k]) ∧ ∀ i, (ϖ : k) * y' i ∈ 𝒪[k]) ∧
    ∃ Ψb : Matrix n n' 𝓀[k] → (n → 𝓀[k]) → ℂ, ∀ (x₀ : Matrix n n' 𝒪[k]) (y : n → 𝒪[k]),
      Ψ (withCol (x₀.map (algebraMap 𝒪[k] k)) fun i => ((ϖ⁻¹ : kˣ) : k) * (y i : k)) =
        Ψb (x₀.map (IsLocalRing.residue 𝒪[k])) fun i => IsLocalRing.residue 𝒪[k] (y i)
def PenStep (ψ : AddChar k Circle) (ν : Measure k) (ε : k) (ϖ : kˣ)
    (Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ) : Prop :=

  ResidueFun ϖ Ψ ∧

  (∀ x₀ y', slice Ψ (box n 1) (Submodule.Quotient.mk y') x₀ = Ψ (withCol x₀ y')) ∧
  (∃ F : Finset ((n → k) ⧸ box n (1 : kˣ)), (F : Set _) = cosets (box n ϖ⁻¹) (box n 1) ∧

    (∀ yb ∈ F, slice Ψ (box n 1) yb ∈ SB (Matrix n n' k) ∧ cosetInd (box n 1) yb ∈ SB (n → k)) ∧
    Ψ = ∑ yb ∈ F, tens (slice Ψ (box n 1) yb) (cosetInd (box n 1) yb) ∧

    (∀ x₀ η, Integrable (fun y' => Ψ (withCol x₀ y') * (ψ (ε * (η ⬝ᵥ y')) : ℂ)) (Measure.pi fun _ => ν)) ∧
    ∀ (pt : ((n → k) ⧸ box n (1 : kˣ)) → n → k), (∀ yb, Submodule.Quotient.mk (pt yb) = yb) → ∀ x₀ η,
      hatCol ψ ν ε Ψ x₀ η = (dualStd k n).indicator
        (fun η => ∑ yb ∈ F, Ψ (withCol x₀ (pt yb)) * (ψ (ε * (η ⬝ᵥ pt yb)) : ℂ)) η) ∧

  (∀ x₀ η, hatCol ψ ν ε Ψ x₀ η ≠ 0 → η ∈ dualStd k n) ∧

  (∀ x₀ η, ∀ η' ∈ dualStd k n, hatCol ψ ν ε Ψ x₀ (η + (ϖ : k) • η') = hatCol ψ ν ε Ψ x₀ η) ∧

  (∀ x₀ η, hatCol ψ ν ε Ψ x₀ η ∈ Subring.closure ({ζ : ℂ | ζ ^ ringChar 𝓀[k] = 1} ∪ Set.range Ψ)) ∧

  ∀ x₀ η, hatCol ψ ν ε Ψ x₀ η ≠ 0 → InjMod ϖ (box n' 1) (box n 1) x₀
variable (n n') in

def Intertwining (ψ : AddChar k Circle) (ν : Measure k) (ε : k) : Prop :=
  ∀ (μ' μz : kˣ →* ℂˣ) (h : GL n k),
    (∀ Φ₀ ∈ SB (Matrix n n' k), ∀ φ ∈ SB (n → k),
      om (μ' * μz) 1 (embX 0 h) (tens Φ₀ φ) = tens (om μ' 1 h Φ₀) (omCol μz h φ)) ∧
    (∀ φ ∈ SB (n → k), om μz 1 h (asCol φ) = asCol (omCol μz h φ)) ∧
    (∀ φ' ∈ SB (n → k), om μz⁻¹ h 1 (asRow φ') = asRow (omRow μz h φ')) ∧
    ∀ φ ∈ SB (n → k), hat ψ ν ε φ ∈ SB (n → k) ∧ hat ψ ν ε (omCol μz h φ) = omRow μz h (hat ψ ν ε φ)
end Pen
section Top
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
def topDatum (T : Chain k s X Z) (ψ : AddChar k Circle) (ν : Measure k) (ε : k)
    (Ψ : Matrix (X (s + 1) ⊕ Fin 0) (X s ⊕ Fin (0 + 1)) k → ℂ) (x₀ : Matrix (X (s + 1)) (X s) k) :
    Matrix (Z ⊕ Unit) (X (s + 1)) k → ℂ := fun x =>
  T.PhiTop (fromCols x.toRows₁ 0) * hatCol ψ ν ε Ψ x₀ (x (Sum.inr ()))
def Law (T : Chain k s X Z) (A : RepFam k s X) (S M : Submodule 𝒪[k] (X (s + 1) → k))
    (ψ : AddChar k Circle) (ν : Measure k) (ε : k) : Prop :=
  ∃ F : Finset ((X (s + 1) → k) ⧸ M), (F : Set _) = T.coupIdx A S M ∧ ∀ g ∈ A s 0 rfl,
    om (T.mu (s + 1)) g 1 (T.Phi s 0 rfl) = ∑ yb ∈ F, tens (T.xiPen M g yb) (cosetInd M yb) ∧
    (∀ x₀ x, ∑ yb ∈ F, T.xiPen M g yb x₀ * T.xiTop M ψ ν ε yb x =
      topDatum T ψ ν ε (om (T.mu (s + 1)) g 1 (T.Phi s 0 rfl)) x₀ x) ∧
    ∀ η₁ η₂ : kˣ →* ℂˣ, IsUnram η₁ → IsUnram η₂ →
      ∀ κ : GL (X (s + 1)) k, embX 0 κ ∈ (T.lev (s + 1) 0 rfl).J → ∀ x₀ x,
        ∑ yb ∈ F, om (T.mu (s + 1) * η₁) 1 κ (T.xiPen M g yb) x₀ * om (T.mu (s + 2) * η₂) κ 1 (T.xiTop M ψ ν ε yb) x =
          ∑ yb ∈ F, T.xiPen M g yb x₀ * T.xiTop M ψ ν ε yb x
end Top
def LastSteps : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) (ε : k) (ϖ : kˣ),
    HasConductor ψ 1 → IsUnitVol ν → valuation k ε = 1 → valuation k (ϖ : k) = uniformizer k →

    (∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'],
      (∀ Ψ : Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ,
        Shaped ϖ (srcLat n' ϖ) (box (n ⊕ Fin 0) 1) Ψ → PenStep ψ ν ε ϖ Ψ) ∧
      Intertwining n n' ψ ν ε) ∧
    ∀ (s : ℕ) (X : ℕ → Type) [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] (Z r t : Type) [Fintype Z] [DecidableEq Z]
      [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]
      (F : ∀ j c, j + c = s + 1 → LatFrame k (Ix r t j) (X j ⊕ Fin c)) (Ftop : LatFrame k (Ix r t (s + 2)) Z),

      latOf (F (s + 1) 0 rfl).bas = box _ 1 →

      (latOf (F s (0 + 1) rfl).bas = srcLat (X s) ϖ →
        ∀ (P : TypeDatum k r) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)),

          (∀ h' ∈ stabLat (F s (0 + 1) rfl).bas,
            Shaped ϖ (srcLat (X s) ϖ) (box (X (s + 1) ⊕ Fin 0) 1)
                (om (μ (s + 1)) h' 1 ((Chain.ofType P μ hμ F Ftop).Phi s 0 rfl)) ∧
              PenStep ψ ν ε ϖ (om (μ (s + 1)) h' 1 ((Chain.ofType P μ hμ F Ftop).Phi s 0 rfl))) ∧

          (∀ Ψ : Matrix (X (s + 1) ⊕ Fin 0) (X s ⊕ Fin (0 + 1)) k → ℂ,
            Shaped ϖ (srcLat (X s) ϖ) (box (X (s + 1) ⊕ Fin 0) 1) Ψ → ∀ x₀,
              Shaped ϖ (box (X (s + 1)) 1) (addLine (latOf Ftop.bas))
                (topDatum (Chain.ofType P μ hμ F Ftop) ψ ν ε Ψ x₀)) ∧

          ∀ A : RepFam k s X, (∀ g ∈ A s 0 rfl, g ∈ stabLat (F s (0 + 1) rfl).bas) →
            Law (Chain.ofType P μ hμ F Ftop) A (box _ ϖ⁻¹) (box _ 1) ψ ν ε) ∧

      (latOf (F s (0 + 1) rfl).bas = box _ 1 →
        ∀ (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (υ : ℕ → kˣ →* ℂˣ), (∀ j, IsUnram (υ j)) →
          ∀ (A : RepFam k s X) (e : ℕ), 1 ≤ e →
            (Chain.ofTwist δ hδ υ F Ftop).Adapted A (box _ (ϖ ^ e)⁻¹) (box _ (ϖ ^ e)) →
            Law (Chain.ofTwist δ hδ υ F Ftop) A (box _ (ϖ ^ e)⁻¹) (box _ (ϖ ^ e)) ψ ν ε)
section Checks
variable {k : Type} [Field k] [ValuativeRel k] {ι n : Type} [Fintype n] [DecidableEq n]
example (ϖ : kˣ) (o : ι ≃ n ⊕ Fin (0 + 1)) : latOf (typeFrame ϖ o).bas = srcLat n ϖ := by
  ext y
  rw [mem_latOf_typeFrame]
  simp [srcLat, mem_box, Valuation.mem_integer_iff, LinearMap.funLeft_apply]
example (ϖ : kˣ) (o : ι ≃ n ⊕ Fin 0) : latOf (typeFrame ϖ o).bas = box _ 1 := by
  ext y
  rw [mem_latOf_typeFrame]
  simp [mem_box, Valuation.mem_integer_iff]
example {c : ℕ} (o : ι ≃ n ⊕ Fin c) : latOf (plainFrame (k := k) o).bas = box _ 1 := box_one.symm
example (η : n → k) : η ∈ dualStd k n ↔ ∀ i, η i ∈ 𝒪[k] := by
  constructor
  · intro h i
    have := h (Pi.single i 1) (fun j => by
      rw [Pi.single_apply]; split_ifs <;> simp)
    simpa using this
  · intro h y hy
    exact sum_mem fun i _ => mul_mem (h i) (by simpa [Valuation.mem_integer_iff] using hy i)
end Checks
end GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices


