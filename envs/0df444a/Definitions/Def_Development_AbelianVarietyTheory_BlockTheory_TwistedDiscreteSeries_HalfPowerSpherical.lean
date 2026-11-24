-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_HalfPowerSpherical
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:23.574733+00:00
-- url     : https://prove2.me/theorems/582a51ea-f85c-4a8e-bf99-322fca04c8fd
-- title:
--   Half Power Spherical
-- statement:
--   Definitions and structural lemmas for Half Power Spherical, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/HalfPowerSpherical.lean

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
open GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical
section Defs
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def idl (b : kˣ) : Submodule 𝒪[k] k := Submodule.span 𝒪[k] {(b : k)}
def monLat {n : Type} (c : ℕ) (L : Submodule 𝒪[k] (n → k)) (b : ℕ → kˣ) :
    Submodule 𝒪[k] (n ⊕ Fin c → k) where
  carrier := {v | (fun r => v (Sum.inl r)) ∈ L ∧ ∀ i : Fin c, v (Sum.inr i) ∈ idl (b (i.val + 1))}
  add_mem' hv hw := ⟨L.add_mem hv.1 hw.1, fun i => (idl _).add_mem (hv.2 i) (hw.2 i)⟩
  zero_mem' := ⟨L.zero_mem, fun _ => (idl _).zero_mem⟩
  smul_mem' s _ hv := ⟨L.smul_mem s hv.1, fun i => (idl _).smul_mem s (hv.2 i)⟩
def act {ι : Type} [Fintype ι] [DecidableEq ι] (h : GL ι k) (Λ : Submodule 𝒪[k] (ι → k)) :
    Submodule 𝒪[k] (ι → k) :=
  Λ.map ((Matrix.mulVecLin h.val).restrictScalars 𝒪[k])
theorem act_mul {ι : Type} [Fintype ι] [DecidableEq ι] (g h : GL ι k) (Λ : Submodule 𝒪[k] (ι → k)) :
    act (g * h) Λ = act g (act h Λ) := by
  unfold act
  rw [← Submodule.map_comp]
  congr 1
  ext v i
  simp
theorem act_one {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule 𝒪[k] (ι → k)) : act 1 Λ = Λ := by
  ext v
  simp [act]
def stab {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule 𝒪[k] (ι → k)) : Subgroup (GL ι k) where
  carrier := {h | act h Λ = Λ}
  mul_mem' {g h} hg hh := by
    have hg' : act g Λ = Λ := hg
    have hh' : act h Λ = Λ := hh
    show act (g * h) Λ = Λ
    rw [act_mul, hh', hg']
  one_mem' := act_one Λ
  inv_mem' {g} hg := by
    have hg' : act g Λ = Λ := hg
    show act g⁻¹ Λ = Λ
    conv_lhs => rw [← hg']
    rw [← act_mul, inv_mul_cancel, act_one]
open Classical in

def sph {ι ι' : Type} [Fintype ι'] (α : kˣ) (Λ' : Submodule 𝒪[k] (ι' → k)) (Λ : Submodule 𝒪[k] (ι → k))
    (x : Matrix ι ι' k) : ℂ :=
  if ∀ v ∈ Λ', ∃ w ∈ Λ, x *ᵥ v = (α : k) • w then 1 else 0
open Classical in

def colInd {n : Type} (b : kˣ) (L : Submodule 𝒪[k] (n → k)) (β : n → k) : ℂ :=
  if (b : k) • β ∈ L then 1 else 0
open Classical in

def rowInd {n : Type} [Fintype n] (Λ : Submodule 𝒪[k] (n → k)) (d : kˣ) (η : n → k) : ℂ :=
  if ∀ v ∈ Λ, η ⬝ᵥ v ∈ idl d then 1 else 0
def IsPrimitive {n : Type} [DecidableEq n] {c : ℕ} (ψ : AddChar k Circle)
    (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) : Prop :=
  ∀ i j : Fin c, j.val = i.val + 1 → ∀ s : k,
    (∀ t : k, valuation k t ≤ valuation k s → ψ t = 1) ↔
      ∀ v ∈ Λ, v + Pi.single (Sum.inr i) (s * v (Sum.inr j)) ∈ Λ
def HasRatio (β : kˣ) (c : ℕ) (b : ℕ → kˣ) : Prop :=
  ∀ i, 1 ≤ i → i + 1 ≤ c → idl (b i / b (i + 1)) = idl β
def IsHalfPow (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (C : ℝ) : Prop := ∃ e : ℤ, C = (resCard k : ℝ) ^ ((e : ℝ) / 2)
def RFJ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ) : Subgroup (GL (n ⊕ Fin c) k) :=
  R k n c (ρ + 1) ⊔ Subgroup.closure (Set.range (colE c (ρ + 1)))
def chainGen (α α' : kˣ) (m j i : ℕ) : kˣ :=
  α ^ (-(j : ℤ)) * (α / α') ^ (m / 2) * (α * α') ^ (((m / 2 : ℕ) : ℤ) - (i : ℤ))
def chainLat {n : Type} (α α' : kˣ) (j c : ℕ) (L : Submodule 𝒪[k] (n → k)) : Submodule 𝒪[k] (n ⊕ Fin c → k) :=
  monLat c L (chainGen α α' (j + c + 1) j)
def IsChain (α α' : kˣ) (m : ℕ) (b : ℕ → ℕ → kˣ) : Prop :=
  HasRatio (α * α') (m - 1) (b 0) ∧
    ∀ j i, 1 ≤ i → i + (j + 1) + 1 ≤ m → idl (b (j + 1) i) = idl (α⁻¹ * b j i)
def frame (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (b : ℕ → kˣ) : GL (n ⊕ Fin c) k :=
  embA n ⟨Matrix.diagonal fun i : Fin c => (b (i.val + 1) : k),
    Matrix.diagonal fun i : Fin c => ((b (i.val + 1))⁻¹ : kˣ),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩
variable [MeasurableSpace k] [BorelSpace k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}
def flat (ψ : AddChar k Circle) (ν : Measure k) (μ : kˣ →* ℂˣ) (ρ : ℕ)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k) (β : n → k) : ℂ :=
  opE ψ ν (ρ + 1) (om μ 1 (colE c (ρ + 1) β) Ψ) x
def rowMat (n : Type) (c ρ : ℕ) (u : n' → k) : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
  fromBlocks 0 0 (Matrix.of fun l s => if l.val + 1 = ρ then u s else 0) 0
def opEW (ψ : AddChar k Circle) (ν : Measure k) (ρ : ℕ) (Φ₀ : (n' → k) → ℂ)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x : Matrix n n' k) : ℂ :=
  ∫ u : n' → k, (∫ β : n' → k, Φ₀ β * (ψ (u ⬝ᵥ β) : ℂ) ∂(Measure.pi fun _ => ν)) *
    opE ψ ν ρ (fun y => Ψ (y + rowMat n c ρ u)) x ∂(Measure.pi fun _ => ν)
def ReceivesZ (ψ : AddChar k Circle) (ν : Measure k) (ε : ℤˣ) (α : kˣ) (L' : Submodule 𝒪[k] (n' → k))
    (Λ : Submodule 𝒪[k] (n → k)) (b' bz : kˣ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (x₀ : Matrix n n' k) (η : n → k),
    ∫ y : n → k, sph α (monLat 1 L' fun _ => b') Λ (Matrix.fromCols x₀ (Matrix.of fun r _ => y r)) *
        (ψ ((((ε : ℤ) : k)) * (η ⬝ᵥ y)) : ℂ) ∂(Measure.pi fun _ => ν) =
      C * sph α L' Λ x₀ * rowInd Λ (α * bz) η
end Defs
section Statements
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
def OneOrbit : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (α α' : kˣ)
    (L : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) (Λ₀ : Submodule 𝒪[k] (n ⊕ Fin c → k))
    (b' : ℕ → kˣ) (ν : Measure k),
    L.IsLattice k → L'.IsLattice k → Λ₀.IsLattice k → HasRatio (α * α') (c + 1) b' → ν.IsAddHaarMeasure →
    let Λ := monLat c L fun i => α⁻¹ * b' i
    let Φ := sph α (monLat (c + 1) L' b') Λ₀
    (∀ p, 1 ≤ p → p ≤ c →
      (∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k), HasConductor ψ (α * α') →
        opE ψ ν p (om μ 1 h Φ) ≠ 0 → ∃ r ∈ R k n c p, act h Λ₀ = act r Λ) ∧
      ∃ C : ℝ, 0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k C) ∧
        ∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k), HasConductor ψ (α * α') →
          act h Λ₀ = Λ → ∀ x, opE ψ ν p (om μ 1 h Φ) x =
            (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * C * sph α L' L x) ∧
    (∀ ρ, 1 ≤ ρ → c = 2 * ρ →
      (∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k), HasConductor ψ (α * α') →
        flat ψ ν μ ρ (om μ 1 h Φ) ≠ 0 → ∃ r ∈ RFJ k n c ρ, act h Λ₀ = act r Λ) ∧
      ∃ C : ℝ, 0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k C) ∧
        ∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k), HasConductor ψ (α * α') →
          act h Λ₀ = Λ → ∀ x β, flat ψ ν μ ρ (om μ 1 h Φ) x β =
            (((μ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) * C * sph α L' L x *
              colInd (α⁻¹ * b' (ρ + 1)) L β) ∧
    HasRatio (α * α') c (fun i => α⁻¹ * b' i) ∧
    ∀ ψ : AddChar k Circle, HasConductor ψ (α * α') → IsPrimitive ψ Λ
def MiddleIdeals : Prop :=
  ∀ (α α' : kˣ) (m : ℕ) (b : ℕ → ℕ → kˣ), Even m → 2 ≤ m → IsChain α α' m b →
    (∀ j, Even j → j + 2 ≤ m → idl (b j ((m - j) / 2)) = idl (b 0 (m / 2) * (α' / α) ^ (j / 2))) ∧
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      (Λ : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) (ψ : AddChar k Circle) (ν : Measure k) (ε : ℤˣ),
      Λ.IsLattice k → L'.IsLattice k → HasConductor ψ (α * α') → ν.IsAddHaarMeasure →
      ReceivesZ ψ ν ε α L' Λ (b (m - 2) 1) (b 0 (m / 2) * (α' / α) ^ (m / 2)) ∧
      (Nonempty n → ∀ bz, ReceivesZ ψ ν ε α L' Λ (b (m - 2) 1) bz →
        idl bz = idl (b 0 (m / 2) * (α' / α) ^ (m / 2))) ∧
      (Nonempty n → ReceivesZ ψ ν ε α L' Λ (b (m - 2) 1) 1 →
        (∀ i, 1 ≤ i → i + 1 ≤ m → idl (b 0 i) =
          idl ((α / α') ^ (m / 2) * (α * α') ^ (((m / 2 : ℕ) : ℤ) - (i : ℤ)))) ∧
        ∀ (n₀ : Type) (c : ℕ) (L₀ : Submodule 𝒪[k] (n₀ → k)), m = c + 1 →
          monLat c L₀ (b 0) = chainLat α α' 0 c L₀)
def LastDatum : Prop :=
  ∀ (n n'' : Type) [Fintype n] (α bz : kˣ) (Λ : Submodule 𝒪[k] (n → k)) (L'' : Submodule 𝒪[k] (n'' → k))
    (x : Matrix n'' n k) (η : n → k),
    sph α Λ (monLat 1 L'' fun _ => bz) (Matrix.fromRows x (Matrix.of fun _ s => η s)) =
      sph α Λ L'' x * rowInd Λ (α * bz) η
def Rescale : Prop :=
  ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (α α' : kˣ)
    (L : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) (b' : ℕ → kˣ),
    L.IsLattice k → L'.IsLattice k → (∀ i, 1 ≤ i → i ≤ c → b' i / b' (i + 1) = α * α') →
    let β₀ : k := ((α * α' : kˣ) : k)
    let b : ℕ → kˣ := fun i => α⁻¹ * b' i
    let D := frame n c b
    let D' := frame n' (c + 1) b'
    let T : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k :=
      fun y => (α : k) • (D.val * y * (D'⁻¹).val)
    let Φ := sph α (monLat (c + 1) L' b') (monLat c L b)
    let Φs := sph 1 (monLat (c + 1) L' fun _ => 1) (monLat c L fun _ => 1)
    (∀ ψ : AddChar k Circle, HasConductor ψ (α * α') → HasConductor (ψ.mulShift β₀) 1) ∧
    (∀ p, 1 ≤ p → p ≤ c → ∀ (x : Matrix n n' k) y,
      T y ∈ Set.range (affPt p x) ↔ y ∈ Set.range (affPt p (((α⁻¹ : kˣ) : k) • x))) ∧
    (∀ y, ch (T y) = β₀ * ch y) ∧
    (∀ g, simpleSum (D * g * D⁻¹) = β₀ * simpleSum g) ∧
    (∀ g', simpleSum (D' * g' * D'⁻¹) = β₀ * simpleSum g') ∧
    (∀ p, 1 ≤ p → p ≤ c → ∀ u β : n' → k,
      D' * rowE (c + 1) p u * D'⁻¹ = rowE (c + 1) p ((b' p : k) • u) ∧
      D' * colE (c + 1) (p + 1) β * D'⁻¹ = colE (c + 1) (p + 1) ((((b' (p + 1))⁻¹ : kˣ) : k) • β) ∧
      ((b' p : k) • u) ⬝ᵥ ((((b' (p + 1))⁻¹ : kˣ) : k) • β) = β₀ * (u ⬝ᵥ β)) ∧
    (∀ y, Φ (T y) = Φs y) ∧
    act D (monLat c L fun _ => 1) = monLat c L b ∧
    act D' (monLat (c + 1) L' fun _ => 1) = monLat (c + 1) L' b' ∧
    (∀ p, 1 ≤ p → p ≤ c → ∀ g, (D * g * D⁻¹ ∈ N k n c p ↔ g ∈ N k n c p) ∧
      (D * g * D⁻¹ ∈ R k n c p ↔ g ∈ R k n c p)) ∧
    (∀ ρ, 1 ≤ ρ → c = 2 * ρ → ∀ g, D * g * D⁻¹ ∈ RFJ k n c ρ ↔ g ∈ RFJ k n c ρ) ∧
    ∀ ν νs : Measure k, ν.IsAddHaarMeasure → νs.IsAddHaarMeasure →
      let Pw : ℝ → Prop := fun C => 0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal →
        IsHalfPow k (νs (𝒪[k] : Set k)).toReal → IsHalfPow k C)
      (∀ p, 1 ≤ p → p ≤ c → ∃ C, Pw C ∧
        ∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k) (x : Matrix n n' k),
          HasConductor ψ (α * α') → opE ψ ν p (om μ 1 (D * h * D⁻¹) Φ) x =
            C * opE (ψ.mulShift β₀) νs p (om μ 1 h Φs) (((α⁻¹ : kˣ) : k) • x)) ∧
      (∀ ρ, 1 ≤ ρ → c = 2 * ρ → ∃ C, Pw C ∧
        ∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k) (x : Matrix n n' k) (β : n → k),
          HasConductor ψ (α * α') → flat ψ ν μ ρ (om μ 1 (D * h * D⁻¹) Φ) x β =
            C * flat (ψ.mulShift β₀) νs μ ρ (om μ 1 h Φs) (((α⁻¹ : kˣ) : k) • x) ((b (ρ + 1) : k) • β)) ∧
      (∀ ρ, c + 1 = 2 * ρ → ∃ C, Pw C ∧
        ∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k) (x : Matrix n n' k),
          HasConductor ψ (α * α') → ∀ Φ₀ ∈ SB (n' → k),
            opEW ψ ν ρ (fun β => Φ₀ ((b' (ρ + 1) : k) • β)) (om μ 1 (D * h * D⁻¹) Φ) x =
              C * opEW (ψ.mulShift β₀) νs ρ Φ₀ (om μ 1 h Φs) (((α⁻¹ : kˣ) : k) • x))
def EvenStep : Prop :=
  ∀ (n n' n'' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype n''] [DecidableEq n'']
    (c ρ : ℕ) (α α' : kˣ) (Λ : Submodule 𝒪[k] (n ⊕ Fin c → k)) (L' : Submodule 𝒪[k] (n' → k))
    (L'' : Submodule 𝒪[k] (n'' → k)) (b'' : ℕ → kˣ) (ψ : AddChar k Circle) (ν : Measure k),
    c + 1 = 2 * ρ → Λ.IsLattice k → L'.IsLattice k → L''.IsLattice k → HasRatio (α * α') (c + 1 + 1) b'' →
    HasConductor ψ (α * α') → IsSelfDual ψ ν →
    let b' : ℕ → kˣ := fun i => α⁻¹ * b'' i
    (∃ C : ℝ, 0 < C ∧ IsHalfPow k C ∧ ∀ (μ : kˣ →* ℂˣ) x β,
      flat ψ ν μ ρ (sph α (monLat (c + 1 + 1) L'' b'') (monLat (c + 1) L' b')) x β =
        C * sph α L'' L' x * colInd (b' (ρ + 1)) L' β) ∧
    ∀ (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k),
      opEW ψ ν ρ (colInd (b' (ρ + 1)) L') (om μ 1 h (sph α (monLat (c + 1) L' b') Λ)) =
        opE ψ ν ρ (om μ 1 h (sph α (monLat (c + 1) L' b') Λ))
end Statements
section Chain
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]
def ChainLemma : Prop :=
  ∀ (α α' : kˣ) (m : ℕ), Even m → 2 ≤ m →
    IsChain α α' m (chainGen α α' m) ∧
    (∀ i, 1 ≤ i → i + 1 ≤ m → chainGen α α' m 0 i = α ^ (m - i) * α' ^ (-(i : ℤ)) ∧
      (chainGen α' α m 0 i)⁻¹ = chainGen α α' m 0 (m - i)) ∧
    (∀ (n : Type) [DecidableEq n] (j c : ℕ) (L : Submodule 𝒪[k] (n → k)), m = j + c + 1 → L.IsLattice k →
      (chainLat α α' j c L).IsLattice k ∧ HasRatio (α * α') c (chainGen α α' m j) ∧
      ∀ ψ : AddChar k Circle, HasConductor ψ (α * α') → IsPrimitive ψ (chainLat α α' j c L)) ∧
    (∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (j c : ℕ)
      (L : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) (ν : Measure k),
      m = j + c + 1 → 1 ≤ j → 1 ≤ c → L.IsLattice k → L'.IsLattice k → ν.IsAddHaarMeasure →
      let Λ := chainLat α α' j c L
      let Φ := sph α (chainLat α α' (j - 1) (c + 1) L') Λ
      (∀ p, 1 ≤ p → p ≤ c →
        (∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k), HasConductor ψ (α * α') →
          opE ψ ν p (om μ 1 h Φ) ≠ 0 →
            (∃ r ∈ R k n c p, act h Λ = act r Λ) ∧ ∃ r ∈ R k n c p, ∃ κ ∈ stab Λ, h = r * κ) ∧
        ∃ C : ℝ, 0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k C) ∧
          ∀ ψ : AddChar k Circle, HasConductor ψ (α * α') → ∀ x, opE ψ ν p Φ x = C * sph α L' L x) ∧
      (∀ ρ, c = 2 * ρ →
        (∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ) (h : GL (n ⊕ Fin c) k), HasConductor ψ (α * α') →
          flat ψ ν μ ρ (om μ 1 h Φ) ≠ 0 →
            (∃ r ∈ RFJ k n c ρ, act h Λ = act r Λ) ∧ ∃ r ∈ RFJ k n c ρ, ∃ κ ∈ stab Λ, h = r * κ) ∧
        ∃ C : ℝ, 0 < C ∧ (IsHalfPow k (ν (𝒪[k] : Set k)).toReal → IsHalfPow k C) ∧
          ∀ (ψ : AddChar k Circle) (μ : kˣ →* ℂˣ), HasConductor ψ (α * α') → ∀ x β,
            flat ψ ν μ ρ Φ x β = C * sph α L' L x * colInd (chainGen α α' m j (ρ + 1)) L β)) ∧
    idl (chainGen α α' m (m - 2) 1 * α' / α) = idl 1 ∧
    ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
      (Λ : Submodule 𝒪[k] (n → k)) (L' : Submodule 𝒪[k] (n' → k)) (ψ : AddChar k Circle) (ν : Measure k) (ε : ℤˣ),
      Λ.IsLattice k → L'.IsLattice k → HasConductor ψ (α * α') → ν.IsAddHaarMeasure →
      ReceivesZ ψ ν ε α L' Λ (chainGen α α' m (m - 2) 1) 1
end Chain
def Statement : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k],
    OneOrbit k ∧ MiddleIdeals k ∧ LastDatum k ∧ Rescale k ∧ EvenStep k ∧ ChainLemma k
section Basic₂
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
example (α α' : kˣ) : chainGen α α' 4 2 1 * α' / α = 1 := by
  ext
  simp [chainGen, zpow_ofNat]
  field_simp
end Basic₂
end GlobalTheory.IndefiniteRowSideFullHecke.HalfPowerSpherical


