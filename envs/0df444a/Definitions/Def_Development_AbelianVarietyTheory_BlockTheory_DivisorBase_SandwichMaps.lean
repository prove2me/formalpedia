-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SandwichMaps
-- name    : Development_AbelianVarietyTheory_BlockTheory_DivisorBase_SandwichMaps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:38.300019+00:00
-- url     : https://prove2.me/theorems/849773d2-91d1-455c-8807-4e47ed8bbcd7
-- title:
--   Sandwich Maps
-- statement:
--   Definitions and structural lemmas for Sandwich Maps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/SandwichMaps.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_XiMulNu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal Matrix GlobalTheory.Sandwich
namespace GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
section Eigen
variable {O : Type} [CommRing O] (C : Type) [Field C] [Algebra O C]
  {Λ : Type} [CommRing Λ] {h : ℕ}
def eig (ρ : Λ → Matrix (Fin h) (Fin h) O) (σ : Λ →+* O) : Submodule C (Fin h → C) :=
  ⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C)))
    (algebraMap O C (σ a))
def quotLattice (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) : Set (eig C ρ τ) :=
  {x | ∃ t : Fin h → O, (fun i => algebraMap O C (t i)) - (x : Fin h → C) ∈
    ⨆ σ : {σ : Λ →+* O // σ ≠ τ}, eig C ρ σ.1}
abbrev detLine (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) : Type :=
  ⋀[C]^N (eig C ρ τ)
def detLattice (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) :
    Submodule O (detLine C ρ τ N) :=
  Submodule.span O
    {w | ∃ x : Fin N → eig C ρ τ, (∀ i, x i ∈ quotLattice C ρ τ) ∧ w = exteriorPower.ιMulti C N x}
example (ρ : Λ → Matrix (Fin h) (Fin h) O) (τ : Λ →+* O) (N : ℕ) (a : O) (w : detLine C ρ τ N) :
    a • w = algebraMap O C a • w := (algebraMap_smul C a w).symm
end Eigen
section Datum
variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O] (C : Type) [Field C] [Algebra O C]
  {ε : PreTilt O p} {h h' : ℕ} {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]
def actT (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρT a).map (padicToO p O)
def actH (D : Datum ε h Λ) (a : Λ) : Matrix (Fin h) (Fin h) O := (D.ρM a).map (fontaineTheta O p)
def redC {m n : ℕ} (X : Matrix (Fin m) (Fin n) (Ainf p O)) : (Fin n → C) →ₗ[C] (Fin m → C) :=
  Matrix.toLin' (X.map ((algebraMap O C).comp (fontaineTheta O p)))
def alC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.F
def bC (D : Datum ε h Λ) : (Fin h → C) →ₗ[C] (Fin h → C) := redC C D.G
def IsIota (D : Datum ε h Λ) (τ : Λ →+* O) (N : ℕ)
    (ι : detLine C (actT D) τ N →ₗ[C] detLine C (actH D) τ N) : Prop :=
  ∀ (x : Fin N → eig C (actT D) τ) (y : Fin N → eig C (actH D) τ),
    (∀ i : Fin N, (i : ℕ) < D.lieRank τ → (x i : Fin h → C) = bC C D (y i)) →
    (∀ i : Fin N, D.lieRank τ ≤ (i : ℕ) → (y i : Fin h → C) = alC C D (x i)) →
    ι (exteriorPower.ιMulti C N x) = exteriorPower.ιMulti C N y
def IsIsogeny (D : Datum ε h Λ) (D' : Datum ε h' Λ) (fT : Matrix (Fin h') (Fin h) ℤ_[p])
    (fM : Matrix (Fin h') (Fin h) (Ainf p O)) : Prop :=
  D'.F * fT.map (ofPadic p O) = fM * D.F ∧
  (∀ a, fT * D.ρT a = D'.ρT a * fT) ∧ (∀ a, fM * D.ρM a = D'.ρM a * fM) ∧
  ∃ (n : ℕ) (gT : Matrix (Fin h) (Fin h') ℤ_[p]) (gM : Matrix (Fin h) (Fin h') (Ainf p O)),
    D.F * gT.map (ofPadic p O) = gM * D'.F ∧
    gT * fT = ((p : ℤ_[p]) ^ n) • (1 : Matrix (Fin h) (Fin h) ℤ_[p]) ∧
    fT * gT = ((p : ℤ_[p]) ^ n) • (1 : Matrix (Fin h') (Fin h') ℤ_[p]) ∧
    gM * fM = ((p : Ainf p O) ^ n) • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) ∧
    fM * gM = ((p : Ainf p O) ^ n) • (1 : Matrix (Fin h') (Fin h') (Ainf p O))
end Datum
def DetOver (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O] : Prop :=
  ∀ (ε : PreTilt O p), IsPrimitiveRoot (GlobalTheory.Sandwich.root ε).untilt p →
  ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ],
    (∃ c_vp : ℕ → ((Λ →+* O) → ℕ) → (Λ →+* O) → ℝ,
      ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O),
        (∃! ι, IsIota C D τ N ι) ∧
        ∀ ι, IsIota C D τ N ι → Function.Bijective ι ∧
          ∃ lam : C, v lam = v (p : C) ^ (c_vp N D.lieRank τ) ∧
            ι '' (detLattice C (actT D) τ N : Set (detLine C (actT D) τ N)) =
              (fun w => lam • w) '' (detLattice C (actH D) τ N : Set (detLine C (actH D) τ N))) ∧
    (∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D D' : Datum ε h Λ)
      (fT : Matrix (Fin h) (Fin h) ℤ_[p]) (fM : Matrix (Fin h) (Fin h) (Ainf p O)),
      IsIsogeny D D' fT fM → ∀ (τ : Λ →+* O),
        ∃ (u : eig C (actT D) τ →ₗ[C] eig C (actT D') τ)
          (w : eig C (actH D) τ →ₗ[C] eig C (actH D') τ),
          (∀ x, (u x : Fin h → C) = redC C (fT.map (ofPadic p O)) x) ∧
          (∀ y, (w y : Fin h → C) = redC C fM y) ∧
          ∀ ι ι', IsIota C D τ N ι → IsIota C D' τ N ι' →
            ι' ∘ₗ exteriorPower.map N u = exteriorPower.map N w ∘ₗ ι)
def LemmaDet : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (span {(p : O)}) O], v.Integers O → DetOver p C v O
end GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps


