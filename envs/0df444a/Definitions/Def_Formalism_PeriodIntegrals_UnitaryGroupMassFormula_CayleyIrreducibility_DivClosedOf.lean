-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CayleyIrreducibility_DivClosedOf
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T11:09:45.453077+00:00
-- url     : https://prove2.me/theorems/d5c899b5-0137-5c0a-97b4-a6679c377f5b
-- title:
--   Div Closed Of
-- statement:
--   Definitions and structural lemmas for Div Closed Of, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/CayleyIrreducibility/DivClosedOf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_ColDictValC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Pf.ColDictValCPf
open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.L2.SG.Pf.ColDictPf Matrix MvPolynomial
open scoped ComplexOrder
def famAct {ι : Type} {n : ℕ} (g : ι → Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (ι × Fin n × Fin n) ℂ :=
  aeval fun v => ∑ c : Fin n, C (g v.1 v.2.1 c) * X (v.1, c, v.2.2)
def bigGen {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) :
    MvPolynomial (ι × Fin n × Fin n) ℂ →ₐ[ℂ] Polynomial (MvPolynomial (ι × Fin n × Fin n) ℂ) :=
  aeval fun v => Polynomial.C (X v) +
    (if v.1 = τ ∧ v.2.1 = b then Polynomial.X * Polynomial.C (X (τ, a, v.2.2)) else 0)
def bigDiv {ι : Type} [DecidableEq ι] {n : ℕ} (τ : ι) (a b : Fin n) (k : ℕ)
    (P : MvPolynomial (ι × Fin n × Fin n) ℂ) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  (bigGen τ a b P).coeff k
def tenHW {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) : MvPolynomial (ι × Fin n × Fin n) ℂ :=
  tenV fun τ => extremal ℂ n (lam τ)
def Transfer : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ),
    (∀ τ, (G τ).PosDef ∨ (-G τ).PosDef) →
    ∀ (lam : ι → DomWeight n) (W : Submodule ℂ (FramesV G → ℂ)), W ≤ ValCV G lam → W ≠ ⊥ →
      (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) →
        ∀ F ∈ W, ∃ F' ∈ W, ∀ y y' : FramesV G, (∀ τ, y'.1 τ = g τ * y.1 τ) → F' y = F y') →
      ∃ M : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ), M ≤ CSpanV lam ∧ M ≠ ⊥ ∧
        (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) → ∀ P ∈ M, famAct g P ∈ M) ∧
        (CSpanV lam ≤ M → W = ValCV G lam)
def Dens : Prop :=
  ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), G.PosDef →
    ∀ p : MvPolynomial (Fin n × Fin n) ℂ,
      (∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * G * g = G → eval (fun x => g x.1 x.2) p = 0) →
      ∀ g : Matrix (Fin n) (Fin n) ℂ, IsUnit (1 + g).det → eval (fun x => g x.1 x.2) p = 0
def DivClosed : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (G : ι → Matrix (Fin n) (Fin n) ℂ),
    (∀ τ, (G τ).PosDef ∨ (-G τ).PosDef) →
    ∀ M : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ),
      (∀ g : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (g τ)ᴴ * G τ * g τ = G τ) → ∀ P ∈ M, famAct g P ∈ M) →
      ∀ (τ : ι) (a b : Fin n) (k : ℕ), ∀ P ∈ M, bigDiv τ a b k P ∈ M
def DivClosedOf : Prop := Dens → DivClosed
def HiEx : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (M : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ)),
    (∀ (τ : ι) (a b : Fin n) (k : ℕ), ∀ P ∈ M, bigDiv τ a b k P ∈ M) → M ≠ ⊥ →
    ∃ Q ∈ M, Q ≠ 0 ∧ ∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0
def Uniq : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n)
    (Q : MvPolynomial (ι × Fin n × Fin n) ℂ), Q ∈ CSpanV lam →
    (∀ (τ : ι) (a b : Fin n), a < b → ∀ k, 1 ≤ k → bigDiv τ a b k Q = 0) →
    ∃ c : ℂ, Q = c • tenHW lam
def Gen : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (lam : ι → DomWeight n)
    (M : Submodule ℂ (MvPolynomial (ι × Fin n × Fin n) ℂ)),
    (∀ (τ : ι) (a b : Fin n) (k : ℕ), ∀ P ∈ M, bigDiv τ a b k P ∈ M) → tenHW lam ∈ M → CSpanV lam ≤ M
end Formalism.L2.SG.Pf.ColDictValCPf


