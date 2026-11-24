-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- name    : Formalism_HermitianCurvature_CapelliDeterminantAndBranching
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T16:12:40.626102+00:00
-- url     : https://prove2.me/theorems/b86f467e-87e9-43b4-959a-bb5728dba34a
-- title:
--   Capelli Determinant And Branching
-- statement:
--   Definitions and structural lemmas for Capelli Determinant And Branching, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/CapelliDeterminantAndBranching.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_succ
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_succ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
section Defs
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def Stab {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (S : Submodule ℂ V) : Prop :=
  ∀ a b, ∀ v ∈ S, E a b v ∈ S
def Irr {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Prop :=
  Nontrivial V ∧ ∀ S : Submodule ℂ V, Stab E S → S = ⊥ ∨ S = ⊤
def cpol {n : ℕ} (m : Fin n → ℂ) (w : ℂ) : ℂ := ∏ j, (w + m j)
def CapSp {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ) : Submodule ℂ V :=
  ⨅ w : ℂ, LinearMap.ker (qdet E w - cpol m w • (1 : Module.End ℂ V))
def SDec {n : ℕ} (m : Fin n → ℂ) : Prop := ∀ a b : Fin n, a < b → ∃ N : ℕ, m a - m b = (N : ℂ) + 1
def hval {n : ℕ} (θ : Fin n → ℂ) : ℝ := ∑ a : Fin n, ((n : ℝ) - ((a : ℕ) : ℝ)) * (θ a).re
def mono {n : ℕ} (f : Fin n → Module.End ℂ V) (a : Fin n → ℕ) : Module.End ℂ V :=
  (List.ofFn fun x => f x ^ a x).prod
def dualE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ V) : Fin n → Fin n → Module.End ℂ (Module.Dual ℂ V) :=
  fun a b => (E b a).dualMap
end Defs
def subA {A : Type*} {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) : Fin n → Fin n → A :=
  fun a b => E a.castSucc b.castSucc
def etaK {A : Type*} {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (x : Fin n) : A := E x.castSucc (Fin.last n)
def yK {A : Type*} {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → A) (x : Fin n) : A := E (Fin.last n) x.castSucc
def Box {n : ℕ} (L : Fin (n + 1) → ℤ) (M : Fin n → ℤ) : Prop := ∀ j : Fin n, L j.succ < M j ∧ M j ≤ L j.castSucc
def shf {n : ℕ} (β : ℂ) (M : Fin n → ℤ) : Fin n → ℂ := fun j => β + (M j : ℂ)
structure Hyp {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ)
    (L : Fin (n + 1) → ℤ) : Prop where
  gl : GlRel E
  irr : Irr E
  anti : StrictAnti L
  cap : ∀ (w : ℂ) (v : V), qdet E w v = cpol (shf β L) w • v
def ExistsSingMax : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V),
    GlRel E → ∀ S : Submodule ℂ V, Stab E S → S ≠ ⊥ →
    ∃ (ν : Fin n → ℂ) (v : V), v ∈ S ∧ v ≠ 0 ∧ IsHW E ν v ∧
      ∀ (θ : Fin n → ℂ) (x : V), x ∈ S → x ≠ 0 → (∀ a, E a a x = θ a • x) → hval θ ≤ hval ν
def SingDom : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (ν : Fin n → ℂ) (v : V), GlRel E → IsHW E ν v → v ≠ 0 → ∀ a b : Fin n, a < b → ∃ N : ℕ, ν a - ν b = (N : ℂ)
def SepPoly : Prop :=
  ∀ (n : ℕ) (m m' : Fin n → ℂ), (∀ w, cpol m w = cpol m' w) → SDec m' →
    Function.Injective m ∧ (SDec m → m = m')
def CapStab : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (m : Fin n → ℂ), GlRel E →
    Stab E (CapSp E m) ∧
      ∀ X : Module.End ℂ V, (∀ a b, X * E a b = E a b * X) → ∀ v ∈ CapSp E m, X v ∈ CapSp E m
def CapSing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (m : Fin n → ℂ), GlRel E → CapSp E m ≠ ⊥ →
    Function.Injective m ∧
      (SDec m → ∀ (ν : Fin n → ℂ) (v : V), v ∈ CapSp E m → v ≠ 0 → IsHW E ν v → ∀ j, ν j = m j + ((j : ℕ) : ℂ))
def TopWeightSing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V)
    (m : Fin n → ℂ), GlRel E → SDec m → ∀ x ∈ CapSp E m, (∀ a, E a a x = (m a + ((a : ℕ) : ℂ)) • x) →
      IsHW E (fun a => m a + ((a : ℕ) : ℂ)) x
def QminorPoly : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (a b : Fin t → Fin n),
    ∃ c : ℕ → A, ∀ u : ℂ, qminor E a b u = ∑ s ∈ Finset.range (t + 1), (u ^ s) • c s
def PolyVanish : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module ℂ X] (d : ℕ) (c : ℕ → X) (F : Finset ℂ),
    (∀ u : ℂ, u ∉ F → ∑ s ∈ Finset.range d, (u ^ s) • c s = 0) → ∀ s ∈ Finset.range d, c s = 0
def CovUp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (η : Fin n → Module.End ℂ V),
    GlRel E → IsCov E η → ∀ m : Fin n → ℂ, Function.Injective m → ∀ v ∈ CapSp E m,
    ∃ Ψ : Fin n → Fin n → V,
      (∀ x, ∑ i, Ψ i x = η x v) ∧
      (∀ i x, Ψ i x ∈ CapSp E (Function.update m i (m i + 1))) ∧
      ∀ (i x : Fin n) (u : ℂ),
        ∑ a : Fin n, ((-1 : ℂ) ^ ((a : ℕ) + (x : ℕ))) • qminor E (skip1 a) (skip1 x) u (Ψ i a) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Ψ i x
def VecDown : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (y : Fin n → Module.End ℂ V),
    GlRel E → IsVec E y → (∀ a b, y a * y b = y b * y a) → ∀ m : Fin n → ℂ, Function.Injective m → ∀ v ∈ CapSp E m,
    ∃ Φ : Fin n → Fin n → V,
      (∀ x, ∑ i, Φ i x = y x v) ∧
      (∀ i x, Φ i x ∈ CapSp E (Function.update m i (m i - 1))) ∧
      ∀ (i x : Fin n) (u : ℂ),
        ∑ l : Fin n, ((-1 : ℂ) ^ ((x : ℕ) + (l : ℕ))) • qminor E (skip1 x) (skip1 l) (u - 1) (Φ i l) =
          (∏ j ∈ Finset.univ.erase i, (u + m j)) • Φ i x
def BorderLast : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A), GlRel E → ∀ u : ℂ,
    qdet E u = qdet (subA E) u * Tm E (u - (n : ℂ)) (Fin.last n) (Fin.last n) -
      ∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (yK E x * qminor (subA E) (skip1 w) (skip1 x) u * etaK E w)
def BorderFirst : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A), GlRel E → ∀ u : ℂ,
    qdet E u = Tm E u (Fin.last n) (Fin.last n) * qdet (subA E) (u - 1) -
      ∑ w : Fin n, ∑ x : Fin n, (((-1 : ℤ) ^ ((w : ℕ) + (x : ℕ)) : ℤ) : A) *
        (etaK E w * qminor (subA E) (skip1 w) (skip1 x) (u - 2) * yK E x)
def SubRel : Prop :=
  ∀ (A : Type) [Ring A] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → A), GlRel E →
    GlRel (subA E) ∧ IsCov (subA E) (etaK E) ∧ IsVec (subA E) (yK E) ∧ (∀ a b, etaK E a * etaK E b = etaK E b * etaK E a) ∧
      (∀ a b, yK E a * yK E b = yK E b * yK E a) ∧
      ∀ a b, E (Fin.last n) (Fin.last n) * subA E a b = subA E a b * E (Fin.last n) (Fin.last n)
def RaiseNZ : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (l : Fin (n + 1) → ℂ), GlRel E → (∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) →
    ∀ m : Fin n → ℂ, Function.Injective m → CapSp (subA E) m ≠ ⊥ → ∀ i : Fin n, (∀ j, m i ≠ l j) →
      CapSp (subA E) (Function.update m i (m i + 1)) ≠ ⊥
def LowerNZ : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (l : Fin (n + 1) → ℂ), GlRel E → (∀ (w : ℂ) (v : V), qdet E w v = cpol l w • v) →
    ∀ m : Fin n → ℂ, Function.Injective m → CapSp (subA E) m ≠ ⊥ → ∀ i : Fin n, (∀ j, m i - 1 ≠ l j) →
      CapSp (subA E) (Function.update m i (m i - 1)) ≠ ⊥
def Decomp : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ), Hyp E β L →
    (∀ M, Box L M → CapSp (subA E) (shf β M) ≠ ⊥) ∧
      (⨆ (M : Fin n → ℤ) (_ : Box L M), CapSp (subA E) (shf β M)) = ⊤
def CapIndep : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (β : ℂ),
    iSupIndep fun M : {M : Fin n → ℤ // StrictAnti M} => CapSp E (shf β M.1)
def DualMinor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V), GlRel E →
    GlRel (dualE E) ∧ ∀ (t : ℕ) (a b : Fin t → Fin n) (w : ℂ), qminor (dualE E) a b w = (qminor E b a w).dualMap
def SpanTop : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (n : ℕ) (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V)
    (ν : Fin (n + 1) → ℂ) (v₀ : V), GlRel E → Irr E → IsHW E ν v₀ → v₀ ≠ 0 → ∀ ξ : Module.Dual ℂ V,
    (∀ a b : Fin n, b < a → ∀ v, ξ (subA E a b v) = 0) → (∀ a : Fin n → ℕ, ξ (mono (yK E) a v₀) = 0) → ξ = 0
def SpanSing : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (ξ₀ : Module.Dual ℂ V) (μ : Fin n → ℂ) (w : V),
    GlRel E → Irr E → ξ₀ ≠ 0 → (∀ a b : Fin (n + 1), b < a → ∀ v, ξ₀ (E a b v) = 0) → IsHW (subA E) μ w →
    (∀ a : Fin n → ℕ, ξ₀ (mono (etaK E) a w) = 0) → w = 0
def MultOne : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (μ : Fin n → ℂ) (w₁ w₂ : V), GlRel E → Irr E →
    IsHW (subA E) μ w₁ → IsHW (subA E) μ w₂ → w₁ ≠ 0 → ∃ c : ℂ, w₂ = c • w₁
def IrredCap : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ), Hyp E β L →
    ∀ M, Box L M → ∀ S' : Submodule ℂ V, S' ≤ CapSp (subA E) (shf β M) → Stab (subA E) S' →
      S' = ⊥ ∨ S' = CapSp (subA E) (shf β M)
def BranchingAlg : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (n : ℕ)
    (E : Fin (n + 1) → Fin (n + 1) → Module.End ℂ V) (β : ℂ) (L : Fin (n + 1) → ℤ), Hyp E β L →
    DirectSum.IsInternal (fun M : {M : Fin n → ℤ // Box L M} => CapSp (subA E) (shf β M.1)) ∧
      ∀ M : {M : Fin n → ℤ // Box L M}, CapSp (subA E) (shf β M.1) ≠ ⊥ ∧
        ∀ S' : Submodule ℂ V, S' ≤ CapSp (subA E) (shf β M.1) → Stab (subA E) S' →
          S' = ⊥ ∨ S' = CapSp (subA E) (shf β M.1)
end Formalism.FourierDecayAlt.Qr


