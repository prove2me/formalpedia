-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:40:15.854241+00:00
-- url     : https://prove2.me/theorems/52d61aa9-1613-469e-b5b6-95acb10f3296
-- title:
--   Col Choice Fintype
-- statement:
--   Definitions and structural lemmas for Col Choice Fintype, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InvariantMetricIsometry/ColChoiceFintype.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoInvMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace PI.IsoInvMetricW
open PI.IsoInvMetric
instance finOE (h N : ℕ) : Fintype (Fin h ↪o Fin N) :=
  haveI : Finite (Fin h ↪o Fin N) :=
    Finite.of_injective (fun e : Fin h ↪o Fin N => (e : Fin h → Fin N)) DFunLike.coe_injective
  Fintype.ofFinite _
instance colChoiceFintype {Lt : Type} [Fintype Lt] [DecidableEq Lt] (N : ℕ)
    (nu : Lt → YoungDiagram) : Fintype (ColChoice N nu) := by
  unfold ColChoice; infer_instance
def E {Lt : Type} [Fintype Lt] {N N' : ℕ} (nu : Lt → YoungDiagram)
    (f : Lt → Matrix (Fin N') (Fin N) ℂ) (I : ColChoice N' nu) (J : ColChoice N nu) : ℂ :=
  ∏ s, ∏ c : Fin ((nu s).rowLen 0),
    Matrix.det (Matrix.of fun i k : Fin ((nu s).colLen c) => f s (I s c i) (J s c k))
def fr {Lt : Type} {N : ℕ} (f : Lt → Matrix (Fin N) (Fin N) ℂ) (x : Lt → Fin N → ℕ → ℂ) :
    Lt → Fin N → ℕ → ℂ :=
  fun s a j => ∑ b, f s a b * x s b j
def ipl {Lt : Type} [Fintype Lt] [DecidableEq Lt] {N : ℕ} {nu : Lt → YoungDiagram}
    (φ ψ : LaC N nu) : ℂ :=
  ∑ J, star (φ J) * ψ J
def u0 {Lt : Type} [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram) : LaC N nu :=
  hvC N nu fun _ => colsOf 1
def CB : Prop :=
  ∀ (h N : ℕ) (A : Matrix (Fin h) (Fin N) ℂ) (B : Matrix (Fin N) (Fin h) ℂ),
    (A * B).det = ∑ J : Fin h ↪o Fin N, (A.submatrix id J).det * (B.submatrix J id).det
def HvMap : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (f : Lt → Matrix (Fin N) (Fin N) ℂ) (x : Lt → Fin N → ℕ → ℂ),
    VnuMap nu f (hvC N nu x) = hvC N nu (fr f x)
def EMul : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (f g : Lt → Matrix (Fin N) (Fin N) ℂ) (I K : ColChoice N nu),
    ∑ J, E nu f I J * E nu g J K = E nu (fun s => f s * g s) I K
open Classical in

def EDiag : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (d : Lt → Fin N → ℂ) (I J : ColChoice N nu),
    E nu (fun s => Matrix.diagonal (d s)) I J =
      if I = J then ∏ s, ∏ c : Fin ((nu s).rowLen 0), ∏ i, d s (J s c i) else 0
def QR : Prop :=
  ∀ (N : ℕ) (X : Matrix (Fin N) (Fin N) ℂ),
    ∃ k ∈ Matrix.unitaryGroup (Fin N) ℂ, ∀ a j : Fin N, j < a → (star k * X) a j = 0
def Unit : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (k : Lt → Matrix (Fin N) (Fin N) ℂ), (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
    ∀ φ ψ : LaC N nu, ipl (VnuMap nu k φ) (VnuMap nu k ψ) = ipl φ ψ
def InvK : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (k : Lt → Matrix (Fin N) (Fin N) ℂ), (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
    ∀ φ : LaC N nu, VnuMap nu k (VnuMap nu (fun z => star (k z)) φ) = φ
def Stab : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (f : Lt → Matrix (Fin N) (Fin N) ℂ) (φ : LaC N nu), φ ∈ Vnu N nu → VnuMap nu f φ ∈ Vnu N nu
def HvCols : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (k : Lt → Matrix (Fin N) (Fin N) ℂ),
    (hvC N nu fun z => colsOf (k z)) = VnuMap nu k (u0 N nu)
def Norm1 : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram),
    (∀ z, (nu z).colLen 0 ≤ N) → l2 (u0 N nu) = 1
def Gen : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (x : Lt → Fin N → ℕ → ℂ), ∃ k : Lt → Matrix (Fin N) (Fin N) ℂ,
      (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) ∧
      ∃ c : ℂ, hvC N nu x = c • hvC N nu (fun z => colsOf (k z))
def HW : Prop :=
  ∀ (Lt : Type) [Fintype Lt] [DecidableEq Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (ip : LaC N nu →ₗ⋆[ℂ] LaC N nu →ₗ[ℂ] ℂ),
    (∀ k : Lt → Matrix (Fin N) (Fin N) ℂ, (∀ z, k z ∈ Matrix.unitaryGroup (Fin N) ℂ) →
      (∀ φ ∈ Vnu N nu, ∀ ψ ∈ Vnu N nu, ip (VnuMap nu k φ) (VnuMap nu k ψ) = ip φ ψ) ∧
      ip (hvC N nu fun z => colsOf (k z)) (hvC N nu fun z => colsOf (k z)) = 1) →
    ∀ ψ ∈ Vnu N nu, ip (u0 N nu) ψ = ipl (u0 N nu) ψ
end PI.IsoInvMetricW


