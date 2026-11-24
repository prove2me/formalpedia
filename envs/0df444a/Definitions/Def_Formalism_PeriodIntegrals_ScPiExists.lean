-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
-- name    : Formalism_PeriodIntegrals_ScPiExists
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T12:24:12.472813+00:00
-- url     : https://prove2.me/theorems/8bfd3b70-5e38-45bb-9067-e0348180e2c4
-- title:
--   Sc Pi Exists
-- statement:
--   Definitions and structural lemmas for Sc Pi Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ScPiExists.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct ENNReal
open Matrix
namespace PI.ScPiExists
section Real
variable {n r : ℕ}
def hJ (ε : Fin n → Bool) (x y : Fin n → ℂ) : ℂ := star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)
def spanLt (e : Fin r → Fin n → ℂ) (a : ℕ) : Submodule ℂ (Fin n → ℂ) :=
  Submodule.span ℂ (e '' {b | b.1 < a})
def InS (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  (∀ a : Fin r, (g - 1) *ᵥ e a ∈ spanLt e a.1) ∧ (g - 1) *ᵥ z ∈ spanLt e r
def InN (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ) :
    Prop :=
  InS e z g ∧ ∀ y, (∀ a, hJ ε (e a) y = 0) → (g - 1) *ᵥ y ∈ spanLt e r
end Real
section Inst
variable (I : Formalism.MainNotions.S.AutInst)
def rv (v : InfinitePlace I.F) (x : Fin I.n → I.E) : Fin I.n → ℂ :=
  (I.P v)⁻¹ *ᵥ fun i => I.φ v (x i)
variable {r : ℕ}
def Sinf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InS (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}
def Ninf (e : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Set I.Ginf :=
  {s | ∀ v, InN (I.ε v) (fun a => rv I v (e a)) (rv I v z) (uMat (s v))}
def Hset (S : Set (Fin I.n → I.E)) : Set I.Ginf :=
  {s | ∀ v, ∀ x ∈ S, uMat (s v) *ᵥ rv I v x = rv I v x}
def matW {k : ℕ} (wf : Fin k → Fin I.n → ℂ) (v : InfinitePlace I.F) (s : I.Ginf) :
    Matrix (Fin k) (Fin k) ℂ :=
  fun a b => hJ (I.ε v) (wf a) (uMat (s v) *ᵥ wf b)
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
def IsRepS (S N : Set I.Ginf) (rho : I.Ginf → (V →L[ℂ] V)) : Prop :=
  rho 1 = 1 ∧ (∀ s ∈ S, ∀ t ∈ S, rho (s * t) = rho s * rho t) ∧
    (∀ s ∈ S, ∀ x y : V, ⟪rho s x, rho s y⟫_ℂ = ⟪x, y⟫_ℂ) ∧ (∀ s ∈ N, rho s = 1) ∧
    ∀ x : V, ContinuousOn (fun s => rho s x) S
end Inst
structure PiData (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (lam : InfinitePlace I.F → Fin k → ℝ) where
  Vpi : Type
  [vN : NormedAddCommGroup Vpi]
  [vI : InnerProductSpace ℂ Vpi]
  [vF : FiniteDimensional ℂ Vpi]
  piU : I.Ginf → (Vpi →L[ℂ] Vpi)
  piU_rep : IsRepS I (Sinf I e z) (Ninf I e z) piU
  Vloc : InfinitePlace I.F → Type
  [lN : ∀ v, NormedAddCommGroup (Vloc v)]
  [lI : ∀ v, InnerProductSpace ℂ (Vloc v)]
  [lF : ∀ v, FiniteDimensional ℂ (Vloc v)]
  piLoc : ∀ v, Matrix (Fin k) (Fin k) ℂ → (Vloc v →L[ℂ] Vloc v)
  piLoc_type : ∀ v, PI.UpqRep.IsHCTypeU k (lam v) (piLoc v)
  wfr : InfinitePlace I.F → Fin k → Fin I.n → ℂ
  wfr_on : ∀ v a b, hJ (I.ε v) (wfr v a) (wfr v b) = if a = b then 1 else 0
  wfr_perp : ∀ v a, (∀ c, hJ (I.ε v) (rv I v (e c)) (wfr v a) = 0 ∧
      hJ (I.ε v) (rv I v (f c)) (wfr v a) = 0) ∧
    hJ (I.ε v) (rv I v z) (wfr v a) = 0
  tensU : (∀ v, Vloc v) → Vpi
  tensU_inner : ∀ x y, ⟪tensU x, tensU y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ
  tensU_span : Submodule.span ℂ (Set.range tensU) = ⊤
  tensU_equiv : ∀ s ∈ Hset I (Set.range e ∪ Set.range f ∪ {z}), ∀ x,
    piU s (tensU x) = tensU (fun v => piLoc v (matW I (wfr v) v s) (x v))
attribute [instance] PiData.vN PiData.vI PiData.vF PiData.lN PiData.lI PiData.lF
def WeylHyp : Prop :=
  ∀ (k : ℕ) (u : Fin k → ℝ), PI.UpqRep.IsHCParam u →
    ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
      (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)), PI.UpqRep.IsHCTypeU k u π
def IsFrame (I : Formalism.MainNotions.S.AutInst) {r : ℕ} (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E) : Prop :=
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (e b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (f a) (f b) = 0) ∧
  (∀ a b, Formalism.UG.hform (starRingEnd I.E) I.J (e a) (f b) = if a = b then 1 else 0) ∧
  (∀ a, Formalism.UG.hform (starRingEnd I.E) I.J (e a) z = 0 ∧ Formalism.UG.hform (starRingEnd I.E) I.J (f a) z = 0)
def Frame : Prop :=
  ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E),
    I.n = 2 * r + k + 1 → IsFrame I e f z →
    (∃ t : ℕ, 0 < t ∧ Formalism.UG.hform (starRingEnd I.E) I.J z z = -(t : I.E)) →
    (∀ v (i : Fin I.n), I.ε v i = if i.val < k - 1 then true else decide ((i.val - (k - 1)) % 2 = 0)) →
    ∀ v, ∃ w : Fin k → Fin I.n → ℂ, (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0
def Build : Prop :=
  WeylHyp →
  ∀ (I : Formalism.MainNotions.S.AutInst) (r k : ℕ) (e f : Fin r → Fin I.n → I.E) (z : Fin I.n → I.E)
    (lam : InfinitePlace I.F → Fin k → ℝ),
    I.n = 2 * r + k + 1 → IsFrame I e f z → Formalism.UG.hform (starRingEnd I.E) I.J z z ≠ 0 →
    (∀ v, PI.UpqRep.IsHCParam (lam v)) →
    (∀ v, ∃ w : Fin k → Fin I.n → ℂ, (∀ a b, hJ (I.ε v) (w a) (w b) = if a = b then 1 else 0) ∧
      ∀ a, (∀ c, hJ (I.ε v) (rv I v (e c)) (w a) = 0 ∧ hJ (I.ε v) (rv I v (f c)) (w a) = 0) ∧
        hJ (I.ε v) (rv I v z) (w a) = 0) →
    Nonempty (PiData I k e f z lam)
end PI.ScPiExists


