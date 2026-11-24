-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementNF
-- name    : Formalism_HermitianCurvature_StatementNF
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-24T14:26:17.104807+00:00
-- url     : https://prove2.me/theorems/d1a7ed3e-b42b-4d21-88a8-30ae49a195f9
-- title:
--   Statement NF
-- statement:
--   Definitions and structural lemmas for Statement NF, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementNF.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_WeylElementCommutesLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
namespace Formalism.FourierDecayAlt.NF
open Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
def muZ (k r : ℕ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) : Q.Mx k r :=
  B2.embWb k r (μsec ζ)
def QR (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × ℂ) :=
  {q | q.1 ∈ OmX r ∧ Tz k r z * Tz k r z' < Complex.normSq q.2}
def Stab (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) : Set (Q.Mx k r × Q.Mx k r) :=
  {p | p.1 ∈ UWset k r z ∧ p.2 ∈ UWset k r z' ∧ p.1 * muZ k r μsec ζ * p.2 = muZ k r μsec ζ}
def Fib {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (ζ : ℂ) : Set (Wq →L[ℂ] Wp) :=
  {X | ∀ p ∈ Stab k r z z' μsec ζ, (π p.1).comp (X.comp (π' p.2)) = X}
def radR {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (Φ : Q.Fn k r E) :
    (Fin r → ℂ) × ℂ → E :=
  (QR k r z z').indicator fun q => Φ q.1 (muZ k r μsec q.2)
def RadSec {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) : Set ((Fin r → ℂ) × ℂ → (Wq →L[ℂ] Wp)) :=
  {φ | ContDiffOn ℝ ∞ φ (QR k r z z') ∧ (∀ q ∈ QR k r z z', φ q ∈ Fib k r z z' μsec π π' q.2) ∧
    ∀ q, q ∉ QR k r z z' → φ q = 0}
def RadBase {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) : Prop :=
  1 ≤ k ∧ inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧ 0 < Tz k r z' ∧ IsSection k r z z' μsec ∧
    IsCRepOn (UWset k r z) π ∧ IsCRepOn (UWset k r z') π' ∧ ContinuousOn π (UWset k r z) ∧
    ContinuousOn π' (UWset k r z')
def RadRedMem : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    RadBase k r z z' μsec π π' → ∀ Φ ∈ Q.RadSp k r z z' π π', radR k r z z' μsec Φ ∈ RadSec k r z z' μsec π π'
def RadRedInj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    RadBase k r z z' μsec π π' → ∀ Φ ∈ Q.RadSp k r z z' π π', ∀ Ψ ∈ Q.RadSp k r z z' π π',
      radR k r z z' μsec Φ = radR k r z z' μsec Ψ → Φ = Ψ
def RadRedSurj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    RadBase k r z z' μsec π π' → ∀ φ ∈ RadSec k r z z' μsec π π', ∃ Φ ∈ Q.RadSp k r z z' π π',
      radR k r z z' μsec Φ = φ
def mulZ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (f : ℂ → ℂ) (Φ : Q.Fn k r E) :
    Q.Fn k r E := fun c g =>
  (Q.DomR k r z z').indicator (fun x => f (Q.zetaL k r z z' (Fin.last r) x.2) • Φ x.1 x.2) (c, g)
def dZ (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 - Complex.I * fderiv ℝ f ζ Complex.I)
def dZb (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (1 / 2 : ℂ) * (fderiv ℝ f ζ 1 + Complex.I * fderiv ℝ f ζ Complex.I)
def IsRadDiff {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (T : Module.End ℂ (Q.RadSp k r z z' π π')) : Prop :=
  ∃ (n : ℕ) (A : (j : ℕ) → (Fin r → ℂ) × ℂ →
      (ContinuousMultilinearMap ℝ (fun _ : Fin j => (Fin r → ℂ) × ℂ) (Wq →L[ℂ] Wp) →L[ℝ] (Wq →L[ℂ] Wp))),
    (∀ j, ContDiffOn ℝ ∞ (A j) (QR k r z z')) ∧
    ∀ (Φ : Q.RadSp k r z z' π π'), ∀ q ∈ QR k r z z',
      radR k r z z' μsec (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) q =
        ∑ j ∈ Finset.range (n + 1), A j q (iteratedFDeriv ℝ j (radR k r z z' μsec (Φ : Q.Fn k r (Wq →L[ℂ] Wp))) q)
def RadOrder0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    RadBase k r z z' μsec π π' →
    ∀ (T : Module.End ℂ (Q.RadSp k r z z' π π')) (a b : ℂ), IsRadDiff k r z z' μsec π π' T →
      (∀ Φ Ψ : Q.RadSp k r z z' π π', (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' id (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' id (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) + a • (Φ : Q.Fn k r (Wq →L[ℂ] Wp))) →
      (∀ Φ Ψ : Q.RadSp k r z z' π π', (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' (starRingEnd ℂ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' (starRingEnd ℂ) (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) + b • (Φ : Q.Fn k r (Wq →L[ℂ] Wp))) →
      ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | Tz k r z * Tz k r z' < Complex.normSq ζ} →
      ∀ Φ Ψ : Q.RadSp k r z z' π π', (Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (Φ : Q.Fn k r (Wq →L[ℂ] Wp)) →
        (T Ψ : Q.Fn k r (Wq →L[ℂ] Wp)) = mulZ k r z z' f (T Φ : Q.Fn k r (Wq →L[ℂ] Wp)) +
          mulZ k r z z' (fun ζ => a * dZ f ζ + b * dZb f ζ) (Φ : Q.Fn k r (Wq →L[ℂ] Wp))
def TCoordComm : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ (X : Q.ActualOps P.k P.r z z' π π') (l : Fin P.r) (i : Fin 6),
      (∀ (Y : ℂ) (a b : Fin 2), X.t Y a b * X.op l i = X.op l i * X.t Y a b) ∧
      ∀ j : Fin 6, X.fn j * X.op l i = X.op l i * X.fn j
structure PreLevel (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) where
  p : Fin r → A
  pb : Fin r → A
  c : Fin r → A
  ci : Fin r → A
  cb : Fin r → A
  cbi : Fin r → A
  ζ : A
  ζi : A
  ζb : A
  ζbi : A
  GG : A
  GGi : A
  TT : ℂ

  fns_comm : ∀ x ∈ Set.range c ∪ Set.range ci ∪ Set.range cb ∪ Set.range cbi ∪ {ζ, ζi, ζb, ζbi, GG, GGi},
    ∀ y ∈ Set.range c ∪ Set.range ci ∪ Set.range cb ∪ Set.range cbi ∪ {ζ, ζi, ζb, ζbi, GG, GGi},
    x * y = y * x
  c_ci : ∀ l, c l * ci l = 1
  ci_c : ∀ l, ci l * c l = 1
  cb_cbi : ∀ l, cb l * cbi l = 1
  cbi_cb : ∀ l, cbi l * cb l = 1
  ζ_ζi : ζ * ζi = 1
  ζi_ζ : ζi * ζ = 1
  ζb_ζbi : ζb * ζbi = 1
  ζbi_ζb : ζbi * ζb = 1
  GG_GGi : GG * GGi = 1
  GGi_GG : GGi * GG = 1
  GG_def : GG = ζ * ζb - algebraMap ℂ A TT
  p_c : ∀ l m, p l * c m = c m * p l + (if l = m then c m else 0)
  p_ci : ∀ l m, p l * ci m = ci m * p l - (if l = m then ci m else 0)
  p_cb : ∀ l m, p l * cb m = cb m * p l
  p_cbi : ∀ l m, p l * cbi m = cbi m * p l
  p_ζ : ∀ l, p l * ζ = ζ * p l
  p_ζi : ∀ l, p l * ζi = ζi * p l
  p_ζb : ∀ l, p l * ζb = ζb * p l
  p_ζbi : ∀ l, p l * ζbi = ζbi * p l
  p_GG : ∀ l, p l * GG = GG * p l
  p_GGi : ∀ l, p l * GGi = GGi * p l
  pb_cb : ∀ l m, pb l * cb m = cb m * pb l + (if l = m then cb m else 0)
  pb_cbi : ∀ l m, pb l * cbi m = cbi m * pb l - (if l = m then cbi m else 0)
  pb_c : ∀ l m, pb l * c m = c m * pb l
  pb_ci : ∀ l m, pb l * ci m = ci m * pb l
  pb_ζ : ∀ l, pb l * ζ = ζ * pb l
  pb_ζi : ∀ l, pb l * ζi = ζi * pb l
  pb_ζb : ∀ l, pb l * ζb = ζb * pb l
  pb_ζbi : ∀ l, pb l * ζbi = ζbi * pb l
  pb_GG : ∀ l, pb l * GG = GG * pb l
  pb_GGi : ∀ l, pb l * GGi = GGi * pb l
  p_p : ∀ l m, p l * p m = p m * p l
  p_pb : ∀ l m, p l * pb m = pb m * p l
  pb_pb : ∀ l m, pb l * pb m = pb m * pb l
namespace PreLevel
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
def ofLevel (L : R.LevelData A r) : PreLevel A r where
  p := L.p
  pb := L.pb
  c := L.c
  ci := L.ci
  cb := L.cb
  cbi := L.cbi
  ζ := L.ζ
  ζi := L.ζi
  ζb := L.ζb
  ζbi := L.ζbi
  GG := L.GG
  GGi := L.GGi
  TT := L.TT
  fns_comm := L.fns_comm
  c_ci := L.c_ci
  ci_c := L.ci_c
  cb_cbi := L.cb_cbi
  cbi_cb := L.cbi_cb
  ζ_ζi := L.ζ_ζi
  ζi_ζ := L.ζi_ζ
  ζb_ζbi := L.ζb_ζbi
  ζbi_ζb := L.ζbi_ζb
  GG_GGi := L.GG_GGi
  GGi_GG := L.GGi_GG
  GG_def := L.GG_def
  p_c := L.p_c
  p_ci := L.p_ci
  p_cb := L.p_cb
  p_cbi := L.p_cbi
  p_ζ := L.p_ζ
  p_ζi := L.p_ζi
  p_ζb := L.p_ζb
  p_ζbi := L.p_ζbi
  p_GG := L.p_GG
  p_GGi := L.p_GGi
  pb_cb := L.pb_cb
  pb_cbi := L.pb_cbi
  pb_c := L.pb_c
  pb_ci := L.pb_ci
  pb_ζ := L.pb_ζ
  pb_ζi := L.pb_ζi
  pb_ζb := L.pb_ζb
  pb_ζbi := L.pb_ζbi
  pb_GG := L.pb_GG
  pb_GGi := L.pb_GGi
  p_p := L.p_p
  p_pb := L.p_pb
  pb_pb := L.pb_pb
variable (L0 : PreLevel A r)
def fns : Set A :=
  Set.range L0.c ∪ Set.range L0.ci ∪ Set.range L0.cb ∪ Set.range L0.cbi ∪ {L0.ζ, L0.ζi, L0.ζb, L0.ζbi, L0.GG, L0.GGi}
def crdOps : Set A :=
  Set.range L0.c ∪ Set.range L0.ci ∪ Set.range L0.cb ∪ Set.range L0.cbi ∪ Set.range L0.p ∪ Set.range L0.pb
def ops : Set A := L0.fns ∪ Set.range L0.p ∪ Set.range L0.pb
def Ext (L : R.LevelData A r) : Prop :=
  L.p = L0.p ∧
    L.pb = L0.pb ∧
    L.c = L0.c ∧
    L.ci = L0.ci ∧
    L.cb = L0.cb ∧
    L.cbi = L0.cbi ∧
    L.ζ = L0.ζ ∧
    L.ζi = L0.ζi ∧
    L.ζb = L0.ζb ∧
    L.ζbi = L0.ζbi ∧
    L.GG = L0.GG ∧
    L.GGi = L0.GGi ∧
    L.TT = L0.TT
end PreLevel
def IsActualPre {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} (X : Q.ActualOps k r z z' π π')
    (L0 : PreLevel (Q.Pr (Q.RadSp k r z z' π π')) r) : Prop :=
  (∀ l, L0.p l = Q.mkP (X.op l 0) (-X.op l 3)) ∧ (∀ l, L0.pb l = Q.mkP (X.op l 3) (-X.op l 0)) ∧
  (∀ l, L0.c l = Q.mkP (X.op l 1) (X.op l 4)) ∧ (∀ l, L0.ci l = Q.mkP (X.op l 2) (X.op l 5)) ∧
  (∀ l, L0.cb l = Q.mkP (X.op l 4) (X.op l 1)) ∧ (∀ l, L0.cbi l = Q.mkP (X.op l 5) (X.op l 2)) ∧
  L0.ζ = Q.mkP (X.fn 0) (X.fn 2) ∧ L0.ζi = Q.mkP (X.fn 1) (X.fn 3) ∧ L0.ζb = Q.mkP (X.fn 2) (X.fn 0) ∧
  L0.ζbi = Q.mkP (X.fn 3) (X.fn 1) ∧ L0.GG = Q.mkP (X.fn 4) (X.fn 4) ∧ L0.GGi = Q.mkP (X.fn 5) (X.fn 5) ∧
  L0.TT = ((Tz k r z * Tz k r z' : ℝ) : ℂ)
section Ring
variable {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A]
def proj (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (ρ : M.Ty P) : A := κ fun ρ' => if ρ' = ρ then 1 else 0
def xA (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (Y : ℂ) : A := κ fun ρ => M.xC P ρ Y
def xiA (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (Y : ℂ) : A := κ fun ρ => (M.xC P ρ Y)⁻¹
def lA (L0 : PreLevel A P.r) (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (Y : ℂ) : A :=
  xiA κ Y * L0.GGi * QQ Y 1 0
def nabDef (L0 : PreLevel A P.r) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) : A :=
  -(∑ ρ, proj κ ρ * b ρ * proj κ ρ) - (1 / 2 : ℂ) • (L0.ζb * L0.GGi)
def Raises (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (SS : ℕ → A) : Prop :=
  ∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → κ g * SS l = SS l * κ f
end Ring
def Reg (P : M.Par) (Y : ℂ) : Prop := ∀ ρ : M.Ty P, M.xC P ρ Y ≠ 0
def SHyp (P : M.Par) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (L0 : PreLevel A P.r)
    (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) : Prop :=
  star L0.ζ = L0.ζb ∧ star L0.TT = L0.TT ∧
  (∀ l, star (L0.c l) = L0.cb l ∧ star (L0.ci l) = L0.cbi l ∧ star (L0.p l) = -L0.pb l) ∧
  Wd.IsStart QQ (M.qC P) ∧ (∀ Y Y', Commute (QQ Y 1 0) (QQ Y' 1 0)) ∧
  (∀ Y, QQ Y 1 1 = L0.GG * xA κ Y) ∧
  (∀ f : M.Ty P → ℂ, star (κ f) = κ fun ρ => star (f ρ)) ∧
  (∀ f : M.Ty P → ℂ, ∀ g ∈ L0.ops, Commute (κ f) g) ∧
  (∃ (n : ℕ) (C : Fin 2 → Fin 2 → ℕ → A), (∀ Y a b, QQ Y a b = ∑ j ∈ Finset.range n, Y ^ j • C a b j) ∧
    ∀ Y, QQ Y 1 0 = -(Y ^ P.k • L0.ζb) + ∑ j ∈ Finset.range P.k, Y ^ j • C 1 0 j) ∧
  (∀ Y, QQ Y 1 0 * L0.ζ = L0.ζ * QQ Y 1 0 - QQ Y 1 1 ∧ QQ Y 1 1 * L0.ζ = L0.ζ * QQ Y 1 1 ∧
    QQ Y 0 1 * L0.ζ = L0.ζ * QQ Y 0 1 ∧ QQ Y 0 1 * L0.ζb = L0.ζb * QQ Y 0 1 + QQ Y 1 1 ∧
    QQ Y 1 0 * L0.ζb = L0.ζb * QQ Y 1 0 ∧ QQ Y 1 1 * L0.ζb = L0.ζb * QQ Y 1 1) ∧
  (∀ Y (a b : Fin 2), ∀ g ∈ L0.crdOps, Commute (QQ Y a b) g)
def ModelSHyp : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (M.A P) P.r), P.OK → M.IsModelLevel P L →
    SHyp P (PreLevel.ofLevel L) (M.QQr P) (M.kap P)
def SForm (P : M.Par) {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (L0 : PreLevel A P.r)
    (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) (SS : ℕ → A) : Prop :=
  ∀ Y, Reg P Y → ∀ ρ ρ' : M.Ty P,
    proj κ ρ' * lA L0 QQ κ Y * proj κ ρ =
      (if ρ' = ρ then (b ρ - Y • (L0.ζb * L0.GGi)) * proj κ ρ else 0) +
        ∑ l ∈ Finset.Icc 1 (P.k - 1),
          if M.Up P l ρ ρ' then (Y + (M.rho P ρ l : ℂ) + 1)⁻¹ • (L0.GGi * SS l * proj κ ρ) else 0
def RelCore {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : Prop :=
  (∀ f : M.Ty P → ℂ, star (d.κ f) = d.κ (fun ρ => star (f ρ))) ∧
  (∀ f : M.Ty P → ℂ, ∀ g ∈ d.L.fns ∪ {d.L.nab, d.L.nabs}, Commute (d.κ f) g) ∧
  (∀ l, ∀ g ∈ d.L.fns ∪ Set.range d.L.p ∪ Set.range d.L.pb, Commute (d.SS l) g) ∧
  (∀ l (f g : M.Ty P → ℂ), (∀ ρ ρ', M.Up P l ρ ρ' → g ρ' = f ρ) → d.κ g * d.SS l = d.SS l * d.κ f) ∧
  (∀ l ∈ Finset.Icc 1 (P.k - 1),
    d.L.nab * d.SS l = d.SS l * d.L.nab - d.L.ζb * d.L.GGi * d.SS l ∧
    d.L.nabs * d.SS l = d.SS l * d.L.nabs - d.L.ζ * d.L.GGi * d.SS l)
def RelNorm {P : M.Par} {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), star (d.SS l) * d.SS l = d.κ fun ρ => ((M.Nrm P l ρ : ℝ) : ℂ)
def RelIsCoreNorm : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (d : Q.NFData P A), d.Rel ↔ RelCore d ∧ RelNorm d
def SBlock : Prop :=
  M.TyInterlaces → M.TyComplete → M.RhoUp →
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (L0 : PreLevel A P.r)
    (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A), P.OK → SHyp P L0 QQ κ →
    ∃ (b : M.Ty P → A) (SS : ℕ → A), SForm P L0 QQ κ b SS ∧ Raises κ SS ∧ ∀ l, ∀ g ∈ L0.ops, Commute (SS l) g
def SConn : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (L0 : PreLevel A P.r)
    (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) (SS : ℕ → A),
    P.OK → SHyp P L0 QQ κ → SForm P L0 QQ κ b SS → Raises κ SS → (∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) →
    ∃ L : R.LevelData A P.r, L0.Ext L ∧ L.nab = nabDef L0 κ b ∧ L.nabs = star (nabDef L0 κ b) ∧
      Fr.IsStarLevel L ∧ RelCore (⟨L, κ, SS⟩ : Q.NFData P A) ∧
      ∀ Y, QQ Y 1 0 = (Q.NFData.QQ ⟨L, κ, SS⟩ Y) 1 0 ∧ QQ Y 0 1 = (Q.NFData.QQ ⟨L, κ, SS⟩ Y) 0 1 ∧
        QQ Y 1 1 = (Q.NFData.QQ ⟨L, κ, SS⟩ Y) 1 1
def SNorm : Prop :=
  M.TyInterlaces → M.TyComplete → M.RhoUp → M.NrmFacts → M.RealPoints → M.WExact →
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (L0 : PreLevel A P.r)
    (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A) (b : M.Ty P → A) (SS : ℕ → A)
    (L : R.LevelData A P.r),
    P.OK → SHyp P L0 QQ κ → SForm P L0 QQ κ b SS → Raises κ SS → (∀ l, ∀ g ∈ L0.ops, Commute (SS l) g) →
    L0.Ext L → L.nab = nabDef L0 κ b → L.nabs = star (nabDef L0 κ b) → Fr.IsStarLevel L →
    RelCore (⟨L, κ, SS⟩ : Q.NFData P A) →
    (∀ Y, QQ Y 1 0 = (Q.NFData.QQ ⟨L, κ, SS⟩ Y) 1 0 ∧ QQ Y 0 1 = (Q.NFData.QQ ⟨L, κ, SS⟩ Y) 0 1) →
    RelNorm (⟨L, κ, SS⟩ : Q.NFData P A) ∧ ∀ Y, QQ Y 0 0 = (Q.NFData.QQ ⟨L, κ, SS⟩ Y) 0 0
def ThmSRing : Prop :=
  ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] (L0 : PreLevel A P.r)
    (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (κ : (M.Ty P → ℂ) →ₐ[ℂ] A), P.OK → SHyp P L0 QQ κ →
    ∃ d : Q.NFData P A, L0.Ext d.L ∧ d.κ = κ ∧ Fr.IsStarLevel d.L ∧ d.Rel ∧ ∀ Y, QQ Y = d.QQ Y
def ThmSOfSteps : Prop :=
  M.TyInterlaces → M.TyComplete → M.RhoUp → M.NrmFacts → M.RealPoints → M.WExact →
    SBlock → SConn → SNorm → RelIsCoreNorm → ThmSRing
def ActualPreLevel : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ X : Q.ActualOps P.k P.r z z' π π',
      ∃ L0 : PreLevel (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r, IsActualPre X L0
def ActualSHyp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → ∀ (X : Q.ActualOps P.k P.r z z' π π') (L0 : PreLevel (Q.Pr (Q.RadSp P.k P.r z z' π π')) P.r),
      IsActualPre X L0 → ∃ κ : (M.Ty P → ℂ) →ₐ[ℂ] Q.Pr (Q.RadSp P.k P.r z z' π π'), SHyp P L0 X.QQ κ
def ActualSHypOfParts : Prop :=
  Q.ActualStart → Q.ZetaComm → Q.Leading → Q.RadialDecompositionSpectral → TCoordComm → M.TyComplete → ActualSHyp
def NormalFormOfS : Prop := ThmSRing → ActualPreLevel → ActualSHyp → Q.NormalFormActual
def NormalFormFromModuleOfParts : Prop :=
  ThmSRing → ActualPreLevel → ActualSHypOfParts → TCoordComm → M.TyComplete → Q.NormalFormFromModule
end
end Formalism.FourierDecayAlt.NF


