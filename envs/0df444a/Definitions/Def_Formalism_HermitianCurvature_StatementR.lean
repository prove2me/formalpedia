-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementR
-- name    : Formalism_HermitianCurvature_StatementR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:11:58.212571+00:00
-- url     : https://prove2.me/theorems/c87c5976-efd8-4f61-910e-06eadb6934ca
-- title:
--   Statement R
-- statement:
--   Definitions and structural lemmas for Statement R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementR.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.R
open Matrix
structure LevelData (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) where
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
  nab : A
  nabs : A
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
  p_nab : ∀ l, p l * nab = nab * p l
  pb_nab : ∀ l, pb l * nab = nab * pb l
  p_nabs : ∀ l, p l * nabs = nabs * p l
  pb_nabs : ∀ l, pb l * nabs = nabs * pb l
  nab_ζ : nab * ζ = ζ * nab + 1
  nab_ζi : nab * ζi = ζi * nab - ζi * ζi
  nab_ζb : nab * ζb = ζb * nab
  nab_ζbi : nab * ζbi = ζbi * nab
  nab_GG : nab * GG = GG * nab + ζb
  nab_GGi : nab * GGi = GGi * nab - ζb * GGi * GGi
  nab_c : ∀ l, nab * c l = c l * nab
  nab_ci : ∀ l, nab * ci l = ci l * nab
  nab_cb : ∀ l, nab * cb l = cb l * nab
  nab_cbi : ∀ l, nab * cbi l = cbi l * nab
  nabs_ζb : nabs * ζb = ζb * nabs - 1
  nabs_ζbi : nabs * ζbi = ζbi * nabs + ζbi * ζbi
  nabs_ζ : nabs * ζ = ζ * nabs
  nabs_ζi : nabs * ζi = ζi * nabs
  nabs_GG : nabs * GG = GG * nabs - ζ
  nabs_GGi : nabs * GGi = GGi * nabs + ζ * GGi * GGi
  nabs_c : ∀ l, nabs * c l = c l * nabs
  nabs_ci : ∀ l, nabs * ci l = ci l * nabs
  nabs_cb : ∀ l, nabs * cb l = cb l * nabs
  nabs_cbi : ∀ l, nabs * cbi l = cbi l * nabs
variable {A : Type} [Ring A] [Algebra ℂ A] {r : ℕ}
namespace LevelData
noncomputable section
variable (L : LevelData A r)
def fns : Set A :=
  Set.range L.c ∪ Set.range L.ci ∪ Set.range L.cb ∪ Set.range L.cbi ∪ {L.ζ, L.ζi, L.ζb, L.ζbi, L.GG, L.GGi}
def Tl (Y : ℂ) (l : Fin r) : Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap ℂ A Y + L.p l, -L.c l; L.ci l, 0]
def Tvl (Y : ℂ) (l : Fin r) : Matrix (Fin 2) (Fin 2) A :=
  !![algebraMap ℂ A Y - L.pb l, -L.cb l; L.cbi l, 0]
def Tprod (Y : ℂ) : Matrix (Fin 2) (Fin 2) A := ((List.ofFn (L.Tl Y)).reverse).prod
def Tvprod (Y : ℂ) : Matrix (Fin 2) (Fin 2) A := ((List.ofFn (L.Tvl Y)).reverse).prod
def Ar (Y : ℂ) : A := L.Tprod Y 0 0
def Br (Y : ℂ) : A := L.Tprod Y 1 0
def Avr (Y : ℂ) : A := L.Tvprod Y 0 0
def Bvr (Y : ℂ) : A := L.Tvprod Y 1 0
def Dr : A := (List.ofFn L.c).prod
def Drb : A := (List.ofFn L.cb).prod
def Dri : A := (List.ofFn L.ci).prod
def Drbi : A := (List.ofFn L.cbi).prod
def l0 (Y : ℂ) : A := -L.nab - algebraMap ℂ A (Y + 1/2) * (L.ζb * L.GGi)
def m0 (Y : ℂ) : A := -L.nabs - algebraMap ℂ A (Y - 1/2) * (L.ζ * L.GGi)
def Ahat (Y : ℂ) : A := L.Dr * L.Ar Y
def R0 (Y : ℂ) : A := L.Drb * L.GG * (L.l0 Y * L.Ar Y + L.Br Y)
def Ahatv (Y : ℂ) : A := L.Drb * L.Avr Y
def R0v (Y : ℂ) : A := L.Dr * L.GG * (L.m0 Y * L.Avr Y + L.Bvr Y)
def D : A := L.Dr * L.ζ
def Di : A := L.ζi * L.Dri
def Db : A := L.Drb * L.ζb
def Dbi : A := L.ζbi * L.Drbi
def G : A := L.Dr * L.Drb * L.GG
end
end LevelData
open LevelData
def RuleG : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (s : ℂ) (Gs Gsi : A),
    Gs * Gsi = 1 → Gsi * Gs = 1 → (∀ x ∈ L.fns, x * Gs = Gs * x) →
    (∀ l, L.p l * Gs = Gs * L.p l + algebraMap ℂ A s * Gs) →
    (∀ l, L.pb l * Gs = Gs * L.pb l + algebraMap ℂ A s * Gs) →
    L.nab * Gs = Gs * L.nab + algebraMap ℂ A s * (L.ζb * L.GGi * Gs) →
    L.nabs * Gs = Gs * L.nabs - algebraMap ℂ A s * (L.ζ * L.GGi * Gs) →
    ∀ Y : ℂ, Gsi * L.Ahat Y * Gs = L.Ahat (Y + s) ∧ Gsi * L.R0 Y * Gs = L.R0 (Y + s) ∧
      Gsi * L.Ahatv Y * Gs = L.Ahatv (Y - s) ∧ Gsi * L.R0v Y * Gs = L.R0v (Y - s)
def RuleD : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (Y : ℂ),
    L.Di * L.Ahat Y * L.D = L.Ahat (Y + 1) ∧
    L.Di * L.R0 Y * L.D = L.R0 (Y + 1) + algebraMap ℂ A L.TT * (L.Drb * L.Di * L.Ahat (Y + 1)) ∧
    L.Dbi * L.Ahatv Y * L.Db = L.Ahatv (Y - 1) ∧
    L.Dbi * L.R0v Y * L.Db = L.R0v (Y - 1) - algebraMap ℂ A L.TT * (L.Dr * L.Dbi * L.Ahatv (Y - 1)) ∧
    (∀ x ∈ Set.range L.cb ∪ Set.range L.cbi ∪ {L.ζb, L.ζbi},
      x * L.Ahat Y = L.Ahat Y * x ∧ x * L.R0 Y = L.R0 Y * x) ∧
    (∀ x ∈ Set.range L.c ∪ Set.range L.ci ∪ {L.ζ, L.ζi},
      x * L.Ahatv Y = L.Ahatv Y * x ∧ x * L.R0v Y = L.R0v Y * x)
def RuleSS : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (SS SSs : A),
    (∀ x ∈ L.fns, x * SS = SS * x) → (∀ l, L.p l * SS = SS * L.p l) →
    (∀ l, L.pb l * SS = SS * L.pb l) →
    L.nab * SS = SS * L.nab - L.ζb * L.GGi * SS → L.nabs * SS = SS * L.nabs - L.ζ * L.GGi * SS →
    (∀ x ∈ L.fns, x * SSs = SSs * x) → (∀ l, L.p l * SSs = SSs * L.p l) →
    (∀ l, L.pb l * SSs = SSs * L.pb l) →
    L.nab * SSs = SSs * L.nab + L.ζb * L.GGi * SSs →
    L.nabs * SSs = SSs * L.nabs + L.ζ * L.GGi * SSs →
    ∀ Y : ℂ,
      L.Ahat Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.Ahat (Y - 1) ∧
      L.R0 Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.R0 (Y - 1) ∧
      L.Ahatv Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.Ahatv (Y - 1) ∧
      L.R0v Y * (L.Drb * L.Dri * SS) = (L.Drb * L.Dri * SS) * L.R0v (Y - 1) ∧
      L.Ahat Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.Ahat (Y + 1) ∧
      L.R0 Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.R0 (Y + 1) ∧
      L.Ahatv Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.Ahatv (Y + 1) ∧
      L.R0v Y * (SSs * (L.Dr * L.Drbi)) = (SSs * (L.Dr * L.Drbi)) * L.R0v (Y + 1)
def RuleInv : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r) (Y : ℂ),
    L.ζbi * L.Ahat Y = L.Ahat Y * L.ζbi ∧ L.ζbi * L.R0 Y = L.R0 Y * L.ζbi ∧
    L.ζbi * L.Ahatv Y = L.Ahatv Y * L.ζbi ∧
    L.R0v Y * L.ζbi - L.ζbi * L.R0v Y = -(L.G * L.Dbi * L.Dbi * L.Ahatv Y) ∧
    L.ζi * L.Ahat Y = L.Ahat Y * L.ζi ∧ L.ζi * L.Ahatv Y = L.Ahatv Y * L.ζi ∧
    L.ζi * L.R0v Y = L.R0v Y * L.ζi ∧
    L.R0 Y * L.ζi - L.ζi * L.R0 Y = L.G * L.Di * L.Di * L.Ahat Y
end Formalism.FourierDecayAlt.R


