-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
-- name    : Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T16:31:38.621323+00:00
-- url     : https://prove2.me/theorems/b66a34a4-47f1-4823-9d83-0536406038bc
-- title:
--   Sum Io Pr Alt
-- statement:
--   Definitions and structural lemmas for Sum Io Pr Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/SumIoPrAlt.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_CapelliEig
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothAdd
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_smooth_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
noncomputable section
namespace BranchingSupport
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData
abbrev GG (k r : ℕ) : Set (Mx k r) := Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)
structure Rep (k r : ℕ) : Type 1 where
  H : Type
  [nacg : NormedAddCommGroup H]
  [ips : InnerProductSpace ℂ H]
  [cs : CompleteSpace H]
  σ : Mx k r → (H →L[ℂ] H)
attribute [instance] Rep.nacg Rep.ips Rep.cs
variable {k r : ℕ}
abbrev Rep.sm (R : Rep k r) : Set R.H := PI.UpqRep.smoothVecs (k := k) (r := r) R.σ
abbrev Rep.KFin (R : Rep k r) (v : R.H) : Prop := PI.UpqRep.IsKFinHpk (k := k) (r := r) R.σ v
def Rep.IsDS (R : Rep k r) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  Formalism.QuantumDeterminants.IsHCParam mu ∧ PI.UpqRep.IsDSHpk k r ε mu R.σ
def Rep.TK (R : Rep k r) : Submodule ℂ R.H :=
  Submodule.span ℂ {v | ∃ g ∈ GG k r, ∃ v₀, R.KFin v₀ ∧ v = R.σ g v₀}
def Rep.smSub (R : Rep k r) : Submodule ℂ R.H where
  carrier := R.sm
  zero_mem' := Formalism.FourierDecayAlt.P.DDSmoothness.smooth_zero R.σ
  add_mem' := fun hv hw => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_add hv hw
  smul_mem' := fun a _ hv => Formalism.FourierDecayAlt.P.DDSmoothness.smooth_smul a hv
def Rep.dC (R : Rep k r) (Y : Mx k r) (v : R.H) : R.H :=
  PI.UpqRep.dsig (k := k) (r := r) R.σ
      ((1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) v +
    Complex.I • PI.UpqRep.dsig (k := k) (r := r) R.σ
      ((1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))) v
def Rep.IsE (R : Rep k r) (Q : Mx k r)
    (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub) : Prop :=
  ∀ a b (v : R.smSub), ((E a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b 1 * Q) v
structure SmMap (R R' : Rep k r) (T : R.H → R'.H) : Prop where
  mem : ∀ v ∈ R.sm, T v ∈ R'.sm
  add : ∀ v ∈ R.sm, ∀ w ∈ R.sm, T (v + w) = T v + T w
  smul : ∀ (a : ℂ), ∀ v ∈ R.sm, T (a • v) = a • T v
  cont : ∀ W : List (Mx k r), (∀ X ∈ W, PI.UpqRep.InLieHpk k r X) →
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ
      (fun v => PI.UpqRep.dsigW (k := k) (r := r) R'.σ W (T v))
section tens
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
def act (ρ : Mx k r → Matrix ι ι ℂ) (R : Rep k r) (g : Mx k r) (x : ι → R.H) : ι → R.H :=
  fun i => ∑ j, ρ g i j • R.σ g (x j)
def hh (Γ : Matrix ι ι ℂ) (R : Rep k r) (x y : ι → R.H) : ℂ := ∑ i, ∑ j, Γ i j * ⟪y i, x j⟫_ℂ
def tm (R : Rep k r) (a : ι → ℂ) (w : R.H) : ι → R.H := fun i => a i • w
def ev (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) : R.H :=
  ∑ i, ∑ j, (star (a i) * Γ i j) • x j
structure TensRaw (ρ : Mx k r → Matrix ι ι ℂ) (R : Rep k r) (RI : κ → Rep k r)
    (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) : Prop where
  io_sm : ∀ I c, SmMap (RI I) R (io I c)
  pr_sm : ∀ I c, SmMap R (RI I) (pr I c)
  io_eq : ∀ I, ∀ g ∈ GG k r, ∀ y ∈ (RI I).sm, (fun c => io I c ((RI I).σ g y)) = act ρ R g (fun c => io I c y)
  pr_eq : ∀ I, ∀ g ∈ GG k r, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) →
    ∑ c, pr I c (act ρ R g x c) = (RI I).σ g (∑ c, pr I c (x c))
  sum_io_pr : ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → ∀ c, ∑ I, io I c (∑ d, pr I d (x d)) = x c
  pr_io : ∀ I, ∀ y ∈ (RI I).sm, ∑ c, pr I c (io I c y) = y
  pr_io_ne : ∀ I J, I ≠ J → ∀ y ∈ (RI J).sm, ∑ c, pr I c (io J c y) = 0
structure TensH (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (R : Rep k r) (RI : κ → Rep k r)
    (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) : Prop where
  raw : TensRaw ρ R RI io pr
  ep_sq : ∀ I, ep I = 1 ∨ ep I = -1
  iso : ∀ I, ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI I).sm,
    hh Γ R (fun c => io I c y) (fun c => io I c y') = (ep I : ℂ) * ⟪y', y⟫_ℂ
  orth : ∀ I J, I ≠ J → ∀ y ∈ (RI I).sm, ∀ y' ∈ (RI J).sm, hh Γ R (fun c => io I c y) (fun c => io J c y') = 0
def IsFRep (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) : Prop :=
  Γᴴ = Γ ∧ Γ * Γ = 1 ∧ ρ 1 = 1 ∧ (∀ g ∈ GG k r, ∀ h ∈ GG k r, ρ (g * h) = ρ g * ρ h) ∧
  (∀ g ∈ GG k r, (ρ g)ᴴ * Γ * ρ g = Γ) ∧ (∀ i j, ContinuousOn (fun g => ρ g i j) (GG k r)) ∧
  (∃ C : ℝ, ∀ g ∈ GG k r, ∀ i j, ‖ρ g i j‖ ≤ C * B.gN g ^ d) ∧
  ∀ g ∈ GG k r, g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ → ρ g ∈ Matrix.unitaryGroup ι ℂ
end tens
abbrev Sub (n l : ℕ) : Type := {I : Finset (Fin n) // I.card = l}
def cmp {n : ℕ} (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Sub n l) (Sub n l) ℂ :=
  fun I J => (g.submatrix (I.1.orderEmbOfFin I.2) (J.1.orderEmbOfFin J.2)).det
def wedge {n l : ℕ} (f : Fin l → Fin n → ℂ) : Sub n l → ℂ :=
  fun I => (Matrix.of fun a b : Fin l => f b (I.1.orderEmbOfFin I.2 a)).det
def dualM {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (g⁻¹)ᵀ
def flat (k r : ℕ) (f : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun c => Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (Pi.single c 1) f
def addSet {n : ℕ} (mu : Fin n → ℝ) (I : Finset (Fin n)) : Fin n → ℝ := fun a => mu a + if a ∈ I then 1 else 0
section side
variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
def SideG (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ)
    (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) : Prop :=
  Formalism.QuantumDeterminants.inWb k r z ∧ 0 < Formalism.QuantumDeterminants.Tz k r z ∧ (∃ u₀, PI.UpqRep.IsHCTypeW k r z u₀ π) ∧
    Q.CapParam k r z π u ∧
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW ∧
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN ∧
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG ∧
    PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq
abbrev IsBes (R : Rep k r) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp) : Prop :=
  PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd) R.σ π l
def IsBeL (R : Rep k r) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) : Prop :=
  IsBes R z π l ∧ ∀ w ∈ R.sm, ∀ v ∈ R.TK,
    Integrable (beInt z Formalism.QuantumDeterminants.cStd π R.σ w v) (μW.prod μN) ∧
    be z Formalism.QuantumDeterminants.cStd π R.σ μW μN w v = (innerSL ℂ (l v)).smulRight (l w)
def IsIsoB (R : Rep k r) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (Bm : R.H → Wp) : Prop :=
  IsBes R z π Bm ∧ ∀ w ∈ R.sm,
    PI.BesselPeriodGGP.l2SG νq (fun g => Bm (R.σ g w)) = ENNReal.ofReal (‖w‖ ^ 2)
def NzOn (R : Rep k r) (l : R.H → Wp) : Prop := ∃ w ∈ R.sm, l w ≠ 0
end side
def lenA (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : Mx k r) (a : Fin (r + 1)) : ℝ :=
  Metric.infDist (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z a) : EuclideanSpace ℂ (Fin (2 * r + k + 1)))
    (Submodule.span ℂ ((fun b => (WithLp.toLp 2 (g⁻¹ *ᵥ Formalism.QuantumDeterminants.fvec k r z b) :
      EuclideanSpace ℂ (Fin (2 * r + k + 1)))) '' {b | b < a}) : Set _)
def Num (k r : ℕ) (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) : Prop :=
  1 ≤ k ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
  (∀ a, ∀ i ∈ Icc 1 k, ∃ m : ℤ, lam a - u i = (m : ℝ) + 1 / 2) ∧
  (∀ a : Fin (2 * r + k + 1), a.val < k → lam a < u (a.val + 1)) ∧
  (∀ a : Fin (2 * r + k + 1), a.val + 1 < k → u (a.val + 2) < lam a) ∧
  (∀ a : Fin (2 * r + k + 1), a.val + 1 < k → 0 ≤ lam a ∧ lam a ≤ bv / 8) ∧
  (∀ a : Fin (2 * r + k + 1), k ≤ a.val + 1 → -2 * bv ≤ lam a ∧ lam a ≤ -bv) ∧
  (∀ a, |lam a| ≤ b) ∧ (∀ i ∈ Icc 1 k, |u i| ≤ b) ∧
  (∀ a c : Fin (2 * r + k + 1), a < c → c.val + 1 < k → ga ≤ lam a - lam c) ∧
  Formalism.QuantumDeterminants.GapAtLeast (PI.BesselPeriodGGP.eps48 k r) lam h ∧ GapOK k r (h / 4) ∧
  100 * ((q0 : ℝ) + 1) ≤ ga ∧ 100 * ((q0 : ℝ) + 1) ≤ h ∧
  10 ^ 6 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 7 ≤ bv
def IsFam (lam : Fin (2 * r + k + 1) → ℝ) (q0 : ℕ) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) : Prop :=
  ∀ ν, ∑ a, (ν a).natAbs ≤ q0 → (R ν).IsDS (PI.BesselPeriodGGP.eps48 k r) (fun a => lam a + (ν a : ℝ))
end BranchingSupport


