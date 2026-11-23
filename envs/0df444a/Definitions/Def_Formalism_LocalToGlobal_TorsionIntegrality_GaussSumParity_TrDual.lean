-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TrDual
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_TrDual
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:21.137102+00:00
-- url     : https://prove2.me/theorems/952f5628-fc0d-41ef-b2dc-7807da5a2236
-- title:
--   Tr Dual
-- statement:
--   Definitions and structural lemmas for Tr Dual, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/TrDual.lean

import Mathlib
import Definitions.Def_Formalism_GaussJetBounds_StatementP
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_IsLawOfLog
import Definitions.Def_Formalism_FormalGroupWitt_ShiftSOneLetter
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Formalism.L2.Th1.D
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2)
section Alg
variable {K : Type} [Field K]
open Classical in

def expF (K : Type) [Field K] (l : ℕ) : PowerSeries K :=
  if h : IsUnit (PowerSeries.coeff 1 (lgF K l)) then PowerSeries.substInvOfIsUnit (lgF K l) h else 0
def IsMul (l : ℕ) (c : K) (e : PowerSeries K) : Prop :=
  PowerSeries.constantCoeff e = 0 ∧ PowerSeries.subst e (lgF K l) = PowerSeries.C c * lgF K l
def addC (l : ℕ) (be0 : MvPowerSeries (Fin 2) K) : MvPowerSeries (Fin 2) K :=
  MvPowerSeries.subst ![at1 (0 : Fin 2) (expF K l), at1 (1 : Fin 2) (expF K l)] be0
variable {d : ℕ} [NeZero d]
def linE (σ : K →+* K) (c : K) : MvPowerSeries (ZMod d) K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then MvPowerSeries.C (σ^[s.val] c) * MvPowerSeries.X s else 0
def linO (σ : K →+* K) (c : K) : MvPowerSeries (ZMod d) K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then 0 else MvPowerSeries.C (σ^[s.val] c) * MvPowerSeries.X s
def beTil {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) : MvPowerSeries (ZMod d) K :=
  ∑ r, MvPowerSeries.subst ![linE σ (oms r), linO σ (om r)] (addC l be0)
def beMean {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K)
    (om oms : ι → K) (ζ : K) : MvPowerSeries (ZMod d) K :=
  MvPowerSeries.C (((l ^ d - 1 : ℕ) : K)⁻¹) *
    ∑ k ∈ Finset.range (l ^ d - 1), MvPowerSeries.subst (torus l (ζ ^ k)) (beTil l σ be0 om oms)
def letLog (l : ℕ) (s : ZMod d) : MvPowerSeries (ZMod d) K :=
  fun n => ∑ e ∈ Finset.range (n.degree + 1),
    if n = Finsupp.single (s - 2 * (e : ZMod d)) ((l ^ 2) ^ e) then ((l : K) ^ e)⁻¹ else 0
def zXY {ι : Type} [Fintype ι] (l : ℕ) (σ : K →+* K) (om oms : ι → K) (s : ZMod d) :
    MvPowerSeries (Bool × ι) K :=
  if s.val % 2 = 0 then ∑ r, MvPowerSeries.C (σ^[s.val] (om r)) * at1 (false, r) (lgF K l)
  else ∑ r, MvPowerSeries.C (σ^[s.val] (oms r)) * at1 (true, r) (lgF K l)
def mXY {ι : Type} (σ : K →+* K) (om oms : ι → K) (s : ZMod d) (x : Bool × ι) : K :=
  if s.val % 2 = 0 then (if x.1 = false then σ^[s.val] (om x.2) else 0)
  else (if x.1 = true then σ^[s.val] (oms x.2) else 0)
def beXY {ι : Type} [Fintype ι] (be0 : MvPowerSeries (Fin 2) K) : MvPowerSeries (Bool × ι) K :=
  ∑ r : ι, MvPowerSeries.subst
    ![(MvPowerSeries.X (false, r) : MvPowerSeries (Bool × ι) K), MvPowerSeries.X (true, r)] be0
def TrDual {ι : Type} [Fintype ι] [DecidableEq ι] (d : ℕ) [NeZero d] (σ : K →+* K)
    (om oms : ι → K) : Prop :=
  2 * Fintype.card ι = d ∧
  ∀ r r' : ι, (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (om r * oms r') else 0) =
    if r = r' then 1 else 0
end Alg
section Normed
variable {K : Type} [NormedField K]
def F1 [CharZero K] (F be0 : MvPowerSeries (Fin 2) K) : Prop :=
  DivAB be0 ∧ Simeq (d1 F be0) 0 ∧ Simeq (d1 F (swap2 be0)) 0
def F2 [CharZero K] (l : ℕ) (σ : K →+* K) (be0 : MvPowerSeries (Fin 2) K) : Prop :=
  ∀ α : K, ‖α‖ ≤ 1 → σ (σ α) = α → ∀ e e' : PowerSeries K, IsMul l α e → IsMul l (σ α) e' →
    Simeq (MvPowerSeries.subst ![at1 (0 : Fin 2) e, MvPowerSeries.X 1] be0)
      (MvPowerSeries.subst ![MvPowerSeries.X 0, at1 (1 : Fin 2) e'] be0)
def OwOK {ι : Type} (d : ℕ) (σ : K →+* K) (om oms : ι → K) : Prop :=
  (∀ r, ‖om r‖ ≤ 1 ∧ ‖oms r‖ ≤ 1) ∧ ∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r
end Normed
end Formalism.L2.Th1.D


