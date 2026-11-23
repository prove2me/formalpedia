-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_LetterShift
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:33.277869+00:00
-- url     : https://prove2.me/theorems/4da2a963-9e21-4858-bf12-f123ec732f5e
-- title:
--   Letter Shift
-- statement:
--   Definitions and structural lemmas for Letter Shift, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/GaussSumParity/LetterShift.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementA
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
open Formalism.DworkPowerSeriesWeights (Integral mvExp torus BHyp Unram NoLowBidegree letterLog entLog de1 de2)
open Formalism.InvariantFactorPaths.G7 (lgF at1 Simeq DivAB d1 swap2 UnrOK IsLawOfLog BetaHyp frobVar)
section Defs
variable {K : Type} [NormedField K] {τ : Type}
def IP (l : ℕ) (σ : K →+* K) (g : MvPowerSeries τ K) : Prop :=
  MvPowerSeries.constantCoeff g = 0 ∧
  Integral (g - MvPowerSeries.C ((l : K)⁻¹) * frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) g))
def ShiftType {d : ℕ} (l : ℕ) (σ : K →+* K) (L : ZMod d → MvPowerSeries τ K) : Prop :=
  ∀ s, MvPowerSeries.constantCoeff (L s) = 0 ∧
    Integral (L s - MvPowerSeries.C ((l : K)⁻¹) *
      frobVar (l ^ 2) (MvPowerSeries.map (σ.comp σ) (L (s - 2))))
def linEL {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) (L : ZMod d → MvPowerSeries τ K) :
    MvPowerSeries τ K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then MvPowerSeries.C (σ^[s.val] c) * L s else 0
def linOL {d : ℕ} [NeZero d] (σ : K →+* K) (c : K) (L : ZMod d → MvPowerSeries τ K) :
    MvPowerSeries τ K :=
  ∑ s : ZMod d, if s.val % 2 = 0 then 0 else MvPowerSeries.C (σ^[s.val] c) * L s
end Defs
def FrobSq : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → Formalism.G.FunctionalEquationSetting K l (l ^ 2) (σ.comp σ) ∧ ∀ a : K, ‖a‖ ≤ 1 → ‖σ a‖ ≤ 1
def IPLemma : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ (τ : Type) [Finite τ] (g : MvPowerSeries τ K), IP l σ g →
      ∃ h : MvPowerSeries τ K, MvPowerSeries.constantCoeff h = 0 ∧ Integral h ∧
        PowerSeries.subst h (lgF K l) = g
def IPClosure : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K)
    (τ : Type) [Finite τ],
    IP l σ (0 : MvPowerSeries τ K) ∧
    (∀ g g' : MvPowerSeries τ K, IP l σ g → IP l σ g' → IP l σ (g + g')) ∧
    (∀ (c : K) (g : MvPowerSeries τ K), ‖c‖ ≤ 1 → σ (σ c) = c → IP l σ g →
      IP l σ (MvPowerSeries.C c * g))
def ShiftIP : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), UnrOK K l σ → Even d → ∀ (τ : Type) [Finite τ] (L : ZMod d → MvPowerSeries τ K),
    ShiftType l σ L → ∀ c : K, ‖c‖ ≤ 1 → σ^[d] c = c →
      IP l σ (linEL σ c L) ∧ IP l σ (linOL σ c L)
def LetterShift : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l d : ℕ) [NeZero d]
    (σ : K →+* K), l.Prime →
    (∀ b : Bool, ShiftType l σ (fun s : ZMod d => letterLog (K := K) l (b, s))) ∧
    ShiftType l σ (fun s : ZMod d => letLog (K := K) l s) ∧
    ∀ (N0 N1 : ℕ) (a : Fin N0) (b : Fin N1),
      ShiftType l σ (fun s : ZMod d => entLog (K := K) (N0 := N0) (N1 := N1) l (s, a, b))
def PairRules : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K),
    UnrOK K l σ → ∀ F : MvPowerSeries (Fin 2) K, IsLawOfLog l F →
    ∀ be0 : MvPowerSeries (Fin 2) K, F1 F be0 → ∀ (τ : Type) [Finite τ],
    (∀ G G' H : MvPowerSeries τ K, IP l σ G → IP l σ G' → IP l σ H →
      Simeq (MvPowerSeries.subst ![G + G', H] (addC l be0))
        (MvPowerSeries.subst ![G, H] (addC l be0) + MvPowerSeries.subst ![G', H] (addC l be0))) ∧
    (∀ G H H' : MvPowerSeries τ K, IP l σ G → IP l σ H → IP l σ H' →
      Simeq (MvPowerSeries.subst ![G, H + H'] (addC l be0))
        (MvPowerSeries.subst ![G, H] (addC l be0) + MvPowerSeries.subst ![G, H'] (addC l be0))) ∧
    (F2 l σ be0 → ∀ (c : K) (G H : MvPowerSeries τ K), ‖c‖ ≤ 1 → σ (σ c) = c → IP l σ G →
      IP l σ H →
      Simeq (MvPowerSeries.subst ![MvPowerSeries.C c * G, H] (addC l be0))
        (MvPowerSeries.subst ![G, MvPowerSeries.C (σ c) * H] (addC l be0)))
def SubstTil : Prop :=
  ∀ (K : Type) [NormedField K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l →
    ∀ (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι] (om oms : ι → K) (τ : Type) [Finite τ]
      (L : ZMod d → MvPowerSeries τ K), (∀ s, MvPowerSeries.constantCoeff (L s) = 0) →
      MvPowerSeries.subst L (beTil l σ be0 om oms) =
        ∑ r, MvPowerSeries.subst ![linEL σ (oms r) L, linOL σ (om r) L] (addC l be0)
def TorusTil : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (σ : K →+* K), 2 ≤ l →
    ∀ (be0 : MvPowerSeries (Fin 2) K) (ι : Type) [Fintype ι] (om oms : ι → K) (u : K), u ≠ 0 →
      σ u = u ^ l →
      MvPowerSeries.subst (torus l u) (beTil (d := d) l σ be0 om oms) =
        beTil l σ be0 (fun r => u⁻¹ * om r) (fun r => u * oms r)
def TorusCoeff : Prop :=
  ∀ (K : Type) [Field K] (l d : ℕ) [NeZero d] (u : K) (f : MvPowerSeries (ZMod d) K)
    (n : ZMod d →₀ ℕ),
    MvPowerSeries.coeff n (MvPowerSeries.subst (torus l u) f) =
      (∏ s : ZMod d, (u ^ Formalism.DworkPowerSeriesWeights.lw l s) ^ n s) * MvPowerSeries.coeff n f
def DualExpand : Prop :=
  ∀ (K : Type) [Field K] (d : ℕ) [NeZero d] (σ : K →+* K), Even d →
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (om oms : ι → K),
      (∀ r, σ^[d] (om r) = om r ∧ σ^[d] (oms r) = oms r) → TrDual d σ om oms →
    ∀ x : K, σ^[d] x = x →
      (∀ r r', σ (σ (∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0)) =
        ∑ s : ZMod d, if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0) ∧
      (∀ r, x * oms r = ∑ r', (∑ s : ZMod d,
        if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0) * oms r') ∧
      (∀ r', x * om r' = ∑ r, (∑ s : ZMod d,
        if s.val % 2 = 0 then σ^[s.val] (x * oms r * om r') else 0) * om r)
end Formalism.L2.Th1.D


