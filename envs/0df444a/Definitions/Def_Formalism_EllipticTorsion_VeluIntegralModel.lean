-- Prove2me | Definitions.Def_Formalism_EllipticTorsion_VeluIntegralModel
-- name    : Formalism_EllipticTorsion_VeluIntegralModel
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:56:18.121948+00:00
-- url     : https://prove2.me/theorems/5c6a1e30-c196-4224-9c35-b33b765269a2
-- title:
--   Velu Integral Model
-- statement:
--   Definitions and structural lemmas for Velu Integral Model, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/EllipticTorsion/VeluIntegralModel.lean

import Mathlib
import Definitions.Def_Formalism_EllipticTorsion_Statement
import Definitions.Def_Formalism_EllipticTorsion_WSeriesUnique
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
universe u
noncomputable section
namespace Formalism.ELL
open Formalism.G
section Velu
variable {L : Type u} [Field L]
def veluGx (W : WeierstrassCurve L) (x y : L) : L := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
def veluGy (W : WeierstrassCurve L) (x y : L) : L := -2 * y - W.a₁ * x - W.a₃
open Classical in
def veluV (W : WeierstrassCurve L) (x y : L) : L :=
  if veluGy W x y = 0 then veluGx W x y else 2 * veluGx W x y - W.a₁ * veluGy W x y
def veluU (W : WeierstrassCurve L) (x y : L) : L := veluGy W x y ^ 2
def veluCurve (W : WeierstrassCurve L) {k : ℕ} (S : Fin k → L × L) : WeierstrassCurve L :=
  ⟨W.a₁, W.a₂, W.a₃,
    W.a₄ - 5 * (∑ i, veluV W (S i).1 (S i).2),
    W.a₆ - (W.a₁ ^ 2 + 4 * W.a₂) * (∑ i, veluV W (S i).1 (S i).2)
      - 7 * (∑ i, (veluU W (S i).1 (S i).2 + (S i).1 * veluV W (S i).1 (S i).2))⟩
def veluX (W : WeierstrassCurve L) {k : ℕ} (S : Fin k → L × L) (x : L) : L :=
  x + ∑ i, (veluV W (S i).1 (S i).2 / (x - (S i).1) + veluU W (S i).1 (S i).2 / (x - (S i).1) ^ 2)
def veluY (W : WeierstrassCurve L) {k : ℕ} (S : Fin k → L × L) (x y : L) : L :=
  y - ∑ i, (veluU W (S i).1 (S i).2 * (2 * y + W.a₁ * x + W.a₃) / (x - (S i).1) ^ 3
      + veluV W (S i).1 (S i).2 * (W.a₁ * (x - (S i).1) + y - (S i).2) / (x - (S i).1) ^ 2
      + (W.a₁ * veluU W (S i).1 (S i).2 - veluGx W (S i).1 (S i).2 * veluGy W (S i).1 (S i).2)
          / (x - (S i).1) ^ 2)
end Velu
def VeluIntegralModel : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K) (k : ℕ)
    (S : Fin k → K × K), IntegralModel W → (∀ i, ‖(S i).1‖ ≤ 1 ∧ ‖(S i).2‖ ≤ 1) →
      IntegralModel (veluCurve W S)
def VeluUSeries : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] (W : WeierstrassCurve K)
    (w : PowerSeries K) (k : ℕ) (S : Fin k → K × K),
    IntegralModel W → WFixed W w → (∀ i, ‖(S i).1‖ ≤ 1 ∧ ‖(S i).2‖ ≤ 1) →
    let L := FractionRing (MvPowerSeries Unit K)
    let WL := W.map (algebraMap K L)
    let SL : Fin k → L × L := fun i => (algebraMap K L (S i).1, algebraMap K L (S i).2)
    let x := xOf w (MvPowerSeries.X () : MvPowerSeries Unit K)
    let y := yOf w (MvPowerSeries.X () : MvPowerSeries Unit K)
    ∃ f : PowerSeries K, IntegralPS f ∧ coeff 0 f = 0 ∧ coeff 1 f = 1 ∧
      algebraMap (MvPowerSeries Unit K) L f = -(veluX WL SL x) / veluY WL SL x y
end Formalism.ELL


