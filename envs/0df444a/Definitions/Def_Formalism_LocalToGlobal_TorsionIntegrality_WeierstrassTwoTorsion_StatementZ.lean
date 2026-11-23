-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementZ
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:58:30.483822+00:00
-- url     : https://prove2.me/theorems/e1fa8ce9-5803-44bd-beff-abd7a32d1cea
-- title:
--   Statement Z
-- statement:
--   Definitions and structural lemmas for Statement Z, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/WeierstrassTwoTorsion/StatementZ.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementC
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
namespace Formalism.L2.Th1.A
def LogSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (logSer W) = 0 ∧ coeff 1 (logSer W) = 1 ∧ derivative K (logSer W) = om W ∧
    D W (logSer W) = 1
def ExpSpec : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    constantCoeff (expSer W) = 0 ∧ coeff 1 (expSer W) = 1 ∧
    (logSer W).subst (expSer W) = X ∧ (expSer W).subst (logSer W) = X ∧
    derivative K (expSer W) = (fw W).subst (expSer W)
def ChainZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (f : K⟦X⟧),
    derivative K (f.subst (expSer W)) = (D W f).subst (expSer W)
def LogNeg : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    (logSer W).subst (iSer W) = -logSer W ∧
    (expSer W).subst (-X : K⟦X⟧) = (iSer W).subst (expSer W)
def FlowZ : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    IsFlow (curveL W) dL (xZ W) (yZ W) ∧ toL (expSer W) * yZ W = -xZ W
def WpODE : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    dL (wpL W) = 2 * yZ W + HahnSeries.C W.a₁ * xZ W + HahnSeries.C W.a₃ ∧
    dL (wpL W) ^ 2 = 4 * wpL W ^ 3 - HahnSeries.C (g₂ W) * wpL W - HahnSeries.C (g₃ W) ∧
    dL (dL (wpL W)) = 6 * wpL W ^ 2 - HahnSeries.C (g₂ W / 2)
def WpShape : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K),
    wpL W = uPow (-2) + toL (wpReg W) ∧ coeff 0 (wpReg W) = 0 ∧
    (∀ n : ℕ, Odd n → coeff n (wpReg W) = 0) ∧
    coeff 2 (wpReg W) = g₂ W / 20 ∧ coeff 4 (wpReg W) = g₃ W / 28
def WpUnique : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (g2 g3 : K) (r r' : K⟦X⟧),
    dL (uPow (-2) + toL r) ^ 2 = 4 * (uPow (-2) + toL r) ^ 3
      - HahnSeries.C g2 * (uPow (-2) + toL r) - HahnSeries.C g3 →
    dL (uPow (-2) + toL r') ^ 2 = 4 * (uPow (-2) + toL r') ^ 3
      - HahnSeries.C g2 * (uPow (-2) + toL r') - HahnSeries.C g3 →
    r = r'
def WpRecursion : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (W : WeierstrassCurve K) (k : ℕ), 3 ≤ k →
    ((k : K) - 2) * (2 * (k : K) + 3) * coeff (2 * k) (wpReg W) =
      3 * ∑ i ∈ Finset.Icc 1 (k - 2), coeff (2 * i) (wpReg W) * coeff (2 * (k - 1 - i)) (wpReg W)
end Formalism.L2.Th1.A


