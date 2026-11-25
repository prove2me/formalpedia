-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PBFCstmt
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_PBFCstmt
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T02:57:55.536738+00:00
-- url     : https://prove2.me/theorems/379ee743-1f4b-46c3-9c20-cb21539b1405
-- title:
--   PBFCstmt
-- statement:
--   Definitions and structural lemmas for PBFCstmt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PBFCstmt.lean

import Definitions.Def_Formalism_HermitianCurvature_RealInputsClosedAdmissibleSettings
import Definitions.Def_Formalism_HermitianCurvature_HerGenC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.KB
open Finset Filter Topology NumberField MeasureTheory Matrix Formalism.QuantumDeterminants
noncomputable section
def SizeStdCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (ys : List ℝ),
    CutWord P p.l0 (plusW ys w) → CutWord P p.l0 (minusW ys w) → ys.Pairwise (fun y y' => 2 < |y - y'|) →
    (∀ y ∈ ys, 0 < (Wd.qw (M.qC P) (D.positionted w) y).re) ∧
    ∀ x x', (∀ e, CptCoef (p.T.bs j) (x e)) → (∀ e, CptCoef (p.T.bs j) (x' e)) →
      ‖pairJ (p.form j hj w) ys x x'‖ ^ 2 * (ys.map fun y : ℝ => (Wd.qw (M.qC P) (D.positionted w) y).re).prod ≤
        (p.form j hj (plusW ys w) x x).re * (p.form j hj (minusW ys w) x' x').re
def VIsoCpt : Prop :=
  P5.ThmPActualCpt → ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : Pl P Wp Wq) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter), CutWord P p.l0 w →
    ∀ (s : ℂ) x x', (∀ e, CptCoef (p.T.bs j) (x e)) → (∀ e, CptCoef (p.T.bs j) (x' e)) →
      (∀ e, CptCoef (p.T.bs j) (waveG (p.T.bs j) s w x e)) ∧
      p.form j hj w (waveG (p.T.bs j) s w x) (waveG (p.T.bs j) s w x') = p.form j hj w x x'
end
end Formalism.FourierDecayAlt.KB


