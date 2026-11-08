-- Prove2me | Definitions.Def_MaxCompForest_respForm
-- name    : MaxCompForest_respForm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:34:20.189892+00:00
-- url     : https://prove2.me/theorems/0895c4cd-5be4-41c9-8918-20cb8e577af0
-- title:
--   The family form $C_F^{1/2}B_F^{\top}(D^{-1}+R)B_FC_F^{1/2}$
-- statement:
--   For positive vertex masses $d$, $D=\mathrm{diag}(d_v)$, a vertex matrix $R$ and a set $F$ of edge labels, the matrix
--   $$
--   C_F^{1/2}B_F^{\top}(D^{-1}+R)B_FC_F^{1/2} ,
--   $$
--   indexed by $F$. With $R$ the slow response this is $P_F$ of (E.8), and with $R=\mathbf F^{\top}\mathbf F$ it is $\widehat P_F$ of (E.15).
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), (E.8) p.39, (E.15) p.40, (3.8) p.16

import Mathlib
import Definitions.Def_MaxCompForest_edgeMat
import Definitions.Def_MaxCompForest_onLabels
open EffResSparsify.ResistanceSketch

namespace MaxCompForest

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- **The family form** `P_F = C_F^{1/2} B_Fᵀ (D⁻¹ + R) B_F C_F^{1/2}` for vertex masses `d` and a vertex
matrix `R`.
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), (E.8) p.39; (E.15) p.40 and (3.8) p.16 for `R = 𝐅ᵀ𝐅`.

**Formalization Note.** The inverse is junk at a zero mass; every use has positive masses. -/
noncomputable def respForm (G : WGraph V E) (d : V → ℝ) (R : Matrix V V ℝ) (F : Finset E) :
    Matrix F F ℝ :=
  onLabels (edgeMat G (Matrix.diagonal (fun v => (d v)⁻¹) + R)) F

end MaxCompForest


