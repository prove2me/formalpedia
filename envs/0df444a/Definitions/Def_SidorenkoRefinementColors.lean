-- Prove2me | Definitions.Def_SidorenkoRefinementColors
-- name    : SidorenkoRefinementColors
-- status  : Definition
-- author  : @abcdefg
-- created : 2026-10-08T17:16:52.913397+00:00
-- url     : https://prove2.me/theorems/6f1bf393-415a-47cd-9db5-8aeee0e23f70
-- title:
--   The four incidence-color refinement tables
-- statement:
--   The fixed incidence graph has point set $I=\mathrm{Fin}(13)$, face set $J=\mathrm{Fin}(22)$, and corner set $E=\mathrm{Fin}(22)\times\mathrm{Fin}(3)$. Given $t:E\to A$ and a corner-color map $c:E\to C$, its neighbor histogram is
--   $$
--   H(v,d)=|\{e\in E:t(e)=v,\ c(e)=d\}|.
--   $$
--   The interface specifies five successive color maps on each vertex class, with colors in $\mathrm{Fin}(35)$. Stage zero colors the two classes constantly. The remaining maps are the explicit refinement tables in the source.
--
--   These data define the finite objects used by the separate refinement-certificate theorems. The definition file contains no refinement claims or pinning theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Sidorenko/Refinement.lean#L11, definitions refineLeft0 through refineRight4; Dilution.lean#L127, neighborHistogram.

import Mathlib
import Definitions.Def_SidorenkoPinningScores
namespace OAI.SidorenkoCounterexample
open scoped BigOperators
variable {I E C : Type*} [Fintype E] [DecidableEq I] [DecidableEq C]
def neighborHistogram (t : E → I) (c : E → C) (i : I) (d : C) : ℕ :=
  ∑ e,if t e=i ∧ c e=d then 1 else 0
def refineLeft0 : Fin 13 → Fin 35 := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def refineRight0 : Fin 22 → Fin 35 := ![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def refineLeft1 : Fin 13 → Fin 35 := ![0, 2, 0, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1]
def refineRight1 : Fin 22 → Fin 35 := ![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]
def refineLeft2 : Fin 13 → Fin 35 := ![0, 2, 0, 2, 1, 0, 1, 1, 1, 2, 1, 2, 1]
def refineRight2 : Fin 22 → Fin 35 := ![6, 6, 9, 9, 3, 4, 4, 3, 7, 7, 3, 3, 4, 4, 8, 7, 8, 7, 5, 4, 5, 4]
def refineLeft3 : Fin 13 → Fin 35 := ![2, 11, 0, 12, 6, 1, 3, 4, 5, 9, 8, 10, 7]
def refineRight3 : Fin 22 → Fin 35 := ![16, 16, 19, 19, 13, 14, 14, 13, 17, 17, 13, 13, 14, 14, 18, 17, 18, 17, 15, 14, 15, 14]
def refineLeft4 : Fin 13 → Fin 35 := ![2, 11, 0, 12, 6, 1, 3, 4, 5, 9, 8, 10, 7]
def refineRight4 : Fin 22 → Fin 35 := ![25, 26, 33, 34, 13, 20, 21, 15, 29, 30, 16, 14, 19, 18, 32, 28, 31, 27, 24, 22, 23, 17]
end OAI.SidorenkoCounterexample


