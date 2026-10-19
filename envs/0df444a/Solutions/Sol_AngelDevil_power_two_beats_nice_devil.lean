-- Prove2me | solution 1 for AngelDevil.power_two_beats_nice_devil
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-18T14:15:14.111302+00:00
-- url     : https://prove2.me/submissions/b8f1dd37-d9a2-4dec-8cd8-df14d87cadd5

import Theorems.Thm_AngelDevil_niceAngelWins_of_wall_no_return
import Theorems.Thm_AngelDevil_wallTrace_never_returns

theorem solution : AngelDevil.NiceAngelWins 2 :=
  AngelDevil.niceAngelWins_of_wall_no_return AngelDevil.wallTrace_never_returns
