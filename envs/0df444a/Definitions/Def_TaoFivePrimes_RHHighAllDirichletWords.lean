-- Prove2me | Definitions.Def_TaoFivePrimes_RHHighAllDirichletWords
-- name    : TaoFivePrimes_RHHighAllDirichletWords
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T05:32:50.21085+00:00
-- url     : https://prove2.me/theorems/eee814a4-cbe5-4bf3-bc86-9ffe39b13be1
-- title:
--   All50000 proposed finite Dirichlet words with bounded block lookup
-- statement:
--   Collects the33 existing proposed Dirichlet-word packets and gives an index lookup through1536-term packets and512-entry rows. The total50000-word length is checked by the ordinary kernel. This definition asserts no arithmetic/analytic correctness, binning identity, sign, count or RH.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHHighDirichletValues00
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues01
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues02
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues03
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues04
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues05
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues06
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues07
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues08
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues09
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues10
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues11
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues12
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues13
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues14
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues15
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues16
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues17
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues18
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues19
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues20
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues21
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues22
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues23
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues24
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues25
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues26
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues27
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues28
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues29
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues30
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues31
import Definitions.Def_TaoFivePrimes_RHHighDirichletValues32
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHHighAllDirichletWords
noncomputable def packets : List (List (List Nat)) := [RHHighDirichletValues00.rows,RHHighDirichletValues01.rows,RHHighDirichletValues02.rows,RHHighDirichletValues03.rows,RHHighDirichletValues04.rows,RHHighDirichletValues05.rows,RHHighDirichletValues06.rows,RHHighDirichletValues07.rows,RHHighDirichletValues08.rows,RHHighDirichletValues09.rows,RHHighDirichletValues10.rows,RHHighDirichletValues11.rows,RHHighDirichletValues12.rows,RHHighDirichletValues13.rows,RHHighDirichletValues14.rows,RHHighDirichletValues15.rows,RHHighDirichletValues16.rows,RHHighDirichletValues17.rows,RHHighDirichletValues18.rows,RHHighDirichletValues19.rows,RHHighDirichletValues20.rows,RHHighDirichletValues21.rows,RHHighDirichletValues22.rows,RHHighDirichletValues23.rows,RHHighDirichletValues24.rows,RHHighDirichletValues25.rows,RHHighDirichletValues26.rows,RHHighDirichletValues27.rows,RHHighDirichletValues28.rows,RHHighDirichletValues29.rows,RHHighDirichletValues30.rows,RHHighDirichletValues31.rows,RHHighDirichletValues32.rows]
noncomputable def values : List Nat := packets.flatten.flatten
noncomputable def word (n : Nat) : Nat :=
  let i:=n-1
  let rows:=(packets[i/1536]?).getD []
  let row:=(rows[(i%1536)/512]?).getD []
  (row[i%512]?).getD 0
theorem values_length : values.length=50000 := by decide +kernel
end RHHighAllDirichletWords
noncomputable def TaoFivePrimes_RHHighAllDirichletWords : Nat := 50000


