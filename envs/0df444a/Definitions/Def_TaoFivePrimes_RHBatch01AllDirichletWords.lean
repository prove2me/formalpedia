-- Prove2me | Definitions.Def_TaoFivePrimes_RHBatch01AllDirichletWords
-- name    : TaoFivePrimes_RHBatch01AllDirichletWords
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-15T21:58:53.096574+00:00
-- url     : https://prove2.me/theorems/9e882864-b78f-44c4-b222-73183083b16f
-- title:
--   All50000 proposed finite Dirichlet words with bounded block lookup
-- statement:
--   Collects the33 existing proposed Dirichlet-word packets and gives an index lookup through1536-term packets and512-entry rows. The total50000-word length is checked by the ordinary kernel. This definition asserts no arithmetic/analytic correctness, binning identity, sign, count or RH.
-- source:
--   Existing Platt Fourier construction, DOI10.1090/mcom/3198. Original surrounding attribution sometik179 c9908072-d99a-4431-aad8-a72c6352619a and Gabewhigham.

import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues00
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues01
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues02
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues03
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues04
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues05
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues06
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues07
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues08
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues09
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues10
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues11
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues12
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues13
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues14
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues15
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues16
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues17
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues18
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues19
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues20
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues21
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues22
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues23
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues24
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues25
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues26
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues27
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues28
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues29
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues30
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues31
import Definitions.Def_TaoFivePrimes_RHBatch01DirichletValues32
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace RHBatch01AllDirichletWords
noncomputable def packets : List (List (List Nat)) := [RHBatch01DirichletValues00.rows,RHBatch01DirichletValues01.rows,RHBatch01DirichletValues02.rows,RHBatch01DirichletValues03.rows,RHBatch01DirichletValues04.rows,RHBatch01DirichletValues05.rows,RHBatch01DirichletValues06.rows,RHBatch01DirichletValues07.rows,RHBatch01DirichletValues08.rows,RHBatch01DirichletValues09.rows,RHBatch01DirichletValues10.rows,RHBatch01DirichletValues11.rows,RHBatch01DirichletValues12.rows,RHBatch01DirichletValues13.rows,RHBatch01DirichletValues14.rows,RHBatch01DirichletValues15.rows,RHBatch01DirichletValues16.rows,RHBatch01DirichletValues17.rows,RHBatch01DirichletValues18.rows,RHBatch01DirichletValues19.rows,RHBatch01DirichletValues20.rows,RHBatch01DirichletValues21.rows,RHBatch01DirichletValues22.rows,RHBatch01DirichletValues23.rows,RHBatch01DirichletValues24.rows,RHBatch01DirichletValues25.rows,RHBatch01DirichletValues26.rows,RHBatch01DirichletValues27.rows,RHBatch01DirichletValues28.rows,RHBatch01DirichletValues29.rows,RHBatch01DirichletValues30.rows,RHBatch01DirichletValues31.rows,RHBatch01DirichletValues32.rows]
noncomputable def values : List Nat := packets.flatten.flatten
noncomputable def word (n : Nat) : Nat :=
  let i:=n-1
  let rows:=(packets[i/1536]?).getD []
  let row:=(rows[(i%1536)/512]?).getD []
  (row[i%512]?).getD 0
theorem values_length : values.length=50000 := by decide +kernel
end RHBatch01AllDirichletWords
noncomputable def TaoFivePrimes_RHBatch01AllDirichletWords : Nat := 50000


