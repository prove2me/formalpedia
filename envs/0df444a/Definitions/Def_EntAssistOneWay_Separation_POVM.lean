-- Prove2me | Definitions.Def_EntAssistOneWay_Separation_POVM
-- name    : EntAssistOneWay_Separation_POVM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:43:33.889213+00:00
-- url     : https://prove2.me/theorems/5e8a54b7-fa14-4947-88a8-942b8dbe08b9
-- title:
--   Bundled published POVMs and binary effects
-- statement:
--   On $\mathbb C^I$, a finite positive operator-valued measurement with outcomes $Z$ consists of operators $A_z$ satisfying
--   $$A_z\succeq0\quad(z\in Z),\qquad\sum_z A_z=I.$$
--   A binary effect $B$ satisfies $B\succeq0$ and $I-B\succeq0$; these are the two outcome operators of a binary measurement.
--
--   The POVM bundle uses the published Wilde predicate with no extra conditions. This general measurement interface is shared by the entanglement-assisted communication and remote preparation models. Positive semidefiniteness includes Hermiticity; it is not replaced by a condition on diagonal entries.
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), pp. 16, 18–19, POVM descriptions in Lemma 3.2 and the one-way model

import Definitions.Def_WildeQIT_QMemory_IsPOVM

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- A finite positive operator-valued measurement on a coordinate Hilbert space. -/
structure POVM (I Z : Type) [Fintype I] [DecidableEq I] [Fintype Z] where
  op : Z → Matrix I I ℂ
  valid : WildeQIT.QMemory.IsPOVM op

/-- One element of a binary POVM; the other is I - B. -/
structure BinaryEffect (I : Type) [Fintype I] [DecidableEq I] where
  op : Matrix I I ℂ
  positive : op.PosSemidef
  complement_positive : (1 - op).PosSemidef

end

end EntAssistOneWay.Separation


