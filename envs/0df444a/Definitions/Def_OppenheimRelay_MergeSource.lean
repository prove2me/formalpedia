-- Prove2me | Definitions.Def_OppenheimRelay_MergeSource
-- name    : OppenheimRelay_MergeSource
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:26:29.901991+00:00
-- url     : https://prove2.me/theorems/7f09fced-290c-4fda-8612-6dd941e72fba
-- title:
--   The merging source: registers $R, A, B$ of one copy
-- statement:
--   One copy of a state-merging source has three registers: $A$, held by the sender Alice; $B$, held by the receiver Bob; and a reference $R$ purifying $\rho_{AB}$. The joint basis is $R\times(A\times B)$, and statements quantify over unit vectors $\phi$ on this space.
--
--   It is the setting of the paper's account of (coherent) state merging, which the relay protocol applies twice.
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, paragraphs "We will show that redistribution uses quantum state merging…" and "Now, to perform merging…"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20

namespace OppenheimRelay

/-- **The merging source.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, paragraph "We will show that redistribution uses…" ("In
state merging Alice and Bob share n copies of state ρAB"), purified as on p.1: the three registers
of one copy, in the order R, A, B, with A the sender's share, B the receiver's and R the reference. -/
abbrev MergeSource (A B R : Type*) := R × (A × B)

end OppenheimRelay


