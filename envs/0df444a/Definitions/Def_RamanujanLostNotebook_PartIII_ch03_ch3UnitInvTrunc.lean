-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartIII_ch03_ch3UnitInvTrunc
-- name    : RamanujanLostNotebook_PartIII_ch03_ch3UnitInvTrunc
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-11T09:01:29.198279+00:00
-- url     : https://prove2.me/theorems/54a71192-ab57-49bc-80f2-c85399c35cf6
-- title:
--   Ramanujan's Lost Notebook Part III, Ch. 3: ch3UnitInvTrunc
-- statement:
--   Sum_{j=0}^N(1-P)^j, representing 1/P through degree N when P(0)=1.
--   Every use here has constant term one. Higher geometric terms have degree >N;
--   there is no division in the coefficient ring and no assumption of an identity.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part III, Springer 2012, Chapter 3.

import Mathlib

noncomputable section

namespace RamanujanLostNotebook.PartIII

/-- Sum_{j=0}^N(1-P)^j, representing 1/P through degree N when P(0)=1.
Every use here has constant term one. Higher geometric terms have degree >N;
there is no division in the coefficient ring and no assumption of an identity. -/
noncomputable def ch3UnitInvTrunc {R : Type*} [CommRing R]
    (N : ℕ) (P : Polynomial R) : Polynomial R :=
  ∑ j ∈ Finset.range (N + 1), (1 - P) ^ j

end RamanujanLostNotebook.PartIII

end


