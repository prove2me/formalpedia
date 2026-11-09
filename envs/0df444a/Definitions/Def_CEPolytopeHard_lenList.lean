-- Prove2me | Definitions.Def_CEPolytopeHard_lenList
-- name    : CEPolytopeHard_lenList
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:26.025351+00:00
-- url     : https://prove2.me/theorems/a0dd5cfc-840e-4868-9c89-de1872a72a1b
-- title:
--   Length-prefixed list code
-- statement:
--   For a code $\mathrm{enc}$ of the elements of a type as finite lists of natural numbers, a finite list $(a_1, \dots, a_n)$ is coded as
--   $$
--   \big(n,\ \mathrm{enc}(a_1),\ \dots,\ \mathrm{enc}(a_n)\big),
--   $$
--   its length followed by the concatenated codes of its entries. Together with the binary self-delimiting code of natural numbers (`pack`), this makes the codes of games, distributions and circuits uniquely decodable.
--
--   This is an auxiliary piece of the binary representation of Section 2.1 ("All numbers are rational numbers encoded in binary").
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.1, p.10 (representation)

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- A **length-prefixed list code** (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang,
*The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version
of November 2, 2026, sha256 6aec500a…7820, Section 2.1, p.10: "All numbers are rational numbers
encoded in binary"). A list `l` whose entries are coded by `enc` as lists of natural numbers is
coded as its length followed by the concatenated codes of its entries.

**Formalization Note** The natural numbers produced here are turned into bits by the public
self-delimiting binary codec `CorrelatedAuctionComplexity.Main.pack`; the length prefix makes
codes of nested lists uniquely decodable. -/
def lenList {α : Type} (enc : α → List ℕ) (l : List α) : List ℕ :=
  l.length :: l.flatMap enc

end CEPolytopeHard


