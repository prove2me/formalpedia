-- Prove2me | Definitions.Def_CongestionTaxes_EqClass
-- name    : CongestionTaxes_EqClass
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T13:31:46.308019+00:00
-- url     : https://prove2.me/theorems/12ba2a5c-db75-4a35-9d62-6387fc1982ab
-- title:
--   The four equilibrium classes
-- statement:
--   The four classes of equilibria for which the paper measures the price of anarchy: pure Nash equilibria, mixed Nash equilibria, correlated equilibria and coarse correlated equilibria. Each class contains the previous one (footnote 3), and the paper's $\mathrm{PoA}(T)$ refers to "any and all these equilibrium classes" (p.5).
-- source:
--   Paccagnan, Gairing, In Congestion Games, Taxes Achieve Optimal Approximation, arXiv:2105.07480v2 (19 May 2022), https://arxiv.org/abs/2105.07480v2, p.4, footnote 3, p.4, and p.5

import Mathlib

namespace CongestionTaxes

/-- The four **equilibrium classes** of Paccagnan, Gairing, arXiv:2105.07480v2, p.4 and footnote 3:
pure Nash, mixed Nash, correlated and coarse correlated equilibria. The price of anarchy (3) is
taken for each of them (p.5: "we will simply use PoA(T) to refer to the efficiency values of any
and all these equilibrium classes"). -/
inductive EqClass where
  | pure
  | mixed
  | correlated
  | coarseCorrelated
  deriving DecidableEq

end CongestionTaxes


