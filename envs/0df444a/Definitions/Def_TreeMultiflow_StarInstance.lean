-- Prove2me | Definitions.Def_TreeMultiflow_StarInstance
-- name    : TreeMultiflow_StarInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:58:11.790361+00:00
-- url     : https://prove2.me/theorems/299a1005-2f30-4f42-9e31-01408308e2db
-- title:
--   Encoded instance of Lemma 5.1
-- statement:
--   An **encoded star instance** consists of a list of local paths, each given by the pair of bins $(\beta_1,\beta_2)$ of its two ends, and a list of crossing paths, each given by its bin $\beta$ and its prescribed colour $i$ (a number below ten). Bins are named by natural numbers.
--
--   This is the input of the polynomial-time clause of Lemma 5.1.
-- source:
--   Harb, Improved Integrality Gap for Multicommodity Flow on Trees, arXiv:2609.07949, Lemma 5.1, p.9 (We can do this in polynomial time)

import Mathlib

namespace TreeMultiflow

/-- **An encoded instance of Lemma 5.1.**
Harb, *Improved Integrality Gap for Multicommodity Flow on Trees*, arXiv:2609.07949, Lemma 5.1,
pp.8–9 ("We can do this in polynomial time").

Bins are named by natural numbers.

* `locals` : one pair `(β₁, β₂)` per local path, the bins of its two ends;
* `crossing` : one pair `(β, i)` per crossing path, its bin `β` and its colour `i` (a colour is a
  number below `10`).

Local path `l` is the `l`-th entry of `locals`, crossing path `c` the `c`-th entry of
`crossing`. -/
structure StarInstance where
  /-- local paths: the bins of their two ends -/
  locals : List (ℕ × ℕ)
  /-- crossing paths: bin and prescribed colour -/
  crossing : List (ℕ × ℕ)

end TreeMultiflow


