-- Prove2me | Definitions.Def_AvoidPlast_Supplement_Ensemble
-- name    : AvoidPlast_Supplement_Ensemble
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:55:45.078804+00:00
-- url     : https://prove2.me/theorems/5e455ddc-c222-44d9-af47-ddf66bdbdcd1
-- title:
--   Distribution ensembles
-- statement:
--   A distribution ensemble $D=\{D_n\}_{n\in\mathbb N}$ assigns to every $n$ a probability distribution $D_n$ supported on $\{0,1\}^n$.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Definition 3.4, p.14; Theorem 5.1, p.21

import Mathlib

namespace AvoidPlast.Supplement

/-- A distribution ensemble `D = {D_n}` (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Definition 3.4, p.14; Theorem 5.1, p.21):
`D_n` is a probability distribution on strings whose support consists of `n`-bit strings. -/
structure Ensemble where
  /-- the distribution `D_n` -/
  dist : ℕ → PMF (List Bool)
  /-- `D_n` lives on `{0,1}^n` -/
  supp : ∀ n x, dist n x ≠ 0 → x.length = n

end AvoidPlast.Supplement


