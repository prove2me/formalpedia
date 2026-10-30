-- Prove2me | Definitions.Def_DerivativeChainPrivate_SpokeRows
-- name    : DerivativeChainPrivate_SpokeRows
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T20:12:50.124229+00:00
-- url     : https://prove2.me/theorems/981222e0-aec8-44c1-a83d-dd507bdbbb0a
-- title:
--   A complex spoke polynomial with arbitrary central multiplicity
-- statement:
--   For natural numbers k,r and Q∈ℝ[X], define spokePoly(k,r,Q)=X^r Q(X^k)∈ℂ[X], mapping the coefficients of Q into ℂ. No restriction on r, no lower bound on k, and no root condition on Q belongs to this definition. The positive aligned-ray theorems supply their hypotheses separately.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), ray_trinomial/Source/SpokeRows.lean, lines 10-11, SHA-256 c08f5ce51bc6fe4a096ac924fc1de45ccf9631e93365f5e3169f976353e10784.

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations


set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial

noncomputable def spokePoly (k r : ℕ) (q : Polynomial ℝ) : Polynomial ℂ :=
  X ^ r * (q.map Complex.ofRealHom).comp (X ^ k)















end DerivativeChainPrivate


