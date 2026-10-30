-- Prove2me | Definitions.Def_DerivativeChainContinuation_TwoModeChain
-- name    : DerivativeChainContinuation_TwoModeChain
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T19:31:47.133753+00:00
-- url     : https://prove2.me/theorems/9081831e-39ae-4def-b48b-8bc7f0de1aff
-- title:
--   Support of centered polynomial modes
-- statement:
--   For $p\in\mathbb C[X]$ of degree $n$ and root centroid $u$, define the finite set
--
--   $$\{j\in\{2,\ldots,n\}:[X^{n-j}]p(X+u)
--   e0\}.$$
--
--   Its cardinality expresses the at-most-two-mode hypothesis without choosing the mode indices in advance.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/TwoModeChain.lean#L24-L26

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChain_root_probability

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate



noncomputable def centeredModeSupport (p : Polynomial ℂ) : Finset ℕ := by
  classical
  exact (Finset.Icc 2 p.natDegree).filter (fun j => (centeredSource p).coeff (p.natDegree-j) ≠ 0)

end DerivativeChainContinuation


