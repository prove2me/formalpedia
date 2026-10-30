-- Prove2me | Definitions.Def_DerivativeChainContinuation_CenteredSource
-- name    : DerivativeChainContinuation_CenteredSource
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-26T18:03:46.083997+00:00
-- url     : https://prove2.me/theorems/517eca47-cac5-48ff-ac33-3933ce8ebc02
-- title:
--   Root centroid and centered source
-- statement:
--   Define the root centroid by the multiplicity-weighted mean of the complex roots. The centered source translates the polynomial by this centroid, retaining its actual degree and root multiplicities.
-- source:
--   https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CenteredSource.lean#L9-L10; https://github.com/Amal-David/derivative-chain-prize/blob/21d2a2ac5cd4b4e6263cbc715dd5f925427fc976/continuation_formal/Source/CenteredSource.lean#L6-L7

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations

set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

noncomputable def rootCentroid (p : Polynomial ℂ) : ℂ :=
  p.roots.sum / (p.natDegree : ℂ)

noncomputable def centeredSource (p : Polynomial ℂ) : Polynomial ℂ :=
  p.comp (X + C (rootCentroid p))












end DerivativeChainContinuation


