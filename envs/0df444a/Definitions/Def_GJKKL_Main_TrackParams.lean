-- Prove2me | Definitions.Def_GJKKL_Main_TrackParams
-- name    : GJKKL_Main_TrackParams
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:41:02.739482+00:00
-- url     : https://prove2.me/theorems/8e4a51ec-53f3-4496-bd3c-a733d773366f
-- title:
--   Track Params
-- statement:
--   Definitions and structural lemmas for Track Params, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/TrackParams.lean

module
public import Definitions.Def_GJKKL_Main_Parameters
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
namespace Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
variable {V : Type*} [Fintype V] [DecidableEq V] {H : Finset (Finset V)}
section Point
variable {a : ℝ} {m : ℕ} (ha : 0 < a) (hm : (m : ℝ) ≤ (1 - d ^ (-(ε ^ 3))) * a)
include ha hm
end Point
end Regime
end GJKKL.Main


