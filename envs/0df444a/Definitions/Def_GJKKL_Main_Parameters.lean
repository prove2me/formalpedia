-- Prove2me | Definitions.Def_GJKKL_Main_Parameters
-- name    : GJKKL_Main_Parameters
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T12:39:37.688963+00:00
-- url     : https://prove2.me/theorems/3c196d1c-465d-4b4d-ae2a-f8ebd4dcfb36
-- title:
--   Parameters
-- statement:
--   Definitions and structural lemmas for Parameters, from Juan Pablo Traverso Gianini and CDR III contributors's pinned Counting matchings in regular graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Main/Parameters.lean

module
public import Definitions.Def_GJKKL_Trajectory_Tracking
public import Definitions.Def_GJKKL_Trajectory_Functions
public import Definitions.Def_GJKKL_Greedy_VertexCount
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory
structure Regime (k : ℕ) (ε d : ℝ) : Prop where
  two_le : 2 ≤ k
  ε_pos : 0 < ε
  ε_small : ε * (64 * (k : ℝ) ^ 2) ≤ 1
  d_ge : 2 ≤ d
  h16 : 2 ≤ d ^ (ε / 16)
  h2 : 19200 * (k : ℝ) ^ 4 ≤ d ^ (ε / 2)
def Bn (k : ℕ) : ℕ := 32 * k ^ 2
noncomputable def dhat (k : ℕ) (d a : ℝ) (t : ℕ) : ℝ := d * pfrac a t ^ (k - 1)
noncomputable def delta (k : ℕ) (ε d a : ℝ) (t : ℕ) : ℝ := d ^ (1 - ε / 8) / pfrac a t ^ Bn k
namespace Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
section Size
variable {n : ℝ} (hn : ((k : ℝ) - 1) * d ^ ε / 2 ≤ n)
include hn
end Size
end Regime
section Trajectory
variable {a μ x y : ℝ}
end Trajectory
namespace Regime
variable {k : ℕ} {ε d : ℝ} (R : Regime k ε d)
include R
end Regime
end GJKKL.Main


