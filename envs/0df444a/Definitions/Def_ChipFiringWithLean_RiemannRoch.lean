-- Prove2me | Definitions.Def_ChipFiringWithLean_RiemannRoch
-- name    : ChipFiringWithLean_RiemannRoch
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:51:57.002875+00:00
-- url     : https://prove2.me/theorems/ae680b26-442d-4960-94f0-dac942d5d9d9
-- title:
--   Riemann Roch
-- statement:
--   Definitions and structural lemmas for Riemann Roch, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RiemannRoch.lean

module
public import Definitions.Def_ChipFiringWithLean_RRGHelpers
set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option trace.split.failure true
universe u
open Multiset Finset
def gonality_leq (G : CFGraph) (k : ℤ) : Prop := ∃ D : CFDiv G, rank G D ≥ 1 ∧ deg D = k
def gonality_geq (G : CFGraph) (k : ℤ) : Prop :=
  ∀ l : ℤ, l < k → ¬ gonality_leq G l
noncomputable def gonality {G : CFGraph} (_h_conn : graph_connected G) : ℤ :=
  sInf {k : ℤ | gonality_leq G k}
def max_gonality_existence (g : ℕ) : Prop :=
  ∃ (G : CFGraph.{u}) (h_conn : graph_connected G) (_g_eq : genus G = g),
    gonality h_conn = (g + 3) / 2
def brill_noether_general_existence (g : ℤ) : Prop :=
  ∃ (G : CFGraph.{u}) (_h_conn : graph_connected G) (_g_eq : genus G = g),
    ∀ (D : CFDiv G), (rank G D + 1) * (rank G (canonical_divisor G - D) + 1) ≤ g
def gonality_conjecture {G : CFGraph} (h_conn : graph_connected G) : Prop :=
  gonality h_conn ≤ (genus G + 3) / 2
def brill_noether_conjecture {G : CFGraph} (_h_conn : graph_connected G) (r d : ℤ) : Prop :=
  let g := genus G
  let ρ := g - (r + 1) * (g - d + r)
  0 ≤ ρ → ∃ (D : CFDiv G), rank G D ≥ r ∧ deg D = d


