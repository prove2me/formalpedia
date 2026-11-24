-- Prove2me | Definitions.Def_ChipFiringWithLean_RRGHelpers
-- name    : ChipFiringWithLean_RRGHelpers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T21:51:24.536275+00:00
-- url     : https://prove2.me/theorems/4a292c5c-64f5-44c6-a668-adc133e4fccd
-- title:
--   RRGHelpers
-- statement:
--   Definitions and structural lemmas for RRGHelpers, from DhyeyMavani2003/chip-firing-with-lean contributors (see pinned LICENSE and source headers)'s pinned Chip-firing on multigraphs and Riemann-Roch for graphs development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/RRGHelpers.lean

module
public import Definitions.Def_ChipFiringWithLean_Orientation
public import Definitions.Def_ChipFiringWithLean_Rank
public import Theorems.Thm_unique_q_reduced

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option trace.split.failure true
open Multiset Finset
noncomputable def qReducedRep {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) : CFDiv G :=
  Classical.choose (unique_q_reduced h_conn q D)
lemma qReducedRep_spec {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) :
    linear_equiv G D (qReducedRep h_conn q D) ∧ q_reduced G q (qReducedRep h_conn q D) :=
  (Classical.choose_spec (unique_q_reduced h_conn q D)).1
noncomputable def qReducedConfig {G : CFGraph}
    (h_conn : graph_connected G) (q : G.V) (D : CFDiv G) : Config G q :=
  toConfig ⟨qReducedRep h_conn q D, (qReducedRep_spec h_conn q D).2.1⟩
def is_moderator {G : CFGraph} (D : CFDiv G) : Prop :=
  ∃ (O : CFOrientation G), is_acyclic G O ∧ D = ordiv G O


