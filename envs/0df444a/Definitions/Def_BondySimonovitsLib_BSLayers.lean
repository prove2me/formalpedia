-- Prove2me | Definitions.Def_BondySimonovitsLib_BSLayers
-- name    : BondySimonovitsLib_BSLayers
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:02:54.047411+00:00
-- url     : https://prove2.me/theorems/4639eec7-9df8-4904-905a-322790a1d8a0
-- title:
--   BSLayers
-- statement:
--   Definitions and structural lemmas for BSLayers, from Juan Pablo Traverso Gianini (jtraverso/bondy-simonovits; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bondy-Simonovits even cycle theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSLayers.lean

module
public import Definitions.Def_BondySimonovitsLib_BSBasic
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BondySimonovits
section Layers
variable {V : Type*} (K : SimpleGraph V)
noncomputable def anc (par : V → V) (x : V) (t : ℕ) (v : V) : V := par^[K.dist x v - t] v
variable {K} {par : V → V} {x : V}
  (hpar : ∀ v, K.Reachable x v → 0 < K.dist x v →
    K.Adj v (par v) ∧ K.dist x (par v) + 1 = K.dist x v)
include hpar
end Layers
end BondySimonovits


