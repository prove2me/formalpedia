-- Prove2me | Definitions.Def_BondySimonovitsLib_BSFinal
-- name    : BondySimonovitsLib_BSFinal
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-24T05:05:58.888783+00:00
-- url     : https://prove2.me/theorems/11bd8314-4479-4170-87a0-8b03f1a1f0da
-- title:
--   BSFinal
-- statement:
--   Definitions and structural lemmas for BSFinal, from Juan Pablo Traverso Gianini (jtraverso/bondy-simonovits; see pinned Apache-2.0 LICENSE and source headers)'s pinned Bondy-Simonovits even cycle theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/jtraverso/bondy-simonovits/blob/a4ca4b28a0d82735316fd73a5a11303231109fc7/BondySimonovitsLib/BSFinal.lean

module
public import Definitions.Def_BondySimonovitsLib_BSGrowth
set_option autoImplicit true
@[expose] public section
@[expose] public section
open SimpleGraph Finset
namespace BondySimonovits
variable {V : Type*}
def cutGraph (G : SimpleGraph V) (f : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u ≠ f v
  symm := ⟨fun _ _ h => ⟨h.1.symm, Ne.symm h.2⟩⟩
  loopless := ⟨fun v h => G.loopless.irrefl v h.1⟩
def restrictGraph (H : SimpleGraph V) (Y : Set V) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ u ∈ Y ∧ v ∈ Y
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun v h => H.loopless.irrefl v h.1⟩
end BondySimonovits


