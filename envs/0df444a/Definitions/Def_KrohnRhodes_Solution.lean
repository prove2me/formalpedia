-- Prove2me | Definitions.Def_KrohnRhodes_Solution
-- name    : KrohnRhodes_Solution
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T04:12:18.087173+00:00
-- url     : https://prove2.me/theorems/f8f10a50-1eb6-46af-a4a4-52507ee46218
-- title:
--   Solution
-- statement:
--   Definitions and structural lemmas for Solution, from Aditya Rao (adii800/krohn-rhodes-lean; see pinned Apache-2.0 LICENSE and README.md)'s pinned Krohn-Rhodes prime decomposition of finite monoids into aperiodic and simple-group factors development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/adii800/krohn-rhodes-lean/blob/1f4a7e39ba2baede5434ac48c7571a442f8d521d/Solution.lean

module
public import Definitions.Def_KrohnRhodes
public import Theorems.Thm_KrohnRhodes_dks_aux
public import Theorems.Thm_KrohnRhodes_monoid_faithful_self
public import Theorems.Thm_KrohnRhodes_sgdiv_closure_monoid
public import Theorems.Thm_divTowerWreath_of_sgDiv

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace KrohnRhodes
open Green
theorem krohn_rhodes_prime_decomposition (M : Type) [Monoid M] [Finite M] :
    Nonempty (KRFactorTowerGrp M) := by
  classical
  have : Fintype M := Fintype.ofFinite M
  -- Cayley: the left regular representation `M →* End M` is injective
  -- (`monoid_faithful_self`).
  have hf : Function.Injective (MulAction.toEndHom (M := M) (α := M)) :=
    KrohnRhodes.monoid_faithful_self M
  -- The DKS induction at `n := Nat.card M`: a factor list, a tower for the constants
  -- closure `(M,M)‾`, and the simple-group divisibility into `M`.
  obtain ⟨factors, towC, hdiv⟩ :=
    dks_aux (Nat.card M) M M (MulAction.toEndHom (M := M) (α := M)) hf le_rfl
  -- `M ≼ (M,M)‾` pulls the tower back to `M` (`divTowerWreath_of_sgDiv`);
  -- the `groupFactorsDivide` field carries over unchanged.
  exact ⟨⟨factors,
    divTowerWreath_of_sgDiv (sgdiv_closure_monoid _ hf) towC, hdiv⟩⟩
noncomputable def krFactorTowerGrpOf (M : Type) [Monoid M] [Finite M] :
    KRFactorTowerGrp M :=
  (krohn_rhodes_prime_decomposition M).some
end KrohnRhodes


