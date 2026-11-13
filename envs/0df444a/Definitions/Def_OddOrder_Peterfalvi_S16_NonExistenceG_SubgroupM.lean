-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
-- name    : OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T17:29:34.163746+00:00
-- url     : https://prove2.me/theorems/8dc125ad-e08f-4ad9-94f9-75ea80bac87b
-- title:
--   Peterfalvi (14.4)/(14.6)/(14.11.3): Frobenius kernels over the $M$-carrier
-- statement:
--   Formalizes the $S$- and $T$-side Frobenius kernels over the $M$-carrier, including the generic data for the $\eta$-grid on the set $G_0$ (Peterfalvi (3.9.a,c)).
--
--   Main declarations: `EtaGenericData` (Peterfalvi (3.9.a,c) for the `η`-grid on the generic set `G₀`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- **Peterfalvi (3.9.a,c) for the `η`-grid on the generic set `G₀`** (faithful §3 Dade obligation).
For `g ∈ G₀` (an element of order prime to `pq` lying outside `Ã(M)`):

* (3.9.c) each grid value `η_ij(g)` is a rational integer (`eta_int`);
* (3.9.a) the grid is invariant under the conjugation `(i,j) ↦ (−i,−j)` (`finNeg`), i.e. the values
  pair up (`eta_pair`), with principal value `η₀₀(g) = 1` (`eta_principal`);
* `β_M^τ(g) = 0`, since `g ∉ Ã(M)` (`betaM_vanish`).

These are the Dade-character integrality/symmetry facts of Peterfalvi (3.9) specialised to the
`M`-grid plus the support vanishing of (14.10); their honest construction lives in the §3/§4
Dade-isometry layer (the abstract §16 `ω`/`η`/`tau3` carriers do not yet pin it). -/
structure EtaGenericData [Finite G]
    (hyp : Hypothesis (G := G)) (Mdata : MHypothesis hyp) where
  eta_int : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    ∃ m : ℤ, hyp.base.eta i j g = (m : ℂ)
  eta_pair : ∀ g ∈ Mdata.G0, ∀ (i : Fin hyp.base.q) (j : Fin hyp.base.p),
    hyp.base.eta (finNeg hyp.base.q_prime.pos i) (finNeg hyp.base.p_prime.pos j) g
      = hyp.base.eta i j g
  eta_principal : ∀ g ∈ Mdata.G0,
    hyp.base.eta ⟨0, hyp.base.q_prime.pos⟩ ⟨0, hyp.base.p_prime.pos⟩ g = 1
  betaM_vanish : ∀ g ∈ Mdata.G0, Mdata.betaM g = 0

end OddOrder.Peterfalvi.S16


