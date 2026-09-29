-- Prove2me | Definitions.Def_mme_CW_2376_marginal_support_hypergraph
-- name    : mme_CW_2376_marginal_support_hypergraph
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T19:55:09.197658+00:00
-- url     : https://prove2.me/theorems/3c833aa2-4b85-4c30-be4d-70a949d9aad9
-- title:
--   Full marginal-supported hypergraph for outer CW pruning
-- statement:
--   Fix the optimized five-grade marginal of the squared Coppersmith--Winograd tensor. This module defines the finite three-partite hypergraph whose edges are all coordinatewise-supported address triples with that marginal in every mode. It also records the collision potential
--
--   $$
--   P(E)=Σ_{i=0}^{2}Σ_w C(deg_{E,i}(w),2)
--   $$
--
--   and the predicate selecting the dominant joint profile from equation (13).
--
--   The full edge type is intentionally larger than the exact-profile subtype. This reflects the source proof on journal pp. 267--269: collision deletion must eliminate every supported mixed triple with the chosen marginals before the dominant joint profile is retained. Pruning only exact-profile edges would not establish inducedness.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), equations (12)--(13) and the usual pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_profile_induced_family

open BigOperators

namespace MME

def cw2376MarginalMultiplicity (m : ℕ) : Fin 5 → ℕ
  | ⟨0, _⟩ => 384072 * m
  | ⟨1, _⟩ => 1308290 * m
  | ⟨2, _⟩ => 1231903 * m
  | ⟨3, _⟩ => 75036 * m
  | ⟨4, _⟩ => 699 * m

def CW2376MarginallyRegular {m : ℕ}
    (a : CW2376ProfileAddress m) : Prop :=
  ∀ i : Fin 3, ∀ r : Fin 5,
    (Finset.univ.filter (fun j => a i j = r)).card =
      cw2376MarginalMultiplicity m r

def CW2376MarginalSupportedAddress (m : ℕ) : Type :=
  {a : CW2376ProfileAddress m //
    CW2376CoordinatewiseSupported a ∧ CW2376MarginallyRegular a}

def cw2376MarginalCollisionPotential {m : ℕ}
    (E : Finset (CW2376MarginalSupportedAddress m)) : ℕ :=
  ∑ i : Fin 3, ∑ w ∈ E.image (fun a => a.1 i),
    Nat.choose (E.filter (fun a => a.1 i = w)).card 2

def CW2376HasExactJointProfile {m : ℕ}
    (a : CW2376MarginalSupportedAddress m) : Prop :=
  ∀ σ : Fin 3 → Fin 5,
    (Finset.univ.filter
      (fun j => cw2376AddressType a.1 j = σ)).card =
      cw2376ProfileMultiplicity m σ

end MME


