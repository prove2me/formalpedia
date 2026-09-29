-- Prove2me | Definitions.Def_mme_CW_q6_exact_address_incidence
-- name    : mme_CW_q6_exact_address_incidence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T19:12:38.000263+00:00
-- url     : https://prove2.me/theorems/57634c68-b9d5-4cb5-9c8f-6dd614e9e3c2
-- title:
--   Finite exact-profile incidence hypergraph for the coupled q=6 constituent
-- statement:
--   For fixed integers $N,L,G$, this definition packages the finite three-partite incidence hypergraph of all length-$2N$ coupled q=6 addresses with supported coordinate types and exact marginals $(N,N,0)$, $(N,N,0)$, and $(L,L,2G)$. It also records the three finite sets of mode words obtained as projections of the address set.
--
--   The proposition `CWQ6ExactAddressRegularity` names the exact enumeration data needed by the first hash: total edge count, the number of words in each mode, and the common X-, Y-, and Z-fiber degrees. It contains only finite sets and cardinality equalities; no hashing choice or tensor restriction is included.
--
--   This is reusable incidence infrastructure for making the counts on CW90 pp. 270–271 explicit.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–271: exact X/Y balance, the L/L/2G Z profile, number of X blocks, fixed-X degree, number of Z blocks, and fixed-Z degree; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib.Data.Fintype.Pi
import Definitions.Def_mme_CW_q6_primary_hash_family

namespace MME

noncomputable def cwQ6ExactAddresses (N L G : ℕ) :
    Finset (CWQ6CoupledAddress N) := by
  classical
  letI : Fintype (CWQ6CoupledAddress N) :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 3))
  exact Finset.univ.filter (fun a =>
    CWQ6CoupledCoordinatewiseSupported a ∧
      ∀ i r : Fin 3,
        (Finset.univ.filter (fun j : Fin (2 * N) => a i j = r)).card =
          cwQ6CoupledMarginalMultiplicity N L G i r)

noncomputable def cwQ6ExactXWords (N L G : ℕ) :
    Finset (Fin (2 * N) → Fin 3) := by
  classical
  exact (cwQ6ExactAddresses N L G).image (fun e => e 0)

noncomputable def cwQ6ExactYWords (N L G : ℕ) :
    Finset (Fin (2 * N) → Fin 3) := by
  classical
  exact (cwQ6ExactAddresses N L G).image (fun e => e 1)

noncomputable def cwQ6ExactZWords (N L G : ℕ) :
    Finset (Fin (2 * N) → Fin 3) := by
  classical
  exact (cwQ6ExactAddresses N L G).image (fun e => e 2)

structure CWQ6ExactAddressRegularity (N L G : ℕ) : Prop where
  total_card :
    (cwQ6ExactAddresses N L G).card =
      (Nat.choose (2 * N) L * Nat.choose (2 * N - L) L) *
        Nat.choose (2 * G) G
  x_word_card : (cwQ6ExactXWords N L G).card = Nat.choose (2 * N) N
  y_word_card : (cwQ6ExactYWords N L G).card = Nat.choose (2 * N) N
  z_word_card :
    (cwQ6ExactZWords N L G).card =
      Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
  x_degree : ∀ x ∈ cwQ6ExactXWords N L G,
    ((cwQ6ExactAddresses N L G).filter (fun e => e 0 = x)).card =
      (Nat.choose N G) ^ 2
  y_degree : ∀ y ∈ cwQ6ExactYWords N L G,
    ((cwQ6ExactAddresses N L G).filter (fun e => e 1 = y)).card =
      (Nat.choose N G) ^ 2
  z_degree : ∀ z ∈ cwQ6ExactZWords N L G,
    ((cwQ6ExactAddresses N L G).filter (fun e => e 2 = z)).card =
      Nat.choose (2 * G) G

end MME


