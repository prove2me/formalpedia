-- Prove2me | Definitions.Def_mme_CW_2376_marginal_hash_retained_edges
-- name    : mme_CW_2376_marginal_hash_retained_edges
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-24T21:24:30.30626+00:00
-- url     : https://prove2.me/theorems/2ca97f27-759d-4170-91f3-396372207e31
-- title:
--   Hash-retained edges of the full CW marginal hypergraph
-- statement:
--   Fix the full hypergraph of coordinatewise-supported Coppersmith--Winograd addresses whose three mode words have the prescribed five marginals. Given a modulus $p$, affine hash parameters, and a set $S$ of integer labels, retain an address exactly when its three mode hashes all equal the residue of one common label in $S$.
--
--   The definition deliberately filters the full marginal-supported ambient hypergraph, not merely addresses with the optimized exact joint profile. This makes it possible to prove closure under every supported mixed triple before selecting the exact target profile for collision deletion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), affine hashing and outer pruning on journal pp. 267--269; https://doi.org/10.1016/S0747-7171(08)80013-2

import Definitions.Def_mme_CW_2376_marginal_hash_state
import Definitions.Def_mme_CW_2376_modular_hash

namespace MME

noncomputable def cw2376MarginalHashRetainedEdges
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (cw2376ProfileLength m) → ZMod p) :
    Finset (CW2376MarginalSupportedAddress m) := by
  classical
  letI : Fintype (CW2376ProfileAddress m) :=
    inferInstanceAs (Fintype
      (Fin 3 → Fin (cw2376ProfileLength m) → Fin 5))
  letI : Fintype (CW2376MarginalSupportedAddress m) :=
    inferInstanceAs (Fintype
      {a : CW2376ProfileAddress m //
        CW2376CoordinatewiseSupported a ∧ CW2376MarginallyRegular a})
  exact Finset.univ.filter (fun a =>
    ∃ s ∈ S,
      cw2376XHashMod w (a.1 0) = (s : ZMod p) ∧
      cw2376YHashMod b0 w (a.1 1) = (s : ZMod p) ∧
      cw2376ZHashMod b0 w (a.1 2) = (s : ZMod p))

end MME


