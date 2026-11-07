-- Prove2me | Definitions.Def_TimeSpaceMA_keyPairCount
-- name    : TimeSpaceMA_keyPairCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:58:03.370265+00:00
-- url     : https://prove2.me/theorems/9b33c49b-66ec-4de1-8747-a99cdec10d6c
-- title:
--   Keys and the number of large key pairs
-- statement:
--   A **key** is a tuple $\kappa$ whose coordinates are their own $\mathrm{rep}$. The count at level $j$ is the number of pairs of keys $\kappa,\kappa'$ of $[L]^{m-j}$ with $q^j|\mathrm{sources}(\kappa)||\mathrm{sources}(\kappa')|>D$. These pairs are the entries of the table $R_j$ that Merlin supplies when $q^j>A$.
-- source:
--   Williams, Xi, Short Non-Interactive Proofs for Time-Space Computations, STOC 2027 submission (manuscript sha256 184c2f95…), §3.5, p.17; §3.7, p.20

import Definitions.Def_TimeSpaceMA_tensorEncode
import Definitions.Def_TimeSpaceMA_EncodesFamily

namespace TimeSpaceMA

/-- A key: a tuple of coordinates, each the least index of its support; p.12. -/
def IsKey {q L r : ℕ} (G : SubsetSumCode q L) (κ : Fin r → Fin L) : Prop :=
  ∀ i, familyRep G.supp (κ i) = (κ i).val

open Classical in
/-- The number of pairs of keys of `[L]^{m−j}` with `q^j |sources(κ)| |sources(κ′)| > D`; p.20. -/
noncomputable def keyPairCount {q L : ℕ} (G : SubsetSumCode q L) (m j : ℕ) (D : ℝ) : ℕ :=
  (Finset.univ.filter fun κκ' : (Fin (m - j) → Fin L) × (Fin (m - j) → Fin L) =>
    IsKey G κκ'.1 ∧ IsKey G κκ'.2 ∧
      D < (q : ℝ) ^ j * ((sources G κκ'.1).card : ℝ) * ((sources G κκ'.2).card : ℝ)).card

end TimeSpaceMA


