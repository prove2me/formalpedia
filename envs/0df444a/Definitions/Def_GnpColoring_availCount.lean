-- Prove2me | Definitions.Def_GnpColoring_availCount
-- name    : GnpColoring_availCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:19.753197+00:00
-- url     : https://prove2.me/theorems/cf66d355-869e-42e2-99e2-6ae830cf5582
-- title:
--   The number of available colours $a_s(\sigma)$
-- statement:
--   $a_s(\sigma)=|A_s(\sigma)|$, where $A_s(\sigma)=[q]\setminus\{\sigma_u:u\in N_G(s)\}$ is the set of colours not used by the neighbours of $s$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 2.2, p.13; Section 3.2, p.16

import Mathlib

open scoped Classical
open Finset

namespace GnpColoring

/-- **The number of available colours** `a_s(σ) = |A_s(σ)|`, `A_s(σ) = [q] ∖ {σ_u : u ∈ N_G(s)}`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 2.2, p.13 ("The available colors at v are A_v(σ) = [q] ∖ {σ_u : u ∈ N_G(v)}") and
Section 3.2, p.16 ("a_s(σ) is the number of available colors at s"). -/
noncomputable def availCount {n q : ℕ} (G : SimpleGraph (Fin n)) (σ : Fin n → Fin q) (s : Fin n) :
    ℕ :=
  (univ.filter fun c : Fin q => ∀ u, G.Adj s u → σ u ≠ c).card

end GnpColoring


