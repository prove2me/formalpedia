-- Prove2me | Definitions.Def_GnpColoring_separatorConst
-- name    : GnpColoring_separatorConst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:33.344238+00:00
-- url     : https://prove2.me/theorems/eb7de20e-9e76-4ddb-a40b-2152ee6a35bd
-- title:
--   The comparison constant $K_C$ (5.4)
-- statement:
--   For a separator $C$ of $T$ with $k=|C|$, $\ell=|C\setminus H|$, $R_v=|N_G(v)\cap(T\setminus C)|$ and $r_H=\sum_{v\in C\cap H}R_v$,
--
--   $$K_C=3(2k+3)\,q^k\exp\Big(\frac{4\ell+28r_H}{q}\Big).$$
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 5.1.2 and Lemma 5.6, Eq. (5.4), p.46

import Mathlib
import Definitions.Def_GnpColoring_hubs

open scoped Classical
open Finset

namespace GnpColoring

/-- **The one-level comparison constant** (5.4)
`K_C = 3(2k + 3) q^k exp((4ℓ + 28 r_H)/q)`, with `k = |C|`, `ℓ = |C ∖ H|`,
`R_v = |N_G(v) ∩ (T ∖ C)|` and `r_H = Σ_{v ∈ C ∩ H} R_v`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 5.1.2, p.46, and Lemma 5.6, Eq. (5.4), p.46. -/
noncomputable def separatorConst {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (d η : ℝ)
    (T Csep : Finset (Fin n)) : ℝ :=
  3 * (2 * (Csep.card : ℝ) + 3) * (q : ℝ) ^ Csep.card *
    Real.exp ((4 * ((Csep \ hubs G d η).card : ℝ) +
      28 * ∑ v ∈ Csep ∩ hubs G d η, (((G.neighborFinset v).filter fun u => u ∈ T \ Csep).card : ℝ)) /
        (q : ℝ))

end GnpColoring


