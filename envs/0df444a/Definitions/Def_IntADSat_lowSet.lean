-- Prove2me | Definitions.Def_IntADSat_lowSet
-- name    : IntADSat_lowSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:51:35.113135+00:00
-- url     : https://prove2.me/theorems/882ed73b-8b33-4781-835a-d8439f502227
-- title:
--   $R_C=\{v\notin C:\deg_{G[[n]\setminus C]}(v)\le t-K\}$
-- statement:
--   For a simple graph $G$ on $[n]$ and $C\subseteq[n]$,
--
--   $$
--   R_C=\{\,v\notin C:\ \deg_{G[[n]\setminus C]}(v)\le t-K\,\},
--   $$
--
--   where $t$ and $K$ are the parameters of display (B.1) at $n$.
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.9, p.18 (PDF 19)

import Mathlib
import Definitions.Def_IntADSat_degOut
import Definitions.Def_IntADSat_tP
import Definitions.Def_IntADSat_KP__d24af9

set_option autoImplicit false

namespace IntADSat

/-- `R_C = {v ∉ C : deg_{G[[n]∖C]}(v) ≤ t − K}` (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), Lemma B.9, p.18 (PDF 19)), with `t`, `K`
the parameters of display (B.1) at `n`. -/
noncomputable def lowSet {n : ℕ} (G : SimpleGraph (Fin n)) (C : Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => v ∉ C ∧ (degOut G C v : ℤ) ≤ tP n - KP n

end IntADSat


