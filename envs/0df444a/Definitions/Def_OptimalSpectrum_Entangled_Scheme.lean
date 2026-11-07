-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_Scheme
-- name    : OptimalSpectrum_Entangled_Scheme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:20:09.49984+00:00
-- url     : https://prove2.me/theorems/facaae4f-1369-4894-83b1-ab236b320a43
-- title:
--   The two measurement schemes: unentangled and entangled
-- statement:
--   A label for the two measurement schemes of the paper: **unentangled** (each copy measured separately, here with the conditioned uniform POVM of §7.1.1) and **entangled** (a joint measurement of all copies, here weak Schur sampling of the moment observables of §7.1.2).
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, Definition 4.1 and §7.1, pp. 11, 20 (PDF pp. 13, 22)

import Mathlib

namespace OptimalSpectrum.Entangled

/-- **The two measurement schemes.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, Definition 4.1, printed p. 11 (PDF p. 13), and §7.1, printed p. 20 (PDF p. 22): the
unentangled scheme (conditioned uniform POVM, §7.1.1) and the entangled scheme (weak Schur sampling
of the moment observables, §7.1.2). -/
inductive Scheme
  | unentangled
  | entangled
  deriving DecidableEq

end OptimalSpectrum.Entangled


