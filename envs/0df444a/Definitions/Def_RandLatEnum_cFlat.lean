-- Prove2me | Definitions.Def_RandLatEnum_cFlat
-- name    : RandLatEnum_cFlat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:13:04.385314+00:00
-- url     : https://prove2.me/theorems/70881cee-bc94-49ec-b576-e7cac123fce4
-- title:
--   The constant $c_{\mathrm{flat}}=(2-\sqrt2)/4$
-- statement:
--   $$
--   c_{\mathrm{flat}}=\frac{2-\sqrt2}{4}=0.14644\ldots
--   $$
--   It is the smaller root of $c-c^2=1/8$, and it is the exponent constant in the tree-size lower bound $T(B)\ge n^{c_{\mathrm{flat}}n+o(n)}$ of Theorem 1.5.
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.5, (1.6), p.5

import Mathlib

namespace RandLatEnum

/-- The constant `c_flat = (2 − √2)/4 = 0.14644…` (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.5, (1.6), p.5). It is the
smaller root of `c − c² = 1/8`. -/
noncomputable def cFlat : ℝ :=
  (2 - Real.sqrt 2) / 4

end RandLatEnum


