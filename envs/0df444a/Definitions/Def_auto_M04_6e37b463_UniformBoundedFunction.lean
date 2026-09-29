-- Prove2me | Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
-- name    : auto_M04_6e37b463_UniformBoundedFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T18:47:37.009172+00:00
-- url     : https://prove2.me/theorems/2fa168e5-bee2-4cae-8369-2defd7f79be0
-- title:
--   UniformBoundedFunction
-- statement:
--   Actual bounded real functions on E with the uniform norm. Borel measurability is imposed where the source uses B(E); functions are not identified modulo almost-everywhere equality.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986; Chapter 4, Section 4, Theorem 4.1, printed p.182 (PDF p.191); equation (3.4), printed p.174 (PDF p.183); equation (4.2), printed p.183 (PDF p.192).

import Mathlib

open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace EthierKurtz

abbrev UniformBoundedFunction (E : Type*) := lp (fun _ : E => ℝ) ∞

end EthierKurtz


