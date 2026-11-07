-- Prove2me | Definitions.Def_TwoFoldOPI_gateCircuit
-- name    : TwoFoldOPI_gateCircuit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:44:04.173045+00:00
-- url     : https://prove2.me/theorems/03d1e6f7-c3ba-4c69-b3dd-081b9cf106a6
-- title:
--   The circuit of a gate-only program
-- statement:
--   A program of the adaptive model that consists of gates $g_1,\dots,g_t$ from $\{H,T,\mathrm{CNOT}\}$ followed by a halt is the unitary circuit $[g_1,\dots,g_t]$; a program containing any other instruction (oracle query, measurement, reset, coin, classical step, failure) has no circuit. It identifies the unitary that a uniform constructor outputs in the implementation clause of Lemma 7.2.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, Lemma 7.2, p. 38; §5.2, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace TwoFoldOPI

open QAlgorithms QAlgorithms.OPI

/-- **The unitary circuit of a gate-only program.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7, Lemma 7.2, p.38 ("it can be implemented to operator-norm error δ in time
poly(q, log(1/δ))"); §5.2, p.26 (a coherent implementation is a unitary).

A program `g_1; …; g_t; halt` built from gates only gives the circuit `[g_1, …, g_t]`; any other
instruction (query, measurement, preparation, coin, classical step, failure) gives `none`. -/
def gateCircuit {r : ℕ} {a : Fin r → ℕ} {ctl : Fin r → Bool} {N c out : ℕ} :
    AdaptiveMembershipProgram htcxGateSet a ctl N c out → Option (Circuit htcxGateSet N)
  | .halt _ _ => some []
  | .gate g next => (gateCircuit next).map (g :: ·)
  | _ => none

end TwoFoldOPI


