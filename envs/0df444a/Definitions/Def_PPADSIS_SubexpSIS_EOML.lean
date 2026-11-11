-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_EOML
-- name    : PPADSIS_SubexpSIS_EOML
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:48:37.048193+00:00
-- url     : https://prove2.me/theorems/b43c205d-bb36-4db4-aefa-63f2cb188e75
-- title:
--   End-of-Metered-Line: instances, guarantee, solutions and hard distributions (Definition 3.2)
-- statement:
--   An instance of **End-of-Metered-Line (EOML)** (Definition 3.2) consists of a successor circuit $S:\{0,1\}^m\to\{0,1\}^m$, a predecessor circuit $P:\{0,1\}^m\to\{0,1\}^m$, a meter circuit $M:\{0,1\}^m\to[0,2^m]$ and a string $v_0\in\{0,1\}^m$, with the **guarantee**
--   $$P(v_0)=v_0\ne S(v_0)\quad\text{and}\quad M(v_0)=1 .$$
--   A **solution** is a vertex $v\in\{0,1\}^m$ satisfying one of:
--
--   1. end of line: $P(S(v))\ne v$, or $S(P(v))\ne v\ne v_0$;
--   2. false source: $v\ne v_0$ and $M(v)=1$;
--   3. miscount: $M(v)>0$ and $M(S(v))-M(v)\ne1$, or $M(v)>1$ and $M(v)-M(P(v))\ne1$.
--
--   EOML lies in $\mathsf{CLS}\subseteq\mathsf{PPAD}$; solutions of the first type are exactly the End-of-Line solutions of the graph of $S$ and $P$. A **hard distribution of EOML** is a hard distribution (p. 21) of this search problem: a polynomial-time sampler $D(1^\lambda)$ whose outputs for all large $\lambda$ satisfy the guarantee, and on which every non-uniform probabilistic polynomial-size adversary, given the instance's description, outputs a solution with negligible probability.
--
--   **Formalization Note** The arities ($S,P$ with $m$ inputs and outputs, $M$ with $m$ inputs and $m+1$ outputs, $|v_0|=m$, circuits well formed) are part of the guarantee. The meter's $m+1$ output bits are read as a big-endian number and capped at $2^m$, so every circuit with $m+1$ outputs is a meter with values in $[0,2^m]$ and every meter of the paper is represented. The adversary outputs the vertex itself as its output string. The description of an instance is `encNat m`, the circuit descriptions of $S,P,M$ and `encStr v0`.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21, Definition 3.2 and the paragraph after it

import Mathlib
import Definitions.Def_PPADSIS_SubexpSIS_Circuit
import Definitions.Def_PPADSIS_SubexpSIS_HardDistribution

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

/-- An **instance of End-of-Metered-Line** (Choudhuri, *PPAD Hardness from SIS*, STOC 2027
submission (manuscript sha256 17abad73…), Definition 3.2, p. 21): a successor circuit
`S : {0,1}^m → {0,1}^m`, a predecessor circuit `P : {0,1}^m → {0,1}^m`, a meter circuit
`M : {0,1}^m → [0, 2^m]` and a string `v0 ∈ {0,1}^m`. The arities are the condition `WF`. -/
structure EOMLInstance where
  m : ℕ
  S : Circuit
  P : Circuit
  M : Circuit
  v0 : List Bool

/-- The circuits are well formed with the arities of Definition 3.2: `S` and `P` have `m` inputs
and `m` outputs, `M` has `m` inputs and `m + 1` outputs, and `|v0| = m`. -/
def EOMLInstance.WF (I : EOMLInstance) : Prop :=
  I.S.WF ∧ I.S.nIn = I.m ∧ I.S.outs.length = I.m ∧
  I.P.WF ∧ I.P.nIn = I.m ∧ I.P.outs.length = I.m ∧
  I.M.WF ∧ I.M.nIn = I.m ∧ I.M.outs.length = I.m + 1 ∧
  I.v0.length = I.m

/-- The value `M(v) ∈ [0, 2^m]` of the meter: the `m + 1` output bits of the meter circuit read as
a big-endian binary number, capped at `2^m`. -/
def EOMLInstance.meter (I : EOMLInstance) (v : List Bool) : ℕ :=
  min (valBE (I.M.eval v)) (2 ^ I.m)

/-- The **guarantee** of Definition 3.2: `P(v0) = v0 ≠ S(v0)` and `M(v0) = 1` (together with the
arities `WF`). -/
def EOMLInstance.Guarantee (I : EOMLInstance) : Prop :=
  I.WF ∧ I.P.eval I.v0 = I.v0 ∧ I.v0 ≠ I.S.eval I.v0 ∧ I.meter I.v0 = 1

/-- A **solution** of an EOML instance (Definition 3.2): a vertex `v ∈ {0,1}^m` satisfying one of
1. end of line: `P(S(v)) ≠ v`, or `S(P(v)) ≠ v ≠ v0`;
2. false source: `v ≠ v0` and `M(v) = 1`;
3. miscount: `M(v) > 0` and `M(S(v)) − M(v) ≠ 1`, or `M(v) > 1` and `M(v) − M(P(v)) ≠ 1`
(differences of meter values in `ℤ`). -/
def EOMLInstance.IsSolution (I : EOMLInstance) (v : List Bool) : Prop :=
  v.length = I.m ∧
  ((I.P.eval (I.S.eval v) ≠ v ∨ (I.S.eval (I.P.eval v) ≠ v ∧ v ≠ I.v0)) ∨
   (v ≠ I.v0 ∧ I.meter v = 1) ∨
   ((0 < I.meter v ∧ (I.meter (I.S.eval v) : ℤ) - I.meter v ≠ 1) ∨
    (1 < I.meter v ∧ (I.meter v : ℤ) - I.meter (I.P.eval v) ≠ 1)))

/-- The **description** of an EOML instance given to adversaries: `encNat m`, the descriptions of
`S`, `P`, `M`, and `encStr v0`. -/
def EOMLInstance.enc (I : EOMLInstance) : List Bool :=
  encNat I.m ++ I.S.enc ++ I.P.enc ++ I.M.enc ++ encStr I.v0

/-- A **hard distribution of EOML** (p. 21, "Hard distributions for EOML are defined
analogously"): a polynomial-time sampler `D(1^λ)` that, for all sufficiently large `λ`, outputs
only (descriptions of) instances satisfying the guarantee, and on which every non-uniform
polynomial-size probabilistic adversary, given the instance's description, outputs a solution
with negligible probability. -/
def IsHardEOML (D : CoinAlg unary) : Prop :=
  IsHardDistribution EOMLInstance.enc EOMLInstance.Guarantee EOMLInstance.IsSolution D

end PPADSIS.SubexpSIS


