-- Prove2me | Definitions.Def_ModLatSVP_Supplement_IsSVPOracle
-- name    : ModLatSVP_Supplement_IsSVPOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:17:30.710683+00:00
-- url     : https://prove2.me/theorems/090c0e35-6277-490f-9c24-dae9ed960f1e
-- title:
--   Exact SVP oracles, oracle-call counts, and working space of oracle runs
-- statement:
--   An **exact SVP oracle** is a function $O$ on bit strings with the following property: for every $m\ge1$ and every positive definite rational $m\times m$ Gram matrix $G$, the answer to the query that encodes $m$ and $G$ is the integer coefficient vector $x\in\mathbb Z^m$ of some shortest nonzero vector of the lattice with Gram matrix $G$, that is, $x\neq0$ and
--
--   $$x^{T}Gx\le y^{T}Gy\qquad\text{for every }y\in\mathbb Z^m\setminus\{0\}.$$
--
--   Which shortest vector is returned is not specified, and answers to malformed queries are arbitrary.
--
--   For an oracle machine (a multi-stack Turing machine with a query stack, run with an oracle $O$; each oracle call is one step), three notions are defined:
--
--   1. the **number of oracle calls** among the first $T$ steps of a run;
--   2. the run **uses at most $Q$ oracle calls of dimension at most $D$** (with polynomial degree $k$) if it halts with the required output after some number $T$ of steps such that at most $Q$ of the steps are oracle calls, $T\le(Q+1)(\ell+1)^k$ where $\ell$ is the input length, and every query is a positive definite rational Gram matrix of dimension between $1$ and $D$;
--   3. the run uses **working space at most $S$** if at every configuration the total length of all stacks except the output stack, the query stack included, is at most $S$, and the output stack only grows at its end.
--
--   These are the notions behind the paper's statements "using at most $Q$ exact SVP-oracle calls of dimension at most $d+1$" and "polynomial working space apart from the oracle workspace" (Theorems 4.5, 4.9, 5.2, 6.2, 6.7).
--
--   **Formalization Note** The machine is the published oracle machine $\texttt{HMBinPacking.OracleMachine}$. The step bound $(Q+1)(\ell+1)^k$ is part of the notion: a call bound alone would say nothing, because a machine could solve the problem by brute force without calling the oracle. Dimension $m\ge1$ is required of the oracle because a zero-dimensional lattice has no nonzero vector.
-- source:
--   Kim, Lee, Son, Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions, STOC 2027 submission (manuscript sha256 e7151fad…), §4.1, p.24 (PDF p.24): "The oracle takes a positive definite rational Gram matrix and returns a shortest nonzero vector in coefficient coordinates"; Lemma 3.2, p.18 and Lemma 4.8, p.31 (polynomial work per call); §2.1, p.11 (write-only output stream)

import Mathlib
import Definitions.Def_HMBinPacking_OracleMachine
import Definitions.Def_SpikyCVP_encInst
import Definitions.Def_ModLatSVP_encModule
import Definitions.Def_ModLatSVP_IsShortest

open ExponomialAssortment.FPTAS

namespace ModLatSVP

namespace Supplement

/-- The query of an exact SVP oracle: the dimension `m`, then the rational Gram matrix row by row.
Kim, Lee, Son, *Exact SVP and CVP in Structured Lattices: Polynomial-Space Algorithms and Reductions*,
STOC 2027 submission (manuscript sha256 e7151fad…), §4.1, p.24 (PDF p.24): "The oracle takes a positive
definite rational Gram matrix and returns a shortest nonzero vector in coefficient coordinates." -/
def encQuery {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) : List Bool :=
  encodeNat m ++ SpikyCVP.encMat G

/-- An exact SVP oracle (§4.1, p.24): a function `O` on bit strings such that, for every `m ≥ 1` and every
positive definite rational `m × m` Gram matrix `G`, the answer to the query `encQuery G` is the encoding
of the coefficient vector of some shortest nonzero vector of the lattice with Gram matrix `G`.

**Formalization Note.** Which shortest vector the oracle returns is not fixed: the statements quantify
over every such oracle, so the oracle's choice is adversarial. Its answers to malformed queries are
unconstrained. The dimension `m ≥ 1` is required because the zero-dimensional lattice has no nonzero
vector; without it no oracle would exist. -/
def IsSVPOracle (O : List Bool → List Bool) : Prop :=
  ∀ (m : ℕ) (G : Matrix (Fin m) (Fin m) ℚ), 1 ≤ m → (G.map (fun q : ℚ => (q : ℝ))).PosDef →
    ∃ x : Fin m → ℤ, IsShortest G x ∧ O (encQuery G) = encIntVec x

/-- The number of oracle calls an oracle machine makes during its first `T` steps on input `inp`: the
number of steps `j < T` at which the run is at the label `ask`. -/
noncomputable def callCount (OM : HMBinPacking.OracleMachine) (O : List Bool → List Bool)
    (inp : List Bool) (T : ℕ) : ℕ :=
  Set.ncard {j : ℕ | j < T ∧ ∃ c : HMBinPacking.OCfg OM,
    HMBinPacking.oRun OM O inp j = some c ∧ c.l = some OM.ask}

/-- "Using at most `Q` exact SVP-oracle calls of dimension at most `D`" (Theorems 4.5, 4.9, 5.2, 6.2,
6.7, pp.24–41), for one oracle `O`: the run of the oracle machine `OM` with oracle `O` on input `inp`
halts with output `out` after some number `steps` of steps such that
1. at most `Q` of these steps are oracle calls;
2. `steps ≤ (Q + 1)(ℓ + 1)^k`, where `ℓ` is the input length (polynomial work per call: Lemma 3.2,
   p.18, "polynomial additional work per invocation", and Lemma 4.8, p.31, "the uniform bit-complexity
   bound needed to convert oracle-call counts into running times");
3. every oracle call made before the halt asks `encQuery G'` for a positive definite rational Gram
   matrix `G'` of dimension `m` with `1 ≤ m ≤ D`.

**Formalization Note.** The step bound is part of the notion: without it a bound on the number of calls
says nothing, since a machine could solve the problem by brute force with no call at all. The halting
configuration is Mathlib's `Turing.haltList` (every stack but the output stack empty). -/
def OCallsWithin (OM : HMBinPacking.OracleMachine) (O : List Bool → List Bool)
    (inp out : List Bool) (Q : ℝ) (D k : ℕ) : Prop :=
  ∃ steps : ℕ,
    HMBinPacking.oRun OM O inp steps =
      some (Turing.haltList OM.M.tm (out.map OM.M.outputAlphabet.symm)) ∧
    (callCount OM O inp steps : ℝ) ≤ Q ∧
    (steps : ℝ) ≤ (Q + 1) * ((inp.length : ℝ) + 1) ^ k ∧
    ∀ j < steps, ∀ c : HMBinPacking.OCfg OM, HMBinPacking.oRun OM O inp j = some c →
      c.l = some OM.ask →
        ∃ (m : ℕ) (G' : Matrix (Fin m) (Fin m) ℚ), 1 ≤ m ∧ m ≤ D ∧
          (G'.map (fun q : ℚ => (q : ℝ))).PosDef ∧ (c.stk OM.qs).map OM.qsAlphabet = encQuery G'

/-- Working space of an oracle run, "polynomial working space apart from the oracle workspace"
(Theorems 5.2 and 6.7, pp.34, 41; Theorem 4.9, p.31: "both reductions use polynomial working space").
Along every configuration of the run of `OM` with oracle `O` on `inp`:
1. the total length of all stacks other than the output stack (the query stack included) is at most `S`;
2. every step, oracle calls included, leaves the old output stack a suffix of the new one (the output is
   append-only, §2.1, p.11: "A write-only output stream is excluded from working space").

**Formalization Note.** This is `ModLatSVP.SpaceWithin` with the oracle step `HMBinPacking.oStep` in place
of the machine step. An oracle call is one step and its own computation uses no space of the machine,
which is the paper's exclusion of "the oracle workspace"; the query and the answer, written on the query
stack, do count. -/
def OSpaceWithin (OM : HMBinPacking.OracleMachine) (O : List Bool → List Bool) (inp : List Bool)
    (S : ℕ) : Prop :=
  ∀ (j : ℕ) (c : HMBinPacking.OCfg OM), HMBinPacking.oRun OM O inp j = some c →
    (∑ k ∈ (@Finset.univ OM.M.tm.K OM.M.tm.kFin).erase OM.M.tm.k₁, (c.stk k).length) ≤ S ∧
    ∀ c' : HMBinPacking.OCfg OM, HMBinPacking.oStep OM O c = some c' →
      c.stk OM.M.tm.k₁ <:+ c'.stk OM.M.tm.k₁

end Supplement

end ModLatSVP


