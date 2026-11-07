-- Prove2me | Definitions.Def_LaconicBarrier_PolyTimeOn
-- name    : LaconicBarrier_PolyTimeOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:40:39.4778+00:00
-- url     : https://prove2.me/theorems/ab081307-d5cc-4673-9e6d-3800219c6612
-- title:
--   Polynomial-time computation of a family of input–output pairs
-- statement:
--   Let $\iota$ index a family of inputs $\mathrm{inp}(i)$ (tuples of bit strings) and outputs $\mathrm{out}(i)$.
--
--   1. $\mathrm{TimeOn}(\mathrm{inp}, \mathrm{out}, B)$: one machine computes $\mathrm{out}(i)$ from $\mathrm{inp}(i)$ within $B(i)$ steps, for every $i$.
--   2. $\mathrm{PolyTimeOn}(\mathrm{inp}, \mathrm{out})$: there is a constant $c$ with $\mathrm{TimeOn}$ for the bound $(N_i+2)^c$, where $N_i$ is the length of the encoded input $u_1\#\cdots\#u_k$.
--
--   A probabilistic algorithm is a deterministic one that receives its coin string as an extra input; its number of coins is bounded separately where it is used.
--
--   **Formalization Note** The index type lists the arguments an algorithm is run on, so one definition covers algorithms with any number of inputs.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.2, p.16; §4.1.4, p.18; §4.1.5, p.20 ("polynomial time algorithms")

import Mathlib
import Definitions.Def_LaconicBarrier_RunsWithin

namespace LaconicBarrier

open KarpLiptonOM

/-- A family of input/output pairs `(inp i, out i)` is computed by one machine within the step
bounds `B i` (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.6,
p.21: "runs in time at most …").

**Formalization Note** One machine for every index `i`. The index type `ι` lists the arguments the
algorithm is run on; `inp i` is the tuple written on the input tape. -/
def TimeOn {ι : Type*} (inp : ι → List (List Bool)) (out : ι → List Bool) (B : ι → ℕ) : Prop :=
  ∃ M : OracleTM, ∀ i, RunsWithin M (inp i) (out i) (B i)

/-- **Polynomial time**: one machine computes `out i` from `inp i` within `(N + 2)^c` steps, where
`N` is the length of the encoded input `u₁#⋯#u_k` (Jain, Mathialagan, Roy, STOC 2027 submission
(manuscript sha256 1af78662…), §4.1.2, p.16: "specified by the following polynomial time algorithms";
§4.1.4, p.18; §4.1.5, p.20).

**Formalization Note** A probabilistic algorithm is a deterministic one with its coin string as an
extra input; its number of coins is bounded separately. -/
def PolyTimeOn {ι : Type*} (inp : ι → List (List Bool)) (out : ι → List Bool) : Prop :=
  ∃ c : ℕ, TimeOn inp out (fun i => ((tupleEnc (inp i)).length + 2) ^ c)

end LaconicBarrier


