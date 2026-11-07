-- Prove2me | Definitions.Def_LaconicBarrier_RunsWithin
-- name    : LaconicBarrier_RunsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:40.086221+00:00
-- url     : https://prove2.me/theorems/ddfc00a4-a2d7-4f20-b3c0-84cc2de3cb21
-- title:
--   Machine model: a machine computes an output within $t$ steps
-- statement:
--   Every algorithm of the mission (challengers, reductions, provers, verifiers, encryptors, obfuscators) is a deterministic Turing machine of the published two-tape oracle-machine model, run with the empty oracle. A tuple $(u_1,\dots,u_k)$ of bit strings is written on the input tape as $u_1\#\cdots\#u_k$.
--
--   $\mathrm{RunsWithin}(M, (u_1,\dots,u_k), y, t)$ says that $M$ halts on $(u_1,\dots,u_k)$ within $t$ steps and that the bit string on its work tape at step $t$ is $y$. The helpers $1^n$ (unary) and the reading of a coin vector $r \in \{0,1\}^m$ as a string are defined alongside.
--
--   This is the single machine model behind every time bound in the mission: "$T$-time", "polynomial time", "verifier time".
--
--   **Formalization Note** One machine serves all security parameters and inputs; a machine per parameter would make every time bound vacuous. Halted configurations are fixed points, so the work tape at step $t$ holds the output on halting.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1, p.14 (the paper's algorithms; it fixes no machine model)

import Mathlib
import Definitions.Def_KarpLiptonOM_OracleTM_HaltsWithin
import Definitions.Def_KarpLiptonOM_Tape_bits
import Definitions.Def_KarpLiptonOM_tupleEnc

namespace LaconicBarrier

open KarpLiptonOM

/-- The unary string `1ⁿ` (Jain, Mathialagan, Roy, *From Succinct Arguments to Proofs: Lower Bounds
for Obfuscation and SNARGs*, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.1, p.15: the
challenger's "common input `1^λ`"). -/
def unary (n : ℕ) : List Bool := List.replicate n true

/-- A coin string `r ∈ {0,1}^m`, given as a function `Fin m → Bool`, read as a bit string. -/
def bits {m : ℕ} (r : Fin m → Bool) : List Bool := List.ofFn r

/-- The machine `M` (a deterministic oracle Turing machine of the published `KarpLiptonOM` model,
run with the empty oracle) on the tuple `input = (u₁, …, u_k)`, written `u₁#⋯#u_k` on its work tape,
halts within `t` steps, and the bit string on its work tape at step `t` is `out` (Jain, Mathialagan,
Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.1, p.14: the paper's algorithms
"polynomial time", "T-time"; it names no machine model).

**Formalization Note** This is the one machine model of the mission: every algorithm (challengers,
reductions, provers, verifiers, encryptors, obfuscators) is a single uniform machine of this kind,
not one machine per security parameter. Halted configurations are fixed points of the step
function, so the work-tape string at step `t` is the output on halting. -/
def RunsWithin (M : OracleTM) (input : List (List Bool)) (out : List Bool) (t : ℕ) : Prop :=
  M.HaltsWithin ∅ t (tupleEnc input) ∧ (M.run ∅ t (M.init (tupleEnc input))).work.bits M.ι = out

end LaconicBarrier


