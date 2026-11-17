-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_PoQProtocol
-- name    : TwoFoldOPI_Supplement_PoQProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:01:00.017202+00:00
-- url     : https://prove2.me/theorems/111bcf66-11e8-4cee-bba4-99247ca90245
-- title:
--   A noninteractive keyless protocol relative to a random oracle
-- statement:
--   At security parameter $\lambda$ the oracle is a Boolean function $H$ on bit strings of a length $\mathrm{inLen}(\lambda)$. A protocol consists of an **honest prover**, one uniform family of quantum programs on input $\lambda$ with quantum access to $H$ (reversible evaluation), whose output is its message; and a **classical verifier**, a bit program run on $\lambda$ and the message with classical queries to $H$ for a polynomial number of steps in $\lambda+|\mathrm{msg}|$, which accepts or rejects.
--
--   There is one message and no setup, and the verifier uses no secret: the protocol is noninteractive, keyless and publicly verifiable.
--
--   **Formalization Note** A random oracle with several output bits is a Boolean random oracle on a larger domain, so Boolean oracles lose no generality. Running-time and determinism requirements are stated where the structure is used.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.3, p. 61; §11.4, Theorem 11.10, p. 62

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_Defs_OPIUniformity
import Definitions.Def_TwoFoldOPI_Supplement_fnOracle

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

/-- **A noninteractive, keyless protocol relative to a random oracle.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §11.3, p.61: "In a proof of quantumness, a classical verifier accepts an efficient quantum
prover with noticeable probability, and accepts any classical prover making polynomially many
oracle queries with negligible probability. Our protocols are noninteractive, publicly verifiable,
and keyless"; §11.4, Theorem 11.10, p.62 ("there is a keyless noninteractive publicly verifiable
protocol relative to a random oracle").

At security parameter `λ` the oracle is a Boolean function `H` on `inLen λ`-bit strings.
* `prover`: the honest prover, one uniform family of quantum oracle programs on input `λ`
  (`QAlgorithms.OPI.UniformResourceFamily`, Clifford+T); its message is its output string. Its
  oracles are `proverOracle λ H`, the reversible evaluation `|x, z⟩ ↦ |x, z ⊕ H(x)⟩` (`fnOracle`).
* `verifier`: a classical bit program (`QAlgorithms.OPI.BitOracleProgram`) run on input
  `encBin λ ++ msg`, with classical oracle access `verifierOracle λ H` (a query string of length
  `inLen λ` is answered by `H`, any other string by `0`), for `vtime(λ + |msg|)` transitions;
  `accepts λ H msg` says that it has halted accepting by then.

**Formalization Note.** Noninteractive: one message, from prover to verifier. Keyless: there is no
setup; the prover's and verifier's only inputs are `λ` and the message. Publicly verifiable: the
verifier uses no secret, only `λ`, the message and oracle queries. A random oracle with several
output bits is a Boolean random oracle on a domain with the output index appended, so Boolean
oracles lose no generality. Requirements on running time and determinism are stated where the
structure is used. The module holds the structure with its oracle interfaces and acceptance. -/
structure PoQProtocol where
  /-- The oracle input length at security parameter `λ`. -/
  inLen : ℕ → ℕ
  /-- The honest prover. -/
  prover : UniformResourceFamily ℕ LocalHamiltonian.encBin id
  /-- The classical verifier. -/
  verifier : BitOracleProgram
  /-- The verifier's transition budget, as a polynomial in `λ + |msg|`. -/
  vtime : Polynomial ℕ

/-- The classical oracle seen by the verifier. -/
def PoQProtocol.verifierOracle (P : PoQProtocol) (lam : ℕ)
    (H : (Fin (P.inLen lam) → Bool) → Bool) (w : List Bool) : Bool :=
  if h : w.length = P.inLen lam then H fun i => w.get ⟨i.val, by have := i.isLt; omega⟩ else false

/-- The verifier accepts message `msg` at security parameter `λ` relative to oracle `H`. -/
def PoQProtocol.accepts (P : PoQProtocol) (lam : ℕ) (H : (Fin (P.inLen lam) → Bool) → Bool)
    (msg : List Bool) : Prop :=
  (bitProgramExecution P.verifier (LocalHamiltonian.encBin lam ++ msg) (P.verifierOracle lam H)
      (fun _ => false) (P.vtime.eval (lam + msg.length))).status = some true

/-- The quantum oracles of the honest prover: reversible evaluation of `H`. -/
noncomputable def PoQProtocol.proverOracle (P : PoQProtocol) (lam : ℕ)
    (H : (Fin (P.inLen lam) → Bool) → Bool) (k : Fin (P.prover.construct lam).oracles) :
    Matrix (Qubits ((P.prover.construct lam).arity k)) (Qubits ((P.prover.construct lam).arity k)) ℂ :=
  fnOracle ((P.prover.construct lam).arity k) (P.inLen lam) 1 fun x _ => H x

end Supplement

end TwoFoldOPI


