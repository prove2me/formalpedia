-- Prove2me | Definitions.Def_QiOPoQ_Supplement_avgRand
-- name    : QiOPoQ_Supplement_avgRand
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:05:41.280014+00:00
-- url     : https://prove2.me/theorems/697ce3a6-367a-43f1-8224-6cf7a1085e74
-- title:
--   The distributions $\mathcal C_{n,N}$ and $\mathcal E_{C,N}$ of random circuits
-- statement:
--   $R\leftarrow\mathcal C_{n,N}$ chooses the $N$ gate placements of an $n$-qubit circuit independently and uniformly from the legal placements. For an $n$-qubit circuit $C$ and $N\ge|C|$, $\mathcal E_{C,N}$ is the uniform distribution over circuits in $\mathcal C_{n,N}$ that implement exactly the same channel as $C$ (a global phase is allowed, since the channel is the same). `avgRand` and `avgEquiv` are the expectations under these distributions.
--
--   **Formalization Note** The distributions are used only where they are defined ($N\ge|C|$, where $C$ padded with identity gates is in the set); on an empty set the value is $0$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Notation 6.1, p.30

import Mathlib
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_Supplement_Placement

set_option autoImplicit false

namespace QiOPoQ.Supplement

variable {G : GateSet}

/-- **`R ← C_{n,N}`.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and
Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), Notation 6.1,
p.30: "Let C_{n,N} denote the set of n-qubit circuits with exactly N gates. We write R ← C_{n,N}
when its N gate placements are chosen independently and uniformly from the legal gate placements
on n qubits." `E[g(R)]` for this distribution. -/
noncomputable def avgRand (G : GateSet) (n N : ℕ) (g : List (Placement G n) → ℝ) : ℝ :=
  (∑ f : Fin N → Placement G n, g (List.ofFn f)) / (Fintype.card (Placement G n) : ℝ) ^ N

open Classical in
/-- **`E_{C,N}`.** Notation 6.1, p.30: "For an n-qubit circuit C and N ≥ |C|, let E_{C,N} be the
uniform distribution over circuits in C_{n,N} that implement exactly the same quantum channel as
C. The identity gate makes this set nonempty whenever N > |C|, and equality of channels permits a
global phase difference." `E[g(D)]` for `D ← E_{C,N}`.

**Formalization Note.** "The same quantum channel" is equality of the channels (`chan`) as maps on
all operators. The distribution is used only for `N ≥ |C|`, where the set contains `C` padded by
identity gates; on an empty set the value is `0`. -/
noncomputable def avgEquiv (G : GateSet) (n N : ℕ) (C : List (Placement G n))
    (g : List (Placement G n) → ℝ) : ℝ :=
  (∑ f : Fin N → Placement G n,
      if chan (afCirc n (List.ofFn f)) = chan (afCirc n C) then g (List.ofFn f) else 0) /
    (Fintype.card {f : Fin N → Placement G n // chan (afCirc n (List.ofFn f)) = chan (afCirc n C)} : ℝ)

end QiOPoQ.Supplement


