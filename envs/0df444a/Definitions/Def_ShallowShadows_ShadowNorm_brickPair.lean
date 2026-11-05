-- Prove2me | Definitions.Def_ShallowShadows_ShadowNorm_brickPair
-- name    : ShallowShadows_ShadowNorm_brickPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:30:53.201757+00:00
-- url     : https://prove2.me/theorems/151e23d8-162c-45a1-abbd-a9f87e4a318c
-- title:
--   The circular brickwork pattern on $n = 2m$ qubits
-- statement:
--   On $n = 2m$ qubits arranged in a circle (the first and last qubit are neighbours), the $i$-th brickwork layer ($i = 1, 2, \dots$) consists of $m$ two-qubit gates. With qubits labelled $1,\dots,n$:
--
--   1. odd layers act on the pairs $(1,2), (3,4), \dots, (n-1, n)$;
--   2. even layers act on the pairs $(2,3), (4,5), \dots, (n-2, n-1), (n, 1)$.
--
--   For $n = 8$ the second layer contains a gate on qubits $8$ and $1$, as in Fig. 1. Each layer covers every qubit exactly once.
--
--   **Formalization Note** Qubits and layers are indexed from $0$: layer $l$ is the paper's layer $l+1$, and gate $p \in \{0,\dots,m-1\}$ acts on $(2p, 2p+1)$ when $l$ is even and on $(2p+1, (2p+2) \bmod 2m)$ when $l$ is odd. The value is an injective map $\{0,1\}\to\{0,\dots,2m-1\}$, the first and second tensor factor of the gate.
-- source:
--   Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, Shallow shadows: Expectation estimation using low-depth random Clifford circuits, arXiv:2209.12924v3, §V, p. 4, Fig. 1 (caption)

import Mathlib

namespace ShallowShadows.ShadowNorm

/-- Bertoni, Haferkamp, Hinsche, Ioannou, Eisert, Pashayan, *Shallow shadows: Expectation
estimation using low-depth random Clifford circuits*, arXiv:2209.12924v3, §V, p. 4 and Fig. 1
(caption): the ordered pair of qubits on which the `p`-th two-qubit gate of brickwork layer `l`
acts, on `n = 2m` qubits in a "nearest-neighbour circular brickwork pattern … the first and last
qubit are identified as neighbours".

With 0-based qubits and the 0-based layer index `l` (the paper's layer `i = l + 1 ∈ [d]`): for the
paper's odd layers (`l` even) gate `p` acts on `(2p, 2p+1)`; for the paper's even layers (`l` odd)
gate `p` acts on `(2p+1, (2p+2) mod 2m)`. For `m = 4` the paper's second layer contains the pair
`(7, 0)`, i.e. "a two qubit gate acting on qubits 1 and 8" (Fig. 1). Each layer's `m` pairs
partition the `2m` qubits.

**Formalization Note.** The value is an embedding `Fin 2 ↪ Fin (2m)`: entry `0` is the first qubit
of the pair, entry `1` the second (the gate's first and second tensor factor). For `m = 1` the two
parities act on `(0, 1)` and `(1, 0)`, the same pair in opposite order. -/
def brickPair (m l : ℕ) (p : Fin m) : Fin 2 ↪ Fin (2 * m) :=
  if l % 2 = 0 then
    ⟨![⟨2 * p.val, by have := p.isLt; omega⟩, ⟨2 * p.val + 1, by have := p.isLt; omega⟩], by
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]⟩
  else
    ⟨![⟨2 * p.val + 1, by have := p.isLt; omega⟩, ⟨(2 * p.val + 2) % (2 * m), Nat.mod_lt _ (by have := p.isLt; omega)⟩], by
      have hne : 2 * p.val + 1 ≠ (2 * p.val + 2) % (2 * m) := by
        have := p.isLt
        rcases Nat.lt_or_ge (2 * p.val + 2) (2 * m) with h | h
        · rw [Nat.mod_eq_of_lt h]; omega
        · have h2 : 2 * p.val + 2 = 2 * m := by omega
          rw [h2, Nat.mod_self]; omega
      intro a b h
      fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]⟩

end ShallowShadows.ShadowNorm


