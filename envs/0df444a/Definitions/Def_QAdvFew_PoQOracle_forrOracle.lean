-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_forrOracle
-- name    : QAdvFew_PoQOracle_forrOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:48:54.671206+00:00
-- url     : https://prove2.me/theorems/f8abf0bd-9f1f-472d-b481-1590a491d57d
-- title:
--   A string as an oracle
-- statement:
--   A string $x\in\{0,1\}^N$ is accessed as an oracle: the query of length $\lceil\log_2N\rceil$ with binary value $i<N$ is answered $x_i$, and every other query $0$.
--
--   The same addressing is used for the function $B_t((M,x),\cdot)$, whose argument $y\in\{0,1\}^{t^2}$ is an address into a string of length $2^{t^2}$.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, Lemma 3.10, p. 14 (PDF p. 16); §4.1, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Oracle

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- The number with little-endian binary digits `s`. -/
def binVal (s : Str) : ℕ := s.foldr (fun b acc => (if b then 1 else 0) + 2 * acc) 0

/-- A string `x ∈ {0,1}^N` as an oracle (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, Lemma 3.10, p. 14 (PDF p. 16): "a quantum algorithm
`A` making … queries to its input"): the query `s` of length `⌈log₂ N⌉` with binary value `i < N` is
answered `x_i`, every other query `0`.

**Formalization Note** The same addressing is used for `B_t((M, x), ·)`, whose argument
`y ∈ {0,1}^{t²}` is the address `binVal y < 2^{t²} = N` (`levelsBC`). -/
def forrOracle (N : ℕ) (x : Fin N → Bool) : Oracle := fun s =>
  if s.length = Nat.clog 2 N then (if h : binVal s < N then x ⟨binVal s, h⟩ else false) else false

end QAdvFew.PoQOracle


