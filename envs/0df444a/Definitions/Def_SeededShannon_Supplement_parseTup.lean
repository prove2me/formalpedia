-- Prove2me | Definitions.Def_SeededShannon_Supplement_parseTup
-- name    : SeededShannon_Supplement_parseTup
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:35:13.698421+00:00
-- url     : https://prove2.me/theorems/0c4eee02-3b58-418d-98da-054c8bb5b2a2
-- title:
--   Reading tuples, seeds and circuit descriptions back from bit strings
-- statement:
--   Seeds of the codes in this mission are tuples of bit strings, such as $\mathrm{crs}=(\lambda,k,N,\tilde P_{\mathrm{Enc}},\tilde P_{\mathrm{Dec}})$ in Construction 6.1, and some of their components are descriptions of (obfuscated) circuits. This module fixes how an algorithm reads them back.
--
--   1. $\mathrm{parseTup}(s)$ is the list $(u_0,\dots,u_{j-1})$ with $\mathrm{tup}(u_0,\dots,u_{j-1})=s$ for the published tuple encoding $\mathrm{tup}$, and $\bot$ if $s$ is not a tuple; $\mathrm{tupGet}(s,i)$ is its $i$-th component (empty when missing).
--   2. $\mathrm{circOf}(n,s)$ is the multi-output circuit with $n$ inputs whose published description is $s$, and $\bot$ if there is none.
--   3. $\mathrm{slice}(r,\mathit{off},\mathit{len})$ is the block of $\mathit{len}$ consecutive coins of the coin string $r$ starting at $\mathit{off}$ (bits past the end read $0$): the coins of one sub-algorithm of a composed randomized algorithm.
--
--   These helpers let the encoders and decoders of Constructions 6.1 and 7.1 evaluate the obfuscated programs and keys stored in their seeds.
--
--   **Formalization Note** The tuple encoding and the circuit description are injective, so the decoded components are unique; they are selected by choice.
-- source:
--   Dujmovic, Lu, Silbak, Wichs, Shannon Rate Seeded Codes from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 52f4b606…a769709), p.38 (Construction 6.1, Setup/Encode/Decode)

import Mathlib
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace SeededShannon.Supplement

open LaconicBarrier

/-- Reading a tuple `tup [u₀, …, u_{j−1}]` back into its components (Dujmovic, Lu, Silbak, Wichs,
*Shannon Rate Seeded Codes from Indistinguishability Obfuscation*, STOC 2027 submission (manuscript
sha256 52f4b606…a769709), p.38: a seed is a tuple such as `crs = (λ, k, N, P̃_Enc, P̃_Dec)`).

**Formalization Note** The published tuple encoding `QAdvFew.PoQOracle.tup` is injective, so the
components of a well-formed tuple are unique; they are selected by choice. A string that is not a
tuple reads as `none` (a malformed seed). -/
noncomputable def parseTup (s : List Bool) : Option (List (List Bool)) := by
  classical
  exact if h : ∃ l : List (List Bool), QAdvFew.PoQOracle.tup l = s then some (Classical.choose h)
    else none

/-- The `i`-th component of a tuple, `[]` when missing or malformed. -/
noncomputable def tupGet (s : List Bool) (i : ℕ) : List Bool :=
  match parseTup s with
  | some l => l.getD i []
  | none => []

/-- The multi-output circuit with `n` inputs described by the string `s` (the published
description `LaconicBarrier.MCircuit.code`), `none` if `s` describes no such circuit (p.38:
"`Encode(crs, x)`: return `P̃_Enc(x)`", the obfuscated program read from the seed).

**Formalization Note** `MCircuit.code` is injective, so the circuit is unique; it is selected by
choice. -/
noncomputable def circOf (n : ℕ) (s : List Bool) : Option (MCircuit n) := by
  classical
  exact if h : ∃ C : MCircuit n, C.code = s then some (Classical.choose h) else none

/-- The `len`-bit slice of a coin string starting at offset `off` (bits beyond the end read `0`):
the coins of one sub-algorithm of a composed randomized algorithm. -/
def slice {n : ℕ} (r : Fin n → Bool) (off len : ℕ) : Fin len → Bool :=
  fun j => if h : off + j.val < n then r ⟨off + j.val, h⟩ else false

end SeededShannon.Supplement


