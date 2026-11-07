-- Prove2me | Definitions.Def_QiOPoQ_pair
-- name    : QiOPoQ_pair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:48.356817+00:00
-- url     : https://prove2.me/theorems/74a04db8-682d-49ca-9ed0-34324852b16b
-- title:
--   Pairs of bit strings, and parsing of tuples
-- statement:
--   The algorithms of the paper take tuples of strings as input: $(1^\lambda, C)$ for the obfuscator, $(1^\lambda, r, \mathsf{chall}, \mathsf{resp})$ for the verifier, and the challenge itself is the tuple $(\hat C_1,\dots,\hat C_t,y)$. The paper does not fix a bit layout, so one is fixed here: the published injective tuple code `tup`, and $\mathrm{pair}(a,b)=\mathrm{tup}(a,b)$. `untuple` recovers a list from its code and returns nothing on a string that is no tuple code.
--
--   A single fixed code matters: an encoding chosen freely inside an existential could carry the answer to a problem.
--
--   **Formalization Note** The published `encStr` is not used, because it is not injective.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.2–3.3, pp.14–15 and Figure 6, p.21 (tuples such as $(1^\lambda, C)$ and $(\hat C_1,\dots,\hat C_t,y)$)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAdvFew_PoQOracle_tup

set_option autoImplicit false

namespace QiOPoQ

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- The pair `(a, b)` of two strings, the published tuple code `tup [a, b]`. Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…). The paper writes algorithms on tuples such as `(1^λ, C)`,
`(1^λ, r, chall, resp)` and `chall = (Ĉ_1, …, Ĉ_t, y)` (§3.2–3.3, pp.14–15; Figure 6, p.21) without
fixing a bit layout. E.g. `Obf(1^λ, C)` is run on `pair (unary λ) (encCirc C)` and a probabilistic
algorithm on input `x` with coins `r` is run on `pair x r`.

**Formalization Note.** One fixed, injective code is used everywhere: `QAdvFew.PoQOracle.tup`,
also for `chall`, for the list of circuits a quantum algorithm generates, and for the inputs of
Verify and PublicVerify. The published `QAlgorithms.Complexity.encStr` is not used: it is not
injective. -/
def pair (a b : Str) : Str := tup [a, b]

open Classical in
/-- Parsing of `tup`: `untuple s = some l` when `s = tup l`, and `none` when `s` is not a tuple
code. **Formalization Note.** `tup` is injective, so the list chosen is the unique one. -/
noncomputable def untuple (s : Str) : Option (List Str) :=
  if h : ∃ l, tup l = s then some h.choose else none

/-- A bit as a one-letter string; a decision algorithm outputs `[true]` (accept, "= 1") or
`[false]`. -/
def bitStr (b : Bool) : Str := [b]

end QiOPoQ


