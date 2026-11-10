-- Prove2me | Definitions.Def_PPSLattice_encvec
-- name    : PPSLattice_encvec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:32:17.600844+00:00
-- url     : https://prove2.me/theorems/18268618-458b-41e7-8959-6ae3ce5d7cba
-- title:
--   The index code $\mathrm{encvec}(i)\in\{0,1\}^{\lceil\log N\rceil}$
-- statement:
--   For $N\ge1$ and an index $i\in[N]=\{1,\dots,N\}$,
--   $$\mathrm{encvec}(i)=\mathrm{bin}_{\lceil\log_2 N\rceil}(i-1)\in\{0,1\}^{\lceil\log N\rceil},$$
--   the canonical bit vector of the index (least significant bit first).
--
--   It is the input of the set-membership circuit $f_S$ and the vector in $\mathbf A-\mathrm{encvec}(i)\otimes\mathbf G$.
--
--   **Formalization Note** The code of $i-1\in[0,N)$ is used, so that $\lceil\log N\rceil$ bits suffice and the code is injective on $[N]$ (coding $i$ itself would make $i=N=2^k$ collide with $0$).
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Notation, p.20

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_AvoidPlast_fixedBits
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- **`encvec(i)`**, an index `i ∈ [N] = {1, …, N}` written as a bit vector in `{0,1}^{⌈log N⌉}`:
the `⌈log₂ N⌉`-bit binary code of `i − 1`.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), §4.3, Notation, p.20 ("encvec(i) to write an index i ∈ [N] as a canonical bit vector
i^⊤ ∈ {0,1}^{1×⌈log N⌉}").

**Formalization Note.** The index `i − 1 ∈ [0, N)` is coded, so `⌈log₂ N⌉` bits suffice for every
`i ∈ [N]` and the code is injective on `[N]` (coding `i` itself would collide `N = 2^k` with
`0`). Bits are least significant first. -/
def encvec (N i : ℕ) : Str := AvoidPlast.fixedBits (Nat.clog 2 N) (i - 1)

end PPSLattice


