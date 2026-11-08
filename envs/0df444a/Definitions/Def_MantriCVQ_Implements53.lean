-- Prove2me | Definitions.Def_MantriCVQ_Implements53
-- name    : MantriCVQ_Implements53
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:10:42.287883+00:00
-- url     : https://prove2.me/theorems/9b8a1e67-0968-48ab-8086-762e4ad34565
-- title:
--   A verifier that runs Protocol 5.3
-- statement:
--   The public parameters of a claim $(w,b)$ about a node of height $j$ are encoded in one input string, with the size $n$, the height $h$ and $j$ in unary. A verifier **implements Protocol 5.3** if, on every such input with $j\le h\le h_{\max}(n)$, it has $2j$ slots with the prover first, the two messages for the $i$-th list have $4^im_{j-i-1}$ and $3\cdot4^im_{j-i-1}$ bits, and on a transcript of this schedule it accepts iff every claim of the final list matches the leaf stored in the oracle.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Protocol 5.3, pp. 20–21 (PDF pp. 22–23); §5.2, p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_MantriCVQ_Protocol53
import Definitions.Def_MantriCVQ_PCVerifier
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_leafTable

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- The input encoding of a claim `(w, b)` in an instance of size `n` and height `h` about a node of
height `j` (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §5.2, p. 19 (PDF p. 21): "The
public parameters, known to both parties, are the size parameter, the height and dimensions of the
instance, the fixed code family, and the claim"). -/
def claimInput (n h j : ℕ) (w : Str) (b : Bool) : Str :=
  tup [unary n, unary h, unary j, w, [b]]

/-- A transcript that follows the schedule of `V` on the input `inp`. -/
def Conforms (V : PCVerifier) (inp : Str) (tr : List Str) : Prop :=
  tr.length = V.S inp ∧ ∀ (i : ℕ) (hi : i < tr.length), tr[i].length = V.len inp i

/-- The verifier `V` runs Protocol 5.3 (Protocol 5.3, pp. 20–21 (PDF pp. 22–23)) on every claim of an
instance of size `n` and height `h`: there are `2j` slots on a claim about a node of height `j`, the
prover speaks first, the two messages for the `i`-th list have `4^i m_{j-i-1}` and `3 · 4^i m_{j-i-1}`
bits, and on a transcript of the schedule the verifier accepts iff every claim of the final list
matches the leaf stored in the oracle. -/
def Implements53 (C : (m : ℕ) → Bits m → Bits m → Bool) (V : PCVerifier) : Prop :=
  ∀ (n h j : ℕ) (w : Str) (b : Bool), 1 ≤ n → j ≤ h → h ≤ hmax n →
    V.S (claimInput n h j w b) = 2 * j ∧ V.proverFirst (claimInput n h j w b) = true ∧
      (∀ i : ℕ, i < j →
        V.len (claimInput n h j w b) (2 * i) = 4 ^ i * dim n (j - i - 1) ∧
          V.len (claimInput n h j w b) (2 * i + 1) = 3 * (4 ^ i * dim n (j - i - 1))) ∧
      ∀ (O : Oracle) (tr : List Str), Conforms V (claimInput n h j w b) tr →
        (V.decides O (claimInput n h j w b) tr ↔
          ∀ e ∈ runList C (dimsRange n 0 j) [(w, b)] tr, leafTable O n e.1 = e.2)

end MantriCVQ


