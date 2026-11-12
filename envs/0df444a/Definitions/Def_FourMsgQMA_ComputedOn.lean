-- Prove2me | Definitions.Def_FourMsgQMA_ComputedOn
-- name    : FourMsgQMA_ComputedOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:35.944181+00:00
-- url     : https://prove2.me/theorems/1d07aff5-e089-46da-a256-cc0833399d75
-- title:
--   Cost vocabulary: $\lceil\log_2\rceil$, four-variable polynomial bounds, circuit size on the inputs that occur
-- statement:
--   Three pieces of cost vocabulary used throughout the mission.
--
--   1. $\operatorname{clog2}(n)=\lceil\log_2 n\rceil$, so $\lceil\log_2 1\rceil=0$. The paper's $\log(k+1)$ and $\log(s+1)$ (§3.1) are read as $\lceil\log_2(k+1)\rceil$ and $\lceil\log_2(s+1)\rceil$, which cover $k=1$ and $s=0$; its $d=\lceil\log_2 k\rceil$ (§5.1) is $\operatorname{clog2}(k)$.
--   2. A bound "$\mathrm{poly}(a,b,c,d)$" is the value $p(a,b,c,d)$ of a polynomial $p$ in four variables with natural-number coefficients; such a $p$ is monotone in every argument.
--   3. For a function $f$ on bit strings, a set $S$ of inputs, a length $n$ and a size $s$: $f$ is **computed on $S$ at length $n$ with size $s$** if at most $s$ Boolean circuits of total size at most $s$, one per output bit, write the self-delimiting encoding of $f(x)$ for every $x\in S$ of length $n$.
--
--   Item 3 is the published size measure `TightPQRepetition.Main.ComputedBySize` with "every input of length $n$" restricted to the inputs in $S$. It measures the work of an online verifier stage on the inputs its own preprocessing can produce (§3.3: "for every admissible input, setup outcome, and transcript").
--
--   **Formalization Note** Pinned-down version (operator request) of the cost model of §3.3.
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), §3.1, p.9 (PDF 11); §3.3, pp.11–12 (PDF 13–14); §5.1, p.34 (PDF 36)

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Protocol
import Definitions.Def_QAlgorithms_Defs_Complexity

namespace FourMsgQMA

/-!
Goyal, Koppula, *Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from
LWE*, STOC 2027 submission (sha256 6c523d45…), §3.1 and §3.3 (pp.9, 11–12): the cost vocabulary
of the pinned-down version (operator request) of Corollary 5.15.
-/

open TightPQRepetition.Main

/-- `⌈log₂ n⌉` (`Nat.clog 2`), so `clog2 1 = 0`, `clog2 2 = 1`, `clog2 3 = 2`. The paper's
`log(k + 1)` and `log(s + 1)` (p.9) are read as `clog2 (k + 1)` and `clog2 (s + 1)`, and its
`⌈log₂ k⌉` (p.34) as `clog2 k`. -/
def clog2 (n : ℕ) : ℕ := Nat.clog 2 n

/-- The value `p(a, b, c, d)` of a polynomial in four variables with natural-number coefficients.
Such a polynomial is monotone in each argument. "poly(λ, T, log(k+1), log(s+1))" of §3.3 (p.12)
is a bound of this form. -/
noncomputable def eval4 (p : MvPolynomial (Fin 4) ℕ) (a b c d : ℕ) : ℕ :=
  MvPolynomial.eval ![a, b, c, d] p

/-- On the inputs of length `n` that lie in `S`, `f` is computed by at most `s` Boolean circuits,
one per output wire, of total size at most `s`. This is the published
`TightPQRepetition.Main.ComputedBySize` with "for every input of length `n`" restricted to the
inputs in `S`: the work of an online verifier stage is measured on the inputs that its own
preprocessing can produce (§3.3, p.12: "for every admissible input, setup outcome, and transcript"),
not on every string of the same length. -/
def ComputedOn (f : Bits → Bits) (S : Set Bits) (n s : ℕ) : Prop :=
  ∃ (L : ℕ) (C : Fin L → MIPRE.SAT.Circuit), L ≤ s ∧ (∑ i, (C i).size) ≤ s ∧
    ∀ x ∈ S, x.length = n →
      (packOne (f x)).length ≤ L ∧ ∀ i : Fin L, (packOne (f x)).getD i false = (C i).evalBits x

end FourMsgQMA


