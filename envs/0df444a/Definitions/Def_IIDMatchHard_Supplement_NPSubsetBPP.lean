-- Prove2me | Definitions.Def_IIDMatchHard_Supplement_NPSubsetBPP
-- name    : IIDMatchHard_Supplement_NPSubsetBPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T00:19:09.208792+00:00
-- url     : https://prove2.me/theorems/85ce4b2a-9d99-47c5-96af-95d35cd8e1b6
-- title:
--   $\mathrm{NP}\subseteq\mathrm{BPP}$ with explicit fair coins and polynomial clocks
-- statement:
--   A Boolean language is in $\mathrm{BPP}$ when one finite multitape machine uses polynomially many fair random bits, halts on every random branch within a single polynomial worst-case clock, accepts members with probability at least $2/3$, and accepts nonmembers with probability at most $1/3$. The inclusion
--
--   $$
--   \mathrm{NP}\subseteq\mathrm{BPP}
--   $$
--
--   means that every Boolean language in Cook's class $\mathrm{NP}$ has such a bounded-error randomized decider.
--
--   The same module defines randomized rational-output algorithms by an explicit output machine and exact finite seed counts. These are used to state the approximation clause of Theorem 3.10 without an unspecified probability space.
--
--   **Formalization Note** The machine layer is `ApproxPolySatCH.Main.RandomizedDecider` with the oracle fixed to the empty language. Restricting the class notation to Boolean encodings is the standard finite-alphabet encoding convention.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Theorem 3.10, p.10 (PDF p.11); proof p.24 (PDF p.25)

import Mathlib
import Definitions.Def_ApproxPolySatCH_Main_Complexity
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_ImpatientMatching_Input

set_option autoImplicit false

namespace IIDMatchHard

namespace Supplement

abbrev Word := List Bool

/-- A Boolean language is in **BPP** when one finite multitape machine, using an explicitly
polynomial number of fair random bits, halts on every branch in one polynomial clock and has
two-sided error at most `1/3`. Teng–Yang, *Computational Hardness of Online Stochastic Matching*
(manuscript of Nov. 3, 2026, sha256 f0193d92…), Theorem 3.10, p.10 (PDF p.11).

**Formalization Note.** This is the published `ApproxPolySatCH.Main.RandomizedDecider` with no
oracle. Its exact seed count makes the probabilities finite counts divided by a power of two. -/
def InBPP (L : Set Word) : Prop :=
  ∃ (M : NKtLB.Machine) (c d a b : ℕ),
    ApproxPolySatCH.Main.RandomizedDecider M ∅ L c d a b

/-- A randomized polynomial-time rational-output algorithm. On input `x` it uses exactly
`clock a b |x|` fair bits, every branch halts by `clock c d |x|`, and the output tape contains
the canonical rational encoding of `out x r`.

**Formalization Note.** A single machine and four constants govern every input and seed, so
randomness and worst-case branch time are uniformly polynomial. -/
structure RandRatAlg where
  out : Word → Word → ℚ
  machine : NKtLB.Machine
  timeConst : ℕ
  timeDegree : ℕ
  coinConst : ℕ
  coinDegree : ℕ
  computes : ∀ (x : Word)
    (r : Fin (ApproxPolySatCH.Main.clock coinConst coinDegree x.length) → Bool),
      machine.HaltsWith ∅ ⟨x, [], [], List.ofFn r⟩
        (ApproxPolySatCH.Main.clock timeConst timeDegree x.length)
        (NKtLB.bitsSym (ImpatientMatching.encRat (out x (List.ofFn r))))

/-- The number of fair seeds on which `A` returns a rational satisfying `good`. -/
noncomputable def goodSeedCount (A : RandRatAlg) (x : Word) (good : ℚ → Prop) : ℕ := by
  classical
  exact (Finset.univ.filter (fun r :
    Fin (ApproxPolySatCH.Main.clock A.coinConst A.coinDegree x.length) → Bool =>
      good (A.out x (List.ofFn r)))).card

/-- `A` succeeds with probability at least `2/3` on `x`, expressed by exact counting of its
uniform fair seeds. -/
def SucceedsTwoThirds (A : RandRatAlg) (x : Word) (good : ℚ → Prop) : Prop :=
  2 * 2 ^ ApproxPolySatCH.Main.clock A.coinConst A.coinDegree x.length ≤
    3 * goodSeedCount A x good

/-- The unrelativized inclusion `NP ⊆ BPP`, on Boolean encodings: every Boolean language in
Cook's `NP` has a bounded-error randomized decider with explicit polynomially many fair coins
and a worst-case polynomial clock. Teng–Yang (sha256 f0193d92…), Theorem 3.10, p.10 (PDF p.11),
proof p.24 (PDF p.25).

**Formalization Note.** Complexity classes are invariant under standard finite-alphabet binary
encodings; using Boolean languages aligns Cook's `NP` with the finite-machine BPP layer. The
success constant is literally `2/3`. -/
def NPSubsetBPP : Prop :=
  ∀ L : CookPvsNP.Lang Bool, L ∈ CookPvsNP.NP Bool → InBPP L

end Supplement

end IIDMatchHard


