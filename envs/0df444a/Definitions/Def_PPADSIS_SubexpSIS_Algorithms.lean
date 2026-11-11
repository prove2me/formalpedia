-- Prove2me | Definitions.Def_PPADSIS_SubexpSIS_Algorithms
-- name    : PPADSIS_SubexpSIS_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:46:04.1455+00:00
-- url     : https://prove2.me/theorems/9a1cb6b1-bb15-4a34-9621-629df015eedf
-- title:
--   Probabilistic polynomial-time algorithms with explicit coins, uniform averages, time-bounded machines
-- statement:
--   The machine model for the uniform algorithms of the paper (samplers, `Setup`, decoders, puzzle algorithms).
--
--   - $\mathrm{coinAvg}(k,f) = 2^{-k}\sum_{c\in\{0,1\}^k} f(c)$ is the average over $k$ fair coins.
--   - A **probabilistic algorithm with explicit coins** on inputs $a$ written as $\mathrm{code}(a)$ is a polynomial $p\in\mathbb N[X]$ and a map $\mathrm{run}$: on input $a$ it reads $p(|\mathrm{code}(a)|)$ uniform coins $c$ and outputs $\mathrm{run}(a,c)$. The input code is a parameter fixed by the definition that uses the algorithm (for a sampler it is $1^\lambda$), so the algorithm receives no advice.
--   - The algorithm is **probabilistic polynomial time** (`IsPPT`) if one polynomial-time machine (the published `PolyTimeComputable`, multi-stack Turing machines) maps `encStr (code a)` followed by the coins to $\mathrm{run}(a,c)$, for every input and every coin string of the prescribed length.
--   - $\Pr[E(A(a))]$ is the fraction of coin strings $c$ with $E(\mathrm{run}(a,c))$; the **support** of $A(a)$ is the set of its outputs.
--   - **Time-bounded computation** (`TimeBoundedOn code out T`): one machine of Mathlib's `FinTM2` model, started on $\mathrm{code}(a)$, halts with $\mathrm{out}(a)$ within $T(a)$ steps, for every $a$ of the index type. It expresses running times that are not polynomial in the input length, such as $t\cdot\mathrm{poly}(\log t,|x|)$, and running times required only on the inputs a definition names.
--
--   **Formalization Note** The coin count is a fixed polynomial of the input length, as in the published `PPSLattice.PPTSampler`; any polynomial-time algorithm reads at most polynomially many coins, and unused coins do not change its output law.
-- source:
--   Choudhuri, PPAD Hardness from SIS, STOC 2027 submission (manuscript sha256 17abad73…), p. 21 ('sampled in polynomial time'), p. 23 ('Setup ... is a PPT algorithm', deterministic algorithms), p. 26 (Definition 4.3, running times)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_PPADSIS_SubexpSIS_Encoding

set_option autoImplicit false

namespace PPADSIS.SubexpSIS

open QAlgorithms.Complexity Polynomial

/-- The **uniform average** of `f` over `k` fair coins: `2^{−k} ∑_{c ∈ {0,1}^k} f(c)`. -/
noncomputable def coinAvg (k : ℕ) (f : (Fin k → Bool) → ℝ) : ℝ :=
  (∑ c : Fin k → Bool, f c) / 2 ^ k

/-- A **probabilistic algorithm with explicit coins** on inputs `a : ι` written as `code a`
(Choudhuri, *PPAD Hardness from SIS*, STOC 2027 submission (manuscript sha256 17abad73…), §3,
p. 21, "sampled in polynomial time"; §4.1, p. 23, "a PPT algorithm"): on input `a` it reads
`coins.eval |code a|` uniform coins `c` (a polynomial number in the input length) and outputs
`run a c`. The input code is a parameter, not a field, so the algorithm sees exactly `code a`
and its coins. -/
structure CoinAlg {ι : Type} (code : ι → List Bool) where
  coins : ℕ[X]
  run : ι → List Bool → List Bool

/-- The number of coins used on input `a`. -/
def CoinAlg.numCoins {ι : Type} {code : ι → List Bool} (A : CoinAlg code) (a : ι) : ℕ :=
  A.coins.eval (code a).length

/-- The algorithm is **probabilistic polynomial time**: one polynomial-time machine (the published
`PolyTimeComputable`, multi-stack Turing machines) maps `encStr (code a)` followed by the coin
string `c` to `run a c`, for every input `a` and every coin string of the prescribed length. -/
def CoinAlg.IsPPT {ι : Type} {code : ι → List Bool} (A : CoinAlg code) : Prop :=
  ∃ M : List Bool → List Bool, PolyTimeComputable M ∧
    ∀ (a : ι) (c : List Bool), c.length = A.numCoins a → M (encStr (code a) ++ c) = A.run a c

open Classical in
/-- `Pr[E(A(a))]` over the coins of `A`. -/
noncomputable def CoinAlg.prob {ι : Type} {code : ι → List Bool} (A : CoinAlg code) (a : ι)
    (E : List Bool → Prop) : ℝ :=
  coinAvg (A.numCoins a) (fun c => if E (A.run a (List.ofFn c)) then 1 else 0)

/-- `x` is in the **support** of `A(a)`: some coin string of the prescribed length gives `x`. -/
def CoinAlg.InSupport {ι : Type} {code : ι → List Bool} (A : CoinAlg code) (a : ι)
    (x : List Bool) : Prop :=
  ∃ c : List Bool, c.length = A.numCoins a ∧ A.run a c = x

/-- **Time-bounded computation on coded inputs**: one machine of Mathlib's `FinTM2` model (the
model behind `PolyTimeComputable`), with input and output alphabet `Bool`, started on `code a`,
halts with `out a` on its output stack within `T a` steps, for every `a : ι`. Used for running
times that are not polynomial in the input length, such as `t · poly(log t, |x|)`
(Definition 4.3), and for running times bounded only on the inputs a definition names. -/
def TimeBoundedOn {ι : Type} (code : ι → List Bool) (out : ι → List Bool) (T : ι → ℕ) : Prop :=
  ∃ M : Turing.TM2ComputableAux Bool Bool, ∀ a : ι,
    Nonempty (Turing.TM2OutputsInTime M.tm ((code a).map M.inputAlphabet.invFun)
      (some ((out a).map M.outputAlphabet.invFun)) (T a))

end PPADSIS.SubexpSIS


