-- Prove2me | Definitions.Def_QiOPoQ_Supplement_NUQPT
-- name    : QiOPoQ_Supplement_NUQPT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:43:40.59423+00:00
-- url     : https://prove2.me/theorems/57b70e55-9708-4112-9ea1-9ddeb0ab96e6
-- title:
--   Non-uniform quantum polynomial-time algorithms with classical advice
-- statement:
--   The quantum adversaries, provers, distinguishers and inverters of Sections 5 and 6 ("QPT", "non-uniform QPT"). On input $(1^\lambda,x)$ such an algorithm $A$ draws polynomially many uniform coins $r$, forms $w=(\mathrm{adv}(\lambda),1^\lambda,x,r)$ with an advice string $\mathrm{adv}(\lambda)$ of polynomially bounded length, computes in classical polynomial time a list of circuit descriptions, runs each circuit on $|0\cdots0\rangle$ and measures its output register, and returns a classical polynomial-time function of $w$ and the measured outcomes. $\Pr[A(1^\lambda,x)=1]$ is the probability that the output is the one-bit string $1$.
--
--   This class is used for qiO security against quantum adversaries, for cheating provers, for blindness distinguishers and for one-way function inverters.
--
--   **Formalization Note** Advice is classical: the paper never uses quantum advice and excludes quantum auxiliary inputs to circuits (§3.1). The classical pre- and post-processing make the class closed under classical polynomial-time composition, as the hybrid reductions need, and contain every non-uniform classical PPT algorithm. Over a universal gate set, intermediate measurements and adaptivity can be deferred into the circuits, so this is the usual notion.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3, p.13; Definition 3.2, p.14; Definition 3.5, p.16 (QPT adversaries, provers, distinguishers)

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_qptExpect

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- **A non-uniform quantum polynomial-time algorithm with classical input and output.**
Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit
Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…), §3, p.13: "We abbreviate … “quantum
polynomial-time” as … QPT … In general, we consider non-uniform adversaries throughout this
paper"; Definition 3.2, p.14 ("Depending on whether we quantify A over all PPT or QPT
algorithms, Obf is secure against classical or quantum adversaries"); Definition 3.5, p.16
("every possibly nonuniform QPT prover A", "every non-uniform QPT distinguisher D").

On `(1^λ, x)` the algorithm reads `coins(λ + |x|)` uniform coins `r`, forms
`w = (advice(λ), 1^λ, x, r)`, and computes in deterministic polynomial time a tuple `pre(w)` of
circuit descriptions over the gate set; the circuits are run on `|0…0⟩` and their output
registers measured (the published `qptExpect`), giving the outcome string `z`; the output is
`post(w, z)`, computed in deterministic polynomial time. The advice has polynomially bounded
length.

**Formalization Note.** Classical advice only: the paper never mentions quantum advice, and §3.1
excludes quantum auxiliary inputs. Classical pre- and post-processing make the class closed
under composition with classical polynomial-time computations (as the hybrid reductions of §5
require) and contain every non-uniform classical PPT algorithm (`pre` outputs no circuit). Over
a universal gate set this is the standard notion: intermediate measurements and adaptivity can be
deferred into the circuits. -/
structure NUQPT where
  /-- Classical polynomial-time generator of the circuits. -/
  pre : Str → Str
  pre_poly : PolyTimeComputable pre
  /-- Classical polynomial-time post-processing of `(w, z)`. -/
  post : Str → Str
  post_poly : PolyTimeComputable post
  /-- The advice string for security parameter `λ`. -/
  advice : ℕ → Str
  adviceLen : Polynomial ℕ
  advice_le : ∀ n, (advice n).length ≤ adviceLen.eval n
  /-- The number of classical coins, a polynomial in `λ + |x|`. -/
  coins : Polynomial ℕ

/-- `E[g(A(1^λ, x))]`, over the coins of `A` and the measurement outcomes of its circuits. -/
noncomputable def NUQPT.expect (G : GateSet) (A : NUQPT) (n : ℕ) (x : Str) (g : Str → ℝ) : ℝ :=
  avgCoins (A.coins.eval (n + x.length)) fun r =>
    qptExpect G (A.pre (pair (A.advice n) (pair (unary n) (pair x r)))) fun z =>
      g (A.post (pair (pair (A.advice n) (pair (unary n) (pair x r))) z))

/-- `Pr[A(1^λ, x) = 1]` (output `[true]`). -/
noncomputable def NUQPT.acc (G : GateSet) (A : NUQPT) (n : ℕ) (x : Str) : ℝ :=
  A.expect G n x fun o => if o = [true] then 1 else 0

end QiOPoQ.Supplement


