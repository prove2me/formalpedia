-- Prove2me | Definitions.Def_LowDepthPRF_AlmostRandom
-- name    : LowDepthPRF_AlmostRandom
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:37.547312+00:00
-- url     : https://prove2.me/theorems/8d02d838-f2f8-496d-af9b-f42ae7f9604e
-- title:
--   Left-monotone sets and $(q,\epsilon)$-almost-random families
-- statement:
--   Let $X$ and $AUX$ be sets and $X^*$ the power set of $X$. A set $S\subseteq X^*\times AUX$ is **left-monotone** (Definition 3.19) if $(x,aux)\in S$ and $x'\supseteq x$ imply $(x',aux)\in S$.
--
--   A family $F=\{F_{r,aux}:X\to\{0,1\}^b\}$ with key space $R\times AUX$ is **$(q,\epsilon)$-almost-random** (Definition 3.20) if there is a left-monotone $\mathrm{BAD}\subseteq X^*\times AUX$ such that, for every $q'\le q$ and every tuple $x=(x^{(1)},\dots,x^{(q')})$ of distinct inputs, identified with its set:
--
--   1. $\Pr_{aux}[(x,aux)\in\mathrm{BAD}]<\epsilon$;
--   2. for every $aux$ with $(x,aux)\notin\mathrm{BAD}$, the tuple $F_{r,aux}(x)$ is uniform over $(\{0,1\}^b)^{q'}$ when $r$ is uniform.
--
--   The sum $F^{\oplus n}$ has key $((r_1,\dots,r_n),(aux_1,\dots,aux_n))$ and output $F_{r_1,aux_1}(x)\oplus\cdots\oplus F_{r_n,aux_n}(x)$.
--
--   Almost-randomness is the non-adaptive statistical property the security proof of §4 reduces to. It amplifies under sums (Lemma 3.21) and implies adaptive security (Lemma 3.22).
--
--   **Formalization Note** $R$, $AUX$ and $X$ are finite types (any $X$), and outputs are bit strings so that sums are defined. The key space $(R\times AUX)^n$ of $F^{\oplus n}$ is regrouped as $R^n\times AUX^n$, as in the paper's proof (A.1).
-- source:
--   Ding, Jain, Komargodski, Pseudorandom Functions in NC¹ from LWE/LPN/CDH, arXiv:2608.25213 (sha256 89a55849…), Definition 3.19, p.14 (pdf 16); Definition 3.20, p.15 (pdf 17); Appendix A.1, p.36 (pdf 38)

import Mathlib
import Definitions.Def_LowDepthPRF_Pseudorandom

namespace LowDepthPRF

/-!
# Left-monotone sets and (q, ε)-almost-random families

Ding, Jain, Komargodski, *Pseudorandom Functions in NC¹ from LWE/LPN/CDH*, arXiv:2608.25213
(sha256 89a55849…), Definition 3.19, p.14, and Definition 3.20, p.15.

**Formalization Note.**
* The key space is `R × AUX`; the family is written curried, `F r aux x = F_{r,aux}(x)`. The
  input set `X` is any type; outputs are `b`-bit strings (`Y = {0,1}^b`), so that the sum
  `F^{⊕n}` (Definition 3.8, XOR of outputs) applies. `R` and `AUX` are finite types and all
  probabilities are uniform.
* `X^*`, the power set of `X`, is `Set X`; a tuple of distinct inputs is "identified with its
  underlying set" `Set.range x`.
* Condition 2 ("`F_{r,aux}(x)` is uniformly distributed over `Y^{q'}`") says that each output
  tuple has probability `1/|Y|^{q'} = 2^{-b q'}` over `r`.
* The sum `F^{⊕n}` has key space `(R × AUX)^n`; `sumAR` regroups it as `R^n × AUX^n`, which is the
  grouping of the paper's proof (A.1, p.36).
-/

/-- Definition 3.19: `S ⊆ X^* × AUX` is left-monotone — closed under enlarging the set
component. -/
def LeftMonotone {X AUX : Type} (S : Set (Set X × AUX)) : Prop :=
  ∀ x aux, (x, aux) ∈ S → ∀ x' : Set X, x ⊆ x' → (x', aux) ∈ S

/-- Definition 3.20: `F = {F_{r,aux}}` with key space `R × AUX` is `(q, ε)`-almost-random. -/
def AlmostRandom {R AUX X : Type} [Fintype R] [Fintype AUX] {b : ℕ}
    (F : R → AUX → X → (Fin b → Bool)) (q : ℕ) (ε : ℝ) : Prop :=
  ∃ BAD : Set (Set X × AUX), LeftMonotone BAD ∧
    ∀ q' ≤ q, ∀ x : Fin q' → X, Function.Injective x →
      uprob (fun aux : AUX => (Set.range x, aux) ∈ BAD) < ε ∧
      ∀ aux : AUX, (Set.range x, aux) ∉ BAD →
        ∀ y : Fin q' → Fin b → Bool,
          uprob (fun r : R => ∀ i, F r aux (x i) = y i) = 1 / ((2 : ℝ) ^ b) ^ q'

/-- `F^{⊕n}` for a family with key space `R × AUX`, with key regrouped as
`((r_1, …, r_n), (aux_1, …, aux_n)) ∈ R^n × AUX^n`. -/
def sumAR {R AUX X : Type} {b : ℕ} (F : R → AUX → X → (Fin b → Bool)) (n : ℕ) :
    (Fin n → R) → (Fin n → AUX) → X → (Fin b → Bool) :=
  fun r aux x j => bigXor (fun i => F (r i) (aux i) x j)

end LowDepthPRF


