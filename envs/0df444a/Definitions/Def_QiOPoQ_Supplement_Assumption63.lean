-- Prove2me | Definitions.Def_QiOPoQ_Supplement_Assumption63
-- name    : QiOPoQ_Supplement_Assumption63
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:08:45.395058+00:00
-- url     : https://prove2.me/theorems/064dcb8c-e189-4644-9a74-9ded79d13b4f
-- title:
--   Assumption 6.3 (strong quantum random-input obfuscation)
-- statement:
--   For given $p_1,p_2$, classical PPT transformations RIO, Encode and functions $s(\lambda,n)$, $N(\lambda,n,k)$:
--
--   1. RIO and Encode satisfy the correctness guarantee of Definition 3.1; $s,N$ are polynomial-time computable and polynomially bounded;
--   2. $s\ge\max\{1,p_2(\lambda,n)\}$, $N(\lambda,n,k)\ge k$ for $k\in\{s,2s,2s+1\}$, $N(\lambda,n,2s)\ge p_1(\lambda,n)s$, $N(\lambda,n,2s+1)\ge p_1(\lambda,n)(s+1)$;
--   3. for every polynomially bounded width $n$, every $k\in\{s,2s,2s+1\}$, every joint distribution $(\mathsf{aux},C)$ of polynomial-size descriptions with $C$ marginally uniform over $\mathcal C_{n,k}$, and every non-uniform QPT distinguisher,
--   $$(1^\lambda,\mathsf{aux},C,\mathrm{RIO}(1^\lambda,C))\approx_c(1^\lambda,\mathsf{aux},C,\mathrm{Encode}(1^\lambda,D)),\qquad D\leftarrow\mathcal E_{C,N(\lambda,n,k)}.$$
--
--   **Formalization Note** A joint distribution with $C$ marginally uniform is $C\leftarrow\mathcal C_{n,k}$ together with an arbitrary conditional law of $\mathsf{aux}$ given $C$ on strings of polynomially bounded length (not necessarily samplable).
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.3, p.31

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Negligible
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QiOPoQ_pair
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_Supplement_NUQPT
import Definitions.Def_QiOPoQ_Supplement_Placement
import Definitions.Def_QMAvsQCMAH_PolyBounded
import Definitions.Def_QiOPoQ_Supplement_PolyBounded2
import Definitions.Def_QiOPoQ_Supplement_avgRand
import Definitions.Def_QiOPoQ_Supplement_IsAFCorrect

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAdvFew.PoQOracle QAlgorithms.Complexity

/-- The three lengths `k ∈ {s, 2s, 2s + 1}` of Assumption 6.3. -/
def kSel (s : ℕ → ℕ → ℕ) (l n : ℕ) (j : Fin 3) : ℕ :=
  ![s l n, 2 * s l n, 2 * s l n + 1] j

/-- **Assumption 6.3 (Strong quantum random-input obfuscation (RIO)).** Gheorghiu, Gupte,
Havlíček, Liu, *Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation*,
arXiv:2609.40289 (sha256 fe2f9210…), Assumption 6.3, p.31: "There are classical probabilistic
polynomial-time transformations RIO, Encode of ancilla-free quantum circuits, each satisfying the
negligible diamond-distance correctness guarantee of Definition 3.1, and polynomial-time computable
and polynomially bounded functions s = s(λ, n), N(λ, n, k) such that for every polynomially bounded
width n = n(λ), every k ∈ {s, 2s, 2s + 1}, and every joint distribution (aux, C) of polynomial-size
classical descriptions in which C is marginally uniform over C_{n,k},
(1^λ, aux, C, RIO(1^λ, C)) ≈c (1^λ, aux, C, Encode(1^λ, D)), D ← E_{C,N(λ,n,k)}. Here
indistinguishability is against nonuniform QPT distinguishers, and s ≥ max{1, p2(λ, n)},
N(λ, n, k) ≥ k, N(λ, n, 2s) ≥ p1(λ, n)s, and N(λ, n, 2s + 1) ≥ p1(λ, n)(s + 1), where p1, p2 are
the functions from Assumption 6.2."

This is the property of the given data `p1, p2, RIO, Encode, s, N`. A joint distribution with `C`
marginally uniform over `C_{n,k}` is `C ← C_{n,k}` together with an arbitrary conditional law
`aux(λ, C)` on strings of polynomially bounded length. The distinguisher receives
`(1^λ, (aux, C, ·))`.

**Formalization Note.** `N(λ, n, k) ≥ k` is required for the three lengths `k ∈ {s, 2s, 2s + 1}`
named in the assumption. -/
def Assumption63 (G : GateSet) (p1 p2 : ℕ → ℕ → ℕ) (RIO Enc : UPPT) (s : ℕ → ℕ → ℕ)
    (N : ℕ → ℕ → ℕ → ℕ) : Prop :=
  IsAFCorrect G RIO ∧ IsAFCorrect G Enc ∧ PolyTime2 s ∧ PolyBounded2 s ∧ PolyTime3 N ∧
  PolyBounded3 N ∧
  (∀ l n, max 1 (p2 l n) ≤ s l n ∧ (∀ j : Fin 3, kSel s l n j ≤ N l n (kSel s l n j)) ∧
    p1 l n * s l n ≤ N l n (2 * s l n) ∧ p1 l n * (s l n + 1) ≤ N l n (2 * s l n + 1)) ∧
  ∀ nw : ℕ → ℕ, QMAvsQCMAH.PolyBounded nw → ∀ j : Fin 3,
    ∀ aux : (l : ℕ) → List (Placement G (nw l)) → PMF Str,
    (∃ p : Polynomial ℕ, ∀ l C a, a ∈ (aux l C).support → a.length ≤ p.eval l) →
    ∀ D : NUQPT, ∃ μ : ℕ → ℝ, Negligible μ ∧ ∀ l,
      |avgRand G (nw l) (kSel s l (nw l) j) (fun C => ∑' a : Str, (aux l C a).toReal *
          RIO.expect (pair (unary l) (encCirc (afCirc (nw l) C))) fun o =>
            D.acc G l (tup [a, encCirc (afCirc (nw l) C), o])) -
        avgRand G (nw l) (kSel s l (nw l) j) (fun C => ∑' a : Str, (aux l C a).toReal *
          avgEquiv G (nw l) (N l (nw l) (kSel s l (nw l) j)) C fun Dc =>
            Enc.expect (pair (unary l) (encCirc (afCirc (nw l) Dc))) fun o =>
              D.acc G l (tup [a, encCirc (afCirc (nw l) C), o]))| ≤ μ l

end QiOPoQ.Supplement


