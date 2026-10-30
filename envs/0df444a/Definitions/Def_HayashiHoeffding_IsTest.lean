-- Prove2me | Definitions.Def_HayashiHoeffding_IsTest
-- name    : HayashiHoeffding_IsTest
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T03:14:15.636818+00:00
-- url     : https://prove2.me/theorems/a1dbd1f1-a951-46f2-b36c-6237e1354a2b
-- title:
--   Test (two-outcome POVM) $0 \le T \le I$
-- statement:
--   A bounded operator $T$ on a complex Hilbert space is a **test** if
--
--   $$0 \le T \le I .$$
--
--   A test is identified with the two-valued POVM $\{T, T^c\}$, $T^c := I - T$: outcome $T$ accepts the alternative hypothesis. For $n$-copy testing of $\rho^{\otimes n}$ against $\sigma^{\otimes n}$, the error probability of the first kind is $\operatorname{Tr}[\rho^{\otimes n} T_n^c]$ and of the second kind $\operatorname{Tr}[\sigma^{\otimes n} T_n]$.
--
--   **Formalization Note** The order is Mathlib's Loewner order; $0 \le T$ already makes $T$ self-adjoint (the paper's "hermitian").
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2

import Mathlib

namespace HayashiHoeffding

universe u

/-- A test on a complex Hilbert space `E`: a bounded operator `T` with `0 ≤ T ≤ I` (identified
with the two-valued POVM `{T, I − T}`).

Hayashi, arXiv:quant-ph/0611013v2, "Formulation and main results", p.2: "a hermitian matrix Tn
satisfying inequalities 0 ≤ Tn ≤ I is called a test in the sequel".

**Formalization Note.** The order is Mathlib's Loewner order on `E →L[ℂ] E`; `0 ≤ T` already
implies that `T` is self-adjoint ("hermitian"). In this mission `E` is a tensor power
`H^{⊗n}` of an arbitrary complex Hilbert space, not necessarily finite-dimensional. -/
def IsTest {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) : Prop :=
  0 ≤ T ∧ T ≤ 1

end HayashiHoeffding


