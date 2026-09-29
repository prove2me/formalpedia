-- Prove2me | Definitions.Def_mme_tau_value
-- name    : mme_tau_value
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-23T23:17:41.671189+00:00
-- url     : https://prove2.me/theorems/e7bfa315-ef22-4a2e-bcee-27354f1d9a97
-- title:
--   Unrestricted Coppersmith--Winograd tau-value witnesses
-- statement:
--   **The asymptotic $\tau$-value witness** — the Coppersmith–Winograd "value" of a tensor, in witness form.
--
--   Fix a field $K$, an order-three tensor object $T$ over $K$, a weight exponent $\tau\in\mathbb{R}$, and a real number $V\ge 0$ (the claimed value). The predicate $\operatorname{HasTauValueAtLeast}(T,\tau,V)$ asserts that, for every relative error $\varepsilon>0$ and for arbitrarily large tensor powers $N$ (frequently in $N$, not merely for one $N$), there exist a finite index count $k$ and dimension triples $(a_i,b_i,c_i)$ for $i<k$ such that the direct sum $\bigoplus_{i<k}\langle a_i,b_i,c_i\rangle$ of matrix-multiplication tensors is a restriction of $T^{\otimes N}$ — obtained from it by one linear map per mode — and the $\tau$-weighted volumes of the extracted products satisfy
--
--   $$
--   V^{N}\,(1-\varepsilon)\;\le\;\sum_{i<k}\bigl(a_i\,b_i\,c_i\bigr)^{\tau}.
--   $$
--
--   In words: $T$ has $\tau$-value at least $V$ when its powers really contain, as honest restrictions, direct sums of matrix products whose weighted volume grows at exponential rate $V$. This is the witness-level form of the value $V_\tau$ introduced by Coppersmith–Winograd on journal p. 264.
--
--   The number $k$ of surviving summands is deliberately unrestricted — laser extractions produce exponentially many blocks — and the summand dimensions remain part of the witness. This rules out constant-valued or entropy-only "value functionals" with no algebraic content: any theorem stated through this predicate must exhibit actual restrictions.
--
--   **Formalization Note** The target of `TensorObj.Restrict` is written first, so the displayed direct sum is obtained from `T.kronPow N` by modewise linear substitutions. "Arbitrarily large $N$" is the frequently-at-top quantifier `∃ᶠ N in atTop`.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal p. 264 (PDF p. 14), definition of the value V_tau; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Order.Filter.AtTopBot.Defs
import Definitions.Def_mme_tensor_rank

/-!
# Asymptotic tau-value witnesses

This is the witness-level version of the value used by Coppersmith and
Winograd on journal p. 264.  It deliberately keeps the entire finite direct
sum of matrix-multiplication tensors produced by the extraction.  In
particular, there is no bound on the number of summands and no replacement by
a constant-valued or entropy-only functional.

For every positive relative error and arbitrarily large tensor powers, the
witness supplies an actual restriction to a concrete direct sum.  The sum of
the tau-weighted matrix-product volumes grows at exponential rate at least
`V`.
-/

universe u

open BigOperators Filter

namespace MME

/-- `HasTauValueAtLeast T tau V` records an unrestricted, asymptotic
Coppersmith--Winograd value witness for `T`.

The target of `TensorObj.Restrict` is written first, so the displayed direct
sum is obtained from `T.kronPow N` by modewise linear substitutions.  The
frequent quantifier at `atTop` means that suitable powers occur arbitrarily
far out; the number `k` of surviving matrix products is intentionally
unrestricted. -/
def HasTauValueAtLeast {K : Type u} [Field K]
    (T : TensorObj K 3) (tau V : ℝ) : Prop :=
  0 ≤ V ∧
  ∀ epsilon > (0 : ℝ), ∃ᶠ N : ℕ in atTop,
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        (T.kronPow N) ∧
      V ^ N * (1 - epsilon) ≤
        ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)

end MME


