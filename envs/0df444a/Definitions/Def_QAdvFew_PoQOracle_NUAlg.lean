-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_NUAlg
-- name    : QAdvFew_PoQOracle_NUAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:35.792455+00:00
-- url     : https://prove2.me/theorems/e518a6ee-cbca-4855-a99f-aa0ac79417a5
-- title:
--   Nonuniform PPT oracle algorithm
-- statement:
--   A **nonuniform PPT oracle algorithm** is a family $(C_n)$ of oracle circuits, where $C_n$ reads the input $x\in\{0,1\}^n$ and random coins $r\in\{0,1\}^{\rho(n)}$, with size at most $p(n)$ for a polynomial $p$. Its success probability on $f$ at length $n$ is
--   $$
--   \Pr_{x\leftarrow\{0,1\}^n,\ r}\bigl[C_n^O(x,r)=f(x)\bigr].
--   $$
--
--   The family is quantified after the oracle wherever it is used, so it may depend on it (p. 12). With $\rho=0$ this is a $\mathsf P^O/\mathsf{poly}$ family.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §3.2.1, p. 12 (PDF p. 14); Theorem 4.1(4)(a), p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Circuit

open QAlgorithms.Complexity

namespace QAdvFew.PoQOracle

/-- A **nonuniform PPT oracle algorithm** (Goldin, Lombardi, Morimae, *Quantum Advantage has Few
Complexity Implications*, arXiv:2611.05303v1, §3.2.1, p. 12 (PDF p. 14): "Nonuniform algorithms are
polynomial-size circuit families; their descriptions … may depend on the input length and the
oracle"; Theorem 4.1(4)(a), p. 21 (PDF p. 23)): for each input length `n`, an oracle circuit `C_n`
reading the input `x ∈ {0,1}^n` and random coins `r ∈ {0,1}^{ρ(n)}`, with
`size(C_n) ≤ p(n)` for a polynomial `p`.

**Formalization Note** The family is quantified after the oracle, so it may depend on it. The coin
count `ρ` is unrestricted; a circuit of size `p(n)` reads at most `p(n)` coins. With `ρ = 0` this is
a deterministic `P/poly` oracle circuit family. The gate set includes parity and oracle gates. -/
structure NUAlg where
  /-- the number of random coins at input length `n` -/
  ρ : ℕ → ℕ
  /-- the circuit at input length `n` -/
  C : (n : ℕ) → Circuit (Fin n ⊕ Fin (ρ n))
  /-- the size bound -/
  p : Polynomial ℕ
  size_le : ∀ n : ℕ, (C n).size ≤ p.eval n

namespace NUAlg

/-- The success probability `Pr_{x ← {0,1}^n, r}[A^O(x) = f(x)]`. -/
noncomputable def success (A : NUAlg) (O : Oracle) (f : Str → Bool) (n : ℕ) : ℝ :=
  ((Finset.univ.filter (fun xr : (Fin n → Bool) × (Fin (A.ρ n) → Bool) =>
      (A.C n).eval1 O (Sum.elim xr.1 xr.2) = f (List.ofFn xr.1))).card : ℝ) /
    (2 ^ (n + A.ρ n) : ℝ)

end NUAlg

end QAdvFew.PoQOracle


