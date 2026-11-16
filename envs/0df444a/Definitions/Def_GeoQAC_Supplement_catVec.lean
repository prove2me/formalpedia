-- Prove2me | Definitions.Def_GeoQAC_Supplement_catVec
-- name    : GeoQAC_Supplement_catVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:16:44.517078+00:00
-- url     : https://prove2.me/theorems/e92fdb78-e1cc-411d-9231-5073cae11dfb
-- title:
--   Cat states $|\mathrm{cat}_n\rangle$ and Dicke states $|D_{n,k}\rangle$
-- statement:
--   The **cat state** on $n$ qubits and, for $0\le k\le n$, the **Dicke state** of weight $k$ are
--   $$
--   |\mathrm{cat}_n\rangle=\frac{|0^n\rangle+|1^n\rangle}{\sqrt2},\qquad |D_{n,k}\rangle=\binom nk^{-1/2}\sum_{|x|=k}|x\rangle .
--   $$
--
--   They are the targets of the state-synthesis lower bounds (Theorem 3.8) and of the cat-state constructions (Theorem 4.7).
--
--   **Formalization Note** Vectors are functions on $\mathrm{Fin}\,n\to\mathrm{Bool}$. For $n=0$ the strings $0^n$ and $1^n$ coincide and the vector has the single entry $1/\sqrt2$; the paper uses cat states for $n\ge1$. The Dicke vector is zero for $k>n$; every statement assumes $k\le n$.
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), §2.4, p.12 (cat state); §3.2, p.15 (Dicke state)

import Mathlib
import Definitions.Def_GeoQAC_Supplement_hammingWeight

namespace GeoQAC.Supplement

/-!
# Cat states and Dicke states

Dong, Ou, Yao, arXiv:2604.07178 (version of 2026-11-03), §2.4, p.12: `|cat_n⟩ = (|0^n⟩ + |1^n⟩)/√2`;
§3.2, p.15: "For integers `0 ≤ k ≤ n`, the Dicke state is the uniform superposition of all strings
with Hamming weight `k`: `|D_{n,k}⟩ = C(n,k)^{−1/2} Σ_{|x|=k} |x⟩`."

**Formalization Note.** Vectors are functions on `Fin n → Bool`. For `n = 0` the two strings `0^n`
and `1^n` coincide and `catVec 0` has the single entry `1/√2` (the paper uses cat states for
`n ≥ 1`). `dickeVec n k` is the zero vector for `k > n`; the paper and every statement here assume
`k ≤ n`.
-/

/-- The cat state `|cat_n⟩ = (|0^n⟩ + |1^n⟩)/√2` (p.12). -/
noncomputable def catVec (n : ℕ) : (Fin n → Bool) → ℂ :=
  fun t => if (∀ i, t i = false) ∨ (∀ i, t i = true) then ((Real.sqrt 2)⁻¹ : ℂ) else 0

/-- The Dicke state `|D_{n,k}⟩ = C(n,k)^{−1/2} Σ_{|x| = k} |x⟩` (p.15). -/
noncomputable def dickeVec (n k : ℕ) : (Fin n → Bool) → ℂ :=
  fun t => if hammingWeight t = k then ((Real.sqrt (n.choose k))⁻¹ : ℂ) else 0

end GeoQAC.Supplement


