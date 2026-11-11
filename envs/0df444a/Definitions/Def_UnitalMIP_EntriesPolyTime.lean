-- Prove2me | Definitions.Def_UnitalMIP_EntriesPolyTime
-- name    : UnitalMIP_EntriesPolyTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:38:23.096111+00:00
-- url     : https://prove2.me/theorems/83fe3bd5-a0f4-43e8-ae21-834474341260
-- title:
--   Entries computable in polynomial time (the standing assumption of §1.1)
-- statement:
--   A matrix $\psi$ has **entries computable in polynomial time** if, given $b\in\mathbb N$, a rational approximation to each entry with error at most $2^{-b}$ can be computed in time $\mathrm{poly}(b)$. Precisely: there are a closed program $E$ and a polynomial $P$ such that, for every $b$ and every index pair $(i,j)$, $E$ on input $(b,(i,j))$ halts within $P(b)$ steps and outputs rationals $p,q$ with
--
--   $$
--   |\mathrm{Re}\,\psi_{ij}-p|\le 2^{-b},\qquad |\mathrm{Im}\,\psi_{ij}-q|\le 2^{-b}.
--   $$
--
--   This is the paper's standing assumption on the resource state; it is used to bound the running time of the NEXP certificate verifier and to enumerate strategy values in the RE upper bound.
--
--   **Formalization Note** Programs and running time are those of the published MIPRE cost model; indices are encoded through a fixed enumeration of the finite index type and natural numbers in binary; a rational is coded by a sign, a numerator and a denominator. The time bound is polynomial in the value $b$, as printed.
-- source:
--   Dong, Jiang, Qin, Yao, Zhou, A Dichotomy for MIP* in the Presence of Unital Noise, arXiv:2609.39318 (version of 2026-11-03, sha256 56ebc59e…), §1.1, p.4 (standing assumption)

import Mathlib
import Definitions.Def_MIPRE_Foundations_ClassMIPStar

namespace UnitalMIP

open MIPRE MIPRE.Cost

/-- The rational number coded by `((s, n), d)`: `(−1)^s · n / d` (with `n / 0 = 0`). Every
rational number has such a code. -/
noncomputable def ratOfCode (c : (Bool × ℕ) × ℕ) : ℝ :=
  (if c.1.1 then -1 else 1) * (c.1.2 : ℝ) / (c.2 : ℝ)

/-- **Entries computable in polynomial time** (arXiv:2609.39318, version of 2026-11-03, sha256
56ebc59e…, §1.1, p.4, the standing assumption: "assume that its entries are computable in
polynomial time: given b ∈ ℕ, a rational approximation to each entry with error at most 2^{−b}
can be computed in time poly(b)"). There are a closed program `E` of the MIPRE cost model and a
polynomial `P` such that for every precision `b` and every index pair `(i, j)`, `E` on input
`(b, (i, j))` halts within `P(b)` steps with codes of two rationals within `2^{−b}` of the real
and the imaginary part of `ψ_{ij}`.

**Formalization Note** Indices are encoded as natural numbers through the enumeration
`Fintype.equivFin` of the (finite) index type; natural numbers are in binary (the MIPRE
encoding). The time bound is polynomial in the **value** `b`, as printed. A rational is coded as
a sign, a numerator and a denominator (`ratOfCode`). -/
def EntriesPolyTime {ι : Type} [Fintype ι] (ψ : Matrix ι ι ℂ) : Prop :=
  ∃ (E : Prog) (P : Polynomial ℕ), E.WellScoped 1 ∧
    ∀ (b : ℕ) (i j : ι), ∃ (c₁ c₂ : (Bool × ℕ) × ℕ) (t : ℕ), t ≤ P.eval b ∧
      E.Runs (encode (b, ((Fintype.equivFin ι i : ℕ), (Fintype.equivFin ι j : ℕ))))
        (encode (c₁, c₂)) t ∧
      |(ψ i j).re - ratOfCode c₁| ≤ (2 : ℝ) ^ (-(b : ℤ)) ∧
      |(ψ i j).im - ratOfCode c₂| ≤ (2 : ℝ) ^ (-(b : ℤ))

end UnitalMIP


