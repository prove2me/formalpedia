-- Prove2me | Definitions.Def_QuadraticRE_jLam
-- name    : QuadraticRE_jLam
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:11:56.0615+00:00
-- url     : https://prove2.me/theorems/2a211d64-008b-4368-8cef-f71b7194e6fe
-- title:
--   The parameters $j_\lambda$, $L_\lambda$, $h_\lambda$ and the errors $\delta_\lambda$, $\varepsilon_\lambda$
-- statement:
--   For an integer $\lambda\ge1$,
--   $$j_\lambda=4+\Bigl\lceil\log_2\frac{\lambda+2}{\log_25}\Bigr\rceil,\qquad L_\lambda=4^{j_\lambda},\qquad h_\lambda=\lambda+\lceil\log_2(7L_\lambda)\rceil+1,$$
--   and $E_\lambda=E_{j_\lambda,h_\lambda}$. The errors $\delta_\lambda$ and $\varepsilon_\lambda$ are the actual errors of $E_\lambda$: the largest, over the 16 inputs $(a,b,c,d)$, of $\Pr_R[\mathrm{Dec}_\lambda(E_\lambda(a,b,c,d;R))\neq abc+d]$, respectively of $\mathrm{SD}(E_\lambda(a,b,c,d;R),\mathrm{Sim}_\lambda(abc+d))$.
--
--   These parameters instantiate the encoding of $abc+d$ used in Lemma 4.11 and Theorem 4.12.
--
--   **Formalization Note** For $\lambda\ge1$ the argument of the outer logarithm exceeds $1$, so the ceilings are of positive numbers. $\delta_\lambda$, $\varepsilon_\lambda$ are the errors themselves, not the bounds $2^{-\lambda-2}$, $\tfrac32 2^{-\lambda-2}$.
-- source:
--   Orsini, Patra, From Degree Three to Degree Two: Statistical Randomized Encodings for All Functions, STOC 2027 submission manuscript (sha256 0c94deae…), "Choosing the parameters", §4.2.3, p.28

import Mathlib
import Definitions.Def_QuadraticRE_encE

namespace QuadraticRE

/-- `j_λ = 4 + ⌈log₂((λ + 2)/log₂ 5)⌉`, "Choosing the parameters", Orsini, Patra, *From Degree Three to Degree Two*, STOC 2027 submission manuscript (sha256 0c94deae…), p.28.

**Formalization Note.** For `λ ≥ 1` the argument of the outer logarithm exceeds `1`, so the ceiling is
of a positive number and `Nat.ceil` truncates nothing. -/
noncomputable def jLam (lam : ℕ) : ℕ :=
  4 + ⌈Real.logb 2 (((lam : ℝ) + 2) / Real.logb 2 5)⌉₊

/-- `L_λ = 4^{j_λ}`, p.28. -/
noncomputable def LLam (lam : ℕ) : ℕ := 4 ^ jLam lam

/-- `h_λ = λ + ⌈log₂(7 L_λ)⌉ + 1`, p.28. -/
noncomputable def hLam (lam : ℕ) : ℕ :=
  lam + ⌈Real.logb 2 (7 * (LLam lam : ℝ))⌉₊ + 1

/-- The correctness error of `E_{j,h}`: the largest of `Pr_R[Dec(E(a, b, c, d; R)) ≠ abc + d]` over the
16 inputs. -/
noncomputable def deltaE (j h : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin 4 → F2)).sup' Finset.univ_nonempty (fun x =>
    prob (fun R : Tape j h =>
      decE j h (encE j h (x 0) (x 1) (x 2) (x 3) R) ≠ x 0 * x 1 * x 2 + x 3))

/-- The privacy error of `E_{j,h}` with its simulator: the largest of
`SD(E(a, b, c, d; R), Sim(abc + d))` over the 16 inputs. -/
noncomputable def epsE (j h : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin 4 → F2)).sup' Finset.univ_nonempty (fun x =>
    SD (law (encE j h (x 0) (x 1) (x 2) (x 3))) (law (simE j h (x 0 * x 1 * x 2 + x 3))))

/-- `δ_λ`, p.28: the actual correctness error of `E_λ = E_{j_λ,h_λ}`, not the bound `2^{−λ−2}`. -/
noncomputable def deltaLam (lam : ℕ) : ℝ := deltaE (jLam lam) (hLam lam)

/-- `ε_λ`, p.28: the actual privacy error of `E_λ`, not the bound `(3/2) 2^{−λ−2}`. -/
noncomputable def epsLam (lam : ℕ) : ℝ := epsE (jLam lam) (hLam lam)

end QuadraticRE


