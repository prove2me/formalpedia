-- Prove2me | Definitions.Def_CNFLearnMQ_Supplement_CNFGuarantee
-- name    : CNFLearnMQ_Supplement_CNFGuarantee
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:04:25.780797+00:00
-- url     : https://prove2.me/theorems/8cf6da7b-6622-40cb-816d-29fada48d9a4
-- title:
--   The sample-only CNF-learning guarantee of Theorem 7.1 and the parameters $s,k,d$
-- statement:
--   For a Boolean function $H:\{0,1\}^n\to\{0,1\}$ let $\Omega(H)=\{x:H(x)=1\}$ and, when $\Omega(H)\ne\emptyset$, $\mu_H=\mathrm{Unif}(\Omega(H))$. A machine $M$ achieves the **sample-only CNF guarantee** for parameters $k,d$, accuracies $E$ and time $T(n,\varepsilon)$ if for all integers $n\ge k$, all $\varepsilon\in E$ and every satisfiable $n$-variable $(k,d)$-CNF formula $\Phi$ (every clause of width exactly $k$, every variable in at most $d$ clauses), given $n,k,d,\varepsilon$ and only i.i.d. samples from $\mu_\Phi$, it runs within time $T(n,\varepsilon)$ (evaluation of its output included) and with probability at least $2/3$ outputs $H$ with
--   $$\Omega(H)\neq\emptyset\quad\text{and}\quad d_{\mathrm{TV}}(\mu_\Phi,\mu_H)\le\varepsilon .$$
--
--   The module also fixes the parameters of Theorem 7.1: for a real $t>0$ and an integer $r\ge1$, $s=\lceil 2r/t\rceil$, $k=r+s$ and $d=2^r$.
--
--   **Formalization Note** The accuracy is a rational number, handed to the machine as numerator and denominator in binary. The learner never receives $\Phi$.
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Theorem 7.1 and the notation $\Omega(H)$, $\mu_H$, p.40

import Mathlib
import Definitions.Def_CNFLearnMQ_Supplement_JuntaGuarantee
import Definitions.Def_CNFLearnMQ_memOracle

set_option autoImplicit false

namespace CNFLearnMQ.Supplement

open CNFLearning873.Valiant CNFLearnMQ SampleMachine

variable {n : ℕ}

/-- `Ω(H) = {x ∈ {0,1}^n : H(x) = 1}` for a Boolean function `H` (Feng, Yu, Zhang, STOC 2027
submission (manuscript sha256 519ee6d4…), §7, p.40). -/
def omegaOf (H : Assignment n → Bool) : Finset (Assignment n) :=
  Finset.univ.filter fun x => H x = true

/-- The parameters of Theorem 7.1 (p.40): `s = ⌈2r/t⌉`. -/
noncomputable def sParam (t : ℝ) (r : ℕ) : ℕ := ⌈2 * (r : ℝ) / t⌉₊

/-- `k = r + s` (p.40). -/
noncomputable def kParam (t : ℝ) (r : ℕ) : ℕ := r + sParam t r

/-- `d = 2^r` (p.40). -/
def dParam (r : ℕ) : ℕ := 2 ^ r

/-- The parameters handed to a CNF learner: `n, k, d` and the accuracy `ε = p/q` as the numerator
and denominator of the rational `ε`, all in binary. -/
def cnfParams (n k d : ℕ) (ε : ℚ) : List ℕ := [n, k, d, ε.num.natAbs, ε.den]

/-- The guarantee of Theorem 7.1 (p.40) for a machine `M`, parameters `k, d`, a set `E` of
accuracies and a time bound `T(n, ε)`: for all integers `n ≥ k`, all `ε ∈ E` and every satisfiable
`n`-variable `(k, d)`-CNF formula `Φ`, given `n, k, d, ε` and only i.i.d. samples from `µ_Φ`, `M`
runs within time `⌊T(n, ε)⌋` including the evaluation of its output on any input, and with
probability at least `2/3` it outputs a Boolean function `H : {0,1}^n → {0,1}` with `Ω(H) ≠ ∅` and
`d_TV(µ_Φ, µ_H) ≤ ε`, where `µ_H = Unif(Ω(H))`.

**Formalization Note** `(k, d)`-CNF is the published `KD Φ k d` (every clause of width exactly `k`,
every variable in at most `d` clauses). A sample `X ∈ {0,1}^n` is delivered as the bit string
`X_1 … X_n`. The learner never receives `Φ`. Accuracies are rationals (a finite input). -/
def CNFGuarantee (M : SampleMachine) (k d : ℕ) (E : Set ℚ) (T : ℕ → ℝ → ℝ) : Prop :=
  ∀ n : ℕ, k ≤ n → ∀ ε ∈ E, ∀ Φ : CNF n, KD Φ k d → ∀ h : (solutions Φ).Nonempty,
    M.RunsWithin ((solutionPMF Φ h).map List.ofFn) (cnfParams n k d ε) n ⌊T n ε⌋₊ ∧
    (2 / 3 : ENNReal) ≤
      prob (M.runFor ((solutionPMF Φ h).map List.ofFn) ⌊T n ε⌋₊ (M.initCfg (cnfParams n k d ε)))
        (fun o => ∃ c, o = some c ∧
          ∃ hH : (omegaOf (M.hypothesis ⌊T n ε⌋₊ c (n := n))).Nonempty,
            HybridXorLift.tvDist (solutionLaw Φ h).prob
              (RandomQueryXOR.uniformOn (omegaOf (M.hypothesis ⌊T n ε⌋₊ c (n := n))) hH).prob ≤
              (ε : ℝ))

end CNFLearnMQ.Supplement


