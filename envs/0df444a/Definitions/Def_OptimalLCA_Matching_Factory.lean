-- Prove2me | Definitions.Def_OptimalLCA_Matching_Factory
-- name    : OptimalLCA_Matching_Factory
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:47:03.846486+00:00
-- url     : https://prove2.me/theorems/db8e2508-635f-4823-a0e3-6a1446d382fc
-- title:
--   §6.1 — elementary formulas and the Bernoulli-factory model of Lemma 6.1
-- statement:
--   An **elementary formula** $\Phi(p_1,\dots,p_k)$ is a finite syntax tree over the input coordinates $p_i$ and real constants with $+,-,\times,\div,\exp,\sqrt{\cdot}$ and the fourth root $(\cdot)^{1/4}$; $\Phi(p)$ is its value. Condition (a) of Lemma 6.1, `Valid β p Φ`: every denominator and every root argument of the tree, evaluated at $p$, is at least $\beta$.
--
--   A **factory** is a program of the machine of §2.1 that may execute `flip k`, which returns the next flip of input coin $k$. Coin $k$'s $m$-th flip is $\mathbf 1[c_{k,m}<p_k]$ for i.i.d. uniform $c_{k,m}$, so successive flips are independent $\mathrm{Bern}(p_k)$ bits; the program also has the uniform tape $\omega$ as auxiliary randomness and never sees $p$ except through flips. `factoryMeasure` is the joint law of $(\omega,c)$. The number of input flips and the **additional work** (executed instructions other than flips) are $\mathbb N\cup\{\infty\}$-valued.
-- source:
--   Cohen, Roghani, Optimal LCA and Sublinear Estimation for Bipartite Matching in Δ^O(1/ε) Queries, arXiv:2611.06024 (version not printed; PDF sha256 5a43ec12…3eb3), p. 30, §6.1, Lemma 6.1

import Mathlib
import Definitions.Def_OptimalLCA_Matching_Machine

/-!
# Elementary formulas and Bernoulli factories (Cohen–Roghani, §6.1, Lemma 6.1)

* `Formula k`: a finite syntax tree over the input coordinates `p₁, …, p_k` (`var i`,
  `i : Fin k`) and real constants, with `+, −, ×, ÷, exp, √` and the fourth root.
* `Formula.eval Φ p = Φ(p)` (`√` is `Real.sqrt`, the fourth root is `x ^ (1/4 : ℝ)`).
* `Formula.Valid β p Φ`: every denominator and every root argument of `Φ`, evaluated at
  `p`, is at least `β` (condition (a) of Lemma 6.1).
* The factory model: a program of the machine of `Def_OptimalLCA_Matching_Machine` whose
  `flip k` instruction returns the next flip of input coin `k`. Coin `k`'s `m`-th flip is
  `1[c(k, m) < p_k]` for an i.i.d. uniform family `c`, so the flips are independent
  `Bern(p_k)` bits; auxiliary randomness is the tape `ω`. The program sees the biases only
  through flips. `factoryEnv p ω c` is that environment (no graph oracle) and
  `factoryMeasure` the joint law of `(ω, c)`.
-/

namespace OptimalLCA.Matching

open MeasureTheory

/-- Elementary formulas in `k` input coordinates. -/
inductive Formula (k : ℕ) : Type
  | var (i : Fin k)
  | const (c : ℝ)
  | add (a b : Formula k)
  | sub (a b : Formula k)
  | mul (a b : Formula k)
  | div (a b : Formula k)
  | exp (a : Formula k)
  | sqrt (a : Formula k)
  | root4 (a : Formula k)

namespace Formula

variable {k : ℕ}

/-- The value `Φ(p)`. -/
noncomputable def eval (p : Fin k → ℝ) : Formula k → ℝ
  | var i => p i
  | const c => c
  | add a b => eval p a + eval p b
  | sub a b => eval p a - eval p b
  | mul a b => eval p a * eval p b
  | div a b => eval p a / eval p b
  | exp a => Real.exp (eval p a)
  | sqrt a => Real.sqrt (eval p a)
  | root4 a => eval p a ^ (1 / 4 : ℝ)

/-- Condition (a): every denominator and every root argument is at least `β` at `p`. -/
def Valid (β : ℝ) (p : Fin k → ℝ) : Formula k → Prop
  | var _ => True
  | const _ => True
  | add a b => Valid β p a ∧ Valid β p b
  | sub a b => Valid β p a ∧ Valid β p b
  | mul a b => Valid β p a ∧ Valid β p b
  | div a b => Valid β p a ∧ Valid β p b ∧ β ≤ eval p b
  | exp a => Valid β p a
  | sqrt a => Valid β p a ∧ β ≤ eval p a
  | root4 a => Valid β p a ∧ β ≤ eval p a

end Formula

/-- The factory environment: input coin `j < k` flips `1[c(j, m) < p_j]` at its `m`-th
flip, the tape is `ω`; there is no graph, mark or list oracle. -/
noncomputable def factoryEnv {k : ℕ} (p : Fin k → ℝ) (ω : ℤ → unitInterval)
    (c : ℕ × ℕ → unitInterval) : Env where
  deg _ := 0
  nbr _ _ := -1
  tape := tapeReal ω
  coin j m := if h : j < k then decide ((c (j, m) : ℝ) < p ⟨j, h⟩) else false
  mark _ _ _ := false
  list _ _ := []

/-- The law of the input-coin uniforms `c`: i.i.d. uniform `[0, 1]`. -/
noncomputable def coinMeasure : Measure (ℕ × ℕ → unitInterval) :=
  Measure.infinitePi (fun _ : ℕ × ℕ => (volume : Measure unitInterval))

/-- The joint law of the auxiliary tape and the input-coin uniforms. -/
noncomputable def factoryMeasure : Measure ((ℤ → unitInterval) × (ℕ × ℕ → unitInterval)) :=
  tapeMeasure.prod coinMeasure

end OptimalLCA.Matching


