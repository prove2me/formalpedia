-- Prove2me | Definitions.Def_CatalyticTreeEval_Corollary311Parameters
-- name    : CatalyticTreeEval_Corollary311Parameters
-- status  : Definition
-- author  : @Mr Robbins
-- created : 2026-11-22T23:18:03.899115+00:00
-- url     : https://prove2.me/theorems/e018c974-a478-45ec-aad0-4a064869ef7f
-- title:
--   Appendix C's explicit matching-vector parameters and construction interface
-- statement:
--   This module records Appendix C's exact parameter dictionary. For a prime list $p$ of length $t$, modulus $m=\prod_i p_i$, and size exponent $\ell$, put
--
--   $$
--   \eta=\frac{\ell^{t-1}}m,\qquad
--   \theta=\max\!\left(10,\left\lceil\frac{\log\eta}{t^2}\right\rceil\right),\qquad
--   w=\left\lceil\frac{\ell}{\theta}\right\rceil,\qquad H=w2^\theta.
--   $$
--
--   It also abbreviates $r=(mw)^{1/t}$, the explicit dimension cap $D=\sum_{j=0}^{\lfloor r\rfloor}\binom Hj$, and the Theorem 3.10 workspace expression $1+\log_2\binom Hw+r\log_2(H+1)+\log_2m$.
--
--   Finally, `LargeFamilyConstruction` is the precise universal output contract of Theorem 3.10 for a fixed finite printer and positive constant: for every prime list and $1\le w\le H$ it returns a $\binom Hw$-member canonical matching family, the displayed dimension cap, and the charged uniform vector-access certificate. Keeping this interface explicit lets the corollary use Theorem 3.10 without duplicating its construction.
-- source:
--   Alexandra Henzinger, Edward Pyne, Seyoon Ragavan, Catalytic Tree Evaluation from Matching Vectors, STOC 2027 submission #533 (October 2026), Appendix C, proof of Corollary 3.11, printed p.39 (PDF p.41), and Theorem 3.10, printed p.16 (PDF p.18).

import Definitions.Def_CatalyticTreeEval_Main_Polynomials
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The exact output contract of Theorem 3.10 for one printer and constant. -/
def LargeFamilyConstruction (M : Machine) (C : ℝ) : Prop :=
  ∀ (t : ℕ) (p : Fin t → ℕ) (w H : ℕ),
    PrimeData p → 1 ≤ w → w ≤ H →
    ∃ (d : ℕ) (U V : Fin (H.choose w) → Vec (modulus p) d),
      d ≤ binomialDimension H (⌊((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ))⌋₊ + 1) ∧
      SMatching (canonical p (modulus p)) U V ∧
      VectorAccess M (primeCode p ++ natsCode [w,H]) U V
        (C * (1 + log₂ (H.choose w) +
          ((modulus p * w : ℕ) : ℝ) ^ (1 / (t : ℝ)) * log₂ (H + 1) +
          log₂ (modulus p)))

/-- Appendix C's ratio eta = l^(t-1)/m. -/
noncomputable def regimeEta {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℝ :=
  (l : ℝ) ^ (t - 1) / (modulus p : ℝ)

/-- Appendix C's theta = max(10, ceil(log eta / t^2)). -/
noncomputable def regimeTheta {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℕ :=
  max 10 ⌈Real.log (regimeEta p l) / (t : ℝ) ^ 2⌉₊

/-- Appendix C's subset size w = ceil(l/theta). -/
noncomputable def regimeWidth {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℕ :=
  ⌈(l : ℝ) / (regimeTheta p l : ℝ)⌉₊

/-- Appendix C's ambient coordinate count H = w * 2^theta. -/
noncomputable def regimeHeight {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℕ :=
  regimeWidth p l * 2 ^ regimeTheta p l

/-- The real root (mw)^(1/t) at Appendix C's parameters. -/
noncomputable def regimeRoot {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℝ :=
  ((modulus p * regimeWidth p l : ℕ) : ℝ) ^ (1 / (t : ℝ))

/-- Theorem 3.10's dimension bound at Appendix C's parameters. -/
noncomputable def regimeDimension {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℕ :=
  binomialDimension (regimeHeight p l) (⌊regimeRoot p l⌋₊ + 1)

/-- Theorem 3.10's workspace expression at Appendix C's parameters. -/
noncomputable def regimeSpace {t : ℕ} (p : Fin t → ℕ) (l : ℕ) : ℝ :=
  1 + log₂ ((regimeHeight p l).choose (regimeWidth p l)) +
    regimeRoot p l * log₂ (regimeHeight p l + 1) + log₂ (modulus p)

end CatalyticTreeEval.Main


