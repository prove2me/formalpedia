-- Prove2me | Definitions.Def_ValTrackRM_Public_Supplement_Stochastic
-- name    : ValTrackRM_Public_Supplement_Stochastic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T03:57:41.654872+00:00
-- url     : https://prove2.me/theorems/32ab9e2c-48d7-4106-b748-b1f90c770910
-- title:
--   Section 4 and Exp — independent valuation laws and inventory-conditioned pricing
-- statement:
--   For every customer $t\ge1$, let $\nu_t$ be an arbitrary probability distribution on the valuation indices $0,\ldots,m$. Mathlib's probability mass functions supply the generic probability object. Independence is represented by the explicit finite product
--   $$
--    w(u_1,\ldots,u_n)=\prod_{t=1}^{n}\nu_t(u_t).
--   $$
--   Average the published Algorithm 1 sold-vector law over these hidden valuation prefixes. Exp chooses its next price from the resulting joint price/inventory mass divided by its inventory mass. Its inventory law and expected revenue are then computed by forward recursion, drawing the current valuation independently after choosing the price. The expected offline optimum averages the published optimum against the same product valuation law.
--
--   This defines the stochastic policies without giving them access to the hidden past valuations or to the current distribution before posting a price. Zero-mass conditioning states and zero inventory reject. Competitive inequalities use multiplication by the expected optimum, including zero demand, rather than an undefined zero-denominator ratio.
-- source:
--   Ma, Simchi-Levi & Teo, On Policies for Single-Leg Revenue Management with Limited Demand Information, arXiv:1810.10900v2, pp. 17–19, Definition 6, Equation (3), Exp and Equations (4)–(5)

import Mathlib
import Definitions.Def_ValTrackRM_Public_Supplement_Inventory

namespace ValTrackRM.Public.Supplement

/-! §4: independent, possibly different, finite valuation laws. Mathlib's PMF
is the general probability object; no independence or normalization axioms are added.
The product is taken explicitly. Price kernels only read ν at indices < t. -/
noncomputable def valuationWeight {m : ℕ} (ν : ℕ → PMF (Fin (m + 1)))
    {n : ℕ} (W : Fin n → Fin (m + 1)) : ℝ :=
  ∏ i : Fin n, (ν (i.val + 1) (W i)).toReal

noncomputable def jointA1Stock {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (n a : ℕ) : ℝ :=
  ∑ W : Fin n → Fin (m + 1), valuationWeight ν W * a1Stock r sel (List.ofFn W) a

noncomputable def jointA1Price {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (n a : ℕ) (p : Price m) : ℝ :=
  ∑ W : Fin n → Fin (m + 1), valuationWeight ν W * a1Joint r sel (List.ofFn W) a p

/-- Exp, p.18: average over hidden past valuations AND Algorithm 1 randomization.
Reject at an unreachable state, as stipulated on p.18, and at zero stock. -/
noncomputable def expKernel {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1)))
    (t a : ℕ) (p : Price m) : ℝ :=
  if a = 0 ∨ jointA1Stock r sel ν (t - 1) a = 0 then reject p
  else jointA1Price r sel ν (t - 1) a p / jointA1Stock r sel ν (t - 1) a

noncomputable def stochasticStock {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (K : ℕ → ℕ → Price m → ℝ) (ν : ℕ → PMF (Fin (m + 1))) : ℕ → ℕ → ℝ
  | 0, b => if b = k then 1 else 0
  | n + 1, b => ∑ a : Fin (k + 1), ∑ p : Price m, ∑ v : Fin (m + 1),
      stochasticStock r k K ν n a.val * K (n + 1) a.val p * (ν (n + 1) v).toReal *
        if nextStock r a.val p v = b then 1 else 0

noncomputable def stochasticConditional {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (K : ℕ → ℕ → Price m → ℝ) (ν : ℕ → PMF (Fin (m + 1)))
    (t a : ℕ) (p : Price m) : ℝ :=
  stochasticStock r k K ν (t - 1) a * K t a p / stochasticStock r k K ν (t - 1) a

noncomputable def stochasticRevenue {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (K : ℕ → ℕ → Price m → ℝ) (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 T, ∑ a : Fin (k + 1), ∑ p : Price m, ∑ v : Fin (m + 1),
    stochasticStock r k K ν (t - 1) a.val * K t a.val p * (ν t v).toReal * payment r a.val p v

noncomputable def jointA1Revenue {m k : ℕ} (r : ℕ → ℝ)
    (sel : (Fin k → Fin (m + 1)) → Fin k) (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) : ℝ :=
  ∑ W : Fin T → Fin (m + 1), valuationWeight ν W * expRevenue r sel (List.ofFn W)

noncomputable def expectedOpt {m : ℕ} (r : ℕ → ℝ) (k : ℕ)
    (ν : ℕ → PMF (Fin (m + 1))) (T : ℕ) : ℝ :=
  ∑ W : Fin T → Fin (m + 1), valuationWeight ν W * opt r k (List.ofFn W)

end ValTrackRM.Public.Supplement


