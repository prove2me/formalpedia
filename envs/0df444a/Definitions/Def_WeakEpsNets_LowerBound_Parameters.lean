-- Prove2me | Definitions.Def_WeakEpsNets_LowerBound_Parameters
-- name    : WeakEpsNets_LowerBound_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:11.410236+00:00
-- url     : https://prove2.me/theorems/93a91a88-5949-40b0-9fcf-9d1c62eac9b8
-- title:
--   Positive intervals, grid shift, lift dimension, and target exponent
-- statement:
--   The construction uses the positive integer interval $[n]=\{1,\ldots,n\}$, the shift $\tau(q)=1/(9q^5)$, and the dimension $D_s=(s^2+5s)/2$. The headline exponent is
--   $$\gamma_d=\frac12\left\lfloor\frac{\sqrt{8d+25}-1}{2}\right\rfloor.$$
--   The floor is taken before multiplication by $1/2$. In particular $\gamma_3=3/2$, $\gamma_7=2$, and $\gamma_{12}=5/2$.
--
--   These numerical conventions are shared across the milestones and the goal. The construction statements assume $s\ge1$ and even $q\ge2$; on the raw input $q=0$, Lean totalizes the shift to zero, a value unused by those statements. Natural division in $D_s$ is exact because its numerator is even.
-- source:
--   Bhore, Browne, Zheng, Strong Lower Bounds for Weak Epsilon-Nets, STOC 2027 submission #301 (October 2026), Theorem 1, p. 3, line 82; §2.2, p. 7, line 221; §3, p. 9, lines 279–286; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/301.pdf

import Mathlib

noncomputable section

namespace WeakEpsNets.LowerBound

/-- Positive integer interval [n] = {1,...,n}, source p. 7 and p. 9. -/
def positiveInterval (n : ℕ) : Finset ℕ := Finset.Icc 1 n

/-- Shift in the PDF, not the corrupted text extraction; source pp. 7, 9. -/
def tau (q : ℕ) : ℝ := 1 / (9 * (q : ℝ) ^ 5)

/-- Dimension D_s, source p. 9. The numerator is even for every s. -/
def liftDimension (s : ℕ) : ℕ := (s ^ 2 + 5 * s) / 2

/-- The exponent printed in Theorem 1, p. 3. Floor is integer-valued before casting. -/
def gamma (d : ℕ) : ℝ :=
  (1 / 2 : ℝ) * (⌊(Real.sqrt (8 * (d : ℝ) + 25) - 1) / 2⌋ : ℤ)

end WeakEpsNets.LowerBound


