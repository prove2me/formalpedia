-- Prove2me | Definitions.Def_BianchiIX_Statistics_GaussDistortion
-- name    : BianchiIX_Statistics_GaussDistortion
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T16:15:17.453819+00:00
-- url     : https://prove2.me/theorems/d809fb71-6829-45b8-ab21-7328d69bf3ab
-- title:
--   Continuants and logarithmic derivatives of inverse prefixes
-- statement:
--   Let $a=(a_j)_{j\geq0}$ be positive integers and write
--   $g_b(x)=1/(b+x)$ and $G_n=g_{a_0}\circ\cdots\circ g_{a_{n-1}}$, with $G_0$ the identity.
--   Define $q_{-1}=0$, $q_0=1$, and $q_{n+1}=a_nq_n+q_{n-1}$. Set
--   $$Q_n(x)=q_n+q_{n-1}x,\qquad L_n(x)=-2\log Q_n(x).$$
--
--   The continuant pair is $(q_n,q_{n-1})$. For arbitrary real maps $h_j$, define
--   $H_0(x)=x$ and $H_{n+1}(x)=H_n(h_n(x))$. These quantities describe both the
--   Gauss inverse compositions and the actual branch compositions compared with them.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Statistics/GaussDistortion.lean

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.List.Induction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Data.PNat.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Data.Rat.Floor
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Order.OrderIsoNat
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Finite-prefix distortion along the actual branch inputs, Section 3.3. -/

namespace BianchiIX

noncomputable section

open Set Finset

/-- The pair `(q_n, q_{n-1})`, with initial pair `(1, 0)`. -/
def gaussDenoms (a : ℕ → ℕ+) : ℕ → ℝ × ℝ
  | 0 => (1, 0)
  | n + 1 => ((a n : ℝ) * (gaussDenoms a n).1 + (gaussDenoms a n).2,
      (gaussDenoms a n).1)



def gaussDenom (a : ℕ → ℕ+) (n : ℕ) (x : ℝ) : ℝ :=
  (gaussDenoms a n).1 + (gaussDenoms a n).2 * x













def gaussPrefixLog (a : ℕ → ℕ+) (n : ℕ) (x : ℝ) : ℝ :=
  -2 * Real.log (gaussDenom a n x)













def branchPrefix (h : ℕ → ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x => branchPrefix h n (h n x)







end

end BianchiIX


