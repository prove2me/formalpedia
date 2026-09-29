-- Prove2me | Definitions.Def_GeneralCK_E8_semantic_core
-- name    : GeneralCK_E8_semantic_core
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-24T21:25:17.053483+00:00
-- url     : https://prove2.me/theorems/7f4f496a-66ef-483c-9ce3-68d55a5fe1cd
-- title:
--   E8 scalar slope and dyadic interval core
-- statement:
--   A dyadic interval at precision $p$ has integer endpoints $L,U$ and represents $[L/2^p,U/2^p]$. Its Contains predicate states membership without division. For a real parameter $a$, define $z=e^{-2a}$, $r=(1-z)/(1+z)$, $q=4z/(1+z)^2$, $\ell=a+\log(1+z)$, and $h=\log(1+z)+2az/(1+z)$. The stable E8 slope is $Y(a)=\frac{2}{\log2}(a+rh/(q\ell))$. The Inputs record stores intervals for $a$, $e^{-2a}$, $\log(1+e^{-2a})$, and $\log2$. These exact definitions are the semantic interface for the E8 positive-axis certificates; this bundle contains no particular cell's numerical witnesses.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/tree/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace GeneralCK.Certificates

/-- Integer endpoints at the fixed dyadic scale `2^p`. -/
structure DyadicInterval (p : ℕ) where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq, Repr

namespace DyadicInterval

def scale (p : ℕ) : ℤ := 2^p




def Contains {p : ℕ} (a : DyadicInterval p) (x : ℝ) : Prop :=
  (a.lo : ℝ) ≤ (scale p : ℝ)*x ∧ (scale p : ℝ)*x ≤ (a.hi : ℝ)



















































end DyadicInterval
end GeneralCK.Certificates

namespace GeneralCK.Certificates.E8TAxisStableScalar




noncomputable def z (a : ℝ) : ℝ := Real.exp (-2 * a)
noncomputable def r (a : ℝ) : ℝ := (1 - z a) / (1 + z a)
noncomputable def q (a : ℝ) : ℝ := 4 * z a / (1 + z a) ^ 2
noncomputable def l1 (a : ℝ) : ℝ := Real.log (1 + z a)
noncomputable def ell (a : ℝ) : ℝ := a + l1 a
noncomputable def h (a : ℝ) : ℝ := l1 a + 2 * a * z a / (1 + z a)

noncomputable def Y (a : ℝ) : ℝ :=
  (2 / Real.log 2) * (a + r a * h a / (q a * ell a))

















































end GeneralCK.Certificates.E8TAxisStableScalar

namespace GeneralCK.Certificates.E8TAxisStableInterval











structure Inputs (p : ℕ) where
  alpha : DyadicInterval p
  expNegTwo : DyadicInterval p
  logOnePlusExp : DyadicInterval p
  logTwo : DyadicInterval p





































end GeneralCK.Certificates.E8TAxisStableInterval


