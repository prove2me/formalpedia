-- Prove2me | Definitions.Def_MasulloRepair_LogWindows
-- name    : MasulloRepair_LogWindows
-- status  : Definition
-- author  : @ibecca
-- created : 2026-11-21T14:57:47.888915+00:00
-- url     : https://prove2.me/theorems/7c44d2bb-7179-451d-b10c-ca87cd581034
-- title:
--   Logarithmic coordinates for the compact-window repair
-- statement:
--   For real $a,s$, integer $n\ge0$, and $x\in\mathbf R$, define
--   $$W_{a,s,n}(x)=\max\{e^{2ax},e^{2(a+n)x}\}(1+x^2)^{s/2},
--   \qquad d\lambda_{a,s,n}(x)=W_{a,s,n}(x)\,dx.$$
--   For a logarithmic profile $g:\mathbf R\to\mathbf C$, also define
--   $$L(g)(t)=
--   \begin{cases}g(\log t),&t>0,\\0,&t\le0.\end{cases}$$
--   These are the explicit candidate coordinates for the existing compact-window measures. The measure-preserving change of variables, smoothness and support properties, and density statements are separate proof obligations; none is built into the definitions.
-- source:
--   Auxiliary theorem for the compact-window repair of A. M. Masullo, The Music of the Primes, Definition 9.2.2.1 and Lemma 9.2.2.2(3), printed pp. 412-413, and Proposition 9.2.2.4, p. 414. Frozen source: https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . This develops Yi's proposed compact-window replacement (mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2), after the accepted completeness theorem fea3483f-d6b8-43ba-95b4-3acb3895e88f. It is an explicitly stated repair, not a claim that the original uniform supremum is finite. The formulas use the substitution t=exp(x), dt/t=dx; the exact measure identification is proved separately.

import Definitions.Def_MasulloRepair_WindowL2

set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

namespace MasulloRepair

/-- The source compact-window density in the coordinate x = log t. -/
noncomputable def logWindowWeight (a s : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  max (Real.exp (2*a*x)) (Real.exp (2*(a+(n : ℝ))*x)) * (1+x^2)^(s/2)

noncomputable def logWindowMeasure (a s : ℝ) (n : ℕ) : Measure ℝ :=
  volume.withDensity (fun x => ENNReal.ofReal (logWindowWeight a s n x))

/-- Extend a logarithmic profile by zero off the positive real axis. -/
noncomputable def positiveLogLift (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  if 0 < t then g (Real.log t) else 0

end MasulloRepair


