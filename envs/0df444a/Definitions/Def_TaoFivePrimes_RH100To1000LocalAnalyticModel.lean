-- Prove2me | Definitions.Def_TaoFivePrimes_RH100To1000LocalAnalyticModel
-- name    : TaoFivePrimes_RH100To1000LocalAnalyticModel
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-14T02:46:44.382086+00:00
-- url     : https://prove2.me/theorems/af30f811-1ccc-4317-9ce6-49f052ba897b
-- title:
--   RH height 100–1000 — local analytic model
-- statement:
--   Transparent mathematical function definitions for local Taylor approximation of the entire Riemann xi function. The model supplies xi(s)=1/2+s(s-1)completedRiemannZeta₀(s)/2, centers 1/2+iT, and the Taylor polynomial and remainder. Integration majorants and the Jacobi theta functional-equation pair are ordinary supporting definitions; no error bound or RH assertion is included.
-- source:
--   sometik179, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a (2026-10-03), https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a. Theta/Mellin foundations attributed to Gabewhigham. Ordinary definitions extracted from the locally kernel-verified pilot.

/- Local analytic model for the existing height-100–1000 certificate stage.
Transparent definitions from the ACCEPTED height-14–100 proof, originally by
sometik179; theta/Mellin foundations: Gabewhigham. No error or RH assertion. -/
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.MellinTransform
open Complex MeasureTheory Set Finset HurwitzZeta
open scoped BigOperators
set_option autoImplicit false
namespace RH1000Analytic
namespace ZetaSix
noncomputable def P : WeakFEPair ℂ := hurwitzEvenFEPair 0
end ZetaSix
namespace TaoZetaWide
noncomputable def maj (t : ℝ) : ℝ :=
  if t ≤ 1 then 21/10*(t^(-14:ℝ)*Real.exp (-Real.pi/t))
  else 21/10*(t^(12:ℝ)*Real.exp (-Real.pi*t))
noncomputable def gInd : ℝ → ℝ :=
  Set.indicator (Ioi 1) fun u => u^(12:ℝ)*Real.exp (-Real.pi*u)
end TaoZetaWide
namespace CertifiedTaylorQuadrature
noncomputable def coefficient (f : ℂ → ℂ) (c : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f c/(n.factorial:ℂ)
end CertifiedTaylorQuadrature
namespace CertifiedComplexTaylor
open CertifiedTaylorQuadrature
noncomputable def polynomial (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ n ∈ range N, coefficient f c n*(z-c)^n
noncomputable def remainder (f : ℂ → ℂ) (c : ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  f z-polynomial f c N z
end CertifiedComplexTaylor
namespace CertifiedLocalXi
noncomputable def xi (s : ℂ) : ℂ :=
  1/2+s*(s-1)/2*completedRiemannZeta₀ s
noncomputable def center (T : ℝ) : ℂ := 1/2+(T:ℂ)*I
end CertifiedLocalXi
end RH1000Analytic
noncomputable def TaoFivePrimes_RH100To1000LocalAnalyticModel : Nat := 1000


