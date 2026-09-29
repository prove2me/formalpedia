-- Prove2me | Definitions.Def_eulerMascheroni_mixedCoefficients
-- name    : eulerMascheroni_mixedCoefficients
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T14:20:44.409141+00:00
-- url     : https://prove2.me/theorems/969f9b12-edd4-47be-8fd5-80f94e16a095
-- title:
--   Taylor coefficients of the elementary mixed E-value combination
-- statement:
--   Let $e_0=0$ and $e_{n+1}=(-1)^n/((n+1)(n+1)!)$, the coefficients of $\operatorname{Ein}(z)$. For real $a,b,c$, define
--
--   $$f_n(a,b,c)=a\,\mathbf1_{n=0}+\frac{b}{n!}+c\sum_{k=0}^n\frac{e_{n-k}}{k!}.$$
--
--   These are the Taylor coefficients of $a+b e^z+c e^z\operatorname{Ein}(z)$, used to specify an arithmetic quotient at the evaluation point $z=1$.
-- source:
--   Explicit Taylor and Cauchy-product coefficients for the E-functions in Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Lemma 2(ii), Eq. (4.5), and §4.3.

import Definitions.Def_eulerMascheroni_mixedCover

noncomputable section
namespace EulerMascheroni.Mixed

def einCoefficient : ℕ → ℂ
  | 0 => 0
  | n+1 => (-1 : ℂ)^n / (((n+1 : ℕ) : ℂ) * ((n+1).factorial : ℂ))

def valueCoefficient (a b c : ℝ) (n : ℕ) : ℂ :=
  (if n = 0 then (a : ℂ) else 0) + (b : ℂ) / (n.factorial : ℂ) +
    (c : ℂ) * ∑ k ∈ Finset.range (n+1), (1 : ℂ)/(k.factorial : ℂ) * einCoefficient (n-k)

end EulerMascheroni.Mixed


