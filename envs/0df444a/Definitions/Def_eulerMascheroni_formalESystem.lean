-- Prove2me | Definitions.Def_eulerMascheroni_formalESystem
-- name    : eulerMascheroni_formalESystem
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T14:54:17.652076+00:00
-- url     : https://prove2.me/theorems/937730be-cf9b-4344-93ad-69ae74ed97fd
-- title:
--   Formal E-function system for the Euler–Gompertz relation
-- statement:
--   Define the formal power series
--
--   $$\widehat{\operatorname{Ein}}(X)=\sum_{n\ge0}e_nX^n,\qquad\widehat A(X)=e^X\widehat{\operatorname{Ein}}(X),$$
--
--   where $e_0=0$ and $e_{n+1}=(-1)^n/((n+1)(n+1)!)$. These are the formal Taylor series of the entire functions used in the Euler–Gompertz identity.
-- source:
--   Explicit series and norm–Padé growth definitions for this decomposition. Compare Fischler–Rivoal, https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, §4.1 and §4.3, and Matala-aho–Zudilin, https://arxiv.org/html/1703.02633, Eqs. (10)–(11).

import Definitions.Def_eulerMascheroni_mixedCoefficients

noncomputable section
namespace EulerMascheroni.Mixed

def formalEin : PowerSeries ℂ := PowerSeries.mk einCoefficient

def formalExpEin : PowerSeries ℂ := PowerSeries.exp ℂ * formalEin

end EulerMascheroni.Mixed


