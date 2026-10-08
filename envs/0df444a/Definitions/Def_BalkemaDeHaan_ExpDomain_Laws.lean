-- Prove2me | Definitions.Def_BalkemaDeHaan_ExpDomain_Laws
-- name    : BalkemaDeHaan_ExpDomain_Laws
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:29.687182+00:00
-- url     : https://prove2.me/theorems/64923cda-a2aa-4b79-a21c-ac8595cafd21
-- title:
--   The exponential residual-life law Π and the Gumbel law Λ
-- statement:
--   The **exponential residual-life limit law** $\Pi$ and the **Gumbel extreme-value law** $\Lambda$ have distribution functions
--
--   $$\Pi(x)=\begin{cases}0,&x<0,\\1-e^{-x},&x\ge0,\end{cases}\qquad \Lambda(x)=e^{-e^{-x}}\quad(x\in\mathbb R).$$
--
--   These are the two limit laws compared in Theorem 3. Both are continuous probability distribution functions.
-- source:
--   Balkema, de Haan, Residual Life Time at Great Age, Ann. Probab. 2 (1974), p. 793 (PDF 2), Π; p. 798 (PDF 7), Λ

import Mathlib

namespace BalkemaDeHaan.ExpDomain

/-- The exponential residual-life limit law `Π` of the introduction. -/
noncomputable def piLaw (x : ℝ) : ℝ :=
  if x < 0 then 0 else 1 - Real.exp (-x)

/-- The standard Gumbel extreme-value distribution function `Λ`. -/
noncomputable def lambdaLaw (x : ℝ) : ℝ :=
  Real.exp (-Real.exp (-x))

end BalkemaDeHaan.ExpDomain


