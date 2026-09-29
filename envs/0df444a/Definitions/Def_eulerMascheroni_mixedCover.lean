-- Prove2me | Definitions.Def_eulerMascheroni_mixedCover
-- name    : eulerMascheroni_mixedCover
-- status  : Definition
-- author  : @shivm
-- created : 2026-09-11T12:44:28.179139+00:00
-- url     : https://prove2.me/theorems/27431c68-2ce4-4c6a-8b1c-9e4f777b80f4
-- title:
--   An explicit mixed-function family on the logarithmic cover
-- statement:
--   Write $\delta=\int_0^\infty e^{-u}/(1+u)\,du$. Define the entire complementary exponential integral and its exponential multiple by
--
--   $$\operatorname{Ein}(z)=\sum_{n\ge0}\frac{(-1)^n z^{n+1}}{(n+1)(n+1)!},\qquad A(z)=e^z\operatorname{Ein}(z).$$
--
--   On the logarithmic cover, with coordinate $t$ and projection $z=e^t$, define
--
--   $$K(t)=e^{e^t}\left(\operatorname{Ein}(e^t)-\operatorname{Ein}(1)+\frac\delta e-t\right).$$
--
--   This normalization uses the existing integral definition of $\delta$ and contains no assumption about the arithmetic nature of Euler's constant. It gives $K(0)=\delta$ and makes the change under a full turn around zero explicit. The classical Hardy identity identifies $K(\log x)$ with $\int_0^\infty e^{-u}/(u+x)\,du$ for $x>0$; that identification is mathematical content and is not asserted by this definition file. The functions provide a concrete interface for a conjectural mixed-function lifting route to transcendence.
-- source:
--   S. Fischler and T. Rivoal, Relations between values of arithmetic Gevrey series, and applications to values of the Gamma function, J. Number Theory 261 (2024), 36–54; author manuscript https://rivoal.perso.math.cnrs.fr/articles/ssmixte.pdf, Definition 1 and Conjecture 3 (pp. 5–6), Theorem 4 (p. 6), and Eq. (4.5) (p. 14). The logarithmic-cover normalization is an explicit reparameterization for this decomposition, not a quoted definition from the paper.

import Definitions.Def_eulerMascheroni_gompertz

noncomputable section
namespace EulerMascheroni.Mixed

/-- The entire complementary exponential integral, with Ein(0) = 0. -/
def ein (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ) ^ n * z ^ (n + 1) /
    ((n + 1 : ℕ) * (Nat.factorial (n + 1) : ℂ))

/-- The entire E-function exp(z) Ein(z). -/
def expEin (z : ℂ) : ℂ := Complex.exp z * ein z

/-- Analytic continuation of the Euler--Gompertz kernel on the logarithmic
cover z = exp(t), normalized by the integral value at z = 1.
The Borel-integral identification is mathematical content, not a definition. -/
def kernelOnCover (t : ℂ) : ℂ :=
  Complex.exp (Complex.exp t) *
    (ein (Complex.exp t) - ein 1 +
      (EulerMascheroni.gompertzConstant : ℂ) / Complex.exp 1 - t)

end EulerMascheroni.Mixed


