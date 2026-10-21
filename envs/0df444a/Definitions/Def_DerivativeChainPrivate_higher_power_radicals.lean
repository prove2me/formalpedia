-- Prove2me | Definitions.Def_DerivativeChainPrivate_higher_power_radicals
-- name    : DerivativeChainPrivate_higher_power_radicals
-- status  : Definition
-- author  : @labuka
-- created : 2026-10-20T15:43:52.532291+00:00
-- url     : https://prove2.me/theorems/28d2ecda-9ac3-4392-9cfc-a33f2156b08f
-- title:
--   Explicit inverse branches and finite remainder certificates for cubic fourth powers
-- statement:
--   These auxiliary functions specify the selected inverse branches and finite polynomial remainder certificates used for derivative rows of a cubic fourth power. The normalization is $q_0(z)=z^3-\frac{11}{2}z-55\beta$.
--
--   For the sixth-row analysis, the bundle defines
--   $$H(u)=u^2+au+b+\frac{c}{u},\qquad F(u)=i\sqrt{-H(u)},\qquad G(u)=F(u)-u-\frac a2,$$
--   with the fourth-power instance $(a,b,c)=(-11/5,121/120,1331/7560)$.
--
--   For the seventh and eighth rows, it defines finite coefficient arrays, degree-seven square-root approximants, their exact polynomial residuals, and the rational analytic remainder expressions. Their combinations are the functions $R_7$ and $R_8$ used in
--   $$\beta=\alpha_jz^3-b_jz+R_j(z).$$
--   The constants and coefficient arrays are explicit real rational or quadratic-algebraic expressions. Analyticity, positivity, remainder bounds and compatibility with actual derivative roots are proved in separate theorems under their stated domain hypotheses.
-- source:
--   https://gist.github.com/Amal-David/adce933460b7501cb123f483f62775eb (revision f5a76eda649f3e995a8ec6b98387b23b64c6debb); complex/SEXTIC_INVERSE_MEASURE.md, complex/H4_SEPTIC_EXTERIOR_BOUNDS.md, and cone/OCTIC_H4_INVERSE_MEASURE.md. The finite residual formulas are auxiliary definitions used in the accompanying Lean formalization.

import Mathlib
set_option autoImplicit false

section
-- Source module: SexticPick


set_option autoImplicit false
open Set
namespace DerivativeChainPrivate

noncomputable def sexticRadicand (a b c : ℝ) (z : ℂ) : ℂ :=
  z^2 + (a : ℂ)*z + (b : ℂ) + (c : ℂ)/z

noncomputable def sexticUpperBranch (a b c : ℝ) (z : ℂ) : ℂ :=
  Complex.I * Complex.sqrt (-sexticRadicand a b c z)

noncomputable def sexticShift (a b c : ℝ) (z : ℂ) : ℂ :=
  sexticUpperBranch a b c z - z - ((a/2 : ℝ) : ℂ)











end DerivativeChainPrivate

end


section
-- Source module: SexticSupport


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

noncomputable def sexticExteriorExtension (a b c σ : ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  (σ:ℂ)*Complex.sqrt (sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) -
    ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) - ((a/2:ℝ):ℂ)







end DerivativeChainPrivate

end


section
-- Source module: SepticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

noncomputable def septicSqrtCoeffs : Fin 7 → ℝ := ![-11/36, 121/1296, 1331/46656, 14641/3359232, -161051/120932352, -1771561/1451188224, -19487171/52242776064]

noncomputable def septicResidualCoeffs : Fin 7 → ℝ := ![214358881/3761479876608, 30653319983/203119913336832, 440936218217/14624633760251904, 0, -15692141883605/6317841784428822528, -34522712143931/37907050706572935168, -379749833583241/2729307650873251332096]

noncomputable def septicErrorCoeffs : Fin 6 → ℝ := ![-6655/46656, -161051/3359232, -1127357/120932352, 1771561/1451188224, 97435855/52242776064, 214358881/313456656384]

noncomputable def septicSqrtPoly (u : ℂ) : ℂ :=
  1+u*(∑ i : Fin 7, (septicSqrtCoeffs i:ℂ)*u^i.val)

noncomputable def septicSqrtRadicand (u : ℂ) : ℂ :=
  1-(11/18:ℂ)*u+(121/432:ℂ)*u^2

noncomputable def septicSqrtResidual (u : ℂ) : ℂ :=
  ∑ i : Fin 7, (septicResidualCoeffs i:ℂ)*u^i.val















end DerivativeChainPrivate

end


section
-- Source module: SepticTail


set_option autoImplicit false
namespace DerivativeChainPrivate

noncomputable def septicTail (w : ℂ) : ℂ :=
  -((3*Real.sqrt 3/55:ℝ):ℂ)*w^13*(1-(11/6:ℂ)*w^2)*septicSqrtResidual (w^2)/
    (Complex.sqrt (septicSqrtRadicand (w^2))+septicSqrtPoly (w^2))







end DerivativeChainPrivate

end


section
-- Source module: SepticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators

noncomputable def septicPolynomialError (w : ℂ) : ℂ :=
  -((3*Real.sqrt 3/55:ℝ):ℂ)*(∑ i : Fin 6, (septicErrorCoeffs i:ℂ)*w^(2*i.val+3))

noncomputable def septicError (w : ℂ) : ℂ := septicPolynomialError w+septicTail w









end DerivativeChainPrivate

end


section
-- Source module: SepticCoordinates


set_option autoImplicit false
namespace DerivativeChainPrivate



noncomputable def septicLeadingError : ℝ := 11/120-7*(3*Real.sqrt 3/55)*(11/36)^2
noncomputable def septicRemainder (z : ℂ) : ℂ := (septicLeadingError:ℂ)*z⁻¹+septicError z⁻¹





end DerivativeChainPrivate

end


section
-- Source module: OcticSqrtAlgebra


set_option autoImplicit false
namespace DerivativeChainPrivate
open scoped BigOperators

noncomputable def octicSqrtCoeffs : Fin 7 → ℝ := ![11/78, -121/12168, 1331/949104, -73205/296120448, 1127357/23097394944, -12400927/1201064537088, 214358881/93683033892864]

noncomputable def octicResidualCoeffs : Fin 7 → ℝ := ![-2357947691/2248392813428736, 25937424601/263061959171162112, -285311670611/20518832815350644736, 285311670611/133372413299779190784, -109844993185235/332897543596248860196864, 2658248835082687/56259684867766057373270016, -45949729863572161/8776510839371504950230122496]

noncomputable def octicExpansionCoeffs : Fin 7 → ℝ := ![99/2500 - 7249*Real.sqrt 26/1690000, 363/12500 - 11740267*Real.sqrt 26/1977300000, 1331/62500 - 1419760397*Real.sqrt 26/342732000000, 14641/937500 - 1230553517501*Real.sqrt 26/400996440000000, 161051/14062500 - 2106408260641091*Real.sqrt 26/938331669600000000, 1771561/210937500 - 7442473579957471*Real.sqrt 26/4517893224000000000, 19487171/3164062500 - 4419969130587315899*Real.sqrt 26/3659493511440000000000]

noncomputable def octicErrorCoeffs : Fin 6 → ℝ := ![363/12500 - 11740267*Real.sqrt 26/1977300000, 1331/62500 - 1419760397*Real.sqrt 26/342732000000, 14641/937500 - 1230553517501*Real.sqrt 26/400996440000000, 161051/14062500 - 2106408260641091*Real.sqrt 26/938331669600000000, 1771561/210937500 - 7442473579957471*Real.sqrt 26/4517893224000000000, 19487171/3164062500 - 4419969130587315899*Real.sqrt 26/3659493511440000000000]

noncomputable def octicErrorCoeffBounds : Fin 6 → ℝ := ![13/10000, 1/5000, 1/25000, 1/100000, 1/500000, 1/1000000]

noncomputable def octicRationalTailCoeff : ℝ := 214358881/47460937500 - 10804880693278326017*Real.sqrt 26/12198311704800000000000

noncomputable def octicSqrtPoly (u : ℂ) : ℂ :=
  1+u*(∑ i : Fin 7, (octicSqrtCoeffs i:ℂ)*u^i.val)
noncomputable def octicSqrtRadicand (u : ℂ) : ℂ := 1+(11/39:ℂ)*u
noncomputable def octicSqrtResidual (u : ℂ) : ℂ :=
  ∑ i : Fin 7, (octicResidualCoeffs i:ℂ)*u^i.val



















end DerivativeChainPrivate

end


section
-- Source module: OcticTail


set_option autoImplicit false
namespace DerivativeChainPrivate

noncomputable def octicTail (w : ℂ) : ℂ :=
  (octicRationalTailCoeff:ℂ)*w^15/(1-(11/15:ℂ)*w^2)-
    ((3*Real.sqrt 26/550:ℝ):ℂ)*w^13*(1-(11/6:ℂ)*w^2)^2*octicSqrtResidual (w^2)/
      (Complex.sqrt (octicSqrtRadicand (w^2))+octicSqrtPoly (w^2))/(1-(11/15:ℂ)*w^2)







end DerivativeChainPrivate

end


section
-- Source module: OcticErrorDerivative


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open scoped BigOperators

noncomputable def octicPolynomialError (w : ℂ) : ℂ :=
  ∑ i : Fin 6, (octicErrorCoeffs i:ℂ)*w^(2*i.val+3)
noncomputable def octicError (w : ℂ) : ℂ := octicPolynomialError w+octicTail w









end DerivativeChainPrivate

end


section
-- Source module: OcticCoordinates


set_option autoImplicit false
namespace DerivativeChainPrivate



noncomputable def octicLeadingError : ℝ := octicExpansionCoeffs 0
noncomputable def octicRemainder (z : ℂ) : ℂ := (octicLeadingError:ℂ)*z⁻¹+octicError z⁻¹





end DerivativeChainPrivate

end


