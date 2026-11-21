-- Prove2me | Definitions.Def_RiemannMasullo_IntegralAdeleDiagonal
-- name    : RiemannMasullo_IntegralAdeleDiagonal
-- status  : Definition
-- author  : @koffie
-- created : 2026-11-20T23:15:56.688014+00:00
-- url     : https://prove2.me/theorems/0bba3ca5-091e-4f68-9017-611b9aba846e
-- title:
--   Diagonal embedding of $S$-integers into adeles integral outside $S$
-- statement:
--   Let $F$ be a number field, $\mathcal O_F$ its ring of integers, and $S$ a finite set of finite places of $F$. Write $\mathcal O_{F,S}$ for the ring of $S$-integers, the elements of $F$ that are integral at every finite place outside $S$. Write $\mathbb A_{F,S}^{\mathrm{int}}\subseteq\mathbb A_F$ for the subring of adeles integral at every finite place outside $S$.
--
--   The **integral diagonal** is the ring homomorphism
--
--   $$\delta_S:\mathcal O_{F,S}\longrightarrow\mathbb A_{F,S}^{\mathrm{int}},\qquad x\longmapsto(x,x,x,\dots),$$
--
--   the restriction of the diagonal embedding $F\hookrightarrow\mathbb A_F$. It is well defined because a diagonal element is integral outside $S$ exactly when it is an $S$-integer. For $S=\varnothing$ it gives the integral model $\mathbb A_{F,\varnothing}^{\mathrm{int}}/\mathcal O_F$ of the adelic quotient $\mathbb A_F/F$ in Lemma A.1.2.1.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/9d5c8b94a1f1b5d8f903f1b04d1e043877e7bb15/RiemannMasullo/AppA_AlgebraicNT/Sec1.lean#L237-L244 (Apache-2.0); A. M. Masullo, The Music of the Primes (draft 20 Nov 2026), Lemma A.1.2.1, p. 541.

import Mathlib
import Definitions.Def_RiemannMasullo_AdelicExtensions
import Theorems.Thm_RiemannMasullo_diagonal_mem_integralAdelesOutside

/-!
Adapted from mccorvie/riemann-masullo (Apache-2.0),
RiemannMasullo/AppA_AlgebraicNT/Sec1.lean, commit 9d5c8b94a1f1b5d8f903f1b04d1e043877e7bb15.
Masullo, *The Music of the Primes*, Lemma A.1.2.1, p. 541.
-/

noncomputable section

namespace RiemannMasullo

open NumberField IsDedekindDomain
open scoped NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)

/-- Paper: Lemma A.1.2.1, p. 541. The diagonal map on S-integers takes values in the
adeles integral outside S. For empty finite part its domain identifies with the integers. -/
def integralAdeleDiagonal (S : Finset (Primes(F))) :
    (S : Set (Primes(F))).integer F →+* integralAdelesOutside F S :=
  ((algebraMap F 𝔸[F]).comp ((S : Set (Primes(F))).integer F).val.toRingHom).codRestrict _
    (fun x ↦ (diagonal_mem_integralAdelesOutside F S x).2 x.property)

end RiemannMasullo


