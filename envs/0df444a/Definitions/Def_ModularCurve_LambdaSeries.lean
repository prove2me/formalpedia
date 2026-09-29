-- Prove2me | Definitions.Def_ModularCurve_LambdaSeries
-- name    : ModularCurve_LambdaSeries
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/74a32b45-09bd-574e-bb0a-051b63fbdece
-- title:
--   Integral q-expansion of Legendre's λ/16
-- statement:
--   The module introduces, as a formal Laurent series over $\mathbb{Z}$, the $q$-expansion of $\mu = \lambda/16$, where $\lambda$ is Legendre's modular function, together with its reductions and a substitution homomorphism. Recall from the imported material that `etaProd` is the power series $\prod_{n\ge 1}(1-X^{n})$, that `dedekindEtaUnitInv` is the power-series inverse of `etaProd`$^{24}$ (legitimate since the constant coefficient is $1$), and that `qExpand R N` is the injective ring endomorphism of $R((q))$ obtained by scaling exponents by $N$, so that the coefficient of $q^{Nk}$ in `qExpand R N f` is the coefficient of $q^{k}$ in $f$ and all coefficients at exponents not divisible by $N$ vanish. The series `lambdaInt` is the product of the monomial $q$ (the Hahn series `single 1 1`), the eighth power of `etaProd`, the sixteenth power of `etaProd` with $q$ replaced by $q^{4}$, and the inverse of `etaProd`$^{24}$ with $q$ replaced by $q^{2}$; that is,
--   $$\mu(q) \;=\; q\,\frac{\prod_{n\ge 1}(1-q^{n})^{8}\,(1-q^{4n})^{16}}{\prod_{n\ge 1}(1-q^{2n})^{24}} \;=\; q - 8q^{2} + 44q^{3} - \cdots \in \mathbb{Z}((q)),$$
--   the expansion in the parameter whose square is the level-one parameter. For a commutative ring $L$, `lambdaModC L` is the coefficientwise image of `lambdaInt` under $\mathbb{Z}\to L$, and `lambdaNModC L N` is `lambdaModC L` with $q$ replaced by $q^{N}$; for $N=1$ the two agree. Finally `evalAtLambdaInt` is the evaluation ring homomorphism $\mathbb{Z}[X] \to \mathbb{Z}((q))$ determined by $X \mapsto \mu$, the second recorded lemma being that it sends $X$ to `lambdaInt`. Nothing about $\mu$ beyond these definitional identities is asserted here.
--
--   **Relation to Mathlib.** Mathlib supplies the ambient `LaurentSeries`/`HahnSeries` and `PowerSeries` formalism, including the infinite product used for `etaProd` and `PowerSeries.invOfUnit`; it has no $q$-expansion of Legendre's $\lambda$, and the substitution $q \mapsto q^{N}$ (`qExpand`) and the coefficientwise base change `laurentMap` are the project's own, introduced in the imported modules.
--
--   **Where it is used.** The normalisation $\mu = \lambda/16$ has integral coefficients with leading coefficient $1$, so it serves as a Hauptmodul whose modular polynomials are monic; `lambdaInt`, its reductions `lambdaModC`/`lambdaNModC` and the evaluation map `evalAtLambdaInt` are the level-two analogues of the $j$-expansions `jqInt`, `jqMod` and `evalAtJInt`, and feed the construction of models of modular curves and the associated integrality and congruence statements.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_LambdaSeries.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_KroneckerTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def lambdaInt : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) (1 : ℤ) *
    HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 8 *
    qExpand ℤ 4 (HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 16) *
    qExpand ℤ 2 (HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv)

def lambdaModC (L : Type*) [CommRing L] : LaurentSeries L :=
  laurentMap (Int.castRingHom L) lambdaInt

def lambdaNModC (L : Type*) [CommRing L] (N : ℕ) [NeZero N] : LaurentSeries L :=
  qExpand L N (lambdaModC L)

theorem lambdaNModC_one (L : Type*) [CommRing L] : lambdaNModC L 1 = lambdaModC L :=
  qExpand_one_apply _

def evalAtLambdaInt : Polynomial ℤ →+* LaurentSeries ℤ :=
  Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℤ)) lambdaInt

theorem evalAtLambdaInt_X : evalAtLambdaInt Polynomial.X = lambdaInt :=
  Polynomial.eval₂_X _ _

end ModularCurve

end


