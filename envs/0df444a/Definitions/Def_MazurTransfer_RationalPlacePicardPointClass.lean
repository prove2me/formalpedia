-- Prove2me | Definitions.Def_MazurTransfer_RationalPlacePicardPointClass
-- name    : MazurTransfer_RationalPlacePicardPointClass
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T01:32:05.813976+00:00
-- url     : https://prove2.me/theorems/86c5ecf1-cbc6-47ce-aebc-04ddb04c11d8
-- title:
--   The degree-zero divisor class of a difference of rational places
-- statement:
--   Let $K$ and $F$ be fields with a $K$-algebra structure on $F$. For degree-one places $Q$ and $P$ of $F/K$, define
--   $$j_Q(P)=[P-Q]\in\operatorname{Pic}^0(F/K).$$
--   The degree-zero condition follows directly from $\deg P=\deg Q=1$.
--
--   This file supplies only the divisor-class constructor. Its injectivity under the positive-genus and constant-field hypotheses is a separate theorem, used to connect actual curve points to the order-thirteen Picard descent.
-- source:
--   Original structural interface in the MazurTheorem formalization: RationalPlacePicardInjectionOverPerfectField.lean, lines131–135. The declaration body is retained exactly and its complete original two-universe type is independently kernel-checked. Underlying degree-zero divisor class group: Apache-2.0 Anthropic FLT, commit6e837e75355538c7f80bab5b956861e86c4eacc2, https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean .

/- Design boundary: the degree-zero class of the difference of two rational places.
Named downstream consumer: the proved positive-genus point-class injection
and the actual order13 Abel-Jacobi point dictionary. -/
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The pole and independent-power argument reuses official Anthropic FLT at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The original canonical-
differential genus theorem is unchanged; this separate perfect-field bridge
uses the checked Weil-canonical Riemann–Roch formula for genusFF instead.
Design boundary: distinct rational places have distinct Abel–Jacobi divisor
classes on a positive-genus function field. Named downstream consumer: the
literal order-13 rational-point injection into its actual arithmetic Pic0.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorClassGroup


universe u v
open AlgebraicCurve Polynomial
namespace MazurTransfer.RationalPlacePicardInjection



namespace Place
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : AlgebraicCurve.Place K F)

end Place

variable {K : Type u} {F : Type v} [Field K] [PerfectField K] [Field F] [Algebra K F]
variable [IsCurveOver K F] [Algebra.EssFiniteType K F]



noncomputable def pointClass (Q : {v : AlgebraicCurve.Place K F // v.deg = 1})
    (P : {v : AlgebraicCurve.Place K F // v.deg = 1}) : Pic0 K F :=
  Pic0.mk ⟨Finsupp.single P.1 1 - Finsupp.single Q.1 1,
    by rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single,
      P.2, Q.2]; norm_num⟩





end MazurTransfer.RationalPlacePicardInjection

#print axioms MazurTransfer.RationalPlacePicardInjection.pointClass


