-- Prove2me | Definitions.Def_MazurTransfer_Order13InfinityLocalRingCoordinates
-- name    : MazurTransfer_Order13InfinityLocalRingCoordinates
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T11:28:33.644621+00:00
-- url     : https://prove2.me/theorems/5ddd4bfd-59a3-4fbb-8c58-16329b05e997
-- title:
--   The actual local ring and coordinates at either infinity point
-- statement:
--   Let $K$ be a field and let $a\in K$ satisfy $a^2=1$. The evaluation kernel $\mathfrak m_a$ at $(z,w)=(0,a)$ is prime and maximal. The original local ring and its coordinate elements are $$A_{\mathfrak m_a},\qquad z,\quad w,\quad a.$$ These exact objects supply the uniformizer and Pell valuation computations at infinity.
-- source:
--   Original complete seven declarations from MazurTheorem Order13InfinityLocalParameter.lean, Apache-2.0, Vas and contributors. Seven complete original closed types and five data values are kernel-compared. Native, strict and complete frontend checks pass. Public imports alone replace original dependencies. Named downstream consumer: actual infinity uniformizer and Pell orders.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the reciprocal coordinate z generates the maximal ideal
of the actual chart localized at either infinity evaluation, in characteristic
different from two. Named downstream consumer: the order of the Pell function
at infinity. No valuation order or principal-divisor formula is assumed.
-/
import Definitions.Def_MazurTransfer_Order13InfinityEvaluationMaps
noncomputable section
universe u
namespace MazurTransfer.Order13InfinityLocalParameter
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InfinityEvaluationKernel
open Polynomial
variable (K : Type u) [Field K] (a : K) (ha : a ^ 2 = 1)
def infinityIdeal : Ideal (ReciprocalRing K) := RingHom.ker (evaluation K a ha)

instance infinityIdeal_isPrime : (infinityIdeal K a ha).IsPrime :=
  RingHom.ker_isPrime (evaluation K a ha)

instance infinityIdeal_isMaximal : (infinityIdeal K a ha).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (evaluation K a ha) (evaluation_surjective K a ha)

abbrev LocalRing := Localization.AtPrime (infinityIdeal K a ha)

def z : LocalRing K a ha := algebraMap (ReciprocalRing K) (LocalRing K a ha) (zCoordinate K)

def w : LocalRing K a ha := algebraMap (ReciprocalRing K) (LocalRing K a ha) (wCoordinate K)

def constant : LocalRing K a ha :=
  algebraMap (ReciprocalRing K) (LocalRing K a ha) (algebraMap K (ReciprocalRing K) a)
end MazurTransfer.Order13InfinityLocalParameter
#print axioms MazurTransfer.Order13InfinityLocalParameter.infinityIdeal_isMaximal


