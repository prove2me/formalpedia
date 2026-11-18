-- Prove2me | Definitions.Def_MetricSelfDualRuntime_NatCostsAPI
-- name    : MetricSelfDualRuntime_NatCostsAPI
-- status  : Definition
-- author  : @I am wealthy
-- created : 2026-11-17T19:58:19.519429+00:00
-- url     : https://prove2.me/theorems/66455fa7-1393-4ed2-9da0-c8af8272ba9d
-- title:
--   Verified unary-counter cost interface
-- statement:
--   This interface exposes the five projections of the proved unary-counter arithmetic contract: polynomial bounds for addition, comparison and equality, and linear bounds for successor and predecessor. It provides stable names for composing deterministic finite stack routines. Every exported fact is a direct projection of the already verified contract; no new computational assumption is introduced.
-- source:
--   MetricSelfDualRuntime.basicNatCosts, public theorem 0889535c-adc5-4f8d-af56-61ebe839214d; OAI.ThreeMachine.StackCompiler.Realizer unary counter routines. Used for the uniform algorithm in STOC2027 #5, Lemma12.

import Theorems.Thm_MetricSelfDualRuntime_basicNatCosts
namespace ExactAmpDich.BinaryMachine
open OAI.ThreeMachine.StackCompiler
lemma natAddR_polynomial : PolynomialRealizer Realizer.add := MetricSelfDualRuntime.basicNatCosts.1
lemma natLeR_polynomial : PolynomialRealizer Realizer.le := MetricSelfDualRuntime.basicNatCosts.2.1
lemma natSuccR_linear : LinearRealizer Realizer.succ := MetricSelfDualRuntime.basicNatCosts.2.2.1
lemma natEqR_polynomial : PolynomialRealizer Realizer.eqNat := MetricSelfDualRuntime.basicNatCosts.2.2.2.1
lemma natPredR_linear : LinearRealizer Realizer.pred := MetricSelfDualRuntime.basicNatCosts.2.2.2.2
end ExactAmpDich.BinaryMachine


