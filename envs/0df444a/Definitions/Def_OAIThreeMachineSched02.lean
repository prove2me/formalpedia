-- Prove2me | Definitions.Def_OAIThreeMachineSched02
-- name    : OAIThreeMachineSched02
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T06:31:32.351374+00:00
-- url     : https://prove2.me/theorems/2675dabb-2d9d-460d-813d-84b07cea2fde
-- title:
--   Cost models and routine definitions for three-machine scheduling
-- statement:
--   This block collects the supporting declarations of the stack compiler used to prove `OAI.ThreeMachine.main_theorem`, part 2 of 2, in upstream module order.
--
--   Contents: later routine definitions for matrices, families, tables and schedules, the predicate `Poly`, its closure rules, and the size predicates such as `BlockSmall` and `TableSmall`.
--
--   **Formalization Note** Declarations are reproduced from upstream `lean/OAI/Computability/Scheduling/` (openai/math, Apache-2.0, credit OpenAI), together with short lemmas their bodies and instances need, on Lean 4.33. Metaprograms are excluded. Where an upstream proof called the tactic `poly_auto`, the explicit rule applications recorded from that tactic appear instead.
-- source:
--   OpenAI, "A Polynomial-Time Algorithm for Three-Machine Unit-Job Scheduling" (September 24, 2026), openai/math. Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Computability/Scheduling/

import Definitions.Def_OAIThreeMachineSched01

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option linter.all false
set_option Elab.async false

section
-- module StateCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u7} {α : I → Type u8} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
namespace Costs

theorem finEq : Poly (fun x : Σ n, Fin n × Fin n => x.1)
    (fun x => Uniform.finEq.time x.1 x.2) 2 := by
  apply Poly.of_le (g := fun x : Σ n, Fin n × Fin n => 1000000000000*(x.1+2)^2)
  · rintro ⟨n,a,b⟩
    have hf (n : ℕ) (v : Fin n) : Uniform.finVal.time n v = volume v+2 := rfl
    have h := Realizer.time_eqNat_le a.val b.val
    have hsq := Nat.pow_le_pow_left (show a.val+b.val+1 ≤ 2*n+1 by omega) 2
    simp only [Uniform.finEq,Uniform.time_congr,Uniform.time_comp,Uniform.time_pair,
      Uniform.time_fst,Uniform.time_snd,hf,
      Uniform.time_uniform,volume_pair,volume_fin,volume_nat,Function.comp_apply]
    nlinarith [a.isLt,b.isLt]
  · (have polyH0 := Poly.const (fun (x_1 : (n : ℕ) × Fin n × Fin n) => Sigma.fst x_1) (1000000000000); have polyH1 := Poly.base (fun (x_1 : (n : ℕ) × Fin n × Fin n) => Sigma.fst x_1); have polyH2 := Poly.pow polyH1 (2); have polyH3 := Poly.mul polyH0 polyH2; exact Poly.lift polyH3 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem setMem : Poly (fun x : Σ n, Fin n × Finset (Fin n) => x.1)
    (fun x => Uniform.setMem.time x.1 x.2) 3 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1); have polyH1 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => x_1.2.1); have polyH2 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Fin n × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (Fin) (fun (n : ℕ) => Finset (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH7 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => (Sigma.snd x_1).2); have polyH8 := Poly.add polyH7 polyH4; have polyH9 := Poly.add polyH6 polyH8; have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (10); have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (1); have polyH12 := Poly.add polyH7 polyH11; have polyH13 := Poly.mul polyH10 polyH12; have polyH14 := Poly.add polyH9 polyH13; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Fin n × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.snd ℕ Fin (fun (n : ℕ) => Finset (Fin n)) _ _) (Uniform.setList) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH14; have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Fin n × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (Fin) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH17 := Poly.add polyH15 polyH16; have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (20); have polyH19 := Poly.add polyH3 polyH7; have polyH20 := Poly.volumeFin polyH0 (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => (Sigma.snd x_1).1); have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.add polyH21 polyH11; have polyH23 := Poly.mul polyH18 polyH22; have polyH24 := Poly.add polyH17 polyH23; have polyH25 := Poly.of_le (fun (x_2 : (n : ℕ) × Fin n × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => List (Fin n)) (Fin) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i)) => (fun (s : Finset (Fin i)) => Finset.sort s fun (x1 x2 : Fin i) => x1 ≤ x2) (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.snd ℕ Fin (fun (n : ℕ) => Finset (Fin n)) _ _) Uniform.setList) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH24; have polyH26 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => (Sigma.snd x_1).2); have polyH27 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Prod.snd (Sigma.snd x_1)) polyH26; have polyH28 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Prod.fst ((fun (s : Finset (Fin (Sigma.fst x_1))) => Finset.sort s fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)); have polyH29 := Poly.reparam (@Costs.finEq) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Prod.fst ((fun (s : Finset (Fin (Sigma.fst x_1))) => Finset.sort s fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd ((fun (s : Finset (Fin (Sigma.fst (Sigma.fst q)))) => Finset.sort s fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2) (Prod.snd (Sigma.snd (Sigma.fst q))), Prod.fst (Sigma.snd (Sigma.fst q))))) polyH28; have polyH30 := @Poly.anyTime (ℕ) ((n : ℕ) × Fin n × Finset (Fin n)) (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (Fin) (Fin) _ _ (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Prod.fst ((fun (s : Finset (Fin (Sigma.fst x_1))) => Finset.sort s fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => Prod.snd ((fun (s : Finset (Fin (Sigma.fst x_1))) => Finset.sort s fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (Uniform.finEq) (1) (2 * 1) (2 * 1) (1) polyH27 polyH29 polyH7 polyH20; have polyH31 := Poly.add polyH25 polyH30; have polyH32 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Fin n × Finset (Fin n)) => ((fun (s : Finset (Fin (Sigma.fst x_1))) => Finset.sort s fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2) (Prod.snd (Sigma.snd x_1)), Prod.fst (Sigma.snd x_1))) polyH7 polyH20; have polyH33 := Poly.add polyH32 polyH11; have polyH34 := Poly.mul polyH10 polyH33; have polyH35 := Poly.add polyH31 polyH34; have polyH36 := Poly.of_le (fun (x_2 : (n : ℕ) × Fin n × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (i : ℕ) => List (Fin i) × Fin i) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i)) => ((fun (s : Finset (Fin i)) => Finset.sort s fun (x1 x2 : Fin i) => x1 ≤ x2) (Prod.snd x_1), Prod.fst x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Fin i) => List.any (Prod.fst x_1) fun (a : Fin i) => Decidable.decide (Prod.fst (a, Prod.snd x_1) = Prod.snd (a, Prod.snd x_1))) (@Uniform.pair ℕ (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => List (Fin n)) Fin _ _ _ (fun (i : ℕ) (x_1 : Fin i × Finset (Fin i)) => (fun (s : Finset (Fin i)) => Finset.sort s fun (x1 x2 : Fin i) => x1 ≤ x2) (Prod.snd x_1)) (fun (i : ℕ) => Prod.fst) (@Uniform.comp ℕ (fun (i : ℕ) => Fin i × Finset (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.snd ℕ Fin (fun (n : ℕ) => Finset (Fin n)) _ _) Uniform.setList) (@Uniform.fst ℕ Fin (fun (i : ℕ) => Finset (Fin i)) _ _)) (@Uniform.any ℕ Fin Fin _ _ (fun (n : ℕ) (x_1 : Fin n × Fin n) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) Uniform.finEq) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH35; exact Poly.lift polyH36 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem setSubset : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setSubset.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1); have polyH1 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.1); have polyH2 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH7 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1); have polyH8 := Poly.add polyH7 polyH4; have polyH9 := Poly.add polyH6 polyH8; have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (10); have polyH11 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (1); have polyH12 := Poly.add polyH7 polyH11; have polyH13 := Poly.mul polyH10 polyH12; have polyH14 := Poly.add polyH9 polyH13; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Uniform.setList) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH14; have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH17 := Poly.add polyH15 polyH16; have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (20); have polyH19 := Poly.add polyH3 polyH7; have polyH20 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2); have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.add polyH21 polyH11; have polyH23 := Poly.mul polyH18 polyH22; have polyH24 := Poly.add polyH17 polyH23; have polyH25 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) (x_1 : (fun (n : ℕ) => Finset (Fin n)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) => (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) i (Prod.fst x_1)) (fun (i : ℕ) => Prod.snd) (@Uniform.comp ℕ (fun (i : ℕ) => (fun (n : ℕ) => Finset (Fin n)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) (@Uniform.fst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _) Uniform.setList) (@Uniform.snd ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH24; have polyH26 := Poly.finsetCard polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1); have polyH27 := Poly.lengthSort (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Sigma.snd x_1)) polyH26; have polyH28 := Poly.size (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Sigma.fst q)); have polyH29 := Poly.reparam (@Costs.setMem) (fun (q : Poly.Pool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) => Sigma.mk (Sigma.fst (Sigma.fst q)) (Subtype.val (Sigma.snd q), Prod.snd (Finset.sort (Prod.fst (Sigma.snd (Sigma.fst q))) fun (x1 x2 : Fin (Sigma.fst (Sigma.fst q))) => x1 ≤ x2, Prod.snd (Sigma.snd (Sigma.fst q))))) polyH28; have polyH30 := @Poly.allTime (ℕ) ((n : ℕ) × Finset (Fin n) × Finset (Fin n)) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (Fin) (fun (i : ℕ) => Finset (Fin i)) _ _ (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.fst (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Prod.snd (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) (Uniform.setMem) (1) (3 * 1) (2 * 1) (2 * 1) polyH27 polyH29 polyH7 polyH20; have polyH31 := Poly.add polyH25 polyH30; have polyH32 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Finset.sort (Prod.fst (Sigma.snd x_1)) fun (x1 x2 : Fin (Sigma.fst x_1)) => x1 ≤ x2, Prod.snd (Sigma.snd x_1))) polyH7 polyH20; have polyH33 := Poly.add polyH32 polyH11; have polyH34 := Poly.mul polyH10 polyH33; have polyH35 := Poly.add polyH31 polyH34; have polyH36 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => List (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Finset.sort (Prod.fst x_1) fun (x1 x2 : Fin i) => x1 ≤ x2, Prod.snd x_1)) (fun (i : ℕ) (x_1 : List (Fin i) × Finset (Fin i)) => List.all (Prod.fst x_1) fun (a : Fin i) => Decidable.decide (Prod.fst (a, Prod.snd x_1) ∈ Prod.snd (a, Prod.snd x_1))) (@Uniform.onFst ℕ (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => List (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : Finset (Fin n)) => Finset.sort s fun (x1 x2 : Fin n) => x1 ≤ x2) Uniform.setList) (@Uniform.all ℕ Fin (fun (i : ℕ) => Finset (Fin i)) _ _ (fun (n : ℕ) (x_1 : Fin n × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ∈ Prod.snd x_1)) Uniform.setMem) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH35; exact Poly.lift polyH36 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem setEq : Poly (fun x : Σ n, Finset (Fin n) × Finset (Fin n) => x.1)
    (fun x => Uniform.setEq.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.setSubset) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.1); have polyH3 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2.2); have polyH4 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => x_1.2) polyH2 polyH3; have polyH5 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (2); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH6; have polyH8 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH6; have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (20); have polyH11 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).2); have polyH12 := Poly.add polyH4 polyH11; have polyH13 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Sigma.snd x_1).1); have polyH14 := Poly.add polyH12 polyH13; have polyH15 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (1); have polyH16 := Poly.add polyH14 polyH15; have polyH17 := Poly.mul polyH10 polyH16; have polyH18 := Poly.add polyH9 polyH17; have polyH19 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => (fun (i_1 : ℕ) => Finset (Fin i_1)) i × (fun (i_1 : ℕ) => Finset (Fin i_1)) i) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH18; have polyH20 := Poly.reparam (@Costs.setSubset) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.mk (Sigma.fst x_1) (Prod.snd (Sigma.snd x_1), Prod.fst (Sigma.snd x_1))) polyH0; have polyH21 := Poly.add polyH19 polyH20; have polyH22 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (10); have polyH23 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Prod.snd (Sigma.snd x_1), Prod.fst (Sigma.snd x_1))) polyH11 polyH13; have polyH24 := Poly.add polyH23 polyH15; have polyH25 := Poly.mul polyH22 polyH24; have polyH26 := Poly.add polyH21 polyH25; have polyH27 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) (@Uniform.swap ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Uniform.setSubset) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH26; have polyH28 := Poly.add polyH1 polyH27; have polyH29 := Poly.volumeBool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst (Sigma.snd x_1) ⊆ Prod.snd (Sigma.snd x_1))); have polyH30 := Poly.add polyH4 polyH29; have polyH31 := Poly.volumeBool (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst ((fun (x_2 : Finset (Fin (Sigma.fst x_1)) × Finset (Fin (Sigma.fst x_1))) => (Prod.snd x_2, Prod.fst x_2)) (Sigma.snd x_1)) ⊆ Prod.snd ((fun (x_2 : Finset (Fin (Sigma.fst x_1)) × Finset (Fin (Sigma.fst x_1))) => (Prod.snd x_2, Prod.fst x_2)) (Sigma.snd x_1)))); have polyH32 := Poly.add polyH30 polyH31; have polyH33 := Poly.add polyH32 polyH15; have polyH34 := Poly.mul polyH10 polyH33; have polyH35 := Poly.add polyH28 polyH34; have polyH36 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) (fun (n : ℕ) => Bool) (fun (n : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (fun (x_3 : Finset (Fin i) × Finset (Fin i)) => Decidable.decide (Prod.fst x_3 ⊆ Prod.snd x_3)) ((fun (x_3 : Finset (Fin i) × Finset (Fin i)) => (Prod.snd x_3, Prod.fst x_3)) x_1)) (Uniform.setSubset) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) (@Uniform.swap ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) Uniform.setSubset) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH35; have polyH37 := Poly.const (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => Sigma.fst x_1) (10000); have polyH38 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (@Realizer.time_and_le ((Decidable.decide (Prod.fst (Sigma.snd x_2) ⊆ Prod.snd (Sigma.snd x_2)), (fun (x_1 : Finset (Fin (Sigma.fst x_2)) × Finset (Fin (Sigma.fst x_2))) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) ((fun (x_1 : Finset (Fin (Sigma.fst x_2)) × Finset (Fin (Sigma.fst x_2))) => (Prod.snd x_1, Prod.fst x_1)) (Sigma.snd x_2)))))) polyH37; have polyH39 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_uniform (ℕ) (Bool × Bool) (Bool) _ _ (fun (x_1 : Bool × Bool) => Prod.fst x_1 && Prod.snd x_1) (Realizer.and) (Sigma.fst x_2) ((Decidable.decide (Prod.fst (Sigma.snd x_2) ⊆ Prod.snd (Sigma.snd x_2)), (fun (x_1 : Finset (Fin (Sigma.fst x_2)) × Finset (Fin (Sigma.fst x_2))) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) ((fun (x_1 : Finset (Fin (Sigma.fst x_2)) × Finset (Fin (Sigma.fst x_2))) => (Prod.snd x_1, Prod.fst x_1)) (Sigma.snd x_2))))))) polyH38; have polyH40 := Poly.add polyH36 polyH39; have polyH41 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (Decidable.decide (Prod.fst (Sigma.snd x_1) ⊆ Prod.snd (Sigma.snd x_1)), (fun (x_2 : Finset (Fin (Sigma.fst x_1)) × Finset (Fin (Sigma.fst x_1))) => Decidable.decide (Prod.fst x_2 ⊆ Prod.snd x_2)) ((fun (x_2 : Finset (Fin (Sigma.fst x_1)) × Finset (Fin (Sigma.fst x_1))) => (Prod.snd x_2, Prod.fst x_2)) (Sigma.snd x_1)))) polyH29 polyH31; have polyH42 := Poly.add polyH41 polyH15; have polyH43 := Poly.mul polyH22 polyH42; have polyH44 := Poly.add polyH40 polyH43; have polyH45 := Poly.of_le (fun (x_2 : (n : ℕ) × Finset (Fin n) × Finset (Fin n)) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Bool × Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1), (fun (x_3 : Finset (Fin i) × Finset (Fin i)) => Decidable.decide (Prod.fst x_3 ⊆ Prod.snd x_3)) ((fun (x_3 : Finset (Fin i) × Finset (Fin i)) => (Prod.snd x_3, Prod.fst x_3)) x_1))) (fun (x_1 : ℕ) (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) (@Uniform.pair ℕ (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n)) (fun (n : ℕ) => Bool) (fun (n : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (fun (x_3 : Finset (Fin i) × Finset (Fin i)) => Decidable.decide (Prod.fst x_3 ⊆ Prod.snd x_3)) ((fun (x_3 : Finset (Fin i) × Finset (Fin i)) => (Prod.snd x_3, Prod.fst x_3)) x_1)) Uniform.setSubset (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i)) => (Prod.snd x_1, Prod.fst x_1)) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 ⊆ Prod.snd x_1)) (@Uniform.swap ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) Uniform.setSubset)) (Realizer.uniform Realizer.and ℕ) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH44; exact Poly.lift polyH45 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))

end Costs
namespace Uniform

def noEdgeTest : Uniform (fun n (x : Fin n × (Matrix n × Fin n)) => !x.2.1 x.2.2 x.1) :=
  (((snd.comp fst).pair ((snd.comp snd).pair fst)).comp matrixGet).comp (Realizer.not.uniform ℕ)

def noEdgeRow : Uniform (fun n (x : Fin n × (Matrix n × Finset (Fin n))) =>
    decide (∀ b ∈ x.2.2, ¬matrixRel x.2.1 x.1 b)) :=
  (((snd.comp snd).pair ((snd.comp fst).pair fst)).comp noEdgeTest.setAll).congr (fun _ _ => by
    simp only [Function.comp_apply,Bool.not_eq_true,matrixRel,Bool.not_eq_true'])

end Uniform
namespace Costs

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev StateEqInput (n : ℕ) := Algorithm.State (Fin n) × Algorithm.State (Fin n)
def stateEqL : Uniform (fun n (x : StateEqInput n) => decide (x.1.left = x.2.left)) :=
  ((fst.comp stateLeft).pair (snd.comp stateLeft)).comp setEq
def stateEqM : Uniform (fun n (x : StateEqInput n) => decide (x.1.middle = x.2.middle)) :=
  ((fst.comp stateMiddle).pair (snd.comp stateMiddle)).comp setEq
def stateEqR : Uniform (fun n (x : StateEqInput n) => decide (x.1.right = x.2.right)) :=
  ((fst.comp stateRight).pair (snd.comp stateRight)).comp setEq
def stateEqMR := (stateEqM.pair stateEqR).comp (Realizer.and.uniform ℕ)
def stateEqLMR := (stateEqL.pair stateEqMR).comp (Realizer.and.uniform ℕ)
theorem time_stateEq (n : ℕ) (x : StateEqInput n) : stateEq.time n x = stateEqLMR.time n x := rfl
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
theorem stateEqL : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqL.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1); have polyH1 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.1); have polyH2 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH7 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Sigma.snd x_1).1); have polyH8 := Poly.add polyH7 polyH4; have polyH9 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).1); have polyH10 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).2); have polyH11 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).3); have polyH12 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)))) polyH10 polyH11; have polyH13 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)))) polyH9 polyH12; have polyH14 := Poly.add polyH13 polyH4; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH14; have polyH16 := Poly.add polyH8 polyH15; have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10); have polyH18 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (1); have polyH19 := Poly.add polyH13 polyH18; have polyH20 := Poly.mul polyH17 polyH19; have polyH21 := Poly.add polyH16 polyH20; have polyH22 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) => Prod.fst) (Uniform.stateParts) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2))))) polyH21; have polyH23 := Poly.add polyH6 polyH22; have polyH24 := Poly.add polyH7 polyH18; have polyH25 := Poly.mul polyH17 polyH24; have polyH26 := Poly.add polyH23 polyH25; have polyH27 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) (Uniform.stateLeft) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH26; have polyH28 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH29 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Sigma.snd x_1).2); have polyH30 := Poly.add polyH29 polyH4; have polyH31 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).1); have polyH32 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).2); have polyH33 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).3); have polyH34 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))) polyH32 polyH33; have polyH35 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))) polyH31 polyH34; have polyH36 := Poly.add polyH35 polyH4; have polyH37 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH36; have polyH38 := Poly.add polyH30 polyH37; have polyH39 := Poly.add polyH35 polyH18; have polyH40 := Poly.mul polyH17 polyH39; have polyH41 := Poly.add polyH38 polyH40; have polyH42 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) => Prod.fst) (Uniform.stateParts) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH41; have polyH43 := Poly.add polyH28 polyH42; have polyH44 := Poly.add polyH29 polyH18; have polyH45 := Poly.mul polyH17 polyH44; have polyH46 := Poly.add polyH43 polyH45; have polyH47 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) (Uniform.stateLeft) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH46; have polyH48 := Poly.add polyH27 polyH47; have polyH49 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (20); have polyH50 := Poly.add polyH3 polyH9; have polyH51 := Poly.add polyH50 polyH31; have polyH52 := Poly.add polyH51 polyH18; have polyH53 := Poly.mul polyH49 polyH52; have polyH54 := Poly.add polyH48 polyH53; have polyH55 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateLeft) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateLeft) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH54; have polyH56 := Poly.reparam (@Costs.setEq) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst (Sigma.snd x_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.snd (Sigma.snd x_1)))) polyH0; have polyH57 := Poly.add polyH55 polyH56; have polyH58 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst (Sigma.snd x_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.snd (Sigma.snd x_1)))) polyH9 polyH31; have polyH59 := Poly.add polyH58 polyH18; have polyH60 := Poly.mul polyH17 polyH59; have polyH61 := Poly.add polyH57 polyH60; have polyH62 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst x_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.left s) (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateLeft) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.left s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateLeft)) (Uniform.setEq) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH61; exact Poly.lift polyH62 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem stateEqM : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqM.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1); have polyH1 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.1); have polyH2 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH7 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Sigma.snd x_1).1); have polyH8 := Poly.add polyH7 polyH4; have polyH9 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).1); have polyH10 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).2); have polyH11 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).3); have polyH12 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)))) polyH10 polyH11; have polyH13 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)))) polyH9 polyH12; have polyH14 := Poly.add polyH13 polyH4; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH14; have polyH16 := Poly.add polyH12 polyH4; have polyH17 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Prod.snd (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH16; have polyH18 := Poly.add polyH15 polyH17; have polyH19 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10); have polyH20 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (1); have polyH21 := Poly.add polyH12 polyH20; have polyH22 := Poly.mul polyH19 polyH21; have polyH23 := Poly.add polyH18 polyH22; have polyH24 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH23; have polyH25 := Poly.add polyH8 polyH24; have polyH26 := Poly.add polyH13 polyH20; have polyH27 := Poly.mul polyH19 polyH26; have polyH28 := Poly.add polyH25 polyH27; have polyH29 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) => Prod.fst (Prod.snd x_1)) (Uniform.stateParts) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2))))) polyH28; have polyH30 := Poly.add polyH6 polyH29; have polyH31 := Poly.add polyH7 polyH20; have polyH32 := Poly.mul polyH19 polyH31; have polyH33 := Poly.add polyH30 polyH32; have polyH34 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.middle s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) (Uniform.stateMiddle) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH33; have polyH35 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH36 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Sigma.snd x_1).2); have polyH37 := Poly.add polyH36 polyH4; have polyH38 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).1); have polyH39 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).2); have polyH40 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).3); have polyH41 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))) polyH39 polyH40; have polyH42 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))) polyH38 polyH41; have polyH43 := Poly.add polyH42 polyH4; have polyH44 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH43; have polyH45 := Poly.add polyH41 polyH4; have polyH46 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Prod.snd (OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH45; have polyH47 := Poly.add polyH44 polyH46; have polyH48 := Poly.add polyH41 polyH20; have polyH49 := Poly.mul polyH19 polyH48; have polyH50 := Poly.add polyH47 polyH49; have polyH51 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH50; have polyH52 := Poly.add polyH37 polyH51; have polyH53 := Poly.add polyH42 polyH20; have polyH54 := Poly.mul polyH19 polyH53; have polyH55 := Poly.add polyH52 polyH54; have polyH56 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) => Prod.fst (Prod.snd x_1)) (Uniform.stateParts) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.fst) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.fst ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH55; have polyH57 := Poly.add polyH35 polyH56; have polyH58 := Poly.add polyH36 polyH20; have polyH59 := Poly.mul polyH19 polyH58; have polyH60 := Poly.add polyH57 polyH59; have polyH61 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.middle s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) (Uniform.stateMiddle) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH60; have polyH62 := Poly.add polyH34 polyH61; have polyH63 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (20); have polyH64 := Poly.add polyH3 polyH10; have polyH65 := Poly.add polyH64 polyH39; have polyH66 := Poly.add polyH65 polyH20; have polyH67 := Poly.mul polyH63 polyH66; have polyH68 := Poly.add polyH62 polyH67; have polyH69 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.middle s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateMiddle) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.middle s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateMiddle) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH68; have polyH70 := Poly.reparam (@Costs.setEq) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.fst (Sigma.snd x_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.snd (Sigma.snd x_1)))) polyH0; have polyH71 := Poly.add polyH69 polyH70; have polyH72 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.fst (Sigma.snd x_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.snd (Sigma.snd x_1)))) polyH10 polyH39; have polyH73 := Poly.add polyH72 polyH20; have polyH74 := Poly.mul polyH19 polyH73; have polyH75 := Poly.add polyH71 polyH74; have polyH76 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.fst x_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.middle s) (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.middle s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateMiddle) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.middle s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateMiddle)) (Uniform.setEq) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH75; exact Poly.lift polyH76 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem stateEqR : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqR.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1); have polyH1 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.1); have polyH2 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.2); have polyH3 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2) polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_fst (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH7 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Sigma.snd x_1).1); have polyH8 := Poly.add polyH7 polyH4; have polyH9 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).1); have polyH10 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).2); have polyH11 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.fst (Sigma.snd x_1)).3); have polyH12 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)))) polyH10 polyH11; have polyH13 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)))) polyH9 polyH12; have polyH14 := Poly.add polyH13 polyH4; have polyH15 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH14; have polyH16 := Poly.add polyH12 polyH4; have polyH17 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Prod.snd (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH16; have polyH18 := Poly.add polyH15 polyH17; have polyH19 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10); have polyH20 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (1); have polyH21 := Poly.add polyH12 polyH20; have polyH22 := Poly.mul polyH19 polyH21; have polyH23 := Poly.add polyH18 polyH22; have polyH24 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2))))))) polyH23; have polyH25 := Poly.add polyH8 polyH24; have polyH26 := Poly.add polyH13 polyH20; have polyH27 := Poly.mul polyH19 polyH26; have polyH28 := Poly.add polyH25 polyH27; have polyH29 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x_1)) (Uniform.stateParts) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (Sigma.fst x_2) (Prod.fst (Sigma.snd x_2))))) polyH28; have polyH30 := Poly.add polyH6 polyH29; have polyH31 := Poly.add polyH7 polyH20; have polyH32 := Poly.mul polyH19 polyH31; have polyH33 := Poly.add polyH30 polyH32; have polyH34 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) (Uniform.stateRight) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH33; have polyH35 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _ (Sigma.fst x_2) (Sigma.snd x_2)))) polyH5; have polyH36 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Sigma.snd x_1).2); have polyH37 := Poly.add polyH36 polyH4; have polyH38 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).1); have polyH39 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).2); have polyH40 := Poly.volumeFinset polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Prod.snd (Sigma.snd x_1)).3); have polyH41 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))) polyH39 polyH40; have polyH42 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))) polyH38 polyH41; have polyH43 := Poly.add polyH42 polyH4; have polyH44 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _ (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH43; have polyH45 := Poly.add polyH41 polyH4; have polyH46 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_snd (ℕ) (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ (Sigma.fst x_2) (Prod.snd (OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH45; have polyH47 := Poly.add polyH44 polyH46; have polyH48 := Poly.add polyH41 polyH20; have polyH49 := Poly.mul polyH19 polyH48; have polyH50 := Poly.add polyH47 polyH49; have polyH51 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _) (Sigma.fst x_2) ((OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2)), OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH50; have polyH52 := Poly.add polyH37 polyH51; have polyH53 := Poly.add polyH42 polyH20; have polyH54 := Poly.mul polyH19 polyH53; have polyH55 := Poly.add polyH52 polyH54; have polyH56 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n) × Finset (Fin n) × Finset (Fin n)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => (OAI.ThreeMachine.Algorithm.State.left s, OAI.ThreeMachine.Algorithm.State.middle s, OAI.ThreeMachine.Algorithm.State.right s)) (fun (i : ℕ) (x_1 : Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) => Prod.snd (Prod.snd x_1)) (Uniform.stateParts) (@Uniform.comp ℕ (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (i : ℕ) => Prod.snd) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) _ _) (@Uniform.snd ℕ (fun (i : ℕ) => Finset (Fin i)) (fun (i : ℕ) => Finset (Fin i)) _ _)) (Sigma.fst x_2) (Prod.snd (Sigma.snd x_2))))) polyH55; have polyH57 := Poly.add polyH35 polyH56; have polyH58 := Poly.add polyH36 polyH20; have polyH59 := Poly.mul polyH19 polyH58; have polyH60 := Poly.add polyH57 polyH59; have polyH61 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) (Uniform.stateRight) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH60; have polyH62 := Poly.add polyH34 polyH61; have polyH63 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (20); have polyH64 := Poly.add polyH3 polyH11; have polyH65 := Poly.add polyH64 polyH40; have polyH66 := Poly.add polyH65 polyH20; have polyH67 := Poly.mul polyH63 polyH66; have polyH68 := Poly.add polyH62 polyH67; have polyH69 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateRight) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateRight) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH68; have polyH70 := Poly.reparam (@Costs.setEq) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Sigma.snd x_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.snd (Sigma.snd x_1)))) polyH0; have polyH71 := Poly.add polyH69 polyH70; have polyH72 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst (Sigma.snd x_1)), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin (Sigma.fst x_1))) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.snd (Sigma.snd x_1)))) polyH11 polyH40; have polyH73 := Poly.add polyH72 polyH20; have polyH74 := Poly.mul polyH19 polyH73; have polyH75 := Poly.add polyH71 polyH74; have polyH76 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (i : ℕ) => Finset (Fin i) × Finset (Fin i)) (fun (n : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => ((fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst x_1), (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Finset (Fin n) × Finset (Fin n)) => Decidable.decide (Prod.fst x_1 = Prod.snd x_1)) (@Uniform.pair ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => Finset (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.fst x_1)) (fun (i : ℕ) (x_1 : OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) => (fun (s : OAI.ThreeMachine.Algorithm.State (Fin i)) => OAI.ThreeMachine.Algorithm.State.right s) (Prod.snd x_1)) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.fst) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.fst ℕ (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateRight) (@Uniform.comp ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i) × OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) (fun (n : ℕ) => Finset (Fin n)) _ _ _ (fun (i : ℕ) => Prod.snd) (fun (n : ℕ) (s : OAI.ThreeMachine.Algorithm.State (Fin n)) => OAI.ThreeMachine.Algorithm.State.right s) (@Uniform.snd ℕ (fun (i : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin i)) (fun (n : ℕ) => OAI.ThreeMachine.Algorithm.State (Fin n)) _ _) Uniform.stateRight)) (Uniform.setEq) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH75; exact Poly.lift polyH76 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem stateEqMR : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqMR.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.stateEqM) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.reparam (@Costs.stateEqR) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (20); have polyH5 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.1); have polyH6 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.2); have polyH7 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2) polyH5 polyH6; have polyH8 := Poly.volumeBool (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1)))); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.volumeBool (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1)))); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (1); have polyH13 := Poly.add polyH11 polyH12; have polyH14 := Poly.mul polyH4 polyH13; have polyH15 := Poly.add polyH3 polyH14; have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.StateEqInput) (fun (n : ℕ) => Bool) (fun (n : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_1))) (Uniform.stateEqM) (Uniform.stateEqR) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH15; have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10000); have polyH18 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (@Realizer.time_and_le ((Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2))), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2)) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2))))))) polyH17; have polyH19 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_uniform (ℕ) (Bool × Bool) (Bool) _ _ (fun (x_1 : Bool × Bool) => Prod.fst x_1 && Prod.snd x_1) (Realizer.and) (Sigma.fst x_2) ((Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_2)) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_2))), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_2)) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_2)))))))) polyH18; have polyH20 := Poly.add polyH16 polyH19; have polyH21 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10); have polyH22 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst (Sigma.snd x_1)) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd (Sigma.snd x_1))), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst (Sigma.snd x_1)) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd (Sigma.snd x_1))))) polyH8 polyH10; have polyH23 := Poly.add polyH22 polyH12; have polyH24 := Poly.mul polyH21 polyH23; have polyH25 := Poly.add polyH20 polyH24; have polyH26 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.StateEqInput) (fun (i : ℕ) => Bool × Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Uniform.StateEqInput i) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_1)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_1)))) (fun (x_1 : ℕ) (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) (@Uniform.pair ℕ Uniform.StateEqInput (fun (n : ℕ) => Bool) (fun (n : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_1))) (fun (n : ℕ) (x_1 : Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_1))) Uniform.stateEqM Uniform.stateEqR) (Realizer.uniform Realizer.and ℕ) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH25; exact Poly.lift polyH26 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem stateEqLMR : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEqLMR.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.stateEqL) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.reparam (@Costs.stateEqMR) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH3 := Poly.add polyH1 polyH2; have polyH4 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (20); have polyH5 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.1); have polyH6 := Poly.volumeState polyH0 (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2.2); have polyH7 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => x_1.2) polyH5 polyH6; have polyH8 := Poly.volumeBool (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_1)) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_1)))); have polyH9 := Poly.add polyH7 polyH8; have polyH10 := Poly.volumeBool (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Prod.fst ((fun (x_2 : Uniform.StateEqInput (Sigma.fst x_1)) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_2) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_2)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_2) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_2)))) (Sigma.snd x_1)) && Prod.snd ((fun (x_2 : Uniform.StateEqInput (Sigma.fst x_1)) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_2) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_2)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_2) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_2)))) (Sigma.snd x_1))); have polyH11 := Poly.add polyH9 polyH10; have polyH12 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (1); have polyH13 := Poly.add polyH11 polyH12; have polyH14 := Poly.mul polyH4 polyH13; have polyH15 := Poly.add polyH3 polyH14; have polyH16 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_pair (ℕ) (Uniform.StateEqInput) (fun (n : ℕ) => Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Uniform.StateEqInput i) => (fun (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) ((fun (x_3 : Uniform.StateEqInput i) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_3) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_3)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_3) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_3)))) x_1)) (Uniform.stateEqL) (Uniform.stateEqMR) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH15; have polyH17 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10000); have polyH18 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (@Realizer.time_and_le ((Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2))), (fun (x_1 : Bool × Bool) => Prod.fst x_1 && Prod.snd x_1) ((fun (x_1 : Uniform.StateEqInput (Sigma.fst x_2)) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_1)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_1)))) (Sigma.snd x_2)))))) polyH17; have polyH19 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_uniform (ℕ) (Bool × Bool) (Bool) _ _ (fun (x_1 : Bool × Bool) => Prod.fst x_1 && Prod.snd x_1) (Realizer.and) (Sigma.fst x_2) ((Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_2)) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_2))), (fun (x_1 : Bool × Bool) => Prod.fst x_1 && Prod.snd x_1) ((fun (x_1 : Uniform.StateEqInput (Sigma.fst x_2)) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_1)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_1)))) (Sigma.snd x_2))))))) polyH18; have polyH20 := Poly.add polyH16 polyH19; have polyH21 := Poly.const (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1) (10); have polyH22 := Poly.volumeProd (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst (Sigma.snd x_1)) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd (Sigma.snd x_1))), (fun (x_2 : Bool × Bool) => Prod.fst x_2 && Prod.snd x_2) ((fun (x_2 : Uniform.StateEqInput (Sigma.fst x_1)) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_2) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_2)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_2) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_2)))) (Sigma.snd x_1)))) polyH8 polyH10; have polyH23 := Poly.add polyH22 polyH12; have polyH24 := Poly.mul polyH21 polyH23; have polyH25 := Poly.add polyH20 polyH24; have polyH26 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_comp (ℕ) (Uniform.StateEqInput) (fun (i : ℕ) => Bool × Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (i : ℕ) (x_1 : Uniform.StateEqInput i) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd x_1)), (fun (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) ((fun (x_3 : Uniform.StateEqInput i) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_3) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_3)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_3) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_3)))) x_1))) (fun (x_1 : ℕ) (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) (@Uniform.pair ℕ Uniform.StateEqInput (fun (n : ℕ) => Bool) (fun (x_1 : ℕ) => Bool) _ _ _ (fun (n : ℕ) (x_1 : Uniform.StateEqInput n) => Decidable.decide (OAI.ThreeMachine.Algorithm.State.left (Prod.fst x_1) = OAI.ThreeMachine.Algorithm.State.left (Prod.snd x_1))) (fun (i : ℕ) (x_1 : Uniform.StateEqInput i) => (fun (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) ((fun (x_3 : Uniform.StateEqInput i) => (Decidable.decide (OAI.ThreeMachine.Algorithm.State.middle (Prod.fst x_3) = OAI.ThreeMachine.Algorithm.State.middle (Prod.snd x_3)), Decidable.decide (OAI.ThreeMachine.Algorithm.State.right (Prod.fst x_3) = OAI.ThreeMachine.Algorithm.State.right (Prod.snd x_3)))) x_1)) Uniform.stateEqL Uniform.stateEqMR) (Realizer.uniform Realizer.and ℕ) (Sigma.fst x_2) (Sigma.snd x_2)))) polyH25; exact Poly.lift polyH26 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem stateEq : Poly (fun x : Σ n, Uniform.StateEqInput n => x.1)
    (fun x => Uniform.stateEq.time x.1 x.2) 4 := by (have polyH0 := Poly.size (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.fst x_1); have polyH1 := Poly.reparam (@Costs.stateEqLMR) (fun (x_1 : (n : ℕ) × Uniform.StateEqInput n) => Sigma.mk (Sigma.fst x_1) (Sigma.snd x_1)) polyH0; have polyH2 := Poly.of_le (fun (x_2 : (n : ℕ) × Uniform.StateEqInput n) => (le_of_eq (@Uniform.time_stateEq (Sigma.fst x_2) (Sigma.snd x_2)))) polyH1; exact Poly.lift polyH2 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module StateBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.Algorithm

end ThreeMachine.Algorithm

namespace ThreeMachine.StackCompiler
open ThreeMachine.Algorithm

def BlockSmall {n : ℕ} (b : Algorithm.Block (Fin n)) : Prop :=
  b.length ≤ n ∧ ∀ v, b.time v ≤ n

def TableSmall {n : ℕ} (tab : Table n) : Prop := ∀ W b, (W,b) ∈ tab → BlockSmall b

def MarksSmall {n : ℕ} (marks : Marks n) : Prop := ∀ u b, (u,b) ∈ marks → BlockSmall b

namespace Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

namespace Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace Uniform
variable {I : Type u1} {α : I → Type u2} [∀ i, Coding (α i)]

end Uniform
namespace Realizer
variable {α : Type u3} [Coding α]

end Realizer
namespace Uniform
variable {I : Type u4} {α : I → Type u5} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u6} {J : Type u7} {s : J → ℕ} {α : I → Type u8} [∀ i, Coding (α i)]
abbrev IterPool (m : J → ℕ) := Σ j, Fin (m j+1)

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s : J → ℕ} {d e : ℕ} {α β : J → Type}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
open Algorithm
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

end ThreeMachine.StackCompiler.Poly
end

end OAI
end


section
-- module TransitionCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev StatesInput (n : ℕ) := Universe n × (Matrix n ×
    (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n))))
def statesC : Uniform (fun n (x : (Finset (Fin n) × Finset (Fin n)) ×
    (Universe n × Finset (Fin n))) => Algorithm.State.candidate x.2.2 x.1.1 x.1.2) :=
  ((snd.comp fst).pair ((snd.comp snd).pair ((fst.comp fst).pair (fst.comp snd)))).comp stateCandidate
def statesF : Uniform (fun n (x : StatesInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def statesZ : Uniform (fun n (x : StatesInput n) => x.2.2.2.1) := snd.comp (snd.comp (snd.comp fst))
def statesW : Uniform (fun n (x : StatesInput n) => x.2.2.2.2) := snd.comp (snd.comp (snd.comp snd))
def statesPairs := (statesF.pair statesZ).comp product
def statesS := (statesPairs.pair (fst.pair statesW)).comp statesC.map
def statesP : Uniform (fun n (x : Algorithm.State (Fin n) ×
    (Universe n × (Matrix n × Finset (Fin n)))) =>
    decide (x.1.Compatible (matrixRel x.2.2.1) x.2.2.2)) :=
  ((snd.comp fst).pair ((snd.comp (snd.comp fst)).pair ((snd.comp (snd.comp snd)).pair fst))).comp stateCompatible

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (fs zs : ∀ j, List (Finset (Fin (n j)))) (W : ∀ j, Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev BlockAppendCellInput (n : ℕ) := Fin n ×
  (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))
def appendCellS : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def appendCellT : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def appendCellTest : Uniform (fun n (x : BlockAppendCellInput n) => decide (x.1 ∈ x.2.1)) :=
  (fst.pair (snd.comp fst)).comp setMem
def appendCellLeft : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.1.time x.1) :=
  (((appendCellS.comp blockTime).pair fst).comp functionGet)
def appendCellRight : Uniform (fun n (x : BlockAppendCellInput n) => x.2.2.1.length+x.2.2.2.time x.1) :=
  (((appendCellS.comp blockLength).pair (((appendCellT.comp blockTime).pair fst).comp functionGet)).comp
    (Realizer.add.uniform ℕ))
def appendCell : Uniform (fun n (x : BlockAppendCellInput n) =>
    if x.1 ∈ x.2.1 then x.2.2.1.time x.1 else x.2.2.1.length+x.2.2.2.time x.1) :=
  (appendCellTest.ite appendCellLeft appendCellRight).congr (fun _ _ => by simp)
abbrev BlockAppendInput (n : ℕ) := Universe n ×
    (Finset (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))
def appendLength : Uniform (fun n (x : BlockAppendInput n) => x.2.2.1.length+x.2.2.2.length) :=
  ((((snd.comp (snd.comp fst)).comp blockLength).pair
      ((snd.comp (snd.comp snd)).comp blockLength)).comp (Realizer.add.uniform ℕ))
def blockAppendNamed : Uniform (fun n (x : BlockAppendInput n) =>
    Algorithm.Block.append x.2.1 x.2.2.1 x.2.2.2) :=
  (appendLength.pair appendCell.vectorMap).comp blockMake

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.BlockAppendCellInput (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
def appendVector := appendCell.vectorMap

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (W : ∀ j, Finset (Fin (n j)))
variable (b c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev AdvanceInput (n : ℕ) := Universe n ×
    (Algorithm.State (Fin n) × (Algorithm.Block (Fin n) × Algorithm.Block (Fin n)))
def advanceU : Uniform (fun n (x : AdvanceInput n) => x.1) := fst
def advanceV : Uniform (fun n (x : AdvanceInput n) => x.2.1) := snd.comp fst
def advanceS : Uniform (fun n (x : AdvanceInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def advanceT : Uniform (fun n (x : AdvanceInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def advanceB : Uniform (fun n (x : AdvanceInput n) =>
    Algorithm.Block.append x.2.1.left x.2.2.1 Algorithm.Block.triple) :=
  (advanceU.pair ((advanceV.comp stateLeft).pair
    (advanceS.pair (advanceU.comp blockTriple)))).comp blockAppend

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (v : ∀ j, Algorithm.State (Fin (n j))) (b c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u5} {α : I → Type u6} {β : I → Type u7} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev TryInput (n : ℕ) := Universe n ×
    (Table n × ((Algorithm.State (Fin n) × Algorithm.Block (Fin n)) × Algorithm.State (Fin n)))
def tryU : Uniform (fun n (x : TryInput n) => x.1) := fst
def tryT : Uniform (fun n (x : TryInput n) => x.2.1) := snd.comp fst
def tryA : Uniform (fun n (x : TryInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def tryV : Uniform (fun n (x : TryInput n) => x.2.2.2) := snd.comp (snd.comp snd)
def tryW := (tryU.pair (tryA.comp fst)).comp stateUpto
def tryL := tryV.comp stateLeft
def tryP := (tryW.pair tryL).comp setSubset
def tryDiff := (tryL.pair tryW).comp setDiff
def tryO := (tryT.pair tryDiff).comp (lookupA setEq)
def tryWork := (tryO.pair (tryU.pair tryA)).comp advanceLast.optionMap

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (c : ∀ j, Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module SolverCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))
variable (v : ∀ j, Algorithm.State (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (u : ∀ j, Algorithm.State (Fin (n j)) × Algorithm.Block (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev SolveInput (n : ℕ) := Universe n × (Matrix n ×
  (Table n × (List (Finset (Fin n)) × (List (Finset (Fin n)) × Finset (Fin n)))))
def solveU : Uniform (fun n (x : SolveInput n) => x.1) := fst
def solveM : Uniform (fun n (x : SolveInput n) => x.2.1) := snd.comp fst
def solveT : Uniform (fun n (x : SolveInput n) => x.2.2.1) := snd.comp (snd.comp fst)
def solveF : Uniform (fun n (x : SolveInput n) => x.2.2.2.1) := snd.comp (snd.comp (snd.comp fst))
def solveZ : Uniform (fun n (x : SolveInput n) => x.2.2.2.2.1) := snd.comp (snd.comp (snd.comp (snd.comp fst)))
def solveW : Uniform (fun n (x : SolveInput n) => x.2.2.2.2.2) := snd.comp (snd.comp (snd.comp (snd.comp snd)))
def solveS : Uniform (fun n (x : SolveInput n) =>
    Algorithm.states (matrixRel x.2.1) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) := (solveU.pair (solveM.pair (solveF.pair (solveZ.pair solveW)))).comp states
def solveMarks : Uniform (fun n (x : SolveInput n) =>
    Algorithm.markings x.2.2.1 (Algorithm.states (matrixRel x.2.1) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) n) := ((solveU.comp universeNumber).pair (solveU.pair (solveT.pair solveS))).comp markings
def solveOut : Uniform (fun n (x : SolveInput n) =>
    Algorithm.firstResult (fun u => (Algorithm.lookup x.2.2.1 u.1.right).map (u.1.finish u.2))
      (Algorithm.markings x.2.2.1 (Algorithm.states (matrixRel x.2.1) x.2.2.2.1 x.2.2.2.2.1 x.2.2.2.2.2) n)) := (solveMarks.pair (solveU.pair solveT)).comp finishing.firstResultA

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d : ℕ}

end ThreeMachine.StackCompiler.Poly
end

end OAI
end


section
-- module TableCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
def tableBody {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) :
    Uniform (fun i (x : α i × γ i) => (f i x).map (fun b => (x.1,b))) :=
  (R.pair fst).comp ((swap : Uniform (fun i (x : β i × α i) => (x.2,x.1))).optionMap)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler
variable {α : Type u5} {β : Type u6} [Coding α] [Coding β]

end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u7} {J : Type u8} {s : J → ℕ} {α : I → Type u9} {β : I → Type u10} {γ : I → Type u11}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev eval {I : Type u12} {α : I → Type u13} {β : I → Type u14} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
    {f : ∀ i, α i → β i} (_R : Uniform f) := f
end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)
variable (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (ms : ∀ j, Marks (n j)) (v : ∀ j, Algorithm.State (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n : J → ℕ} {d l : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform
def initialMarkBody : Uniform (fun n (x : Algorithm.State (Fin n) × Table n) => Algorithm.lookup x.2 x.1.left) :=
  (snd.pair (fst.comp stateLeft)).comp (lookupA setEq)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (tab : ∀ j, Table (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev MarkEnv (n : ℕ) := Universe n × (Table n × List (Algorithm.State (Fin n)))
def markingsStep : Uniform (fun n (x : MarkEnv n × Marks n) =>
    (x.1,Algorithm.expand x.1.2.1 x.1.2.2 x.2)) :=
  fst.pair ((((fst.comp fst).pair ((fst.comp (snd.comp fst)).pair
      ((fst.comp (snd.comp snd)).pair snd)))).comp expand)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (tab : ∀ j, Table (n j))
variable (sts : ∀ j, List (Algorithm.State (Fin (n j))))

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (sts : ∀ j, List (Algorithm.State (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module MatrixCosts
namespace OAI

universe u1 u2 u3 u4 u5

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev LayerEnv (n : ℕ) := Universe n × (Matrix n × (List (Finset (Fin n)) × List (Finset (Fin n))))
def layerBody : Uniform (fun n (x : Finset (Fin n) × (LayerEnv n × Table n)) =>
    Algorithm.solve (matrixRel x.2.1.2.1) x.2.2 x.2.1.2.2.1 x.2.1.2.2.2 x.1) :=
  ((snd.comp (fst.comp fst)).pair ((snd.comp (fst.comp (snd.comp fst))).pair
      ((snd.comp snd).pair ((snd.comp (fst.comp (snd.comp (snd.comp fst)))).pair
        ((snd.comp (fst.comp (snd.comp (snd.comp snd)))).pair fst))))).comp solve

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler

namespace Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))
variable (W : ∀ j, Finset (Fin (n j)))

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u5} (s n : J → ℕ) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

def paddedCell : Uniform (fun (i : ℕ × ℕ) (x : (Fin i.2 × Fin i.2) × Matrix i.1) =>
      readMatrix x.2 x.1.1.val x.1.2.val) :=
    (snd.pair (((fst.comp fst).comp (finValue Prod.snd)).pair
      ((fst.comp snd).comp (finValue Prod.snd)))).comp (matrixReadNat.reindex Prod.fst)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module ScheduleBounds
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u1} {s n B : J → ℕ} {d e : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler
open Algorithm

namespace Poly
variable {J : Type} (s n T : J → ℕ) (M : ∀ j, Matrix (n j))

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Realizer

end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u2}

def restrictCell : Uniform (fun (i : ℕ × ℕ) (x : Fin i.1 × (Fin i.2 → ℕ)) =>
      (List.ofFn x.2).getD x.1.val 0) :=
    ((((snd.comp (functionListAny Prod.snd)).pair (fst.comp (finValue Prod.fst))).pair zero).comp getElemD)

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n m : J → ℕ) (r : ∀ j, Fin (m j) → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type} {s n m : J → ℕ} {d e : ℕ}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev PredecessorInput (n : ℕ) := Fin n × (Matrix n × Fin n)
def predecessorCell : Uniform (fun n (x : PredecessorInput n) => x.2.1 x.1 x.2.2) :=
  ((snd.comp fst).pair (fst.pair (snd.comp snd))).comp matrixGet

abbrev PredecessorsInput (n : ℕ) := Fin n × (Universe n × Matrix n)
def predecessorsBody : Uniform (fun n (x : PredecessorsInput n) =>
    Structure.predecessorCount (matrixRel x.2.2) x.1) :=
  ((snd.comp fst).pair ((snd.comp snd).pair fst)).comp predecessorCount

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
noncomputable section
namespace ThreeMachine.StackCompiler.Uniform
abbrev RankCellInput (n : ℕ) := Fin n × ((Fin n → ℕ) × Fin n)
def rankCellA : Uniform (fun n (x : RankCellInput n) => x.2.1 x.1) :=
  ((snd.comp fst).pair fst).comp functionGet
def rankCellB : Uniform (fun n (x : RankCellInput n) => x.2.1 x.2.2) :=
  ((snd.comp fst).pair (snd.comp snd)).comp functionGet
def rankCellLT := (rankCellA.pair rankCellB).comp natLT
def rankCellEQ := (rankCellA.pair rankCellB).comp (Realizer.eqNat.uniform ℕ)
def rankCellFinLT : Uniform (fun n (x : RankCellInput n) => decide (x.1 < x.2.2)) :=
  ((fst.comp finVal).pair ((snd.comp snd).comp finVal)).comp natLT
def rankCell := rankCellLT.orD (rankCellEQ.andD rankCellFinLT)

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
end

end

end OAI
end


section
-- module RankCosts
namespace OAI

universe u1 u2

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u1} (n : J → ℕ) (x : ∀ j, Uniform.RankCellInput (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type u2} (n : J → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev ThresholdInput (n : ℕ) := Fin n × (ℕ × (Fin n → ℕ))
def thresholdA : Uniform (fun n (x : ThresholdInput n) => x.2.2 x.1) :=
  ((snd.comp snd).pair fst).comp functionGet
def thresholdB : Uniform (fun n (x : ThresholdInput n) => x.2.1) := snd.comp fst
def thresholdP (upper : Bool) : Uniform (fun n (x : ThresholdInput n) =>
    decide (if upper then x.2.2 x.1 ≤ x.2.1 else x.2.1 ≤ x.2.2 x.1)) := by
  cases upper
  · exact (thresholdB.pair thresholdA).comp (Realizer.le.uniform ℕ)
  · exact (thresholdA.pair thresholdB).comp (Realizer.le.uniform ℕ)
def thresholdF (upper : Bool) : Uniform (fun n (x : ℕ × (Universe n × (Fin n → ℕ))) =>
    Finset.univ.filter (fun v => decide (if upper then x.2.2 v ≤ x.1 else x.1 ≤ x.2.2 v) = true)) :=
  (((snd.comp fst).comp universeSet).pair (fst.pair (snd.comp snd))).comp (thresholdP upper).setFilter
def thresholdN : Uniform (fun n (_ : Universe n × (Fin n → ℕ)) => List.range (n+2)) :=
  (((fst.comp universeNumber).pair (constant 2)).comp (Realizer.add.uniform ℕ)).comp (Realizer.range.uniform ℕ)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
def triplesE := (universeList.pair (universeList.pair universeList |>.comp product)).comp product
def triplesA := (triplesE.pair id).comp (swap.comp tripleSet).map
def triplesP : Uniform (fun n (x : Finset (Fin n) × Unit) => decide (x.1.card = 3)) :=
  (((fst.comp setCard).pair (constant 3)).comp (Realizer.eqNat.uniform ℕ))

def conesF (frame : Bool) (k : Fin 5) :=
  ((((snd.comp fst).pair ((snd.comp snd).pair fst))).comp (cone frame k))
def conesOne (frame : Bool) (k : Fin 5) :=
  (((fst.comp triples).pair id).comp (conesF frame k).map)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module FamilyCosts
namespace OAI

universe u1

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]

def assignmentsInner (k : ℕ) : Uniform (fun i (x : α i × List (Fin k → α i)) =>
    x.2.map (fun f => (Fin.cons x.1 f : Fin (k+1) → α i))) :=
  ((snd.pair fst).comp (swap.comp (finCons k)).map)
def assignmentsStep (k : ℕ) : Uniform (fun i (x : List (α i) × List (Fin k → α i)) =>
    x.1.flatMap (fun a => x.2.map (fun f => (Fin.cons a f : Fin (k+1) → α i)))) := (assignmentsInner k).flatMap

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (k : ℕ)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (xs : ∀ j, List (Finset (Fin (n j))))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j))
variable {K : ℕ} (r : ∀ j, Fin K → Finset (Fin (n j)))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

def atomSetsC : Uniform (fun n (_ : Universe n × Matrix n) => [∅, (Finset.univ : Finset (Fin n))]) :=
  (((fst.comp setEmpty).pair (((fst.comp universeSet).pair nil).comp cons)).comp cons)
def atomSetsT := ((thresholds Bool.false).pair (thresholds true)).comp append
def atomSetsD := ((cones Bool.false (List.finRange 5)).pair (cones true (List.finRange 5))).comp append

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure
variable {J : Type}

end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure
def familyAssignments (K : ℕ) := atomSets.comp (assignments K)
def familyEval (K : ℕ) := swap.comp (evalTemplates (Formula.templates K))
def familyFlatten (K : ℕ) := (familyEval K).flatMap

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Costs
end

section

end

end OAI
end


section
-- module SchedulingCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (tab : ∀ j, Table (n j)) (fs zs : ∀ j, List (Finset (Fin (n j))))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
open ThreeMachine.Structure

def fullLayers (K : ℕ) : Uniform (fun n (x : Universe n × Matrix n) =>
    Algorithm.layers (matrixRel x.2)
      (effectiveFamily (matrixRel x.2) (jobRank (matrixRel x.2))
        (reverseJobRank (matrixRel x.2)) (List.finRange n) K)
      ((tripleList (List.finRange n)).map Subtype.val) n) :=
  (((fst.comp universeNumber).pair (fst.pair (snd.pair ((family K).pair (fst.comp triples))))).comp layers)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open ThreeMachine.Structure

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

def scheduleRestriction : Uniform (fun (i : ℕ × ℕ) (x : Algorithm.Block (Fin (3*i.2)) × Universe i.1) =>
    (fun v : Fin i.1 => (List.ofFn x.1.time).getD v.val 0)) :=
  (snd.pair (fst.comp (blockTime.reindex (fun i : ℕ × ℕ => 3*i.2)))).comp
    (restrictTime.reindex (fun i : ℕ × ℕ => (i.1,3*i.2)))
def scheduleCandidate : Uniform (fun (i : ℕ × ℕ) (x : Universe i.1 × (Cardinal i.2 × Matrix i.1)) =>
    (Algorithm.fullSolve (paddedOrder (matrixRel x.2.2) (3*i.2))).map
      (fun (b : Algorithm.Block (Fin (3*i.2))) => (fun v : Fin i.1 => (List.ofFn b.time).getD v.val 0))) :=
  ((snd.comp paddedSolve).pair fst).comp scheduleRestriction.optionMap

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
abbrev ScheduleInput (i : ℕ × ℕ) := Universe i.1 × (Cardinal i.2 × Matrix i.1)

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module OptimumCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12

section
namespace ThreeMachine.StackCompiler.Uniform
abbrev BestState (n : ℕ) := (Universe n × Matrix n) × (ℕ × Option (ℕ × (Fin n → ℕ)))
def bestNext : Uniform (fun (n : ℕ) (x : BestState n) => x.2.1+1) :=
  (snd.comp fst).comp (Realizer.succ.uniform ℕ)
def bestAttempt : Uniform (fun (n : ℕ) (x : BestState n) =>
    (ThreeMachine.StackCompiler.scheduleMatrix x.1.2 (x.2.1+1)).map (fun t => (x.2.1+1,t))) :=
  ((((fst.comp fst).pair (bestNext.pair (fst.comp snd))).comp scheduleMatrix).pair bestNext).comp swap.optionMap

def bestRetain : Uniform (fun (n : ℕ) (x : BestState n) =>
    if x.2.2.isSome then x.2.2 else
    (ThreeMachine.StackCompiler.scheduleMatrix x.1.2 (x.2.1+1)).map (fun t => (x.2.1+1,t))) :=
  (((snd.comp snd).comp optionIsSome).pair id).comp ((snd.comp snd).choose bestAttempt)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} {γ : I → Type u4}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → Option (β i)} {g : ∀ i, α i → γ i}

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u5} {J : Type u6} {s : J → ℕ} {α : I → Type u7} {β : I → Type u8} {γ : I → Type u9}
variable [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable {f : ∀ i, α i → β i} {g : ∀ i, β i → γ i}
variable (R : Uniform f) (S : Uniform g) (idx : J → I) (x : ∀ j, α (idx j)) {d : ℕ}

variable {g' : ∀ i, α i → γ i}

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))
variable (k : J → ℕ) (o : ∀ j, Option (ℕ × (Fin (n j) → ℕ)))
variable (hn : Poly s n 1) (hk : Poly s k 1) (ho : Poly s (fun j => volume (o j)) 2)
include hn hk ho

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u10} {J : Type u11} {s : J → ℕ} {α : I → Type u12} [∀ i, Coding (α i)]
abbrev StrictIterPool (m : J → ℕ) := Σ j, Fin (m j)

end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module OutputCosts
namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type u2} {β : I → Type u3} [∀ i, Coding (α i)] [∀ i, Coding (β i)]

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler
@[simp] theorem volume_optionFunctionList {n : ℕ} (o : Option (Fin n → ℕ)) :
    volume (o.map List.ofFn) = volume o := by cases o <;> rfl

end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
@[simp] theorem volume_instance {n : ℕ} (G : Instance n) : volume G = volume G.edges := rfl
namespace Poly
variable {J : Type} {s n : J → ℕ} {d e : ℕ}

end Poly
namespace Costs

end Costs
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module Parser
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

section

namespace ThreeMachine.StackCompiler.Binary

def value : List Bool → ℕ
  | [] => 0
  | b :: bs => 2*value bs + if b then 1 else 0

def increment : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: increment bs

def leading (bs : List Bool) : ℕ := (bs.takeWhile id).length

@[simp] theorem leading_nil : leading [] = 0 := rfl
@[simp] theorem leading_false (bs : List Bool) : leading (false :: bs) = 0 := rfl
@[simp] theorem leading_true (bs : List Bool) : leading (true :: bs) = leading bs+1 := by
  simp only [leading,List.takeWhile_cons,id_eq,ite_true,List.length_cons]

theorem increment_formula (bs : List Bool) :
    increment bs = List.replicate (leading bs) false ++ true :: bs.drop (leading bs+1) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | false => rfl
    | true => simp only [increment,leading_true,List.replicate_succ,List.cons_append,
        List.drop_succ_cons,ih]

theorem increment_encodePosNum (p : PosNum) :
    increment (Computability.encodePosNum p) = Computability.encodePosNum p.succ := by
  induction p with
  | one => rfl
  | bit0 p ih => rfl
  | bit1 p ih => simpa only [Computability.encodePosNum,PosNum.succ,increment] using congrArg (List.cons false) ih

theorem increment_encodeNum (p : Num) :
    increment (Computability.encodeNum p) = Computability.encodeNum p.succ := by
  cases p with
  | zero => rfl
  | pos p => exact increment_encodePosNum p

theorem increment_encodeNat (n : ℕ) :
    increment (Computability.encodeNat n) = Computability.encodeNat (n+1) := by
  unfold Computability.encodeNat
  rw [increment_encodeNum]
  congr 1
  apply Num.to_nat_inj.mp
  simp only [Num.succ_to_nat,Num.to_of_nat]

theorem iterate_increment (n : ℕ) : increment^[n] [] = Computability.encodeNat n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply',ih,increment_encodeNat]

theorem value_encodePosNum (p : PosNum) : value (Computability.encodePosNum p) = (p : ℕ) := by
  induction p with
  | one => rfl
  | bit0 p ih => simp only [Computability.encodePosNum,value,ih,PosNum.cast_bit0,Bool.false_eq_true,ite_false]; omega
  | bit1 p ih => simp only [Computability.encodePosNum,value,ih,PosNum.cast_bit1,ite_true]; omega

theorem value_encodeNat (n : ℕ) : value (Computability.encodeNat n) = n := by
  have h : ∀ p : Num, value (Computability.encodeNum p) = (p : ℕ) := by
    intro p; cases p with
    | zero => rfl
    | pos p => exact value_encodePosNum p
  simpa only [Computability.encodeNat,Num.to_of_nat] using h (n : Num)

def leadingStep (x : Bool × (Bool × ℕ)) : Bool × ℕ :=
  if x.2.1 && x.1 then (true,x.2.2+1) else (false,x.2.2)

theorem leading_fold (bs : List Bool) (b : Bool) (k : ℕ) :
    (bs.foldl (fun s a => leadingStep (a,s)) (b,k)).2 = k+if b then leading bs else 0 := by
  induction bs generalizing b k with
  | nil => simp
  | cons a bs ih =>
    rw [List.foldl_cons]
    cases a <;> cases b
    · change (bs.foldl (fun s a => leadingStep (a,s)) (false,k)).2 = k+0
      rw [ih]; rfl
    · change (bs.foldl (fun s a => leadingStep (a,s)) (false,k)).2 = k+0
      rw [ih]; rfl
    · change (bs.foldl (fun s a => leadingStep (a,s)) (false,k)).2 = k+0
      rw [ih]; rfl
    · change (bs.foldl (fun s a => leadingStep (a,s)) (true,k+1)).2 = k+leading (true :: bs)
      rw [ih,leading_true]; simp only [ite_true]; omega

def takeStep {α : Type u1} (x : List α × List α) : List α × List α :=
  (x.1.tail,match x.1 with | [] => x.2 | a :: _ => a :: x.2)

theorem takeStep_iterate {α : Type u2} (n : ℕ) (xs ys : List α) :
    takeStep^[n] (xs,ys) = (xs.drop n,(xs.take n).reverse ++ ys) := by
  induction n generalizing xs ys with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    cases xs with
    | nil => simp only [takeStep,ih,List.tail_nil,List.drop_nil,List.take_nil,List.reverse_nil,List.nil_append]
    | cons a xs =>
      simp only [takeStep,List.tail_cons,ih,List.drop_succ_cons,List.take_succ_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

def valueStep (x : Bool × ℕ) : ℕ := 2*x.2+if x.1 then 1 else 0

theorem value_fold (bs : List Bool) :
    bs.reverse.foldl (fun k b => valueStep (b,k)) 0 = value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [List.reverse_cons,List.foldl_append]
    change valueStep (b,bs.reverse.foldl (fun k b => valueStep (b,k)) 0) = _
    rw [ih]; rfl

def readNat (bs : List Bool) : ℕ × List Bool :=
  let k := leading bs
  let tail := bs.drop (k+1)
  (value (tail.take k),tail.drop k)

theorem leading_encodeNat (n : ℕ) (rest : List Bool) :
    leading (ThreeMachine.encodeNat n ++ rest) = (Computability.encodeNat n).length := by
  have h : ∀ k, leading (List.replicate k true ++ false :: (Computability.encodeNat n ++ rest)) = k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih => simp only [List.replicate_succ,List.cons_append,leading_true,ih]
  simpa only [ThreeMachine.encodeNat,List.append_assoc,List.cons_append] using h (Computability.encodeNat n).length

theorem readNat_encodeNat (n : ℕ) (rest : List Bool) :
    readNat (ThreeMachine.encodeNat n ++ rest) = (n,rest) := by
  unfold readNat
  rw [leading_encodeNat]
  simp only [ThreeMachine.encodeNat,List.append_assoc,List.cons_append]
  have hdrop : (List.replicate (Computability.encodeNat n).length true ++
      false :: (Computability.encodeNat n ++ rest)).drop ((Computability.encodeNat n).length+1) =
      Computability.encodeNat n ++ rest := by
    rw [← List.drop_drop, List.drop_left' (by simp)]
    rfl
  rw [hdrop,List.take_left,List.drop_left,value_encodeNat]

end ThreeMachine.StackCompiler.Binary

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u3} {α : I → Type u4} [∀ i, Coding (α i)]

def replicate : Uniform (fun i (x : ℕ × α i) => List.replicate x.1 x.2) :=
  ((Realizer.unroll.uniform I).onFst.comp snd.map).congr (fun _ x => by
    simp only [Function.comp_apply,List.map_replicate])

def binaryLeadingStep : Uniform (fun (_ : I) => Binary.leadingStep) :=
  ((((snd.comp fst).pair fst).comp (Realizer.and.uniform I)).ite
    ((constant true).pair ((snd.comp snd).comp (Realizer.succ.uniform I)))
    (false.pair (snd.comp snd))).congr (fun _ _ => rfl)

def binaryLeading : Uniform (fun (_ : I) => Binary.leading) :=
  ((((id.pair ((constant true).pair zero)).comp binaryLeadingStep.fold).comp snd)).congr
    (fun _ bs => by simpa only [Function.comp_apply,Nat.zero_add,ite_true] using Binary.leading_fold bs true 0)

def takeStep : Uniform (fun i => @Binary.takeStep (α i)) := by
  let A : Uniform (fun i (x : List (α i) × List (α i)) => x.1.head?.map (fun a => a :: x.2)) := ((fst.comp head?).pair snd).comp cons.optionMap
  exact ((fst.comp tail).pair ((A.pair snd).comp getD)).congr (fun _ x => by
    rcases x with ⟨xs,ys⟩; cases xs <;> rfl)

def take : Uniform (fun i (x : List (α i) × ℕ) => x.1.take x.2) :=
  ((((snd.pair (fst.pair nil)).comp takeStep.iterate).comp (snd.comp reverse))).congr
    (fun _ x => by simp only [Function.comp_apply,Binary.takeStep_iterate,List.append_nil,List.reverse_reverse])

def binaryValueStep : Uniform (fun (_ : I) => Binary.valueStep) :=
  (((((snd.pair snd).comp (Realizer.add.uniform I)).pair
    (fst.ite (constant 1) zero)).comp (Realizer.add.uniform I))).congr (fun _ x => by
      dsimp only [Function.comp_apply,Binary.valueStep]; omega)

def binaryValue : Uniform (fun (_ : I) => Binary.value) :=
  (((reverse.pair zero).comp binaryValueStep.fold)).congr (fun _ bs => Binary.value_fold bs)

def binaryReadNat : Uniform (fun (_ : I) => Binary.readNat) := by
  let K : Uniform (fun (_ : I) => Binary.leading) := binaryLeading
  let Tail : Uniform (fun (_ : I) (bs : List Bool) => bs.drop (Binary.leading bs+1)) :=
    (id.pair (K.comp (Realizer.succ.uniform I))).comp drop
  exact ((((Tail.pair K).comp take).comp binaryValue).pair ((Tail.pair K).comp drop)).congr
    (fun _ _ => rfl)

def binaryIncrement : Uniform (fun (_ : I) => Binary.increment) := by
  let A : Uniform (fun (_ : I) (bs : List Bool) => List.replicate (Binary.leading bs) Bool.false) :=
    (binaryLeading.pair false).comp replicate
  let Tail : Uniform (fun (_ : I) (bs : List Bool) => bs.drop (Binary.leading bs+1)) :=
    (id.pair (binaryLeading.comp (Realizer.succ.uniform I))).comp drop
  exact ((A.pair (((constant true).pair Tail).comp cons)).comp append).congr
    (fun _ bs => (Binary.increment_formula bs).symm)

def rawEncodeNat : Uniform (fun (_ : I) => Computability.encodeNat) :=
  (((id.pair nil).comp binaryIncrement.iterate)).congr (fun _ n => Binary.iterate_increment n)

def binaryEncodeNat : Uniform (fun (_ : I) => ThreeMachine.encodeNat) :=
  (((((rawEncodeNat.comp length).pair (constant true)).comp replicate).pair
    ((false.pair rawEncodeNat).comp cons)).comp append).congr (fun _ _ => rfl)

def binaryEncodeList : Uniform (fun (_ : I) (xs : List ℕ) => ThreeMachine.encodeList ThreeMachine.encodeNat xs) :=
  (((length.comp binaryEncodeNat).pair (binaryEncodeNat.mapList.comp flatten)).comp append).congr
    (fun _ _ => rfl)

def binaryEncodeAnswer : Uniform (fun (_ : I) => ThreeMachine.encodeAnswer) := by
  let A := (((id.pair nil).comp getD).comp binaryEncodeList :
    Uniform (fun (_ : I) (o : Option (List ℕ)) => ThreeMachine.encodeList ThreeMachine.encodeNat (o.getD [])))
  exact (optionIsSome.ite (((constant true).pair A).comp cons) (constant [Bool.false])).congr
    (fun _ o => by cases o <;> rfl)

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u5}

def readStep (reader : List Bool → α × List Bool) (x : List Bool × List α) : List Bool × List α :=
  let a := reader x.1
  (a.2,a.1 :: x.2)

def readMany (reader : List Bool → α × List Bool) (k : ℕ) (bs : List Bool) : List α × List Bool :=
  let x := (readStep reader)^[k] (bs,[])
  (x.2.reverse,x.1)

theorem readStep_iterate {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool) (acc : List α) :
    (readStep reader)^[xs.length] (xs.flatMap encode ++ rest,acc) = (rest,xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.length_cons,Function.iterate_succ_apply]
    simp only [List.flatMap_cons,List.append_assoc,readStep,hr]
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem readMany_correct {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool) :
    readMany reader xs.length (xs.flatMap encode ++ rest) = (xs,rest) := by
  simp only [readMany,readStep_iterate hr,List.append_nil,List.reverse_reverse]

def readList (reader : List Bool → α × List Bool) (bs : List Bool) : List α × List Bool :=
  let a := readNat bs
  readMany reader a.1 a.2

theorem readList_correct {α : Type} {encode : α → List Bool} {reader : List Bool → α × List Bool}
    (hr : ∀ a rest, reader (encode a ++ rest) = (a,rest)) (xs : List α) (rest : List Bool) :
    readList reader (ThreeMachine.encodeList encode xs ++ rest) = (xs,rest) := by
  simp only [readList,ThreeMachine.encodeList,List.append_assoc,readNat_encodeNat]
  exact readMany_correct hr xs rest

def encodeEdge (e : ℕ × ℕ) : List Bool := ThreeMachine.encodeNat (e.1+1) ++ ThreeMachine.encodeNat (e.2+1)

def readEdge (bs : List Bool) : (ℕ × ℕ) × List Bool :=
  let a := readNat bs
  let b := readNat a.2
  ((a.1-1,b.1-1),b.2)

theorem readEdge_correct (e : ℕ × ℕ) (rest : List Bool) :
    readEdge (encodeEdge e ++ rest) = (e,rest) := by
  simp only [readEdge,encodeEdge,List.append_assoc,readNat_encodeNat,Nat.add_sub_cancel]

def readHeader (bs : List Bool) : Option ℕ × List Bool :=
  if bs.head?.getD false then
    let a := readNat bs.tail
    (some a.1,a.2)
  else (none,bs.tail)

def encodeHeader : Option ℕ → List Bool
  | none => [false]
  | some T => true :: ThreeMachine.encodeNat T

theorem readHeader_correct (d : Option ℕ) (rest : List Bool) :
    readHeader (encodeHeader d ++ rest) = (d,rest) := by
  cases d with
  | none => rfl
  | some T =>
    simp only [encodeHeader,List.cons_append,readHeader,List.head?_cons,Option.getD_some,
      ite_true,List.tail_cons,readNat_encodeNat]

def parse (bs : List Bool) : ℕ × (List (ℕ × ℕ) × Option ℕ) :=
  let a := readHeader bs
  let v := readList readNat a.2
  let e := readList readEdge v.2
  (v.1.length,(e.1,a.1))

theorem encodeEdges_map {n : ℕ} (G : Instance n) :
    ThreeMachine.encodeList
      (fun e : Fin n × Fin n => ThreeMachine.encodeNat (e.1.val+1) ++ ThreeMachine.encodeNat (e.2.val+1)) G.edges =
    ThreeMachine.encodeList encodeEdge (G.edges.map (fun e => (e.1.val,e.2.val))) := by
  simp only [ThreeMachine.encodeList,List.length_map,List.flatMap_map,encodeEdge]

theorem parse_input {n : ℕ} (G : Instance n) (d : Option ℕ) :
    parse (ThreeMachine.encodeInput G d) = (n,(G.edges.map (fun e => (e.1.val,e.2.val)),d)) := by
  have he : ThreeMachine.encodeInput G d = encodeHeader d ++
      (ThreeMachine.encodeList ThreeMachine.encodeNat ((List.range n).map (·+1)) ++
        ThreeMachine.encodeList encodeEdge (G.edges.map (fun e => (e.1.val,e.2.val)))) := by
    rw [ThreeMachine.encodeInput.eq_def,encodeEdges_map]
    cases d <;> simp only [encodeHeader,List.append_assoc]
  rw [he]
  simp only [parse,readHeader_correct,readList_correct readNat_encodeNat]
  rw [← List.append_nil (ThreeMachine.encodeList encodeEdge _),readList_correct readEdge_correct]
  simp only [List.length_map,List.length_range]

end ThreeMachine.StackCompiler.Binary

namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u6} {α : I → Type u7} [∀ i, Coding (α i)]

def binaryReadStep {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader) :
    Uniform (fun i => Binary.readStep (reader i)) :=
  ((fst.comp (R.comp snd)).pair (((fst.comp (R.comp fst)).pair snd).comp cons)).congr
    (fun _ _ => rfl)

def binaryReadMany {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader) :
    Uniform (fun i (x : ℕ × List Bool) => Binary.readMany (reader i) x.1 x.2) :=
  (((fst.pair (snd.pair nil)).comp R.binaryReadStep.iterate).comp
      ((snd.comp reverse).pair fst)).congr (fun _ _ => rfl)

def binaryReadList {reader : ∀ i, List Bool → α i × List Bool} (R : Uniform reader) :
    Uniform (fun i => Binary.readList (reader i)) :=
  (binaryReadNat.comp R.binaryReadMany).congr (fun _ _ => rfl)

def binaryReadEdge : Uniform (fun (_ : I) => Binary.readEdge) := by
  let A := binaryReadNat (I := I)
  let B := A.comp (snd.comp binaryReadNat)
  exact (((A.comp (fst.comp (Realizer.pred.uniform I))).pair
      (B.comp (fst.comp (Realizer.pred.uniform I)))).pair (B.comp snd)).congr (fun _ _ => rfl)

def binaryReadHeader : Uniform (fun (_ : I) => Binary.readHeader) := by
  let P : Uniform (fun (_ : I) (bs : List Bool) => bs.head?.getD Bool.false) :=
    (head?.pair false).comp getD
  let A := tail.comp (binaryReadNat (I := I))
  exact (P.ite ((A.comp (fst.comp some)).pair (A.comp snd)) (none.pair tail)).congr (fun _ _ => rfl)

def binaryParse : Uniform (fun (_ : I) => Binary.parse) := by
  let A := binaryReadHeader (I := I)
  let V := A.comp (snd.comp binaryReadNat.binaryReadList)
  let E := V.comp (snd.comp binaryReadEdge.binaryReadList)
  exact ((V.comp (fst.comp length)).pair ((E.comp fst).pair (A.comp fst))).congr (fun _ _ => rfl)

end ThreeMachine.StackCompiler.Uniform

namespace ThreeMachine.StackCompiler

structure Request (n : ℕ) where
  graph : Instance n
  deadline : Option ℕ

instance (n : ℕ) : Coding (Request n) :=
  ⟨fun x => enc (ThreeMachine.encodeInput x.graph x.deadline)⟩

namespace Uniform

def parseRequest : Uniform (fun n (x : Request n) => ((Cardinal.mk () : Cardinal n),(x.graph,x.deadline))) where
  transform := (binaryParse (I := ℕ)).transform
  charge := (binaryParse (I := ℕ)).charge
  routine := (binaryParse (I := ℕ)).routine
  correct n x := by
    change (binaryParse (I := ℕ)).transform (enc (ThreeMachine.encodeInput x.graph x.deadline)) = _
    rw [(binaryParse (I := ℕ)).correct n,Binary.parse_input]
    change Data.pair (enc n) (Data.pair (enc (x.graph.edges.map (fun e => (e.1.val,e.2.val)))) (enc x.deadline)) =
      Data.pair (enc n) (Data.pair (enc x.graph.edges) (enc x.deadline))
    congr 2
    exact enc_list_map (fun e : Fin n × Fin n => (e.1.val,e.2.val)) (fun _ => rfl) x.graph.edges

def requestAnswer : Uniform (fun n (x : Request n) => Algorithm.output x.graph x.deadline) :=
  ((parseRequest.comp (makeUniverse.onFst.comp unaryAnswer)).comp binaryEncodeAnswer).congr
    (fun _ x => answerMatrix_closure x.graph x.deadline)

end Uniform
end ThreeMachine.StackCompiler
end

end OAI
end


section
-- module BinaryCosts
namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11

section
namespace ThreeMachine.StackCompiler.Costs
theorem valueStepCost : Poly (fun x : Bool × ℕ => x.2)
    (fun x => (Uniform.binaryValueStep (I := Unit)).time () x) 2 := by (have polyH0 := Poly.volumeBool (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (fun (x_1 : Bool × ℕ) => x_1.1); have polyH1 := Poly.size (fun (x_1 : Bool × ℕ) => Prod.snd x_1); have polyH2 := Poly.volumeNat polyH1; have polyH3 := Poly.volumeProd (fun (x_1 : Bool × ℕ) => x_1) polyH0 polyH2; have polyH4 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (2); have polyH5 := Poly.add polyH3 polyH4; have polyH6 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_snd (Unit) (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _ (()) (x_2)))) polyH5; have polyH7 := Poly.add polyH6 polyH6; have polyH8 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (20); have polyH9 := Poly.add polyH3 polyH2; have polyH10 := Poly.add polyH9 polyH2; have polyH11 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (1); have polyH12 := Poly.add polyH10 polyH11; have polyH13 := Poly.mul polyH8 polyH12; have polyH14 := Poly.add polyH7 polyH13; have polyH15 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_pair (Unit) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (()) (x_2)))) polyH14; have polyH16 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (10000000); have polyH17 := Poly.add polyH1 polyH1; have polyH18 := Poly.add polyH17 polyH11; have polyH19 := Poly.pow polyH18 (2); have polyH20 := Poly.mul polyH16 polyH19; have polyH21 := Poly.of_le (fun (x_2 : Bool × ℕ) => (@Realizer.time_add_le (Prod.snd x_2) (Prod.snd x_2))) polyH20; have polyH22 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_uniform (Unit) (ℕ × ℕ) (ℕ) _ _ (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) (Realizer.add) (()) ((Prod.snd x_2, Prod.snd x_2))))) polyH21; have polyH23 := Poly.add polyH15 polyH22; have polyH24 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (10); have polyH25 := Poly.volumeProd (fun (x_1 : Bool × ℕ) => (Prod.snd x_1, Prod.snd x_1)) polyH2 polyH2; have polyH26 := Poly.add polyH25 polyH11; have polyH27 := Poly.mul polyH24 polyH26; have polyH28 := Poly.add polyH23 polyH27; have polyH29 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_comp (Unit) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => (Prod.snd x_1, Prod.snd x_1)) (fun (x_1 : Unit) (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) (@Uniform.pair Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _)) (Realizer.uniform Realizer.add Unit) (()) (x_2)))) polyH28; have polyH30 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_fst (Unit) (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _ (()) (x_2)))) polyH5; have polyH31 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (2 * volume (1) + 1); have polyH32 := Poly.mul polyH8 polyH3; have polyH33 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (50 * volume (1)); have polyH34 := Poly.add polyH32 polyH33; have polyH35 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (50); have polyH36 := Poly.add polyH34 polyH35; have polyH37 := Poly.mul polyH31 polyH36; have polyH38 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_constant (Unit) (fun (i : Unit) => Bool × ℕ) _ (ℕ) _ (1) (()) (x_2)))) polyH37; have polyH39 := Poly.add polyH30 polyH38; have polyH40 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_zero (Unit) (fun (i : Unit) => Bool × ℕ) _ (()) (x_2)))) polyH4; have polyH41 := Poly.add polyH39 polyH40; have polyH42 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (1000); have polyH43 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (volume (1)); have polyH44 := Poly.add polyH3 polyH43; have polyH45 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (volume (0)); have polyH46 := Poly.add polyH44 polyH45; have polyH47 := Poly.add polyH46 polyH11; have polyH48 := Poly.mul polyH42 polyH47; have polyH49 := Poly.add polyH41 polyH48; have polyH50 := Poly.of_le (fun (x_2 : Bool × ℕ) => (@Uniform.time_ite_le (Unit) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) _ _ (fun (i : Unit) => Prod.fst) (fun (i : Unit) (x_1 : Bool × ℕ) => 1) (fun (i : Unit) (x_1 : Bool × ℕ) => 0) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.constant Unit (fun (i : Unit) => Bool × ℕ) _ ℕ _ (1)) (@Uniform.zero Unit (fun (i : Unit) => Bool × ℕ) _) (()) (x_2))) polyH49; have polyH51 := Poly.add polyH29 polyH50; have polyH52 := Poly.volumeNat polyH17; have polyH53 := Poly.add polyH3 polyH52; have polyH54 := Poly.volumeIte (fun (x_1 : Bool × ℕ) => Prod.fst x_1 = Bool.true) (fun (x_1 : Bool × ℕ) => 1) (fun (x_1 : Bool × ℕ) => 0) polyH43 polyH45; have polyH55 := Poly.add polyH53 polyH54; have polyH56 := Poly.add polyH55 polyH11; have polyH57 := Poly.mul polyH8 polyH56; have polyH58 := Poly.add polyH51 polyH57; have polyH59 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_pair (Unit) (fun (i : Unit) => Bool × ℕ) (fun (x_1 : Unit) => ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => (fun (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) ((fun (x_3 : Bool × ℕ) => (Prod.snd x_3, Prod.snd x_3)) x_1)) (fun (i : Unit) (x_1 : Bool × ℕ) => if Prod.fst x_1 = Bool.true then 1 else 0) (@Uniform.comp Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => (Prod.snd x_1, Prod.snd x_1)) (fun (x_1 : Unit) (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) (@Uniform.pair Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _)) (Realizer.uniform Realizer.add Unit)) (@Uniform.ite Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => 1) (fun (i : Unit) => Prod.fst) (fun (i : Unit) (x_1 : Bool × ℕ) => 0) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.constant Unit (fun (i : Unit) => Bool × ℕ) _ ℕ _ (1)) (@Uniform.zero Unit (fun (i : Unit) => Bool × ℕ) _)) (()) (x_2)))) polyH58; have polyH60 := Poly.const (fun (x_1 : Bool × ℕ) => Prod.snd x_1) (0); have polyH61 := Poly.iteNat (fun (x_1 : Bool × ℕ) => Prod.fst x_1 = Bool.true) polyH11 polyH60; have polyH62 := Poly.add polyH17 polyH61; have polyH63 := Poly.add polyH62 polyH11; have polyH64 := Poly.pow polyH63 (2); have polyH65 := Poly.mul polyH16 polyH64; have polyH66 := Poly.of_le (fun (x_2 : Bool × ℕ) => (@Realizer.time_add_le ((fun (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) ((fun (x_1 : Bool × ℕ) => (Prod.snd x_1, Prod.snd x_1)) x_2)) (if Prod.fst x_2 = Bool.true then 1 else 0))) polyH65; have polyH67 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_uniform (Unit) (ℕ × ℕ) (ℕ) _ _ (fun (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) (Realizer.add) (()) (((fun (x_1 : ℕ × ℕ) => Prod.fst x_1 + Prod.snd x_1) ((fun (x_1 : Bool × ℕ) => (Prod.snd x_1, Prod.snd x_1)) x_2), if Prod.fst x_2 = Bool.true then 1 else 0))))) polyH66; have polyH68 := Poly.add polyH59 polyH67; have polyH69 := Poly.volumeProd (fun (x_1 : Bool × ℕ) => ((fun (x_2 : ℕ × ℕ) => Prod.fst x_2 + Prod.snd x_2) ((fun (x_2 : Bool × ℕ) => (Prod.snd x_2, Prod.snd x_2)) x_1), if Prod.fst x_1 = Bool.true then 1 else 0)) polyH52 polyH54; have polyH70 := Poly.add polyH69 polyH11; have polyH71 := Poly.mul polyH24 polyH70; have polyH72 := Poly.add polyH68 polyH71; have polyH73 := Poly.of_le (fun (x_2 : Bool × ℕ) => (le_of_eq (@Uniform.time_comp (Unit) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => ((fun (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) ((fun (x_3 : Bool × ℕ) => (Prod.snd x_3, Prod.snd x_3)) x_1), if Prod.fst x_1 = Bool.true then 1 else 0)) (fun (x_1 : Unit) (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) (@Uniform.pair Unit (fun (i : Unit) => Bool × ℕ) (fun (x_1 : Unit) => ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => (fun (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) ((fun (x_3 : Bool × ℕ) => (Prod.snd x_3, Prod.snd x_3)) x_1)) (fun (i : Unit) (x_1 : Bool × ℕ) => if Prod.fst x_1 = Bool.true then 1 else 0) (@Uniform.comp Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => (Prod.snd x_1, Prod.snd x_1)) (fun (x_1 : Unit) (x_3 : ℕ × ℕ) => Prod.fst x_3 + Prod.snd x_3) (@Uniform.pair Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _)) (Realizer.uniform Realizer.add Unit)) (@Uniform.ite Unit (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) _ _ (fun (i : Unit) (x_1 : Bool × ℕ) => 1) (fun (i : Unit) => Prod.fst) (fun (i : Unit) (x_1 : Bool × ℕ) => 0) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _) (@Uniform.constant Unit (fun (i : Unit) => Bool × ℕ) _ ℕ _ (1)) (@Uniform.zero Unit (fun (i : Unit) => Bool × ℕ) _))) (Realizer.uniform Realizer.add Unit) (()) (x_2)))) polyH72; exact Poly.lift polyH73 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
theorem leadingStepCost : Poly (fun x : Bool × (Bool × ℕ) => x.2.2)
    (fun x => (Uniform.binaryLeadingStep (I := Unit)).time () x) 1 := by (have polyH0 := Poly.volumeBool (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Bool × Bool × ℕ) => x_1.1); have polyH1 := Poly.volumeBool (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Bool × Bool × ℕ) => x_1.2.1); have polyH2 := Poly.size (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)); have polyH3 := Poly.volumeNat polyH2; have polyH4 := Poly.volumeProd (fun (x_1 : Bool × Bool × ℕ) => x_1.2) polyH1 polyH3; have polyH5 := Poly.volumeProd (fun (x_1 : Bool × Bool × ℕ) => x_1) polyH0 polyH4; have polyH6 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (2); have polyH7 := Poly.add polyH5 polyH6; have polyH8 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_snd (Unit) (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _ (()) (x_2)))) polyH7; have polyH9 := Poly.add polyH4 polyH6; have polyH10 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_fst (Unit) (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _ (()) (Prod.snd x_2)))) polyH9; have polyH11 := Poly.add polyH8 polyH10; have polyH12 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (10); have polyH13 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (1); have polyH14 := Poly.add polyH4 polyH13; have polyH15 := Poly.mul polyH12 polyH14; have polyH16 := Poly.add polyH11 polyH15; have polyH17 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_comp (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.fst) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _) (()) (x_2)))) polyH16; have polyH18 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_fst (Unit) (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _ (()) (x_2)))) polyH7; have polyH19 := Poly.add polyH17 polyH18; have polyH20 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (20); have polyH21 := Poly.volumeBool (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Bool × Bool × ℕ) => (Prod.snd x_1).1); have polyH22 := Poly.add polyH5 polyH21; have polyH23 := Poly.add polyH22 polyH0; have polyH24 := Poly.add polyH23 polyH13; have polyH25 := Poly.mul polyH20 polyH24; have polyH26 := Poly.add polyH19 polyH25; have polyH27 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_pair (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.fst (Prod.snd x_1)) (fun (i : Unit) => Prod.fst) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.fst) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _)) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (()) (x_2)))) polyH26; have polyH28 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (10000); have polyH29 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (@Realizer.time_and_le ((Prod.fst (Prod.snd x_2), Prod.fst x_2)))) polyH28; have polyH30 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_uniform (Unit) (Bool × Bool) (Bool) _ _ (fun (x_1 : Bool × Bool) => Prod.fst x_1 && Prod.snd x_1) (Realizer.and) (()) ((Prod.fst (Prod.snd x_2), Prod.fst x_2))))) polyH29; have polyH31 := Poly.add polyH27 polyH30; have polyH32 := Poly.volumeProd (fun (x_1 : Bool × Bool × ℕ) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) polyH21 polyH0; have polyH33 := Poly.add polyH32 polyH13; have polyH34 := Poly.mul polyH12 polyH33; have polyH35 := Poly.add polyH31 polyH34; have polyH36 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_comp (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × Bool) (fun (x_1 : Unit) => Bool) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (x_1 : Unit) (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) (@Uniform.pair Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.fst (Prod.snd x_1)) (fun (i : Unit) => Prod.fst) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.fst) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _)) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _)) (Realizer.uniform Realizer.and Unit) (()) (x_2)))) polyH35; have polyH37 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (2 * volume Bool.true + 1); have polyH38 := Poly.mul polyH20 polyH5; have polyH39 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (50 * volume Bool.true); have polyH40 := Poly.add polyH38 polyH39; have polyH41 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (50); have polyH42 := Poly.add polyH40 polyH41; have polyH43 := Poly.mul polyH37 polyH42; have polyH44 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_constant (Unit) (fun (i : Unit) => Bool × Bool × ℕ) _ (Bool) _ (Bool.true) (()) (x_2)))) polyH43; have polyH45 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_snd (Unit) (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _ (()) (Prod.snd x_2)))) polyH9; have polyH46 := Poly.add polyH8 polyH45; have polyH47 := Poly.add polyH46 polyH15; have polyH48 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_comp (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _) (()) (x_2)))) polyH47; have polyH49 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (200); have polyH50 := Poly.add polyH2 polyH13; have polyH51 := Poly.mul polyH49 polyH50; have polyH52 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (@Realizer.time_succ_le (Prod.snd (Prod.snd x_2)))) polyH51; have polyH53 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_uniform (Unit) (ℕ) (ℕ) _ _ (fun (n : ℕ) => n + 1) (Realizer.succ) (()) (Prod.snd (Prod.snd x_2))))) polyH52; have polyH54 := Poly.add polyH48 polyH53; have polyH55 := Poly.add polyH3 polyH13; have polyH56 := Poly.mul polyH12 polyH55; have polyH57 := Poly.add polyH54 polyH56; have polyH58 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_comp (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (x_1 : Unit) => ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Unit) (n : ℕ) => n + 1) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _)) (Realizer.uniform Realizer.succ Unit) (()) (x_2)))) polyH57; have polyH59 := Poly.add polyH44 polyH58; have polyH60 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (volume Bool.true); have polyH61 := Poly.add polyH5 polyH60; have polyH62 := Poly.volumeNat polyH50; have polyH63 := Poly.add polyH61 polyH62; have polyH64 := Poly.add polyH63 polyH13; have polyH65 := Poly.mul polyH20 polyH64; have polyH66 := Poly.add polyH59 polyH65; have polyH67 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_pair (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Bool.true) (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (fun (n : ℕ) => n + 1) (Prod.snd (Prod.snd x_1))) (@Uniform.constant Unit (fun (i : Unit) => Bool × Bool × ℕ) _ Bool _ Bool.true) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (x_1 : Unit) => ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Unit) (n : ℕ) => n + 1) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _)) (Realizer.uniform Realizer.succ Unit)) (()) (x_2)))) polyH66; have polyH68 := Poly.add polyH36 polyH67; have polyH69 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_false (Unit) (fun (i : Unit) => Bool × Bool × ℕ) _ (()) (x_2)))) polyH6; have polyH70 := Poly.add polyH69 polyH48; have polyH71 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (volume Bool.false); have polyH72 := Poly.add polyH5 polyH71; have polyH73 := Poly.add polyH72 polyH3; have polyH74 := Poly.add polyH73 polyH13; have polyH75 := Poly.mul polyH20 polyH74; have polyH76 := Poly.add polyH70 polyH75; have polyH77 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (le_of_eq (@Uniform.time_pair (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Bool.false) (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (@Uniform.false Unit (fun (i : Unit) => Bool × Bool × ℕ) _) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _)) (()) (x_2)))) polyH76; have polyH78 := Poly.add polyH68 polyH77; have polyH79 := Poly.const (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (1000); have polyH80 := Poly.volumeBool (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Bool × Bool × ℕ) => Bool.true); have polyH81 := Poly.volumeProd (fun (x_1 : Bool × Bool × ℕ) => (Bool.true, (fun (n : ℕ) => n + 1) (Prod.snd (Prod.snd x_1)))) polyH80 polyH62; have polyH82 := Poly.add polyH5 polyH81; have polyH83 := Poly.volumeBool (fun (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Bool × Bool × ℕ) => Bool.false); have polyH84 := Poly.volumeProd (fun (x_1 : Bool × Bool × ℕ) => (Bool.false, Prod.snd (Prod.snd x_1))) polyH83 polyH3; have polyH85 := Poly.add polyH82 polyH84; have polyH86 := Poly.add polyH85 polyH13; have polyH87 := Poly.mul polyH79 polyH86; have polyH88 := Poly.add polyH78 polyH87; have polyH89 := Poly.of_le (fun (x_2 : Bool × Bool × ℕ) => (@Uniform.time_ite_le (Unit) (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (fun (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) ((fun (x_3 : Bool × Bool × ℕ) => (Prod.fst (Prod.snd x_3), Prod.fst x_3)) x_1)) (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (Bool.true, (fun (n : ℕ) => n + 1) (Prod.snd (Prod.snd x_1)))) (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (Bool.false, Prod.snd (Prod.snd x_1))) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × Bool) (fun (x_1 : Unit) => Bool) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (Prod.fst (Prod.snd x_1), Prod.fst x_1)) (fun (x_1 : Unit) (x_3 : Bool × Bool) => Prod.fst x_3 && Prod.snd x_3) (@Uniform.pair Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.fst (Prod.snd x_1)) (fun (i : Unit) => Prod.fst) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => Bool) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.fst) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _)) (@Uniform.fst Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _)) (Realizer.uniform Realizer.and Unit)) (@Uniform.pair Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Bool.true) (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => (fun (n : ℕ) => n + 1) (Prod.snd (Prod.snd x_1))) (@Uniform.constant Unit (fun (i : Unit) => Bool × Bool × ℕ) _ Bool _ Bool.true) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (x_1 : Unit) => ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (fun (x_1 : Unit) (n : ℕ) => n + 1) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (x_1 : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (x_1 : Unit) => ℕ) _ _)) (Realizer.uniform Realizer.succ Unit))) (@Uniform.pair Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Bool.false) (fun (i : Unit) (x_1 : Bool × Bool × ℕ) => Prod.snd (Prod.snd x_1)) (@Uniform.false Unit (fun (i : Unit) => Bool × Bool × ℕ) _) (@Uniform.comp Unit (fun (i : Unit) => Bool × Bool × ℕ) (fun (i : Unit) => Bool × ℕ) (fun (i : Unit) => ℕ) _ _ _ (fun (i : Unit) => Prod.snd) (fun (i : Unit) => Prod.snd) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => Bool × ℕ) _ _) (@Uniform.snd Unit (fun (i : Unit) => Bool) (fun (i : Unit) => ℕ) _ _))) (()) (x_2))) polyH88; exact Poly.lift polyH89 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
noncomputable def valueStepC : ℕ := Classical.choose valueStepCost
noncomputable def leadingStepC : ℕ := Classical.choose leadingStepCost
end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1}

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Realizer
variable {α : Type u2} {β : Type u3} [Coding α] [Coding β] {f : α × β → β}

end ThreeMachine.StackCompiler.Realizer
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u4} {α : I → Type u5} {β : I → Type u6} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
variable {f : ∀ i, α i × β i → β i}

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Binary

end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler

namespace Uniform
variable {I : Type u7}

end Uniform
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Costs
theorem takeStepCost (I : Type u8) :
    Poly (fun x : Σ _ : I, List Bool × List Bool => x.2.1.length+x.2.2.length)
      (fun x => (Uniform.takeStep (I := I) (α := fun _ => Bool)).time x.1 x.2) 1 := by
  let sz (x : Σ _ : I, List Bool × List Bool) := x.2.1.length+x.2.2.length
  have hx : Poly sz (fun x => x.2.1.length) 1 := Poly.of_le (fun x => Nat.le_add_right _ _) (Poly.size sz)
  have hy : Poly sz (fun x => x.2.2.length) 1 := Poly.of_le (fun x => Nat.le_add_left _ _) (Poly.size sz)
  have hhead : Poly sz (fun x => volume x.2.1.head?) 0 := by
    apply Poly.volumeOption _ (Poly.const sz 3)
    intro x b hb; exact volume_bool b
  have htail : Poly sz (fun x => x.2.1.tail.length) 1 :=
    Poly.of_le (fun x => by simp only [List.length_tail]; omega) hx
  have hget : Poly sz (fun x => ((x.2.1.head?.map (fun a => a :: x.2.2)).getD x.2.2).length) 1 := by
    apply Poly.of_le (g := fun x => x.2.2.length+1)
    · intro x
      cases x.2.1 <;> simp
    · (have polyH0 := Poly.const (sz) (1); have polyH1 := Poly.add (hy) polyH0; exact Poly.lift polyH1 (by first | decide +kernel | omega))
  (have polyH0 := Poly.volumeBool (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2.1) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2.1) => (Sigma.snd q).1); have polyH1 := Poly.listVolume (fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2.1) (hx) polyH0; have polyH2 := Poly.volumeBool (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2.2) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2.2) => (Sigma.snd q).1); have polyH3 := Poly.listVolume (fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2.2) (hy) polyH2; have polyH4 := Poly.volumeProd (fun (x_1 : (_ : I) × List Bool × List Bool) => x_1.2) polyH1 polyH3; have polyH5 := Poly.const (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (2); have polyH6 := Poly.add polyH4 polyH5; have polyH7 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_fst (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ (Sigma.fst x_9) (Sigma.snd x_9)))) polyH6; have polyH8 := Poly.volumeBool (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => (Sigma.snd x_1).1) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => (Sigma.snd x_1).1) => (Sigma.snd q).1); have polyH9 := Poly.listVolume (fun (x_1 : (_ : I) × List Bool × List Bool) => (Sigma.snd x_1).1) (hx) polyH8; have polyH10 := Poly.add polyH9 polyH5; have polyH11 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_tail (I) (fun (x_1 : I) => Bool) _ (Sigma.fst x_9) (Prod.fst (Sigma.snd x_9))))) polyH10; have polyH12 := Poly.add polyH7 polyH11; have polyH13 := Poly.const (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (10); have polyH14 := Poly.const (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (1); have polyH15 := Poly.add polyH9 polyH14; have polyH16 := Poly.mul polyH13 polyH15; have polyH17 := Poly.add polyH12 polyH16; have polyH18 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.tail xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.tail I (fun (x_1 : I) => Bool) _) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH17; have polyH19 := Poly.const (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (10000); have polyH20 := Poly.mul polyH19 polyH15; have polyH21 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (@Uniform.time_head?_le (I) (fun (x_1 : I) => Bool) _ (Sigma.fst x_9) (Prod.fst (Sigma.snd x_9)))) polyH20; have polyH22 := Poly.add polyH7 polyH21; have polyH23 := Poly.add polyH22 polyH16; have polyH24 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.head? xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.head? I (fun (x_1 : I) => Bool) _) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH23; have polyH25 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_snd (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ (Sigma.fst x_9) (Sigma.snd x_9)))) polyH6; have polyH26 := Poly.add polyH24 polyH25; have polyH27 := Poly.const (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (20); have polyH28 := Poly.add polyH4 (hhead); have polyH29 := Poly.volumeBool (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => (Sigma.snd x_1).2) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => (Sigma.snd x_1).2) => (Sigma.snd q).1); have polyH30 := Poly.listVolume (fun (x_1 : (_ : I) × List Bool × List Bool) => (Sigma.snd x_1).2) (hy) polyH29; have polyH31 := Poly.add polyH28 polyH30; have polyH32 := Poly.add polyH31 polyH14; have polyH33 := Poly.mul polyH27 polyH32; have polyH34 := Poly.add polyH26 polyH33; have polyH35 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.head? xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.head? I (fun (x_1 : I) => Bool) _)) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH34; have polyH36 := Poly.volumeOptionToList (fun (x_1 : (_ : I) × List Bool × List Bool) => Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) (hhead); have polyH37 := Poly.volumePool (fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) polyH36; have polyH38 := Poly.precomp (hy) (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Sigma.fst q); have polyH39 := Poly.volumeBool (fun (q : Poly.ListPool fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd (Sigma.fst q)).2) => (fun (q_1 : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd (Sigma.fst q)).2) => (Sigma.snd q).1); have polyH40 := Poly.listVolume (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Sigma.snd (Sigma.fst q)).2) polyH38 polyH39; have polyH41 := Poly.volumeProd (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))) polyH37 polyH40; have polyH42 := Poly.const (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (2); have polyH43 := Poly.add polyH41 polyH42; have polyH44 := Poly.of_le (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (le_of_eq (@Uniform.time_cons (I) (fun (x_1 : I) => Bool) _ (Sigma.fst (Sigma.fst q)) ((Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))))))) polyH43; have polyH45 := Poly.lengthCons (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Prod.fst (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))) (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Prod.snd (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))) polyH38; have polyH46 := Poly.volumeBool (fun (q : Poly.ListPool fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Prod.fst (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) :: Prod.snd (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))) => (fun (q_1 : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Prod.fst (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) :: Prod.snd (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))) => (Sigma.snd q).1); have polyH47 := Poly.listVolume (fun (q : @Poly.Pool I ((_ : I) × List Bool × List Bool) (fun (x_1 : I) => Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1)))) => Prod.fst (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q)))) :: Prod.snd (Subtype.val (Sigma.snd q), Prod.snd ((fun (xs : List ((fun (x_1 : I) => Bool) (Sigma.fst (Sigma.fst q)))) => List.head? xs) (Prod.fst (Sigma.snd (Sigma.fst q))), Prod.snd (Sigma.snd (Sigma.fst q))))) polyH45 polyH46; have polyH48 := @Poly.optionMapTime (I) ((_ : I) × List Bool × List Bool) (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (fun (x_1 : I) => Bool) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (x_1 : (_ : I) × List Bool × List Bool) => Sigma.fst x_1) (fun (x_1 : (_ : I) × List Bool × List Bool) => Prod.snd ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) (fun (x_1 : (_ : I) × List Bool × List Bool) => Prod.fst ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) (fun (i : I) (x_1 : (fun (x_1 : I) => Bool) i × List ((fun (x_1 : I) => Bool) i)) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.cons I (fun (x_1 : I) => Bool) _) (Max.max (Max.max (0) (1 + 0)) (0)) (0) (1 + 0) (1 + 0) polyH44 (hhead) polyH30 polyH47; have polyH49 := Poly.add polyH35 polyH48; have polyH50 := Poly.volumeProd (fun (x_1 : (_ : I) × List Bool × List Bool) => ((fun (xs : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => List.head? xs) (Prod.fst (Sigma.snd x_1)), Prod.snd (Sigma.snd x_1))) (hhead) polyH30; have polyH51 := Poly.add polyH50 polyH14; have polyH52 := Poly.mul polyH13 polyH51; have polyH53 := Poly.add polyH49 polyH52; have polyH54 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => ((fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1), Prod.snd x_1)) (fun (i : I) (x_1 : Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => Prod.fst (a, Prod.snd x_1) :: Prod.snd (a, Prod.snd x_1)) (Prod.fst x_1)) (@Uniform.pair I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.head? xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.head? I (fun (x_1 : I) => Bool) _)) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _)) (@Uniform.optionMap I (fun (x_1 : I) => Bool) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : (fun (x_1 : I) => Bool) i × List ((fun (x_1 : I) => Bool) i)) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.cons I (fun (x_1 : I) => Bool) _)) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH53; have polyH55 := Poly.add polyH54 polyH25; have polyH56 := Poly.precomp (hy) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => Sigma.fst q); have polyH57 := Poly.lengthCons (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => Subtype.val (Sigma.snd q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => Prod.snd (Sigma.snd (Sigma.fst q))) polyH56; have polyH58 := Poly.volumeBool (fun (q : Poly.ListPool fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => Subtype.val (Sigma.snd q) :: Prod.snd (Sigma.snd (Sigma.fst q))) => (fun (q_1 : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q_1)) (Sigma.fst q)) (fun (q : Poly.ListPool fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => Subtype.val (Sigma.snd q) :: Prod.snd (Sigma.snd (Sigma.fst q))) => (Sigma.snd q).1); have polyH59 := Poly.listVolume (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.toList (List.head? (Prod.fst (Sigma.snd x_1)))) => Subtype.val (Sigma.snd q) :: Prod.snd (Sigma.snd (Sigma.fst q))) polyH57 polyH58; have polyH60 := Poly.volumeOptionMap (fun (x_1 : (_ : I) × List Bool × List Bool) (a : Bool) => a :: Prod.snd (Sigma.snd x_1)) (fun (x_1 : (_ : I) × List Bool × List Bool) => List.head? (Prod.fst (Sigma.snd x_1))) polyH59; have polyH61 := Poly.add polyH4 polyH60; have polyH62 := Poly.add polyH61 polyH30; have polyH63 := Poly.add polyH62 polyH14; have polyH64 := Poly.mul polyH27 polyH63; have polyH65 := Poly.add polyH55 polyH64; have polyH66 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => a :: Prod.snd x_1) (List.head? (Prod.fst x_1))) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => ((fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1), Prod.snd x_1)) (fun (i : I) (x_1 : Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => Prod.fst (a, Prod.snd x_1) :: Prod.snd (a, Prod.snd x_1)) (Prod.fst x_1)) (@Uniform.pair I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.head? xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.head? I (fun (x_1 : I) => Bool) _)) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _)) (@Uniform.optionMap I (fun (x_1 : I) => Bool) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : (fun (x_1 : I) => Bool) i × List ((fun (x_1 : I) => Bool) i)) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.cons I (fun (x_1 : I) => Bool) _))) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH65; have polyH67 := Poly.add polyH60 polyH30; have polyH68 := Poly.add polyH67 polyH14; have polyH69 := Poly.mul polyH19 polyH68; have polyH70 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (@Uniform.time_getD_le (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ (Sigma.fst x_9) (Option.map (fun (a : Bool) => a :: Prod.snd (Sigma.snd x_9)) (List.head? (Prod.fst (Sigma.snd x_9)))) (Prod.snd (Sigma.snd x_9)))) polyH69; have polyH71 := Poly.add polyH66 polyH70; have polyH72 := Poly.volumeProd (fun (x_1 : (_ : I) × List Bool × List Bool) => (Option.map (fun (a : Bool) => a :: Prod.snd (Sigma.snd x_1)) (List.head? (Prod.fst (Sigma.snd x_1))), Prod.snd (Sigma.snd x_1))) polyH60 polyH30; have polyH73 := Poly.add polyH72 polyH14; have polyH74 := Poly.mul polyH13 polyH73; have polyH75 := Poly.add polyH71 polyH74; have polyH76 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_comp (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i)) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (Option.map (fun (a : Bool) => a :: Prod.snd x_1) (List.head? (Prod.fst x_1)), Prod.snd x_1)) (fun (i : I) (x_1 : Option (List ((fun (x_1 : I) => Bool) i)) × List ((fun (x_1 : I) => Bool) i)) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => a :: Prod.snd x_1) (List.head? (Prod.fst x_1))) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => ((fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1), Prod.snd x_1)) (fun (i : I) (x_1 : Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => Prod.fst (a, Prod.snd x_1) :: Prod.snd (a, Prod.snd x_1)) (Prod.fst x_1)) (@Uniform.pair I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.head? xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.head? I (fun (x_1 : I) => Bool) _)) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _)) (@Uniform.optionMap I (fun (x_1 : I) => Bool) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : (fun (x_1 : I) => Bool) i × List ((fun (x_1 : I) => Bool) i)) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.cons I (fun (x_1 : I) => Bool) _))) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _)) (@Uniform.getD I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH75; have polyH77 := Poly.add polyH18 polyH76; have polyH78 := Poly.volumeBool (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => List.tail (Prod.fst (Sigma.snd x_1))) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => List.tail (Prod.fst (Sigma.snd x_1))) => (Sigma.snd q).1); have polyH79 := Poly.listVolume (fun (x_1 : (_ : I) × List Bool × List Bool) => List.tail (Prod.fst (Sigma.snd x_1))) (htail) polyH78; have polyH80 := Poly.add polyH4 polyH79; have polyH81 := Poly.volumeBool (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.getD (Prod.fst ((fun (x_2 : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1)) × List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1)) × List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) (Sigma.snd x_1)))) => (fun (x_1 : (_ : I) × List Bool × List Bool) => List.length (Prod.fst (Sigma.snd x_1)) + List.length (Prod.snd (Sigma.snd x_1))) (Sigma.fst q)) (fun (q : Poly.ListPool fun (x_1 : (_ : I) × List Bool × List Bool) => Option.getD (Prod.fst ((fun (x_2 : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1)) × List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1)) × List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) (Sigma.snd x_1)))) => (Sigma.snd q).1); have polyH82 := Poly.listVolume (fun (x_1 : (_ : I) × List Bool × List Bool) => Option.getD (Prod.fst ((fun (x_2 : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1)) × List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) (Sigma.snd x_1))) (Prod.snd ((fun (x_2 : List ((fun (x_2 : I) => Bool) (Sigma.fst x_1)) × List ((fun (x_2 : I) => Bool) (Sigma.fst x_1))) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) (Sigma.snd x_1)))) (hget) polyH81; have polyH83 := Poly.add polyH80 polyH82; have polyH84 := Poly.add polyH83 polyH14; have polyH85 := Poly.mul polyH27 polyH84; have polyH86 := Poly.add polyH77 polyH85; have polyH87 := Poly.of_le (fun (x_9 : (_ : I) × List Bool × List Bool) => (le_of_eq (@Uniform.time_pair (I) (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.tail xs) (Prod.fst x_1)) (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (x_2 : Option (List ((fun (x_2 : I) => Bool) i)) × List ((fun (x_2 : I) => Bool) i)) => Option.getD (Prod.fst x_2) (Prod.snd x_2)) ((fun (x_2 : List ((fun (x_2 : I) => Bool) i) × List ((fun (x_2 : I) => Bool) i)) => (Option.map (fun (a : Bool) => a :: Prod.snd x_2) (List.head? (Prod.fst x_2)), Prod.snd x_2)) x_1)) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.tail xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.tail I (fun (x_1 : I) => Bool) _)) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i)) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (Option.map (fun (a : Bool) => a :: Prod.snd x_1) (List.head? (Prod.fst x_1)), Prod.snd x_1)) (fun (i : I) (x_1 : Option (List ((fun (x_1 : I) => Bool) i)) × List ((fun (x_1 : I) => Bool) i)) => Option.getD (Prod.fst x_1) (Prod.snd x_1)) (@Uniform.pair I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => a :: Prod.snd x_1) (List.head? (Prod.fst x_1))) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option (List ((fun (x_1 : I) => Bool) i))) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => ((fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1), Prod.snd x_1)) (fun (i : I) (x_1 : Option ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => Option.map (fun (a : Bool) => Prod.fst (a, Prod.snd x_1) :: Prod.snd (a, Prod.snd x_1)) (Prod.fst x_1)) (@Uniform.pair I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) => (fun (xs : List ((fun (x_2 : I) => Bool) i)) => List.head? xs) (Prod.fst x_1)) (fun (i : I) => Prod.snd) (@Uniform.comp I (fun (i : I) => List ((fun (x_1 : I) => Bool) i) × List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => Option ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) => Prod.fst) (fun (i : I) (xs : List ((fun (x_1 : I) => Bool) i)) => List.head? xs) (@Uniform.fst I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _) (@Uniform.head? I (fun (x_1 : I) => Bool) _)) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _)) (@Uniform.optionMap I (fun (x_1 : I) => Bool) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _ _ (fun (i : I) (x_1 : (fun (x_1 : I) => Bool) i × List ((fun (x_1 : I) => Bool) i)) => Prod.fst x_1 :: Prod.snd x_1) (@Uniform.cons I (fun (x_1 : I) => Bool) _))) (@Uniform.snd I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _ _)) (@Uniform.getD I (fun (i : I) => List ((fun (x_1 : I) => Bool) i)) _)) (Sigma.fst x_9) (Sigma.snd x_9)))) polyH86; exact Poly.lift polyH87 (by first | decide +kernel | exact Nat.le_refl _ | assumption | omega))
noncomputable def takeStepC (I : Type u9) : ℕ := Classical.choose (takeStepCost I)
end ThreeMachine.StackCompiler.Costs
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u10}

end ThreeMachine.StackCompiler.Uniform
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u11}

end Uniform
namespace Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I) (bs : J → List Bool)

end Costs
end ThreeMachine.StackCompiler
end

end OAI
end


section
-- module RequestBounds
namespace OAI

section
namespace ThreeMachine.StackCompiler.Costs
variable {J : Type} (s n : J → ℕ) (U : ∀ j, Universe (n j)) (M : ∀ j, Matrix (n j))

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler
namespace Request
def size {n : ℕ} (x : Request n) : ℕ :=
  n+x.graph.edges.length+x.deadline.getD 0+(ThreeMachine.encodeInput x.graph x.deadline).length
end Request
namespace Binary
def vertices (n : ℕ) : List ℕ := (List.range n).map (·+1)
def edges {n : ℕ} (G : Instance n) : List (ℕ × ℕ) := G.edges.map (fun e => (e.1.val,e.2.val))

end Binary

end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler
namespace RequestData
abbrev Index := Σ n, Request n
def size (x : Index) := x.2.size
def bits (x : Index) := ThreeMachine.encodeInput x.2.graph x.2.deadline
def vbytes (x : Index) := ThreeMachine.encodeList ThreeMachine.encodeNat (Binary.vertices x.1)
def ebytes (x : Index) := ThreeMachine.encodeList Binary.encodeEdge (Binary.edges x.2.graph)

end RequestData
end ThreeMachine.StackCompiler
end

end OAI
end


section
-- module ReaderCosts
namespace OAI

universe u1 u2 u3

section
namespace ThreeMachine.StackCompiler.Costs
open RequestData

def requestSlots (x : Index) : Option (List ℕ) :=
  ThreeMachine.StackCompiler.answerMatrix (closureMatrix x.2.graph x.1) x.2.deadline

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u1} {α : I → Type} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} {α : I → Type} [∀ i, Coding (α i)]
variable (s : J → ℕ) (idx : J → I)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Binary
variable {α : Type u2}

end ThreeMachine.StackCompiler.Binary
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type u3} {α : I → Type} [∀ i, Coding (α i)]

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} {α : I → Type} [∀ i, Coding (α i)]
variable (s : J → ℕ) (idx : J → I)

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module RequestCosts
namespace OAI

section
namespace ThreeMachine.StackCompiler.Uniform
variable {I : Type}
def parseVertices : Uniform (fun (_ : I) (bs : List Bool) =>
    Binary.readList Binary.readNat (Binary.readHeader bs).2) :=
  binaryReadHeader.comp (snd.comp binaryReadNat.binaryReadList)
def parseEdges : Uniform (fun (_ : I) (bs : List Bool) =>
    Binary.readList Binary.readEdge (Binary.readList Binary.readNat (Binary.readHeader bs).2).2) :=
  parseVertices.comp (snd.comp binaryReadEdge.binaryReadList)
def parseVertexLength : Uniform (fun (_ : I) (bs : List Bool) =>
    (Binary.readList Binary.readNat (Binary.readHeader bs).2).1.length) :=
  parseVertices.comp (fst.comp length)

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
variable {I J : Type} (s : J → ℕ) (idx : J → I)

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Uniform

end ThreeMachine.StackCompiler.Uniform
namespace ThreeMachine.StackCompiler.Costs
open RequestData

end ThreeMachine.StackCompiler.Costs
end

section
namespace ThreeMachine.StackCompiler.Costs
open RequestData

end ThreeMachine.StackCompiler.Costs
end

end OAI
end


section
-- module MachineBridge
namespace OAI

section

namespace ThreeMachine.StackCompiler.Packed
variable {k : ℕ}

def halt : Packed k := ofProgram (⟨(),fun _ _ => none⟩ : Program k Unit)

def pushWord (dst : Fin (k+1)) : List Bool → Packed k
  | [] => halt
  | b :: bs => (pushWord dst bs).seq (ofProgram (Program.push dst b))

def pop (src : Fin (k+1)) : Packed k := ofProgram (Program.instruction (fun _ => Program.popActions src))

def popN (src : Fin (k+1)) : ℕ → Packed k
  | 0 => halt
  | n+1 => (pop src).seq (popN src n)

end ThreeMachine.StackCompiler.Packed

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

def boolChunk (b : Bool) : List Bool := true :: (enc b).encode

def encodeBody (src dst : Fin (k+1)) : Packed k :=
  Packed.branch (fun h => (h src).getD false)
    ((Packed.pop src).seq (Packed.pushWord dst (boolChunk true)))
    ((Packed.pop src).seq (Packed.pushWord dst (boolChunk false)))

def encodeLoop (src dst : Fin (k+1)) : Packed k :=
  Packed.loop (fun h => (h src).isSome) (encodeBody src dst)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Raw
open Packed
variable {k : ℕ}

def decodeAfterTag (src dst : Fin (k+1)) : Packed k :=
  Packed.branch (fun h => (h src).getD false)
    ((Packed.popN src 3).seq (Packed.ofProgram (Program.push dst true)))
    ((Packed.popN src 1).seq (Packed.ofProgram (Program.push dst false)))

def decodeBody (src dst : Fin (k+1)) : Packed k :=
  (Packed.pop src).seq (decodeAfterTag src dst)

def decodeLoop (src dst : Fin (k+1)) : Packed k :=
  Packed.loop (fun h => (h src).getD false) (decodeBody src dst)

end ThreeMachine.StackCompiler.Raw

namespace ThreeMachine.StackCompiler.Tree
variable {V W : Type} [DecidableEq V] [DecidableEq W]

end ThreeMachine.StackCompiler.Tree

namespace ThreeMachine.StackCompiler.Routine
open ThreeMachine.StackCompiler.Tree
variable {f : Data → Data} {charge : Data → ℕ}
variable (R : Routine f charge)

noncomputable def number (i : R.Vars) : Fin (Fintype.card R.Vars+1) :=
  (Fintype.equivFin R.Vars i).succ

@[simp] theorem number_ne_zero (i : R.Vars) : R.number i ≠ 0 := Fin.succ_ne_zero _

noncomputable def numberedCode : Code (Fin (Fintype.card R.Vars+1)) := R.code.rename R.number

noncomputable def initRegs : Packed (Fintype.card R.Vars+4) :=
  Packed.ofProgram (Program.instruction (fun _ j =>
    if j.val < Fintype.card R.Vars+1 then .push false else .stay))

noncomputable def inputProgram : Packed (Fintype.card R.Vars+4) :=
  (Packed.ofProgram (Program.transfer 0 (temp 0))).seq
    (R.initRegs.seq (Raw.encodeLoop (temp 0) (reg (R.number R.input))))

@[simp] theorem temp_ne_zero : (temp (r := Fintype.card R.Vars+1) 0) ≠ 0 := by
  change temp 0 ≠ reg (0 : Fin (Fintype.card R.Vars+1))
  simp

@[simp] theorem reg_number_ne_zero (i : R.Vars) : reg (R.number i) ≠ 0 := by
  change reg (R.number i) ≠ reg (0 : Fin (Fintype.card R.Vars+1))
  simp

noncomputable def outputProgram : Packed (Fintype.card R.Vars+4) :=
  (Raw.decodeLoop (reg (R.number R.output)) (temp 0)).seq
    ((Packed.pop 0).seq (Packed.ofProgram (Program.transfer (temp 0) 0)))

noncomputable def rawProgram : Packed (Fintype.card R.Vars+4) :=
  R.inputProgram.seq (R.numberedCode.compile.seq R.outputProgram)

end ThreeMachine.StackCompiler.Routine
end

end OAI
end


section
-- module Main
namespace OAI

section
namespace ThreeMachine.StackCompiler

def requestRawBound (x : RequestData.Index) : ℕ :=
  2000*(Uniform.requestAnswer.time x.1 x.2+(RequestData.bits x).length+
    (Algorithm.output x.2.graph x.2.deadline).length+1)

abbrev SmallDeadline := {x : RequestData.Index // x.2.deadline.getD 0 ≤ x.1}

end ThreeMachine.StackCompiler

end

end OAI

namespace OAI
section
namespace ThreeMachine
open StackCompiler

end ThreeMachine
end
end OAI
end


