-- Prove2me | Definitions.Def_Helfgott_MobiusReciprocalCertificate
-- name    : Helfgott_MobiusReciprocalCertificate
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-10-08T22:13:06.186998+00:00
-- url     : https://prove2.me/theorems/159787c4-b8bd-4261-bb38-f9b758361936
-- title:
--   Finite integer reciprocal Mobius certificate checker
-- statement:
--   Generic finite data and arithmetic checks for rounded reciprocal sums. At scale $Q$, a block records the initial and final values of $\sum_{n<N}g(n)\lfloor Q/n\rfloor$, checks each transition, and checks $10(|S_n|+n)K\le3Q$ on the required range. Its logarithm tier uses an explicit rationally certified cutoff grid. A balanced tree joins adjacent block endpoints. These are pure definitions; soundness and concrete numerical checks are separate theorem obligations.
-- source:
--   Original exact integer certificate definitions for reciprocal Mobius decay in the Helfgott minor-arc route. Written by Codex.

import Mathlib.Data.Finset.Range
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Basic

set_option autoImplicit false
open scoped BigOperators
namespace Helfgott

def mobiusRoundedPrefix (g : ℕ → ℤ) (Q n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range n, g i * (Q / i : ℕ)

def mobiusReciprocalLogGrid : List (ℕ × ℕ) := [(94, 12088), (95, 13359), (96, 14764), (97, 16317), (98, 18033), (99, 19930), (100, 22026), (101, 24343), (102, 26903), (103, 29732), (104, 32859), (105, 36315), (106, 40134), (107, 44355), (108, 49020), (109, 54176), (110, 59874), (111, 66171), (112, 73130), (113, 80821), (114, 89321), (115, 98715), (116, 109097), (117, 120571), (118, 133252), (119, 147266), (120, 162754), (121, 179871), (122, 198789), (123, 219695), (124, 242801), (125, 268337), (126, 296558), (127, 327747), (128, 362217), (129, 400312), (130, 442413), (131, 488942), (132, 540364), (133, 597195), (134, 660003), (135, 729416), (136, 806129), (137, 890911), (138, 984609), (139, 1088161), (140, 1202604)]

def mobiusReciprocalScan (g : ℕ → ℤ) (Q A B K : ℕ) :
    ℕ → ℕ → ℤ → Bool × ℤ
  | 0, _, s => (true, s)
  | fuel + 1, n, s =>
      if n < B then
        let next := s + g n * (Q / n : ℕ)
        let own := if A ≤ n then decide (10 * (next.natAbs + n) * K ≤ 3 * Q) else true
        let rest := mobiusReciprocalScan g Q A B K fuel (n + 1) next
        (own && rest.1, rest.2)
      else (true, s)

inductive MobiusReciprocalTree where
  | leaf (start finish : ℤ) (tier cutoff : ℕ)
  | branch (left right : MobiusReciprocalTree)

def mobiusReciprocalStart : MobiusReciprocalTree → ℤ
  | .leaf start _ _ _ => start
  | .branch l _ => mobiusReciprocalStart l

def mobiusReciprocalFinish : MobiusReciprocalTree → ℤ
  | .leaf _ finish _ _ => finish
  | .branch _ r => mobiusReciprocalFinish r

def mobiusReciprocalLeafCheck (g : ℕ → ℤ) (Q A B offset K T : ℕ)
    (start finish : ℤ) : Bool :=
  let scan := mobiusReciprocalScan g Q A B K 32 offset start
  scan.1 && (scan.2 == finish) &&
    (if A < offset + 32 ∧ offset < B then
      decide ((K, T) ∈ mobiusReciprocalLogGrid) && decide (offset + 32 ≤ T)
    else true)

def mobiusReciprocalTreeCheck (g : ℕ → ℤ) (Q A B : ℕ) :
    ℕ → ℕ → MobiusReciprocalTree → Bool
  | d, offset, tree =>
      if B ≤ offset then mobiusReciprocalStart tree == mobiusReciprocalFinish tree else
      match d, tree with
      | 0, .leaf start finish K T =>
          mobiusReciprocalLeafCheck g Q A B offset K T start finish
      | d + 1, .branch l r =>
          mobiusReciprocalTreeCheck g Q A B d offset l &&
          mobiusReciprocalTreeCheck g Q A B d (offset + 32 * 2 ^ d) r &&
          (mobiusReciprocalFinish l == mobiusReciprocalStart r)
      | _, _ => false

end Helfgott


