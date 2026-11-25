-- Prove2me | Definitions.Def_DetDLP_M89_S1_Plans
-- name    : DetDLP_M89_S1_Plans
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T00:32:57.962235+00:00
-- url     : https://prove2.me/theorems/98b7ce63-6a91-4409-b81a-53273f6ffee0
-- title:
--   Stage I seed plans and their block semantics
-- statement:
--   A seed plan is either the small-group marker or the threshold and a winning full seed. Define its word representation and the finite set of permitted elements in each block, for both the multiplicative and elliptic-curve groups.
-- source:
--   S. Liu, B. Zhang, and K. Ren, A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem, Zhejiang University Preprint, 23 November 2026, Section 3.1–3.2 (pp. 11–13), proof of Theorem 3.1; Stage I machine model of Section 2.

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false
namespace DetDLP
open M89S1 OAI.Algorithms.SubexponentialSAT OAI.Algorithms.SubexponentialSAT.Computation
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- `none` is the full-group branch; `some` carries the threshold and the winning seed. -/
def m89_fp_plan_ok {p m : ℕ} [Fact p.Prime] : Option (ℕ × FpSeed p m) → Prop
  | none => ¬ (64 ≤ p-1 ∧ 4096*m ≤ p-1)
  | some (t,s) => 64 ≤ p-1 ∧ 4096*m ≤ p-1 ∧ t = hashThreshold p (p-1) m (p-1) ∧ s ∈ winners fpBits (fpCost p m)

def m89_fp_plan_word {p m : ℕ} : Option (ℕ × FpSeed p m) → List Bool
  | none => [false]
  | some (t,s) => true :: Encoding.encodeList id [countWord t, List.ofFn (fpBits s)]

def m89_fp_plan_block {p m : ℕ} [Fact p.Prime] : Option (ℕ × FpSeed p m) → Fin m → Finset (ZMod p)ˣ
  | none => fun _ => Finset.univ
  | some (t,s) => fpFactorBlock (p := p) t s

def m89_ec_plan_ok {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) : Option (ℕ × ECSeed p m) → Prop
  | none => letI := ecPointFintype E; let g := Fintype.card E.toAffine.Point; ¬ (64 ≤ g ∧ 4096*m ≤ g-1)
  | some (t,s) => letI := ecPointFintype E; let g := Fintype.card E.toAffine.Point
                   64 ≤ g ∧ 4096*m ≤ g-1 ∧ t = hashThreshold p (g-1) m g ∧ s ∈ winners ecBits (ecCost E)

def m89_ec_plan_word {p m : ℕ} : Option (ℕ × ECSeed p m) → List Bool
  | none => [false]
  | some (t,s) => true :: Encoding.encodeList id [countWord t, List.ofFn (ecBits s)]

noncomputable def m89_ec_plan_block {p m : ℕ} [Fact p.Prime] (E : WeierstrassCurve (ZMod p)) : Option (ℕ × ECSeed p m) → Fin m → Finset E.toAffine.Point
  | none => letI := ecPointFintype E; fun _ => Finset.univ
  | some (t,s) => ecFactorBlock E t s

end DetDLP


