-- Prove2me | Definitions.Def_NKtLB_Supplement_sampProb
-- name    : NKtLB_Supplement_sampProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:36:23.157482+00:00
-- url     : https://prove2.me/theorems/5ed77e56-01d5-4b2d-997c-c019c880cf7c
-- title:
--   $\Pr_{(x,y)\sim D_n}[E]$ for a sampled family
-- statement:
--   For a sampler $(A,q)$, $\Pr_{(x,y)\sim D_n}[E(x,y)]$ is the fraction of random strings $r\in\{0,1\}^{n^q+q}$ on which $A(1^n;r)$ outputs a pair $(x,y)\in\{0,1\}^n\times\{0,1\}^n$ satisfying $E$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Theorems 56 and 58, pp.37–38

import Mathlib
import Definitions.Def_NKtLB_Machine
import Definitions.Def_NKtLB_tupleEnc
import Definitions.Def_NKtLB_prob

namespace NKtLB.Supplement

/-- **`Pr_{(x,y)∼D_n}[E(x, y)]`** for the distribution `D_n` sampled by `A` with `n^q + q` random bits
(see `IsPolySampler`; Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Theorems 56 and 58, pp.37–38): the fraction of `r ∈ {0,1}^{n^q + q}` on
which `A(1^n; r)` halts within `n^q + q` steps with output `tupleEnc [x, y]` for some `x, y ∈ {0,1}^n`
satisfying `E`. -/
noncomputable def sampProb (A : Machine) (q n : ℕ) (E : List Bool → List Bool → Prop) : ℝ :=
  prob (n ^ q + q) (fun r => ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
    A.HaltsWith ∅ ⟨List.replicate n true, [], [], r⟩ (n ^ q + q) (bitsSym (tupleEnc [x, y])) ∧ E x y)

end NKtLB.Supplement


