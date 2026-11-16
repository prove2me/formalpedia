-- Prove2me | Definitions.Def_NKtLB_Supplement_MKtP
-- name    : NKtLB_Supplement_MKtP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:23:48.454203+00:00
-- url     : https://prove2.me/theorems/44936a82-8b94-42dd-9d5f-220ec9e14298
-- title:
--   MKtP — the minimum Kt problem
-- statement:
--   **MKtP** is "the set of input pairs $(x,1^s)$ such that $x\in\{0,1\}^*$ and $\mathrm{Kt}(x)\le s$":
--   $$
--   \mathrm{MKtP}=\{(x,1^s) : \mathrm{Kt}(x)\le s\}.
--   $$
--   Whether MKtP is in P is a long-standing open problem in meta-complexity. Theorems 5 and 7 give lower bounds for it, conditional and unconditional.
--
--   **Formalization Note** The pair $(x,1^s)$ is encoded as in the base mission's MnKtP (`NKtLB.pairEnc`); $\mathrm{Kt}$ is unrelativized and taken with respect to $U$.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §3.4, p.24

import Mathlib
import Definitions.Def_NKtLB_Supplement_Kt
import Definitions.Def_NKtLB_pairEnc

namespace NKtLB.Supplement

/-- **MKtP** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §3.4, p.24): "We let MKtP denote the set of input pairs `(x, 1^s)` such that
`x ∈ {0,1}^*` and `Kt(x) ≤ s`." As a language: the encodings `pairEnc x s` with `Kt(x) ≤ s`.

**Formalization Note.** Same pair encoding as the base `MnKtP`; `Kt` unrelativized, relative to `U`. -/
def MKtP (U : Machine) : Set (List Bool) :=
  {z | ∃ (x : List Bool) (s : ℕ), z = pairEnc x s ∧ Kt U ∅ x [] [] ≤ s}

end NKtLB.Supplement


