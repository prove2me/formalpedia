-- Prove2me | Definitions.Def_NKtLB_Supplement_FewEXP
-- name    : NKtLB_Supplement_FewEXP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:32:40.505919+00:00
-- url     : https://prove2.me/theorems/3affb344-3ba8-4aa9-9090-70446327c284
-- title:
--   $\mathsf{FewEXP}$
-- statement:
--   "FewEXP is the set of languages in NEXP where each positive instance admits at most $2^{\mathrm{poly}(n)}$ witnesses" (p.9). Concretely, $L\in\mathsf{FewEXP}$ if there are a verifier $M$ and constants $k,c$ such that, with witness length $g=2^{|x|^k}$,
--   $$
--   x\in L\iff\exists w\in\{0,1\}^g:\ M(x;w)\text{ accepts within }c\,g+c\text{ steps},
--   $$
--   and for every $x$ at most $2^{c|x|^k+c}$ witnesses $w\in\{0,1\}^g$ are accepted. $\mathsf{EXP}\subseteq\mathsf{FewEXP}\subseteq\mathsf{NEXP}$.
--
--   **Formalization Note** Machines are those of the base mission (`NKtLB.Machine`): multi-tape, with input, auxiliary, guess and randomness tapes and an oracle. $O(T)$ time is read as $c\cdot T+c$ steps for a constant $c$, as in the base `NKtLB.NTIME`. Witnesses have length exactly $2^{|x|^k}$ (as in the paper's Claim 76, p.48).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.2.2, p.9

import Mathlib
import Definitions.Def_NKtLB_Machine

namespace NKtLB.Supplement

/-- **`FewEXP`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.2.2, p.9): "Recall that FewEXP is the set of languages in NEXP where each
positive instance admits at most `2^{poly(n)}` witnesses." There are `k`, `c` and a verifier `M` such
that, with witness length `g = 2^{|x|^k}` and time `c·g + c`: `x ∈ L` iff some `w ∈ {0,1}^g` makes `M`
(input `x`, guess `w`) halt within `c·g + c` steps with output `1`; and for every `x` at most
`2^{c·|x|^k + c}` strings `w ∈ {0,1}^g` are accepted.

**Formalization Note.** Witnesses have length exactly `2^{|x|^k}` (the paper's Claim 76, p.48:
"assume each witness has length exactly `2^{ℓ^α}`"). -/
def FewEXP : Set (Set (List Bool)) :=
  {L | ∃ (M : Machine) (k c : ℕ), ∀ x : List Bool,
    (x ∈ L ↔ ∃ w : List Bool, w.length = 2 ^ (x.length ^ k) ∧
      M.HaltsWith ∅ ⟨x, [], w, []⟩ (c * 2 ^ (x.length ^ k) + c) [Sym.one]) ∧
    Set.ncard {w : List Bool | w.length = 2 ^ (x.length ^ k) ∧
      M.HaltsWith ∅ ⟨x, [], w, []⟩ (c * 2 ^ (x.length ^ k) + c) [Sym.one]} ≤ 2 ^ (c * x.length ^ k + c)}

end NKtLB.Supplement


