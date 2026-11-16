-- Prove2me | Definitions.Def_NKtLB_Supplement_KtPar
-- name    : NKtLB_Supplement_KtPar
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:22:49.225188+00:00
-- url     : https://prove2.me/theorems/f16461e0-e981-4a3d-b1b1-c1ece364bbe3
-- title:
--   $\mathrm{Kt}^{\|d\,O}(x\mid y)$ — Levin complexity with $d$ levels of adaptivity
-- statement:
--   For an oracle $O$ and $d\in\mathbb N$, $\mathrm{Kt}^{\|d\,O}$ is "the complexity measure $\mathrm{Kt}$ wherein the universal machine may make oracle calls to $O$ with up to $d$ levels of adaptivity":
--   $$
--   \mathrm{Kt}^{\|d\,O}(x\mid y)=\min_{\Pi,\;t}\bigl\{\,|\Pi|+\lceil\log t\rceil : \Pi^O(y)\text{ outputs }x\text{ within }t\text{ steps, using at most }d\text{ rounds of queries}\bigr\}.
--   $$
--   Theorem 124 uses $d=2$ and $O=\mathrm{SAT}$.
--
--   **Formalization Note** The rounds are those of `AdaptRounds`, counted for the run of $U$ on the program. Values in `ℕ∞`.
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), Appendix A, Theorem 124, p.96

import Mathlib
import Definitions.Def_NKtLB_Supplement_AdaptRounds

namespace NKtLB.Supplement

/-- **`Kt^{∥d O}(x | y)`, Levin–Kolmogorov complexity with `d` levels of adaptive oracle access**
(Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), Appendix A, Theorem 124, p.96): "for an oracle `O` and a constant `d ∈ ℕ`, `Kt^{∥d O}` refers to
the complexity measure `Kt` wherein the universal machine may make oracle calls to `O` with up to
`d` levels of adaptivity."

`Kt` (Definition 12, p.22) restricted to runs of `U` (program `p`, auxiliary string `y`, empty guess
and randomness tapes, oracle `O`) whose first `t` steps make at most `d` rounds of queries.

**Formalization Note.** `⌈log t⌉ = Nat.clog 2 t`; value in `ℕ∞`; the rounds are `AdaptRounds`. -/
noncomputable def KtPar (U : Machine) (O : Set (List Bool)) (d : ℕ) (x y : List Bool) : ℕ∞ :=
  ⨅ (p : List Bool) (t : ℕ)
    (_ : U.HaltsWith O ⟨p, y, [], []⟩ t (bitsSym x) ∧ AdaptRounds U O ⟨p, y, [], []⟩ t d),
    ((p.length + Nat.clog 2 t : ℕ) : ℕ∞)

end NKtLB.Supplement


