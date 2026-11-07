-- Prove2me | Definitions.Def_KTUnitary_Synth_HasFPSEAS
-- name    : KTUnitary_Synth_HasFPSEAS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:37.836499+00:00
-- url     : https://prove2.me/theorems/603bc11c-43bc-4494-b616-26a8a6ba2542
-- title:
--   FPSEAS relative to a language $L$
-- statement:
--   Let $L$ be a language. An encoding function $f:\{0,1\}^*\to\mathbb R$ has a **fully polynomial space exponential approximation scheme relative to $L$** if there are a deterministic $L$-oracle Turing machine $M$ and a polynomial $p$ such that for every $x$ and $\lambda$, the run of $M^L$ on $(x,1^\lambda)$ halts, visits at most $p(|x|+\lambda)$ tape cells (work tape and oracle query tape together), and outputs $\phi$ with $|\phi-f(x)|\le 2^{-\lambda}$.
--
--   This is item 6 of the entrywise characterization of $\mathsf{unitaryPSPACE}^L$ (Theorem 6.17).
--
--   **Formalization Note** The running time is unbounded. The output is read from the work tape, so its length is at most the space bound ("the output has polynomial length"). $\varepsilon=2^{-\lambda}$ in unary, as for the FPTEAS.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.1, p. 14; footnote 8, p. 25

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_fixedPoint

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **FPSEAS relative to a language `L`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.1, p. 14, and footnote 8, p. 25):
defined as an FPTEAS, "but where `M` is a polynomial-space Turing machine, and the output has
polynomial length"; relative to `L`, "`M` may be an `L`-oracle Turing machine".

Here: one `L`-oracle machine `M` and one polynomial `p` such that for every `x` and `l` there is
a step count `T` at which `M^L(tup [x, 1^l])` has halted, has visited at most `p(|x| + l)` cells
(work tape and query tape together), and outputs `ϕ` with `|ϕ − f(x)| ≤ 2^{−l}`.

**Formalization Note** `ε = 2^{−l}` in unary, as in `HasFPTEAS` (footnote 4, p. 14). The output
sits on the work tape, so its length is at most the space bound: "the output has polynomial
length". The running time is not bounded. The unrelativized FPSEAS is the case
`L = fun _ => false`. -/
def HasFPSEAS (L : Oracle) (f : Str → ℝ) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ (x : Str) (l : ℕ), ∃ T : ℕ,
    M.result L (tup [x, unary l]) T ≠ none ∧
    M.space L (tup [x, unary l]) T ≤ p.eval (x.length + l) ∧
    |((fixedPoint (M.output L (tup [x, unary l]) T) : ℚ) : ℝ) - f x| ≤ (2 : ℝ)⁻¹ ^ l

end KTUnitary.Synth


