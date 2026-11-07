-- Prove2me | Definitions.Def_KTUnitary_Synth_HasFPTEAS
-- name    : KTUnitary_Synth_HasFPTEAS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:26:24.310181+00:00
-- url     : https://prove2.me/theorems/0585aa73-ea37-49fa-b5fe-8df3e2c03722
-- title:
--   FPTEAS: polynomial-time exponential approximation scheme
-- statement:
--   An encoding function $f:\{0,1\}^*\to\mathbb R$ has a **fully polynomial time exponential approximation scheme** (FPTEAS) if there are a deterministic Turing machine $M$ (without oracle) and a polynomial $p$ such that for every $x\in\{0,1\}^*$ and every $\lambda\in\mathbb N$, on input $(x,1^\lambda)$ the machine halts within $p(|x|+\lambda)$ steps and outputs a fixed-point number $\phi$ with
--   $$|\phi-f(x)|\le 2^{-\lambda}.$$
--
--   The values of an FPTEAS are the numbers the circuits of the paper may use as exact gate entries: gates are written down by strings $x$ and evaluated through $f(x)$.
--
--   **Formalization Note** The precision is $\varepsilon=2^{-\lambda}$, passed in unary, so the time bound $p(|x|+\lambda)$ is $\mathrm{poly}(|x|,\log 1/\varepsilon)$ (footnote 4: "We will always assume $\varepsilon=2^{-\lambda}$ for some $\lambda\in\mathbb N$ without loss of generality"). Machines are the published deterministic oracle Turing machines `QAdvFew.PoQOracle.OTM` run with the empty oracle; the pair is passed as `tup [x, 1^λ]`.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.1 and footnote 4, p. 14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_OTM
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_KTUnitary_Synth_fixedPoint

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace KTUnitary.Synth

/-- **FPTEAS** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*, arXiv:2610.03705 (revision of 2026-10-31), Definition 4.1, p. 14): an encoding function `f : {0,1}* → ℝ` has a fully
polynomial time exponential approximation scheme if a polynomial-time Turing machine `M` outputs,
on `(x, ε)`, a fixed-point number `ϕ` with `|ϕ − f(x)| ≤ ε`; the time bound is
`poly(|x|, log 1/ε)`.

Here: one machine `M` (without oracle) and one polynomial `p` such that for every `x` and every
`l`, on input `tup [x, 1^l]` the machine halts within `p(|x| + l)` steps and its output `ϕ`
(decoded by `fixedPoint`) satisfies `|ϕ − f(x)| ≤ 2^{−l}`.

**Formalization Note** `ε = 2^{−l}` with `l ∈ ℕ` (footnote 4, p. 14: "We will always assume
`ε = 2^{−λ}` for some `λ ∈ ℕ` without loss of generality"); `ε` is passed in unary as `1^l`,
whose length is that of the fixed-point code of `2^{−l}` up to a constant, so the time bound
`p(|x| + l)` is `poly(|x|, log 1/ε)`. The machine has the empty oracle (`fun _ => false`). -/
def HasFPTEAS (f : Str → ℝ) : Prop :=
  ∃ (M : OTM) (p : Polynomial ℕ), ∀ (x : Str) (l : ℕ),
    M.result (fun _ => false) (tup [x, unary l]) (p.eval (x.length + l)) ≠ none ∧
    |((fixedPoint (M.output (fun _ => false) (tup [x, unary l]) (p.eval (x.length + l))) : ℚ) : ℝ)
      - f x| ≤ (2 : ℝ)⁻¹ ^ l

end KTUnitary.Synth


