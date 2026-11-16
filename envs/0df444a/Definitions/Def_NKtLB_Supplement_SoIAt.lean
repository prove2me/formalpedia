-- Prove2me | Definitions.Def_NKtLB_Supplement_SoIAt
-- name    : NKtLB_Supplement_SoIAt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:23:20.060208+00:00
-- url     : https://prove2.me/theorems/62e23e2a-4d02-43a8-9999-5e141aa217ca
-- title:
--   Symmetry of information at length $n$ with error $e$
-- statement:
--   For a complexity measure $\mu$ (a function of a string and a conditional string), a length $n$ and an error $e\in\mathbb R$, **symmetry of information holds at length $n$ with error $e$** if for all $x,y\in\{0,1\}^n$
--   $$
--   \mu(x,y)\ \ge\ \mu(x)+\mu(y\mid x)-e .
--   $$
--   The paper says that "SoI holds for nKt with error $e(n)$" if this holds at every length $n$ with error $e(n)$ (p.5), and uses the same terminology for $rn\mathrm{Kt}$ and $pn\mathrm{Kt}$. The reverse inequality, up to small terms, holds for all these measures, so the question is whether the joint complexity can be much smaller than the sum.
--
--   **Formalization Note** $\mu(x,y)$ is $\mu$ of the encoded pair (base `NKtLB.tupleEnc`) with empty conditional, and $\mu(y\mid x)$ has conditional string $x$. Values are compared in the extended reals (`NKtLB.toEReal`).
-- source:
--   Goldberg, Hu, Lu, Lyu, Oliveira, Asymmetry and Complexity of Nondeterministic Computations, arXiv:2610.20188 (version of October 13, 2026), §1.1.1, p.5

import Mathlib
import Definitions.Def_NKtLB_toEReal
import Definitions.Def_NKtLB_tupleEnc

namespace NKtLB.Supplement

/-- **Symmetry of information at length `n` with error `e`** (Goldberg, Hu, Lu, Lyu, Oliveira, *Asymmetry and Complexity of Nondeterministic Computations*, arXiv:2610.20188 (version of October 13, 2026), §1.1.1, p.5): "We say that SoI
holds for nKt with error `e(n)` if, for all `x, y ∈ {0,1}^n`, `nKt(x, y) ≥ nKt(x) + nKt(y | x) − e(n)`.
… We use the analogous terminology for rnKt and pnKt."

For a measure `μ` (a function of a string and a conditional string): for all `x, y` of length `n`,
`μ(x, y) ≥ μ(x) + μ(y | x) − e`, where `μ(x, y)` is `μ` of the encoded pair `tupleEnc [x, y]` with
empty conditional and `μ(y | x)` has conditional string `x`.

**Formalization Note.** Values compared in `EReal` through `toEReal` (`⊤ − e = ⊤`). The pair
`(x, y)` is encoded with the base `tupleEnc` (the paper leaves the pairing implicit, p.22: "robust
with respect to encoding choices"). -/
def SoIAt (mu : List Bool → List Bool → ℕ∞) (n : ℕ) (e : ℝ) : Prop :=
  ∀ x y : List Bool, x.length = n → y.length = n →
    toEReal (mu x []) + toEReal (mu y x) - (e : EReal) ≤ toEReal (mu (tupleEnc [x, y]) [])

end NKtLB.Supplement


