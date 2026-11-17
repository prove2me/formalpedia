-- Prove2me | Definitions.Def_SubspaceConv_Supplement_kernelMul
-- name    : SubspaceConv_Supplement_kernelMul
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:46:14.407776+00:00
-- url     : https://prove2.me/theorems/157b9a2a-a419-4c36-a0c1-0f07e941232f
-- title:
--   Grassmann-graph distance and intersection-kernel product $Kf$
-- statement:
--   Let $V = \mathrm{Gr}_q(n,k)$ with $k \le n$, and put $d = \min(k, n-k)$. The **Grassmann-graph distance** of $U, W \in V$ is
--
--   $$\mathrm{dist}(U,W) = k - \dim(U \cap W) \in \{0, \dots, d\}.$$
--
--   Given coefficients $a_0, \dots, a_d$ in a commutative ring $R$ and weights $f : V \to R$, the **intersection kernel** $K(U,W) = a_{\mathrm{dist}(U,W)}$ acts by
--
--   $$(Kf)(U) = \sum_{W \in V} a_{\mathrm{dist}(U,W)}\, f(W), \qquad U \in V.$$
--
--   This is the product computed fast in Theorem 3.
--
--   **Formalization Note** The coefficients are a table indexed by $\{0, \dots, d\}$; since the distance never exceeds $d$, the fallback value $0$ used to make the index typecheck is never reached.
-- source:
--   Perles, Weinstein, A Fast Algorithm for Subspace Convolution, STOC 2027 submission manuscript (sha256 a8ffb1b4e583122875209a3e25ee95aa3a7af933526e165d47c274634e604ab2), §1.1.1, p.3 (PDF p.4)

import Mathlib
import Definitions.Def_SubspaceConv_Supplement_Gr

set_option autoImplicit false

namespace SubspaceConv.Supplement

variable {F : Type*} [Field F] [Fintype F] {n k : ℕ}

/-- The **Grassmann-graph distance** on `V = Gr_q(n, k)` (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1.1, p.3 (PDF p.4)):
`dist(U, W) = k − dim(U ∩ W)`.

**Formalization Note** `U ∩ W` is the infimum `U ⊓ W` of submodules; the subtraction is in `ℕ`
and never truncates, since `dim(U ∩ W) ≤ dim U = k`. -/
noncomputable def grassDist (U W : Gr F n k) : ℕ :=
  k - Module.finrank F ↥(U.1 ⊓ W.1)

/-- The **intersection-kernel product** (Perles–Weinstein, *A Fast Algorithm for Subspace Convolution*, STOC 2027 submission manuscript (sha256 a8ffb1b4…604ab2), §1.1.1, p.3 (PDF p.4)): with `d = min(k, n − k)`,
coefficients `a_0, …, a_d` and weights `f : V → R`,
`(Kf)(U) = ∑_{W ∈ V} a_{dist(U,W)} f(W)`.

**Formalization Note** The coefficients are a table `a : Fin (d + 1) → A`. The distance never
exceeds `d` (paper p.3: "its maximum is d"), so the fallback value `0` in the dependent `if` is
never used; it only makes the index `dist(U, W)` typecheck as an element of `Fin (d + 1)`. -/
noncomputable def kernelMul {A : Type*} [CommRing A] (a : Fin (min k (n - k) + 1) → A)
    (f : Gr F n k → A) (U : Gr F n k) : A :=
  ∑ W : Gr F n k,
    (if h : grassDist U W < min k (n - k) + 1 then a ⟨grassDist U W, h⟩ else 0) * f W

end SubspaceConv.Supplement


