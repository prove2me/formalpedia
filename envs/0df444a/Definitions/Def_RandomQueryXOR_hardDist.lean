-- Prove2me | Definitions.Def_RandomQueryXOR_hardDist
-- name    : RandomQueryXOR_hardDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:57:44.254007+00:00
-- url     : https://prove2.me/theorems/ff247ad1-2edd-4a86-b932-70d71f48200d
-- title:
--   Hard input distribution $\mathcal D_{f\oplus}$
-- statement:
--   Let $f:\{0,1\}^n\to\{0,1\}$ and $x^\star\in\{0,1\}^n$. The distribution $\mathcal D_{f\oplus}$ on $\{0,1\}^{2n}$ samples $y$ as follows:
--
--   1. for each $i\in[n]$ that is a sensitive bit of $x^\star$ with $x^\star(i)=0$, draw $y(2i-1)\in\{0,1\}$ uniformly and set $y(2i)=y(2i-1)$;
--   2. for every other $i\in[n]$, set $y(2i-1)=0$ and $y(2i)=x^\star(i)$.
--
--   The draws in (1) are independent. Every such $y$ has pair-parities equal to $x^\star$, so $g=f\circ\oplus_2$ is constant on the support, while flipping one bit of a planted pair flips $g$ (Observation 4.3). The information cost of Lemma 4.16 is measured under this distribution.
--
--   **Formalization Note** $\mathcal D_{f\oplus}$ is the push-forward of the uniform distribution on $u\in\{0,1\}^n$ under $u\mapsto y$, with $u(i)$ the common value of a planted pair; the unused coordinates of $u$ make it uniform on the $2^d$ inputs of the displayed form, $d=\mathrm{sens}_0[f,x^\star]$. It is defined for every $x^\star$ (the paper's $x^\star_f$ is a maximum-sensitivity input). Pairs are 0-based as in `xorLift`.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, p.16 (PDF p.18), distribution $D_{f⊕}$

import Mathlib
import Definitions.Def_WildeQIT_FinDist
import Definitions.Def_RandomQueryXOR_sens
import Definitions.Def_ShallowShadows_ShadowNorm_uniformDist
import Definitions.Def_RandomQueryXOR_uniformOn

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

open WildeQIT
open ShallowShadows.ShadowNorm (uniformDist)

/-- The input `y ∈ {0,1}^{2n}` of `D_{f⊕}` built from bits `u ∈ {0,1}^n`: on the `i`-th pair,
`y(2i − 1) = y(2i) = u(i)` if `i` is a sensitive zero of `x⋆`, and `y(2i − 1) = 0`,
`y(2i) = x⋆(i)` otherwise. 0-based: index `j` of `Fin (2 * n)` lies in pair `j / 2`, as its
first element (`2i − 1`) if `j` is even. -/
def hardY {n : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) (u : Fin n → Bool) :
    Fin (2 * n) → Bool := fun j =>
  if (⟨j.val / 2, by omega⟩ : Fin n) ∈ sensZeros f xs then u ⟨j.val / 2, by omega⟩
  else if j.val % 2 = 0 then false else xs ⟨j.val / 2, by omega⟩

/-- The hard distribution `D_{f⊕}` over `{0,1}^{2n}` (Garg, Sundaresan, Velusamy,
*XOR-Functions and Beyond in the Random Query Model*, arXiv:2611.04353, p.16 = PDF p.18):
"Sample y ∈ {0, 1}^{2n} as follows: (i) For i ∈ [n], if i is one of the sensitive bits for f in
x⋆_f and x⋆_f(i) = 0, we sample y(2i − 1) ∈ {0, 1} uniformly at random and fix y(2i) = y(2i − 1).
(ii) For all other i ∈ [n], we fix y(2i − 1) = 0 and y(2i) = x⋆_f(i)."

**Formalization Note** `D_{f⊕}` is the law of `hardY f xs u` for `u` uniform on `{0,1}^n`: the
coordinates of `u` outside the sensitive zeros are unused, so this is the uniform distribution
on the `2^d` inputs of the displayed form (`d = sens0[f, x⋆]`), the independent fair bits of
(i). It is defined for every `x⋆ = xs`; the paper's `x⋆_f` is a maximum-sensitivity input
(Assumption 4.2). Pairs are 0-based as in `xorLift`. -/
noncomputable def hardDist {n : ℕ} (f : (Fin n → Bool) → Bool) (xs : Fin n → Bool) :
    FinDist (Fin (2 * n) → Bool) :=
  (uniformDist (Fin n → Bool)).map (hardY f xs)

end RandomQueryXOR


