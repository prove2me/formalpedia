-- Prove2me | Definitions.Def_FriedgutCoalition_maxSel
-- name    : FriedgutCoalition_maxSel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:41.039329+00:00
-- url     : https://prove2.me/theorems/18c5254c-2835-4893-bcf4-1ed10847ca99
-- title:
--   The max selector $\phi_a$, the encoded function $g$ of eq. (1) and the law $\mathbf A$ (Definition 4.1)
-- statement:
--   Let $r\ge1$, $\ell\in\mathbb N$ and $a=(a_1,\dots,a_\ell)\in[r]^\ell$. The max selector $\phi_a:\{0,1\}^\ell\to[r]$ is
--
--   $$\phi_a(y)=\begin{cases}a_{\max\{i\in[\ell]:\,y_i=1\}} & y\ne0^\ell,\\ 1 & y=0^\ell.\end{cases}$$
--
--   For $f:[r]^n\to\{0,1\}$, the encoded function on $m=\ell n$ bits decodes each block of $\ell$ bits by $\phi_a$:
--
--   $$g(y)=f\big(\phi_a(y_1,\dots,y_\ell),\dots,\phi_a(y_{m-\ell+1},\dots,y_m)\big).\qquad(1)$$
--
--   The distribution $\mathbf A$ on $[r]$ is the law of $\phi_a(y)$ for $y\sim\mu_p^\ell$, that is $\mathbf A(i)=\Pr_{y\sim\mu_p^\ell}[\phi_a(y)=i]$.
--
--   For nondecreasing $a$, every nonconstant threshold of $\phi_a$ is an OR of some encoding bits; this is how the paper turns influence towards $0$ into $p$-biased influence.
--
--   **Formalization Note** $[r]$ is `Fin r` with $r\ge1$; its value $1$ is `0 : Fin r`. The selector is defined for every $a$, and the theorems assume $a$ nondecreasing where the paper does. The $m=\ell n$ bits of (1) are indexed by pairs $(j,k)\in[n]\times[\ell]$, block $j$ being the paper's bits $(j-1)\ell+1,\dots,j\ell$ in the same order.
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Definition 4.1 and eq. (1), p.11

import Mathlib
import Definitions.Def_FriedgutCoalition_wProb

namespace FriedgutCoalition

/-!
# The max selector `ϕ_a`, the encoded function and the law `A` (Definition 4.1, eq. (1))

E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on Influential Coalitions*,
arXiv:2609.16401 (held file sha256 51f298ff…), Definition 4.1 and eq. (1), p.11.

For a nondecreasing `a = (a₁, …, a_ℓ) ∈ [r]^ℓ`, `ϕ_a(y) = a_{max{i ∈ [ℓ] : y_i = 1}}` if `y ≠ 0^ℓ` and
`ϕ_a(0^ℓ) = 1`. With `m = ℓ·n`, `g(y) = f(ϕ_a(y₁, …, y_ℓ), …, ϕ_a(y_{m−ℓ+1}, …, y_m))` (eq. (1)), and `A`
is the law of `ϕ_a(y)` for `y ∼ µ^ℓ_p`.

**Formalization Note.** `[r]` is `Fin r` (`[NeZero r]`, i.e. `r ≥ 1`), its value `1` is `0 : Fin r`, so
`ϕ_a(0^ℓ) = 0`. Bits are `Bool`, `1 = true`. The function `maxSel` is defined for every `a`; the
statements that need `a` nondecreasing assume `Monotone a`. The `m = ℓn` bits of eq. (1) are indexed by
`Fin n × Fin ℓ`: block `j` is `{j} × Fin ℓ`, the paper's bits `(j − 1)ℓ + 1, …, jℓ`, in the same order.
`selLaw p a i = Pr_{y ∼ µ^ℓ_p}[ϕ_a(y) = i]` is `A` as weights on `Fin r`.
-/

/-- The max selector `ϕ_a(y)` of Definition 4.1: `a` at the largest index `k` with `y k = true`, or the
value `1` of `[r]` (that is, `0 : Fin r`) when `y` is all `false`. -/
noncomputable def maxSel {ℓ r : ℕ} [NeZero r] (a : Fin ℓ → Fin r) (y : Fin ℓ → Bool) : Fin r :=
  if h : (Finset.univ.filter (fun k => y k = true)).Nonempty then
    a ((Finset.univ.filter (fun k => y k = true)).max' h)
  else 0

/-- The encoded function `g` of eq. (1): block `j` of `ℓ` bits is decoded by `ϕ_a` into coordinate `j`
of `f`. -/
noncomputable def encodeFn {n ℓ r : ℕ} [NeZero r] (a : Fin ℓ → Fin r) (f : (Fin n → Fin r) → Bool) :
    (Fin n × Fin ℓ → Bool) → Bool :=
  fun y => f (fun j => maxSel a (fun k => y (j, k)))

/-- The distribution `A` on `[r]`: `A(i) = Pr_{y ∼ µ^ℓ_p}[ϕ_a(y) = i]`. -/
noncomputable def selLaw {ℓ r : ℕ} [NeZero r] (p : ℝ) (a : Fin ℓ → Fin r) : Fin r → ℝ :=
  fun i => wProb (bern p) (fun y : Fin ℓ → Bool => maxSel a y = i)

end FriedgutCoalition


