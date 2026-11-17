-- Prove2me | Definitions.Def_DetParamSVP_Supplement_LocallyDenseCode
-- name    : DetParamSVP_Supplement_LocallyDenseCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:12:26.914314+00:00
-- url     : https://prove2.me/theorems/3fbe0c08-dd8e-463b-81f7-35711d802ee6
-- title:
--   Locally dense codes $(C,s,S)$ with parameters $(m,k,D,r)$ (Definition 4.1)
-- statement:
--   Let $p$ be prime and let $m,k,D,r$ be positive integers. Let $C\subseteq\mathbb F_p^N$ be a linear code, given by a parity-check matrix $H$ (so $C=\{c: Hc=0\}$), let $s\in\mathbb F_p^N$, and let $S=(x_1,\dots,x_m)$ be an ordered list of $m$ distinct coordinates; write $v|_S=(v_{x_1},\dots,v_{x_m})$ and $C-s=\{c-s:c\in C\}$. The tuple $(C,s,S)$ is an **$(m,k,D,r)$-locally dense code** if
--
--   1. $\lambda(C)>D$, i.e. every nonzero codeword has Hamming weight greater than $D$;
--   2. $s|_S=0$;
--   3. for every $u\in\mathbb F_p^m$ with $\|u\|_0\le k$ there is a **nonzero** $w\in C-s$ with
--   $$\|w\|_0\le r\qquad\text{and}\qquad w|_S=u .$$
--
--   Locally dense codes are the advice of the non-uniform reduction from NCP to MDP (Theorem 4.2); Theorem 4.3 constructs them deterministically.
--
--   **Formalization Note** The coordinates form any finite type ($\mathrm{Fin}\,N$ in the algorithmic statements). $S$ is an injective map from $\{0,\dots,m-1\}$ to the coordinates, and $w\in C-s$ is written $H(w+s)=0$. The positivity of $m,k,D,r$, primality of $p$ and distinctness of $S$ are bundled. Condition 1 holds vacuously for $C=\{0\}$, matching $\lambda(\{0\})=+\infty$.
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), Definition 4.1, pp.24–25 (v|_S and V − s, p.10; λ, p.11)

import Mathlib

set_option autoImplicit false

namespace DetParamSVP.Supplement

/-- **Locally dense code** (Definition 4.1). Let `p` be prime and let `m, k, D, r` be positive
integers. Let `C` be a linear code over `F_p` with coordinates `ι`, given by a parity-check matrix
`H ∈ F_p^{h×ι}` (`C = ker H = {c : Hc = 0}`), let `s ∈ F_p^ι`, and let `S = (x₁, …, x_m)` be an
ordered list of `m` distinct coordinates. `(C, s, S)` is an `(m, k, D, r)`-locally dense code if
(i) `λ(C) > D`; (ii) `s|_S = 0`; (iii) for every `u ∈ F_p^m` with `‖u‖₀ ≤ k` there is a nonzero
`w ∈ C − s` such that `‖w‖₀ ≤ r` and `w|_S = u`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), Definition 4.1,
pp.24–25 (`v|_S` and `V − s` on p.10, `λ` and `λ({0}) = +∞` on p.11).

**Formalization Note.** The standing conditions of the definition's first sentences (`p` prime;
`m, k, D, r` positive; distinct coordinates) are bundled. `S` is an injective map `Fin m → ι` and
`v|_S = v ∘ S`. (i) is "every nonzero `c` with `Hc = 0` has `‖c‖₀ > D`" (Mathlib `hammingNorm`), which
for `C = {0}` holds vacuously, matching `λ({0}) = +∞`. `w ∈ C − s` is `H(w + s) = 0`. -/
def IsLocallyDenseCode (p m k D r : ℕ) {h : ℕ} {ι : Type*} [Fintype ι]
    (H : Matrix (Fin h) ι (ZMod p)) (s : ι → ZMod p) (S : Fin m → ι) : Prop :=
  p.Prime ∧ 0 < m ∧ 0 < k ∧ 0 < D ∧ 0 < r ∧ Function.Injective S ∧
    (∀ c : ι → ZMod p, H.mulVec c = 0 → c ≠ 0 → D < hammingNorm c) ∧
    s ∘ S = 0 ∧
    (∀ u : Fin m → ZMod p, hammingNorm u ≤ k →
      ∃ w : ι → ZMod p, H.mulVec (w + s) = 0 ∧ w ≠ 0 ∧ hammingNorm w ≤ r ∧ w ∘ S = u)

end DetParamSVP.Supplement


