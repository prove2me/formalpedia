-- Prove2me | Definitions.Def_DetParamSVP_LocallyDense
-- name    : DetParamSVP_LocallyDense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:50:37.613656+00:00
-- url     : https://prove2.me/theorems/49dbbf14-e3e6-4a94-a246-9a1797f8c593
-- title:
--   Congruence lattices and locally dense lattices (Definition 3.1)
-- statement:
--   For a prime $q$ and $H\in\mathbb F_q^{r\times N}$ let $\mathcal L=\{v\in\mathbb Z^N:H(v\bmod q)=0\}$.
--
--   Let $p\ge1$, let $m,d,D,W$ be positive integers and let $q>D$ be prime. Let $s\in\mathbb Z^N$ and let $S$ be an ordered list of $m$ distinct coordinates. The tuple $(q,H,s,S)$ is a **locally dense lattice with parameters $(p,m,d,D,W)$** if
--
--   1. $\lambda_1^{(p)}(\mathcal L)>D$;
--   2. $s|_S=0$;
--   3. for every $u\in\mathbb Z^m$ with $\|u\|_p\le d$ there is $w\in\mathcal L-s$ with $w|_S=u$ (over the integers) and $\|w\|_p^p\le W$.
--
--   Here $W$ bounds the $p$-th power of the norm, while $d$ and $D$ are norm thresholds. A locally dense lattice is the gadget that turns the CVP instance into an SVP instance in Theorem 3.2.
--
--   **Formalization Note** The coordinates form any finite type ($\{0,\dots,N-1\}$ in the algorithmic statements, $\mathbb F_q$ in the Reed–Solomon construction). The standing conditions of the definition's first sentence are part of the definition. $S$ is an injective map from $\{1,\dots,m\}$ to the coordinates and $v|_S=v\circ S$. Condition 1 is written "every nonzero $v\in\mathcal L$ has $\|v\|_p>D$" ($\mathcal L$ contains $q e_z\ne0$), and $w\in\mathcal L-s$ is $w+s\in\mathcal L$.
-- source:
--   Hirahara–Lin–Liu–Ogitsuka, Deterministic Parameterized Inapproximability of the Shortest Vector and Minimum Distance Problems, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 2.13, p.13 (congruence lattice), Definition 3.1, p.17

import Definitions.Def_DetParamSVP_LpNorm

set_option autoImplicit false

namespace DetParamSVP

/-- The lattice defined by linear congruences modulo `q`:
`L = {v ∈ ℤ^ι : H(v mod q) = 0}` for `H ∈ F_q^{r×ι}`.

Hirahara–Lin–Liu–Ogitsuka, *Deterministic Parameterized Inapproximability of the Shortest Vector
and Minimum Distance Problems*, STOC 2027 submission (manuscript sha256 4584f5e2…), Lemma 2.13, p.13,
and Definition 3.1, p.17 ("Put L = {v ∈ ZN : H(v mod q) = 0}").

**Formalization Note.** The coordinates form any finite type `ι` (the paper's `N` coordinates;
`ι = Fin N` in the algorithmic statements and `ι = F_q` in the Reed–Solomon construction). -/
def congruenceLattice (q : ℕ) {r : ℕ} {ι : Type*} [Fintype ι] (H : Matrix (Fin r) ι (ZMod q)) :
    Set (ι → ℤ) :=
  {v | H.mulVec (fun z => ((v z : ℤ) : ZMod q)) = 0}

/-- **Locally dense lattice** (Definition 3.1). Let `p ≥ 1`, let `m, d, D, W` be positive
integers, and let `q > D` be prime. Let `H ∈ F_q^{r×N}`, `s ∈ ℤ^N`, and let `S` be an ordered list
of `m` distinct coordinates; put `L = {v ∈ ℤ^N : H(v mod q) = 0}`. The tuple `(q, H, s, S)` is a
locally dense lattice with parameters `(p, m, d, D, W)` if
(i) `λ₁^{(p)}(L) > D`; (ii) `s|_S = 0`; (iii) for every `u ∈ ℤ^m` with `‖u‖_p ≤ d` there is
`w ∈ L − s` with `w|_S = u` and `‖w‖_p^p ≤ W`.

Hirahara–Lin–Liu–Ogitsuka (manuscript sha256 4584f5e2…), Definition 3.1, p.17.

**Formalization Note.** The standing conditions of the definition's first sentence (`p ≥ 1`,
positivity of `m, d, D, W`, `q` prime, `q > D`, distinct coordinates) are bundled. `S` is an
injective map `Fin m → ι`, and `v|_S = v ∘ S`. (i) is written "every nonzero `v ∈ L` has
`‖v‖_p > D`" (`L` contains `q·e_z ≠ 0`, so the minimum is over a nonempty discrete set);
`w ∈ L − s` is `w + s ∈ L`; `w|_S = u` is an equality of integer vectors. -/
def IsLocallyDenseLattice (p : ℝ) (m d D W q : ℕ) {r : ℕ} {ι : Type*} [Fintype ι]
    (H : Matrix (Fin r) ι (ZMod q)) (s : ι → ℤ) (S : Fin m → ι) : Prop :=
  1 ≤ p ∧ 0 < m ∧ 0 < d ∧ 0 < D ∧ 0 < W ∧ q.Prime ∧ D < q ∧ Function.Injective S ∧
    (∀ v ∈ congruenceLattice q H, v ≠ 0 → (D : ℝ) < lpNorm p v) ∧
    s ∘ S = 0 ∧
    (∀ u : Fin m → ℤ, lpNorm p u ≤ d →
      ∃ w : ι → ℤ, w + s ∈ congruenceLattice q H ∧ w ∘ S = u ∧ lpPowSum p w ≤ W)

end DetParamSVP


