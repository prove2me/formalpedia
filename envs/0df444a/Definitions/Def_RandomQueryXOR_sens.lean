-- Prove2me | Definitions.Def_RandomQueryXOR_sens
-- name    : RandomQueryXOR_sens
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T05:54:08.557942+00:00
-- url     : https://prove2.me/theorems/3be89610-69de-4de9-9557-8d93b5f5c852
-- title:
--   Sensitivity $\mathrm{sens}[f]$, $\mathrm{sens}[f,x]$, $\mathrm{sens}_0$, $\mathrm{sens}_1$ of a Boolean function
-- statement:
--   Let $f:\{0,1\}^\iota\to\{0,1\}$ be a Boolean function on a finite index set $\iota$ and $x\in\{0,1\}^\iota$; write $x\oplus e_i$ for $x$ with its $i$-th bit flipped. The bit $i$ is **sensitive** for $x$ if $f(x)\neq f(x\oplus e_i)$, and
--   $$
--   \mathrm{sens}[f,x]=\bigl|\{i : f(x)\neq f(x\oplus e_i)\}\bigr|,\qquad \mathrm{sens}[f]=\max_{x}\mathrm{sens}[f,x].
--   $$
--   $\mathrm{sens}_0[f,x]$ and $\mathrm{sens}_1[f,x]$ count the sensitive bits $i$ of $x$ with $x(i)=0$ and $x(i)=1$ respectively; the set of sensitive bits $i$ with $x(i)=0$ (the "sensitive zeros" of $x$) is also named, since the hard distribution and the embedding protocols use it.
--
--   The sensitivity of the XOR-function $g=f\circ\oplus_2$ is the parameter $k$ of Result 1, and $\mathrm{sens}_0[f,x^\star_f]$ is the number $d$ of pairs into which the two-bit game can be embedded.
--
--   **Formalization Note** Bits are `Bool` (`false` = 0). The same definition serves $f$ (index set `Fin n`) and $g$ (index set `Fin (2 * n)`); the maximum is a `Finset.sup` over all inputs.
-- source:
--   Garg, Sundaresan, Velusamy, XOR-Functions and Beyond in the Random Query Model, arXiv:2611.04353, Definition 3.2, p.14 (PDF p.16)

import Mathlib

set_option autoImplicit false
set_option synthInstance.maxSize 2048

namespace RandomQueryXOR

/-- `x ⊕ e_i`: the input `x` with its `i`-th bit flipped (arXiv:2611.04353, §3, p.13 =
PDF p.15: "We use e_i … to denote the element of {0, 1}^n which has value 1 at index i and 0
everywhere else"). -/
def flip {ι : Type} [DecidableEq ι] (x : ι → Bool) (i : ι) : ι → Bool :=
  Function.update x i (!x i)

/-- `sens[f, x] = |{i : f(x) ≠ f(x ⊕ e_i)}|`, the number of sensitive bits of `x`
(arXiv:2611.04353, Definition 3.2, p.14 = PDF p.16). -/
def sensAt {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => f x ≠ f (flip x i)).card

/-- The sensitive bits `i` of `x` with `x(i) = 0` (the paper's "indices which are sensitive for
x⋆_f with value 0", arXiv:2611.04353, p.19 = PDF p.21). -/
def sensZeros {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) (x : ι → Bool) :
    Finset ι :=
  Finset.univ.filter fun i => x i = false ∧ f x ≠ f (flip x i)

/-- `sens0[f, x]`: the number of sensitive bits of `x` whose value in `x` is `0`
(arXiv:2611.04353, Definition 3.2, p.14 = PDF p.16). -/
def sens0At {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) (x : ι → Bool) : ℕ :=
  (sensZeros f x).card

/-- `sens1[f, x]`: the number of sensitive bits of `x` whose value in `x` is `1`
(arXiv:2611.04353, Definition 3.2, p.14 = PDF p.16). -/
def sens1At {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) (x : ι → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true ∧ f x ≠ f (flip x i)).card

/-- The sensitivity `sens[f] = max_x sens[f, x]` of a Boolean function `f : {0,1}^ι → {0,1}`,
the maximum degree of its sensitivity graph (Garg, Sundaresan, Velusamy, *XOR-Functions and
Beyond in the Random Query Model*, arXiv:2611.04353, Definition 3.2, p.14 = PDF p.16).

**Formalization Note** Boolean functions are `(ι → Bool) → Bool` with `false` ↔ 0 and
`true` ↔ 1, over any finite index set `ι` (`Fin n` for `f`, `Fin (2 * n)` for
`g = f ∘ ⊕2`). The maximum is `Finset.sup` over all inputs (`0` when `ι` has no bits to
flip). -/
def sens {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → Bool) : ℕ :=
  Finset.univ.sup (sensAt f)

end RandomQueryXOR


