-- Prove2me | Definitions.Def_SharpConsist_Supplement_natFn
-- name    : SharpConsist_Supplement_natFn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:20:15.382397+00:00
-- url     : https://prove2.me/theorems/e71a4ef3-4f24-415f-b84b-c2a51a1bb0b2
-- title:
--   A stream instance read on arrival indices
-- statement:
--   The stream model of the paper has a finite ground set $V$ whose elements arrive one at a time; $X_t$ denotes the set of the first $t$ arrivals. Name the elements by their arrival order, $V=\{0,1,\dots,N-1\}$, so that $X_t=\{0,\dots,t-1\}$.
--
--   For an objective $f:2^V\to\mathbb R$, the function $\mathrm{natFn}(f)$ evaluates a finite set $S\subseteq\mathbb N$ of arrival indices by
--   $$\mathrm{natFn}(f)(S)=f\big(\{i\in V: i\in S\}\big).$$
--   On subsets of $X_t$ with $t\le N$ it is exactly $f$.
--
--   This lets one algorithm be run on streams of every length: it refers to elements by their arrival index and never needs the stream length.
--
--   **Formalization Note** $V$ is `Fin N`; an element $i$ is the $(i+1)$-st arrival.
-- source:
--   Fu–Zhang–Tao, A Sharp Barrier of Consistent Submodular Maximization, arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1; §2.1, p.4

import Mathlib

namespace SharpConsist.Supplement

/-- **A stream instance seen through arrival indices.** Fu–Zhang–Tao, *A Sharp Barrier of Consistent Submodular Maximization*, arXiv:2609.09986 (held version, sha256 874ec76c…), §1, p.1 and §2.1, p.4:
a finite ground set `V` whose elements arrive one at a time; `X_t` is the set of the first `t`
arrivals.

`natFn f` reads an objective `f : 2^V → ℝ` on the stream `V = Fin N` (element `i` is the
`(i+1)`-st arrival) as a function of finite sets of arrival indices: a set `S ⊆ ℕ` is evaluated at
its elements below `N`.

**Formalization Note.** Naming the elements by their arrival index loses nothing, since an algorithm
sees the objective only through its values (and, in Theorem 8.2, the revealed weights). The current
set `X_t` is `{0, …, t − 1}`; on subsets of `X_t` with `t ≤ N`, `natFn f` is exactly `f`. -/
def natFn {N : ℕ} (f : Finset (Fin N) → ℝ) : Finset ℕ → ℝ :=
  fun S => f (Finset.univ.filter fun i : Fin N => (i : ℕ) ∈ S)

end SharpConsist.Supplement


