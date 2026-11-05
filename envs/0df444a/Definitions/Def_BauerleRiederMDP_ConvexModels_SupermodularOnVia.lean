-- Prove2me | Definitions.Def_BauerleRiederMDP_ConvexModels_SupermodularOnVia
-- name    : BauerleRiederMDP_ConvexModels_SupermodularOnVia
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:22:49.087701+00:00
-- url     : https://prove2.me/theorems/ddd01a7b-c61a-4a13-b88b-b5c9eae4346c
-- title:
--   Supermodularity of a function on a subset of $\mathbb R^{d+m}$
-- statement:
--   For $x,y\in\mathbb R^k$ write $x\wedge y$ and $x\vee y$ for the componentwise minimum and maximum. A function $f:\mathbb R^k\to\mathbb R$ is **supermodular** if
--   $$
--   f(x)+f(y)\le f(x\wedge y)+f(x\vee y),\qquad x,y\in\mathbb R^k.
--   $$
--   For a set $X$ placed in a lattice by $\iota$ (here $D_n\subset E\times A\subset\mathbb R^d\times\mathbb R^m$), a function $w$ is **supermodular on** $D\subseteq X$ if $w$ is real-valued on $D$ and $w(p)+w(q)\le w(s)+w(t)$ whenever $p,q,s,t\in D$ with $\iota(s)=\iota(p)\wedge\iota(q)$ and $\iota(t)=\iota(p)\vee\iota(q)$.
--
--   Supermodularity of $L_nv$ is the hypothesis under which largest maximizers are increasing (Proposition 2.4.16).
--
--   **Formalization Note** Definition A.3.1 is for real-valued functions, so the function must be finite on $D$. Under the alternative reading with $-\infty$ allowed and $-\infty+c=-\infty$, Proposition 2.4.16 is false (see the mission notes).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Definition A.3.1, p.353 (PDF p.359); applied in Proposition 2.4.16, p.35 (PDF p.50)

import Mathlib

namespace BauerleRiederMDP.ConvexModels

/-- **Supermodularity on a subset** (Bäuerle & Rieder, *Markov Decision Processes with
Applications to Finance* (2011), Definition A.3.1, p.353, PDF p.359: "A function
`f : ℝ^d → ℝ` is called supermodular if `f(x) + f(y) ≤ f(x ∧ y) + f(x ∨ y)`, `x, y ∈ ℝ^d`",
with `∧`, `∨` the componentwise minimum and maximum, p.352–353). Applied in Proposition
2.4.16 (p.35, PDF p.50) as "`L_n v` is supermodular on `D_n`" for `D_n ⊂ E × A ⊂ ℝ^{d+m}`.

With the points of `X` placed in a lattice `Λ` by `ι` (for `D_n` the inclusion
`Prod.map Subtype.val Subtype.val` into `ℝ^d × ℝ^m` with the componentwise order), `w` is
supermodular on `D ⊆ X` if `w` is real-valued on `D` and
`w(p) + w(q) ≤ w(s) + w(t)` whenever `p, q, s, t ∈ D` with `ι(s) = ι(p) ∧ ι(q)` and
`ι(t) = ι(p) ∨ ι(q)`.

**Formalization Note.** Definition A.3.1 is stated for real-valued functions, so `w` is
required to be finite (neither `−∞` nor `+∞`) on `D`; the inequality is then the book's.
"On `D_n`" is read as: for the pairs of points of `D_n` whose componentwise minimum and
maximum also lie in `D_n` (where the function is defined). -/
def SupermodularOnVia {X Λ : Type*} [Lattice Λ] (ι : X → Λ) (D : Set X) (w : X → EReal) :
    Prop :=
  (∀ p ∈ D, w p ≠ ⊥ ∧ w p ≠ ⊤) ∧
  ∀ p ∈ D, ∀ q ∈ D, ∀ s ∈ D, ∀ t ∈ D, ι s = ι p ⊓ ι q → ι t = ι p ⊔ ι q →
    w p + w q ≤ w s + w t

end BauerleRiederMDP.ConvexModels


