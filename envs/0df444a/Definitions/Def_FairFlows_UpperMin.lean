-- Prove2me | Definitions.Def_FairFlows_UpperMin
-- name    : FairFlows_UpperMin
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:16:06.098986+00:00
-- url     : https://prove2.me/theorems/b5e4a8d2-4eed-4452-9168-1695825c627c
-- title:
--   The §4 setting: the set function (4.2), $g$-saturated edges, $L$-upper-minimizers and the criteria (O1)–(O5)
-- statement:
--   Let $D=(V,A)$, $m:V\to\mathbb Z$ with $\widetilde m(V)=0$, bounds $f\le g$, and $L\subseteq A$ with $-\infty<f(e)<g(e)<+\infty$ for $e\in L$ (the **§4 setting**). Let $g^-=g-\chi_L$ (4.1).
--
--   1. The set function (4.2) is $p=\widetilde m-\varrho_{g^-}+\delta_f$: $p(Z)=\widetilde m(Z)-\varrho_{g^-}(Z)+\delta_f(Z)$ when $\varrho_g(Z)-\delta_f(Z)<+\infty$, and $p(Z)=-\infty$ otherwise.
--   2. For an integral flow $x$, the **$g$-saturated** edges of $L$ are $\{e\in L: x(e)=g(e)\}$; $x$ is an **$L$-upper-minimizer** if it is an integral $(f,g)$-bounded $m$-flow whose number of $g$-saturated $L$-edges is as small as possible.
--   3. For a chain $\mathcal C=\{V_1\supset\cdots\supset V_q\}$ the **criteria** (O1)–(O5) of Theorem 4.6 are: $z(e)=f(e)$ on edges leaving a $V_i$; $z(e)=g(e)$ on edges of $A-L$ entering a $V_i$; $g(e)-1\le z(e)\le g(e)$ on edges of $L$ entering exactly one $V_i$; $z(e)=g(e)$ on edges of $L$ entering at least two; $f(e)\le z(e)\le g(e)-1$ on edges of $L$ entering and leaving none.
--
--   These objects connect integral flows to the covering problem of §3 (Lemmas 4.1, 4.2) and give the optimality criteria of Theorem 4.6.
--
--   **Formalization Note** On the finite branch of $p$ every value read through `untopD 0`/`unbotD 0` is finite, so the default is never used. $g(e)-1\le z(e)$ is written $g(e)\le z(e)+1$ in `WithTop ℤ`.
-- source:
--   Frank, Murota, Fair integral network flows, arXiv:1907.02673v5, §4 p.10 (setting, L-upper-minimal, g-saturated, (4.1), (4.2)), Theorem 4.6 p.11 ((O1)–(O5))

import Mathlib
import Definitions.Def_FairFlows_Covering

set_option autoImplicit false

namespace FairFlows

open Finset

variable {V A : Type}

/-- The standing assumptions of §4 (Frank, Murota, *Fair integral network flows*,
arXiv:1907.02673v5, §4, p.10): `m̃(V) = 0`; `f ≤ g`; and `−∞ < f(e) < g(e) < +∞` for every
edge `e` of the edge set `L ⊆ A`. -/
def Setting4 [Fintype V] (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (L : Finset A) :
    Prop :=
  demandSum m univ = 0 ∧ BoundsLE f g ∧
  ∀ e ∈ L, ∃ a b : ℤ, f e = (a : WithBot ℤ) ∧ g e = (b : WithTop ℤ) ∧ a < b

open Classical in
/-- The set function `p := m̃ − ϱ_{g⁻} + δ_f` of (4.2) (arXiv:1907.02673v5, p.10), where
`g⁻ := g − χ_L` is (4.1). Its value is `−∞` exactly when `ϱ_g(Z) − δ_f(Z) = +∞`, i.e. when
some edge entering `Z` has `g = +∞` or some edge leaving `Z` has `f = −∞` (p.10: "`p(Z) > −∞`
precisely if `ϱ_g(Z) − δ_f(Z) < +∞`").

**Formalization Note** On the finite branch every `g⁻`-value of an entering edge and every
`f`-value of a leaving edge is finite, so `untopD 0` / `unbotD 0` return the actual integers;
the default `0` is never read. `ϱ_{g⁻}` and `δ_f` sum over all edges of `A`. -/
noncomputable def pFun [Fintype A] [DecidableEq A] [DecidableEq V] (D : Digraph V A) (m : V → ℤ)
    (f : A → WithBot ℤ) (g : A → WithTop ℤ) (L : Finset A) (Z : Finset V) : WithBot ℤ :=
  if FiniteCut D f g Z then
    ((demandSum m Z - D.inSum (fun e => (shiftOn g L (-1) e).untopD 0) Z
        + D.outSum (fun e => (f e).unbotD 0) Z : ℤ) : WithBot ℤ)
  else ⊥

/-- The `g`-saturated edges of `L` for the integral flow `x`: `{e ∈ L : x(e) = g(e)}`
(arXiv:1907.02673v5, p.10). -/
def satSet [DecidableEq A] (L : Finset A) (g : A → WithTop ℤ) (x : A → ℤ) : Finset A :=
  L.filter (fun e => ((x e : ℤ) : WithTop ℤ) = g e)

/-- `x` is an `L`-upper-minimizer (`L`-upper-minimal): an integral `(f, g)`-bounded `m`-flow
whose number of `g`-saturated edges in `L` is as small as possible among all integral
`(f, g)`-bounded `m`-flows (arXiv:1907.02673v5, p.10). -/
def IsLUpperMin [Fintype A] [DecidableEq A] [DecidableEq V] (D : Digraph V A)
    (f : A → WithBot ℤ) (g : A → WithTop ℤ) (m : V → ℤ) (L : Finset A) (x : A → ℤ) : Prop :=
  x ∈ intFlows D f g m ∧ ∀ y ∈ intFlows D f g m, (satSet L g x).card ≤ (satSet L g y).card

/-- The optimality criteria (O1)–(O5) of Theorem 4.6 (arXiv:1907.02673v5, p.11) for an
integral flow `z` and a chain `C = {V₁ ⊃ ⋯ ⊃ V_q}`:

* (O1) `z(e) = f(e)` for every edge `e ∈ A` leaving a set `Vᵢ`;
* (O2) `z(e) = g(e)` for every edge `e ∈ A − L` entering a set `Vᵢ`;
* (O3) `g(e) − 1 ≤ z(e) ≤ g(e)` for every edge `e ∈ L` entering exactly one `Vᵢ`;
* (O4) `z(e) = g(e)` for every edge `e ∈ L` entering at least two `Vᵢ`'s;
* (O5) `f(e) ≤ z(e) ≤ g(e) − 1` for every edge `e ∈ L` neither entering nor leaving any `Vᵢ`.

**Formalization Note** Comparisons are in `WithBot ℤ` / `WithTop ℤ`; `g(e) − 1 ≤ z(e)` is
written `g(e) ≤ z(e) + 1` and `z(e) ≤ g(e) − 1` as `z(e) + 1 ≤ g(e)`, with no `∞` arithmetic.
"Entering exactly one / at least two" counts the members of `C` entered by `e`. -/
def UpperMinCriteria [DecidableEq V] (D : Digraph V A) (f : A → WithBot ℤ) (g : A → WithTop ℤ)
    (L : Finset A) (C : Finset (Finset V)) (z : A → ℤ) : Prop :=
  (∀ e : A, (∃ Z ∈ C, D.Leaves e Z) → ((z e : ℤ) : WithBot ℤ) = f e) ∧
  (∀ e : A, e ∉ L → (∃ Z ∈ C, D.Enters e Z) → ((z e : ℤ) : WithTop ℤ) = g e) ∧
  (∀ e ∈ L, enterCount D C e = 1 →
      ((z e : ℤ) : WithTop ℤ) ≤ g e ∧ g e ≤ ((z e + 1 : ℤ) : WithTop ℤ)) ∧
  (∀ e ∈ L, 2 ≤ enterCount D C e → ((z e : ℤ) : WithTop ℤ) = g e) ∧
  (∀ e ∈ L, (¬ ∃ Z ∈ C, D.Enters e Z) → (¬ ∃ Z ∈ C, D.Leaves e Z) →
      f e ≤ ((z e : ℤ) : WithBot ℤ) ∧ ((z e + 1 : ℤ) : WithTop ℤ) ≤ g e)

end FairFlows


