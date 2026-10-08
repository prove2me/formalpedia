-- Prove2me | Definitions.Def_ProductFraming_Trunc_Framing
-- name    : ProductFraming_Trunc_Framing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:38.798233+00:00
-- url     : https://prove2.me/theorems/0274892f-879b-4a19-b771-d9eb4b21d3dc
-- title:
--   Product framing, §6: failure rate $h(x)=\lambda(x)/\Lambda(x)$, Assumption B4 (IFR), feasible framings
-- statement:
--   This definition extends the product framing model (choice model, page-count law, tail and consideration sets of `ProductFraming.Nest.Model`) with the objects used in §6 of the paper. There are $n$ products displayed on $m$ virtual pages $[m]=\{1,\dots,m\}$, each holding at most $p$ products. A consumer views a random number $X\in[m]$ of pages with law $\lambda(x)=\mathbb P[X=x]$ and tail $\Lambda(x)=\mathbb P[X\ge x]=\sum_{y=x}^{m}\lambda(y)$.
--
--   1. The **failure rate** of $X$ is
--   $$h(x)=\frac{\lambda(x)}{\Lambda(x)},\qquad x\in[m].$$
--   2. **Assumption B4.** $X$ has an **increasing failure rate (IFR)**: $h$ is nondecreasing on $[m]$ wherever it is defined, i.e. $h(x)\le h(x')$ for all $x\le x'$ in $[m]$ with $\Lambda(x')>0$.
--   3. A **framing** places each product on at most one page; it is **feasible** if every page holds at most $p$ products. These are the constraints of problem (1).
--
--   Assumption B4 is the hypothesis on the page-count law in the analysis of the truncation algorithms TRUNC$(y)$; it is sufficient for the NBUE Assumption A3.
--
--   **Formalization Note** A framing is a map `f : Fin n → ℕ`: product $i$ sits on page $f(i)$ when $1\le f(i)\le m$, and $f(i)=0$ means "not displayed". `Feasible` is an alias of `ProductFraming.Nest.IsFeasibleFraming`, so both chunks of the series use one notion of feasibility. The failure rate is a real quotient, which Lean evaluates to $0$ when $\Lambda(x)=0$; the IFR condition is required only at points with $\Lambda(x')>0$ (then also $\Lambda(x)>0$), so a law whose support ends before page $m$ is not excluded and no value of $h$ outside the support is used. "Increasing" is read as nondecreasing.
-- source:
--   Gallego, Li, Truong, Wang, Approximation Algorithms for Product Framing and Pricing, Operations Research (2020), DOI 10.1287/opre.2019.1875, authors' accepted manuscript, §3, p. 6, (1); §6, Assumption B4, pp. 13–14

import Mathlib
import Definitions.Def_ProductFraming_Nest_Model
open Finset

namespace ProductFraming.Trunc

/-! Additions to the product framing model `ProductFraming.Nest` of Gallego, Li, Truong, Wang
(Operations Research 2020, accepted manuscript) used in §6: the failure rate and Assumption B4
(pp. 13–14), and the name `Feasible` for the constraints of (1) (§3, p. 6).

Products are `Fin n`; pages are the naturals `1, …, m` (`Icc 1 m`), the paper's `[m]`. The page-count
law, its tail `Λ`, the choice model and the consideration sets are those of `ProductFraming.Nest`. -/

/-- The failure rate `h(x) = λ(x)/Λ(x)` (§6, p. 14). It is only meaningful where `Λ(x) > 0`;
every statement using it says so. -/
noncomputable def failureRate (m : ℕ) (lam : ℕ → ℝ) (x : ℕ) : ℝ :=
  lam x / ProductFraming.Nest.tail m lam x

/-- Assumption B4 (p. 13): `X` has increasing failure rate, i.e. (p. 14) `h(x)` is
nondecreasing in `x ∈ [m]`, wherever it is defined: for `x ≤ x'` in `[m]` with `Λ(x') > 0`
(hence also `Λ(x) > 0`), `h(x) ≤ h(x')`. Points with `Λ = 0` (beyond the support of `X`)
impose nothing. -/
def IsIFR (m : ℕ) (lam : ℕ → ℝ) : Prop :=
  ∀ x ∈ Icc 1 m, ∀ x' ∈ Icc 1 m, x ≤ x' → 0 < ProductFraming.Nest.tail m lam x' →
    failureRate m lam x ≤ failureRate m lam x'

/-- A feasible framing (the constraints of (1), p. 6). Product `i` is displayed on page `f i`
when `1 ≤ f i ≤ m`; `f i = 0` means product `i` is not displayed. Each product is on at most
one page (built into the encoding) and each page holds at most `p` products. This is the same
notion as `ProductFraming.Nest.IsFeasibleFraming`, of which it is an alias. -/
def Feasible {n : ℕ} (m p : ℕ) (f : Fin n → ℕ) : Prop :=
  ProductFraming.Nest.IsFeasibleFraming m p f

end ProductFraming.Trunc


