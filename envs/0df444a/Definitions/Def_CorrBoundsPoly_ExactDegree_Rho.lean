-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_Rho
-- name    : CorrBoundsPoly_ExactDegree_Rho
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:57:24.9304+00:00
-- url     : https://prove2.me/theorems/5e656c83-c857-402d-9148-d4f253a79308
-- title:
--   Eq. (1.1) — Boolean functions over $\mathbb F_2$, multilinear degree, correlation and $\rho_d$; XOR on disjoint blocks
-- statement:
--   Identify $\{0,1\}^\iota$ with $\mathbb F_2^\iota$ for a finite variable set $\iota$. A **Boolean function** is a map $f:\mathbb F_2^\iota\to\mathbb F_2$; a polynomial $p$ over $\mathbb F_2$ defines the Boolean function $x\mapsto p(x)$ by evaluation. The **degree** $\deg f$ is the degree of the unique multilinear polynomial over $\mathbb F_2$ representing $f$; thus $\deg f\le d$ holds exactly when $f$ is the evaluation of some polynomial of total degree at most $d$, and $f$ has degree exactly $s$ when $\deg f\le s$ but $\deg f\le e$ fails for every $e<s$.
--
--   The **correlation** of $f$ and $g$ is $\operatorname{Corr}(f,g)=\big|\mathbb E_{x}(-1)^{f(x)+g(x)}\big|$ for uniform $x$, and the **bias** of $f$ is $|\mathbb E_x(-1)^{f(x)}|=\operatorname{Corr}(f,0)$. For an integer $d\ge 0$,
--   $$\rho_d(f)=\max_{\substack{P:\mathbb F_2^\iota\to\mathbb F_2\\ \deg P\le d}}\operatorname{Corr}(f,P),$$
--   the maximum over **all** Boolean functions of degree at most $d$ on the whole input (constants included). So $\rho_d(f)\le\epsilon$ means that every degree-at-most-$d$ polynomial has correlation at most $\epsilon$ with $f$.
--
--   **XOR on disjoint blocks.** For $f$ on $m$ variables and $t\ge 1$, $f^{\oplus t}(x^{(1)},\dots,x^{(t)})=\sum_{j=1}^t f(x^{(j)})$ in $\mathbb F_2$ on $tm$ variables; for cores $f_i$ on $m_i$ variables, $\bigoplus_i f_i$ is the analogous sum on $\sum_i m_i$ variables. A test $P$ in $\rho_d$ of such an XOR may contain monomials that cross the blocks.
--
--   These are the objects in which every correlation statement of the mission is phrased.
--
--   **Formalization Note** `BoolFn ι` is `(ι → ZMod 2) → ZMod 2`; `evalFn p` evaluates a polynomial. `HasDegLE P d` is `∃ p : MvPolynomial ι (ZMod 2), p.totalDegree ≤ d ∧ ∀ x, eval x p = P x`, and `IsDegExactly f s` is `HasDegLE f s ∧ ∀ e < s, ¬ HasDegLE f e`. `bias f = |corr f 0|` and `rho d f` is the `Finset.sup` (in `ℝ≥0`, coerced to `ℝ`) of `|corr f P|` over the finite set of all `P` with `HasDegLE P d`; that set contains the constant `0`, so the sup is the maximum. `corr` is the published signed correlation `RevisitXor.corr` (the absolute value is taken here). `xorPow t f` lives on the variable set `Fin t × κ` (variable `(j, i)` is coordinate `i` of block `j`), and `xorBlocks f` on `Σ i : Fin k, Fin (m i)`.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), p. 1 (PDF 3), Eq. (1.1); p. 2 (PDF 4); §1.4, pp. 17–18 (PDF 19–20)

import Mathlib
import Definitions.Def_RevisitXor_corr

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), p. 1 (PDF 3), Eq. (1.1); §1.4 notation, pp. 17–18 (PDF 19–20).

Boolean functions over `F₂`, their (multilinear) degree, the correlation
`Corr(f, g) = |E_x (−1)^{f(x)+g(x)}|`, the maximum degree-`d` correlation `ρ_d`, and XOR on
disjoint blocks. -/

/-- A Boolean function on the variable set `ι`: a map `F₂^ι → F₂` (`F₂ = ZMod 2`, `{0,1} = F₂`). -/
abbrev BoolFn (ι : Type*) : Type _ := (ι → ZMod 2) → ZMod 2

/-- The Boolean function computed by a polynomial over `F₂`: evaluation on `{0,1}^ι`. -/
noncomputable def evalFn {ι : Type*} (p : MvPolynomial ι (ZMod 2)) : BoolFn ι :=
  fun x => MvPolynomial.eval x p

/-- `deg P ≤ d`: the Boolean function `P` is the evaluation of some polynomial over `F₂` of total
degree at most `d`. Since reducing `x_i² ↦ x_i` never raises the degree, this is exactly "the
unique multilinear polynomial representing `P` has degree at most `d`" (p. 1). -/
def HasDegLE {ι : Type*} (P : BoolFn ι) (d : ℕ) : Prop :=
  ∃ p : MvPolynomial ι (ZMod 2), p.totalDegree ≤ d ∧ ∀ x, MvPolynomial.eval x p = P x

/-- `deg f = s` exactly: `deg f ≤ s` and `deg f ≤ e` fails for every `e < s`. -/
def IsDegExactly {ι : Type*} (f : BoolFn ι) (s : ℕ) : Prop :=
  HasDegLE f s ∧ ∀ e : ℕ, e < s → ¬ HasDegLE f e

/-- The bias `|E_x (−1)^{f(x)}|` under the uniform distribution on `{0,1}^ι`; it equals
`Corr(f, 0)`. -/
noncomputable def bias {ι : Type*} [Fintype ι] [DecidableEq ι] (f : BoolFn ι) : ℝ :=
  |RevisitXor.corr f 0|

/-- **Eq. (1.1).** `ρ_d(f) = max_{P : F₂^ι → F₂, deg P ≤ d} |E_x (−1)^{f(x)+P(x)}|`, the maximum
over **all** Boolean functions of degree at most `d` on the whole input (constants included,
cross-block monomials allowed). The maximum over this finite nonempty set (it contains the
constant `0`) is taken as a `Finset.sup` of nonnegative reals, which is the maximum. -/
noncomputable def rho {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ℕ) (f : BoolFn ι) : ℝ := by
  classical
  exact (((Finset.univ.filter fun P : BoolFn ι => HasDegLE P d).sup
    fun P => (⟨|RevisitXor.corr f P|, abs_nonneg _⟩ : NNReal) : NNReal) : ℝ)

/-- XOR of `t` copies of `f : F₂^m → F₂` on disjoint blocks: the input is
`x = (x^{(1)}, …, x^{(t)})`, variable `(j, i)` being coordinate `i` of block `j`, and
`f^{⊕t}(x) = ∑_j f(x^{(j)})` in `F₂`. -/
def xorPow {κ : Type*} (t : ℕ) (f : BoolFn κ) : BoolFn (Fin t × κ) :=
  fun x => ∑ j : Fin t, f (fun i => x (j, i))

/-- XOR of possibly different cores `f_i` on disjoint blocks of sizes `m_i`: the variable set is
the disjoint union `Σ i, Fin (m i)` and `(⨁_i f_i)(x) = ∑_i f_i(x^{(i)})` in `F₂`. -/
def xorBlocks {k : ℕ} {m : Fin k → ℕ} (f : ∀ i, BoolFn (Fin (m i))) :
    BoolFn (Σ i : Fin k, Fin (m i)) :=
  fun x => ∑ i : Fin k, f i (fun j => x ⟨i, j⟩)

end CorrBoundsPoly.ExactDegree


