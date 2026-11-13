-- Prove2me | Definitions.Def_HararySachs_Hyper_RowProj
-- name    : HararySachs_Hyper_RowProj
-- status  : Definition
-- author  : @milia
-- created : 2026-11-13T03:00:46.263744+00:00
-- url     : https://prove2.me/theorems/0c7e5bb5-11aa-43ba-8397-0433a3c708d1
-- title:
--   Generic tensor, row substitution, and the row projection $\Pi_{i,m}$
-- statement:
--   Fix integers $n \ge 1$ and $k \ge 2$, put $r = k-1$, and fix a row index $i$.
--
--   1. **Generic tensor.** `GenRing n k` is the polynomial ring over $\mathbb{Q}$ in independent indeterminates $X_{j,t}$, one for each row $j$ and each tuple $t \in \{1,\dots,n\}^r$. `genTensor` is the tensor $(j,t) \mapsto X_{j,t}$.
--   2. **Row weight.** `rowWeight i` gives weight $1$ to the variables $X_{i,t}$ of row $i$ and weight $0$ to all others, so weighted homogeneous components are the components of fixed degree in row $i$.
--   3. **Row substitution.** `rowSubst i` is the $\mathbb{Q}$-algebra map into polynomials in new variables $v_1,\dots,v_n$ (with coefficients in `GenRing n k`) that sends $X_{i,t} \mapsto v_{t_1}\cdots v_{t_r}$ and keeps $X_{j,t}$ for $j \ne i$ as coefficients.
--   4. **Row operator.** `rowOp i` is the differential operator
--   $$f_i(\partial_v) = \sum_{t} X_{i,t}\,\frac{\partial}{\partial v_{t_1}}\cdots\frac{\partial}{\partial v_{t_r}}.$$
--   5. **Row projection.** For $m \ge 0$,
--   $$\Pi_{i,m}(Q) = \frac{1}{(rm)!}\Bigl[f_i(\partial_v)^{m}\,Q\bigl(X_{i,t} \mapsto v_{t_1}\cdots v_{t_r}\bigr)\Bigr]_{v=0}.$$
--   6. **Rescaled row series.** For a ring element $C$, a sequence $q_j$ and $M \ge 0$,
--   $$\widehat\Phi(s) = 1 + \sum_{j=1}^{M} C^{\,j-1}\,q_j\,s^j.$$
--   When $q_j$ are the graded pieces of a polynomial $Q$ with degree-$0$ piece $C$, this is $Q(Cs)/C$ truncated at order $M$. Its Newton traces are the numerators $S_m = C^m\sigma_m$ of the row-graded logarithm of $Q$.
--
--   These objects express the single-row Morozov–Shakirov projection for a generic tensor. Applied to a polynomial of degree $m$ in row $i$, $\Pi_{i,m}$ replaces $f_i$ by the power $(v\cdot x)^r$ and then recovers $f_i$ by the shift operator $f_i(\partial_v)^m/(rm)!$. The polynomials fixed by it are exactly the sums of powers $f_i(p)^m$ of point evaluations.
--
--   **Formalization Note** The new variables $v$ are `MvPolynomial.X l` in `MvPolynomial (Fin n) (GenRing n k)`. `rowProj` uses the iterate of `rowOp` and `MvPolynomial.eval 0`. `hatPhi` is a polynomial over any commutative ring.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 3, Proposition I and the shift identity (15), in the degree-preserving variant of mission strategy comment 2173f2a9-fd2e-4d5e-afb5-27607d970161.

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_TensorPhi

namespace HararySachs.Hyper

/-- The coefficient ring of the generic tensor: polynomials over `ℚ` in independent
indeterminates `X (j, t)`, one for each row `j` and each tuple `t`. -/
abbrev GenRing (n k : ℕ) := MvPolynomial (Fin n × (Fin (k - 1) → Fin n)) ℚ

/-- The generic tensor `(j, t) ↦ X (j, t)`. -/
noncomputable def genTensor (n k : ℕ) : Fin n → (Fin (k - 1) → Fin n) → GenRing n k :=
  fun j t => MvPolynomial.X (j, t)

/-- The weight counting the degree in the variables of row `i`. -/
def rowWeight {n k : ℕ} (i : Fin n) : Fin n × (Fin (k - 1) → Fin n) → ℕ :=
  fun v => if v.1 = i then 1 else 0

/-- Replace each variable `X (i, t)` of row `i` by the monomial `v_{t 0} ⋯ v_{t (k-2)}` in new
variables `v`, keeping the other variables as coefficients. -/
noncomputable def rowSubst {n k : ℕ} (i : Fin n) :
    GenRing n k →ₐ[ℚ] MvPolynomial (Fin n) (GenRing n k) :=
  MvPolynomial.aeval (fun v : Fin n × (Fin (k - 1) → Fin n) =>
    if v.1 = i then ∏ s, MvPolynomial.X (v.2 s) else MvPolynomial.C (MvPolynomial.X v))

/-- The operator `f_i(∂_v) = Σ_t X (i, t) ∂_{v_{t 0}} ⋯ ∂_{v_{t (k-2)}}`. -/
noncomputable def rowOp {n k : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) (GenRing n k)) :
    MvPolynomial (Fin n) (GenRing n k) :=
  ∑ t : Fin (k - 1) → Fin n, (MvPolynomial.X (i, t) : GenRing n k) •
    (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv j q) p

/-- The row-`i` projection of order `m`:
`Q ↦ (1 / (m (k-1))!) · [f_i(∂_v)^m Q(row i := v-powers)]_{v = 0}`. -/
noncomputable def rowProj {n k : ℕ} (i : Fin n) (m : ℕ) (Q : GenRing n k) : GenRing n k :=
  (1 / (Nat.factorial (m * (k - 1)) : ℚ)) •
    MvPolynomial.eval 0 ((rowOp i)^[m] (rowSubst i Q))

/-- `1 + Σ_{j=1}^{M} C^{j-1} q_j s^j`; for `q_j` the graded pieces of a polynomial with
degree-`0` piece `C`, this is `Q(C s)/C` truncated at order `M`. -/
noncomputable def hatPhi {R : Type*} [CommRing R] (C : R) (q : ℕ → R) (M : ℕ) : Polynomial R :=
  1 + ∑ j ∈ Finset.Icc 1 M, Polynomial.monomial j (C ^ (j - 1) * q j)

end HararySachs.Hyper


