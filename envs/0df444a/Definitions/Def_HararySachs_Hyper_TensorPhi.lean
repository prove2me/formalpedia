-- Prove2me | Definitions.Def_HararySachs_Hyper_TensorPhi
-- name    : HararySachs_Hyper_TensorPhi
-- status  : Definition
-- author  : @milia
-- created : 2026-11-12T20:23:28.749208+00:00
-- url     : https://prove2.me/theorems/bac763f3-371b-4fc5-b157-f4ba8c41cf75
-- title:
--   Tensor resultant $\Phi_A(z)$, Newton traces, and tensor differential operators
-- statement:
--   Fix integers $n \ge 1$ and $k \ge 2$, and put $r = k-1$. Let $R$ be a commutative ring and let $A$ be an arbitrary (not necessarily symmetric) tensor whose entries $A_{i,t} \in R$ are indexed by a row $i \in \{1,\dots,n\}$ and an ordered tuple $t = (t_1,\dots,t_r) \in \{1,\dots,n\}^r$.
--
--   1. **The system.** `zcoord` is the $j$-th form of the system $x^{[r]} - z\,\mathcal{A}x^{r}$,
--   $$x_j^{r} - z \sum_{t} A_{j,t}\, x_{t_1}\cdots x_{t_r},$$
--   a form of degree $r$ in $x$ whose coefficients are polynomials in $z$.
--   2. **The rescaled characteristic polynomial.** `phiPoly` is
--   $$\Phi_A(z) = \operatorname{Res}\bigl(x^{[r]} - z\,\mathcal{A}x^{r}\bigr) \in R[z],$$
--   obtained by substituting the coefficients of these forms into a resultant `res` of $n$ forms of degree $r$ in $n$ variables.
--   3. **Newton traces.** For a polynomial $\Phi$, `newtonTr` is the sequence with $\tau_0 = 0$ and
--   $$\tau_d = -d\,\Phi_d - \sum_{j=1}^{d-1} \tau_j\,\Phi_{d-j} \qquad (d \ge 1).$$
--   When $\Phi(0) = 1$ it is the unique sequence with $d\,\Phi_d = -\sum_{j=1}^{d} \tau_j\,\Phi_{d-j}$ for all $d \ge 1$, that is, $\log \Phi(z) = -\sum_{d \ge 1} \tau_d\, z^d/d$.
--   4. **Tensor differential operators.** On polynomials in an auxiliary $n \times n$ matrix of indeterminates $V = (V_{ij})$, `tfhat` is the operator
--   $$\hat f_i = \sum_{t} A_{i,t}\,\frac{\partial}{\partial V_{i t_1}}\cdots\frac{\partial}{\partial V_{i t_r}},$$
--   and `tapplyAll` applies $\hat f_1^{a_1}\cdots\hat f_n^{a_n}$ for $a \in \mathbb{N}^n$.
--   5. **The power tensor.** `vTensor` is the tensor $A^V_{i,t} = V_{i t_1}\cdots V_{i t_r}$ with entries in $\mathbb{Q}[V]$. Its system is $x_i^{r} = \bigl((Vx)_i\bigr)^{r}$.
--
--   These definitions extend the platform's `coord`, `charPoly`, `fhat` and `applyAll` from hypergraph adjacency tensors to arbitrary tensors. For the adjacency tensor $A_{i,t} = a_{i t_1 \cdots t_r}$ of a hypergraph, `tfhat` and `tapplyAll` coincide definitionally with `fhat` and `applyAll`. They are used to state the Morozov–Shakirov identity $\log \operatorname{Res} = -\sum_d \mathrm{Tr}_d/d$ for arbitrary tensors. This includes the power tensor of a matrix $V$, where the identity reduces to $\log\det = \operatorname{tr}\log$.
--
--   **Formalization Note** A tensor is a function `Fin n → (Fin (k - 1) → Fin n) → R`. The indeterminate $V_{ij}$ is `MvPolynomial.X (i, j)` in `AuxPoly n`. `newtonTr` is defined by well-founded recursion for every polynomial; the characterization above holds when $\Phi(0) = 1$.
-- source:
--   Morozov and Shakirov, Analogue of the identity Log Det = Trace Log for resultants, arXiv:0804.4632v3, Section 4, Proposition II and eq. (16); Clark and Cooper, A Harary-Sachs theorem for hypergraphs, arXiv:1812.00468v2, p. 4, Equation (1).

import Mathlib
import Definitions.Def_HararySachs_Hyper_CharPoly
import Definitions.Def_HararySachs_Hyper_Operators

namespace HararySachs.Hyper

/-- The `j`-th equation `x_j^{k-1} - z · Σ_t A j t · x_{t 0} ⋯ x_{t (k-2)}` of the system
`x^{[k-1]} - z · A x^{k-1}`, for an arbitrary (not necessarily symmetric) tensor `A`
with entries in a commutative ring `R`; the coefficients are polynomials in `z`. -/
noncomputable def zcoord {R : Type*} [CommRing R] {n k : ℕ}
    (A : Fin n → (Fin (k - 1) → Fin n) → R) (j : Fin n) :
    MvPolynomial (Fin n) (Polynomial R) :=
  MvPolynomial.monomial (Finsupp.single j (k - 1)) 1 -
    ∑ t : Fin (k - 1) → Fin n,
      MvPolynomial.monomial
        ((Finset.univ : Finset (Fin (k - 1))).sum (fun a => Finsupp.single (t a) 1))
        (Polynomial.C (A j t) * Polynomial.X)

/-- `Φ_A(z) = Res(x^{[k-1]} - z · A x^{k-1})`, a polynomial in `z`. -/
noncomputable def phiPoly {R : Type*} [CommRing R] {n k : ℕ}
    (A : Fin n → (Fin (k - 1) → Fin n) → R)
    (res : MvPolynomial (ResVar n (fun _ => k - 1)) ℤ) : Polynomial R :=
  MvPolynomial.aeval (fun v : ResVar n (fun _ => k - 1) =>
    MvPolynomial.coeff v.2.1 (zcoord (k := k) A v.1))
      (MvPolynomial.map (Int.castRingHom (Polynomial R)) res)

/-- The Newton traces of a polynomial `Φ` with `Φ(0) = 1`: the unique sequence with
`d · Φ_d = - Σ_{j=1}^{d} τ_j · Φ_{d-j}` for `d ≥ 1` (so `log Φ = - Σ τ_d z^d / d`). -/
noncomputable def newtonTr {R : Type*} [CommRing R] (Φ : Polynomial R) : ℕ → R
  | 0 => 0
  | d + 1 => -(((d + 1 : ℕ) : R) * Φ.coeff (d + 1)) -
      ∑ j : Fin (d + 1), newtonTr Φ j * Φ.coeff (d + 1 - j)
decreasing_by all_goals (simp_wf; exact Nat.lt_succ_iff.mp j.isLt)

/-- The differential operator `f_i(∂/∂V_{i,·})` attached to row `i` of a tensor `A`
(the tensor version of `fhat`). -/
noncomputable def tfhat {n k : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (i : Fin n) (p : AuxPoly n) : AuxPoly n :=
  ∑ t : Fin (k - 1) → Fin n,
    A i t • (List.ofFn t).foldr (fun j q => MvPolynomial.pderiv (i, j) q) p

/-- `∏_i f_i(∂)^{a_i}` (the tensor version of `applyAll`). -/
noncomputable def tapplyAll {n k d : ℕ} (A : Fin n → (Fin (k - 1) → Fin n) → ℚ)
    (a : Fin n → Fin (d + 1)) (p : AuxPoly n) : AuxPoly n :=
  (List.ofFn (fun i : Fin n => i)).foldl
    (fun q i => ((tfhat (k := k) A i)^[(a i).val]) q) p

/-- The tensor of the system `x_i^{k-1} = ((V x)_i)^{k-1}`, with entries in the
polynomial ring in the matrix entries `V_{ij}`. -/
noncomputable def vTensor (n k : ℕ) : Fin n → (Fin (k - 1) → Fin n) → AuxPoly n :=
  fun i t => ∏ s, MvPolynomial.X (i, t s)

end HararySachs.Hyper


