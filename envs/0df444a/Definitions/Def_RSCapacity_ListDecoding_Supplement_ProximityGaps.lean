-- Prove2me | Definitions.Def_RSCapacity_ListDecoding_Supplement_ProximityGaps
-- name    : RSCapacity_ListDecoding_Supplement_ProximityGaps
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:18:06.098649+00:00
-- url     : https://prove2.me/theorems/4453ac2d-620b-4dea-9dd5-cbcf3fb33714
-- title:
--   Agreement sets, the line hyperplanes $H_i$, TopVar and Kopparty reconstruction values
-- statement:
--   Let $F$ be a field, $n,k\ge 0$ integers, $\alpha=(\alpha_1,\dots,\alpha_n)\in F^n$ the evaluation points, and $u,v,y\in F^n$ received words (the values of functions $E\to F$ at the points $\alpha_i$). For $f,g,h\in F[X]$ define the index sets
--
--   $$\operatorname{agr}(y,f)=\{i\in[n]: f(\alpha_i)=y_i\},\qquad \operatorname{agr}(g,u)\cap\operatorname{agr}(h,v)=\{i\in[n]: g(\alpha_i)=u_i,\ h(\alpha_i)=v_i\},$$
--
--   the latter being the **correlated agreement** set of $(g,h)$ with $(u,v)$; its cardinality is the correlated agreement count. For $i\in[n]$ the **line hyperplane** is
--
--   $$H_i=\{(\zeta,f)\in F\times F[X]:\ \deg f<k,\ f(\alpha_i)=u_i+\zeta v_i\}.$$
--
--   For polynomials in $Z,X,Y_0,\dots,Y_d$: $\operatorname{TopVar}(P)=j$ means that $P$ depends non-trivially on $Y_j$ (positive $Y_j$-degree) and on no $Y_i$ with $i>j$. The specialization $P|_{Z=\zeta}\in F[X,Y_0,\dots,Y_d]$ substitutes the constant $\zeta$ for $Z$. The point $(\zeta,\gamma,a_0,\dots,a_d)$ assigns $Z=\zeta$, $X=\gamma$, $Y_i=a_i$. Given $P$, an index $j$, numerators $N_i$ and exponents $e_i$, the **reconstruction value** at a point $x$ is
--
--   $$\Phi_{P,i}(x)=\begin{cases} Y_i(x) & 0\le i\le d,\\[2pt] \dfrac{N_i(x)}{\bigl((\partial_{Y_j}P)(x)\bigr)^{2e_i}} & i>d,\end{cases}$$
--
--   the value of the rational function $\Phi_{P,i}$ of Lemma 6.6; it is used only where $(\partial_{Y_j}P)(x)\ne0$.
--
--   These are the objects of Section 6: the line $u+\zeta v$ and its correlated agreement (Theorem 1.2), the hyperplanes of the pruning argument (Lemma 6.1), and the rational functions of Kopparty's reconstruction (Lemma 6.6). They impose no condition: no $k\le n$, no finiteness of $F$, no injectivity (which the theorems state explicitly).
--
--   **Formalization Note** The variables of $F[Z,X,Y_0,\dots,Y_d]$ are indexed by `Fin (d+3)` with $0=Z$, $1=X$, $i+2=Y_i$; after $Z=\zeta$ they are indexed by `Fin (d+2)` with $0=X$, $i+1=Y_i$, matching the published `differentialSubstitute`, which computes $Q(X,f,f^{(1)},\dots,f^{(d)})$ with Hasse derivatives. A rational function $N/(\partial_{Y_j}P)^{2e}$ is represented by its numerator polynomial and exponent; Lean's `x / 0 = 0` is never relied upon because the lemma assumes the denominator nonzero. The degree-$<k$ convention includes the zero polynomial.
-- source:
--   Prahladh Harsha, Mrinal Kumar, Ramprasad Saptharishi, STOC 2027 submission #495 (October 2026), §6 p.17 (problem statement), §6.1 p.18 (H_i), §6.3 p.21 (TopVar, Φ_{P,i}); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/495.pdf

import Mathlib
import Definitions.Def_RSCapacity_ListDecoding_Differential

namespace RSCapacity.ListDecoding.Supplement

open RSCapacity.ListDecoding

variable {F : Type} [Field F]

/-! ### Agreement sets and the hyperplanes `H_i` of §6.1 (pp.17–18) -/

/-- `agr(y, f) = {i ∈ [n] : f(αᵢ) = yᵢ}` as a finite set of indices; its card is
the base `agreement α y f`. -/
noncomputable def agreementSet {n : ℕ} (α y : Fin n → F) (f : Polynomial F) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => evaluation α f i = y i

/-- Correlated agreement `agr(g, u) ∩ agr(h, v) = {i : g(αᵢ) = uᵢ ∧ h(αᵢ) = vᵢ}`. -/
noncomputable def correlatedAgreementSet {n : ℕ} (α u v : Fin n → F)
    (g h : Polynomial F) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => evaluation α g i = u i ∧ evaluation α h i = v i

/-- `|{i ∈ [n] : u(αᵢ) = g(αᵢ) and v(αᵢ) = h(αᵢ)}|`. -/
noncomputable def correlatedAgreement {n : ℕ} (α u v : Fin n → F)
    (g h : Polynomial F) : ℕ :=
  (correlatedAgreementSet α u v g h).card

/-- `Hᵢ = {(ζ, f) : deg f < k and f(αᵢ) = (u + ζ v)(αᵢ)}` ⊆ `F × F[X]`. The zero
polynomial has degree `⊥ < k`, so it is included for every `k`. -/
def lineHyperplane {n : ℕ} (k : ℕ) (α u v : Fin n → F) (i : Fin n) :
    Set (F × Polynomial F) :=
  {p | p.2.degree < (k : WithBot ℕ) ∧ evaluation α p.2 i = (u + p.1 • v) i}

/-! ### Polynomials in `Z, X, Y₀, …, Y_d` (§6.3, p.21)

Variables of `MvPolynomial (Fin (d + 3)) F`: `0 = Z`, `1 = X`, `i + 2 = Yᵢ`.
After `Z = ζ` the variables of `MvPolynomial (Fin (d + 2)) F` are `0 = X`,
`i + 1 = Yᵢ`, the base `differentialSubstitute` layout. -/

/-- The variable `Z`. -/
def varZ (d : ℕ) : Fin (d + 3) := 0

/-- The variable `X`. -/
def varX (d : ℕ) : Fin (d + 3) := 1

/-- The variable `Yᵢ`, `0 ≤ i ≤ d`. -/
def varY {d : ℕ} (i : Fin (d + 1)) : Fin (d + 3) := i.succ.succ

/-- `TopVar(P) = j`: `P` depends non-trivially on `Y_j` and on no `Yᵢ` with `i > j`.
`Y` lists the positions of `Y₀, …, Y_d` among the variables of `P`. -/
def IsTopVar {σ : Type} {d : ℕ} (P : MvPolynomial σ F) (Y : Fin (d + 1) → σ)
    (j : Fin (d + 1)) : Prop :=
  0 < P.degreeOf (Y j) ∧ ∀ i : Fin (d + 1), j < i → P.degreeOf (Y i) = 0

/-- `P|_{Z=ζ} ∈ F[X, Y₀, …, Y_d]`: substitute the constant `ζ` for `Z`. -/
noncomputable def specializeZ {d : ℕ} (ζ : F) (P : MvPolynomial (Fin (d + 3)) F) :
    MvPolynomial (Fin (d + 2)) F :=
  MvPolynomial.aeval
    (Fin.cases (motive := fun _ => MvPolynomial (Fin (d + 2)) F)
      (MvPolynomial.C ζ) MvPolynomial.X) P

/-- The point `(Z, X, Y₀, …, Y_d) = (ζ, γ, a₀, …, a_d)`. -/
def zxyPoint {d : ℕ} (ζ γ : F) (a : Fin (d + 1) → F) : Fin (d + 3) → F :=
  Fin.cases (motive := fun _ => F) ζ (Fin.cases (motive := fun _ => F) γ a)

/-- Value at a point `x = (ζ, γ, a₀, …, a_d)` of the rational function
`Φ_{P,i} = Yᵢ` for `i ≤ d` and `Φ_{P,i} = N_i / (∂_{Y_j} P)^{2 eᵢ}` for `i > d`.
It is used only at points where `(∂_{Y_j} P)(x) ≠ 0`. -/
noncomputable def reconstructionValue {d : ℕ} (P : MvPolynomial (Fin (d + 3)) F)
    (j : Fin (d + 1)) (N : ℕ → MvPolynomial (Fin (d + 3)) F) (e : ℕ → ℕ) (i : ℕ)
    (x : Fin (d + 3) → F) : F :=
  if h : i ≤ d then x (varY ⟨i, Nat.lt_succ_of_le h⟩)
  else MvPolynomial.eval x (N i) /
    (MvPolynomial.eval x (MvPolynomial.pderiv (varY j) P)) ^ (2 * e i)

end RSCapacity.ListDecoding.Supplement


