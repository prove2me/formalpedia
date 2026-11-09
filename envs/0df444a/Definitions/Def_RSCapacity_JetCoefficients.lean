-- Prove2me | Definitions.Def_RSCapacity_JetCoefficients
-- name    : RSCapacity_JetCoefficients
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:54.521616+00:00
-- url     : https://prove2.me/theorems/3d8a8c19-3c85-47a6-9c33-679cfd91afd0
-- title:
--   Taylor-coefficient jets: $F_{\alpha,t}$ and $H_\alpha$ of §6.3.1
-- statement:
--   Let $Q\in F[Z,X,Y_0,\dots,Y_r]$, fix $\alpha\in F$ and $d\ge0$, and treat the Taylor coefficients of a polynomial $P$ of degree at most $d$ at $\alpha$ as indeterminates: $P(\alpha+U)=\sum_{j=0}^d c_jU^j$, so that
--   $$P^{[i]}(\alpha+U)=\sum_{j=i}^d\binom{j}{i}c_jU^{j-i}.$$
--   For $t\ge0$, $F_{\alpha,t}\in F[Z,c_0,\dots,c_d]$ is the coefficient of $U^t$ in
--   $$Q\bigl(Z,\alpha+U,P(\alpha+U),P^{[1]}(\alpha+U),\dots\bigr),$$
--   and for a variable $Y_s$,
--   $$H_\alpha(Z,c_0,\dots,c_s)=\frac{\partial Q}{\partial Y_s}(Z,\alpha,c_0,\dots,c_s).$$
--   The lifted jet relation says that, at every point with $H_\alpha\neq0$, the equations $F_{\alpha,t}=0$ ($1\le t\le d-s$) hold exactly when $c_{s+t}=N_t/H_\alpha^{2t-1}$ for $1\le t\le d-s$, for given polynomials $N_t$.
--
--   These are the coordinates in which the solutions of a differential equation are parameterized by a few base variables.
--
--   **Formalization Note** $F[Z,X,Y_0,\dots,Y_r]$ is `MvPolynomial (Fin (r + 3)) F` ($Z=0$, $X=1$, $Y_j=j+2$); the jet ring is `MvPolynomial (Fin (d + 2)) F` ($Z=0$, $c_l=l+1$). Every $Y_i$ is replaced by $P^{[i]}(\alpha+U)$; the theorems assume $Q$ does not depend on $Y_j$ for $j>s$, so this is the paper's substitution. The total $Y$-degree on $F[Z,X,Y_0,\dots,Y_r]$ gives $Z$ and $X$ weight $0$.
-- source:
--   Jeronimo, Algorithmic List Decoding at Capacity and Optimal Proximity Gaps for Reed–Solomon Codes, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…), §6.3, p.25 (PDF 27); §6.3.1, p.26 (PDF 28), Equations (14), (59), (60), (62)

import Mathlib

set_option autoImplicit false

namespace RSCapacity

/-!
# Taylor-coefficient jets: F_{α,t} and H_α of §6.3.1

Jeronimo, arXiv:2609.05870 (held version of November 1, 2026, sha256 9a0069bd…): §6.3, p.25
(PDF 27) and §6.3.1, p.26 (PDF 28), Equations (14), (59), (60).

"Suppose Q depends on Y_s but on no Y_j with j > s. Fix α ∈ F and write
P(α + U) = ∑_{j=0}^{d} c_j U^j. Set H_α(Z, c_0, …, c_s) := ∂Q/∂Y_s (Z, α, c_0, …, c_s). (59)
For t ≥ 0, let F_{α,t} be the coefficient of U^t in
Q(Z, α + U, P(α + U), P^{[1]}(α + U), …, P^{[s]}(α + U)). (60)" Here
Q ∈ F[Z, X, Y_0, …, Y_r] and, by (14), P^{[i]}(α + U) = ∑_{j=i}^{d} C(j, i) c_j U^{j−i}.

**Formalization Note.**
* F[Z, X, Y_0, …, Y_r] is `MvPolynomial (Fin (r + 3)) F`: variable `0` = Z, `1` = X,
  `j + 2` = Y_j.
* The jet ring F[Z, c_0, …, c_d] is `MvPolynomial (Fin (d + 2)) F`: variable `0` = Z and
  `l + 1` = c_l. `cVar d l` is c_l for l ≤ d and `0` for l > d (the coefficient c_l of a
  polynomial of degree at most d).
* The Taylor coefficients c_j are indeterminates, so P(α + U) is the generic polynomial of degree
  at most d; Y_i is replaced by P^{[i]}(α + U) = ∑_{l=i}^{d} C(l, i) c_l U^{l−i} for every
  i ≤ r (this is `0` for i > d). Since Q does not depend on Y_j for j > s, this is (60).
* H_α substitutes X ↦ α and Y_i ↦ P^{[i]}(α) = c_i in ∂Q/∂Y_s.
* A point of the jet space is `x : Fin (d + 2) → F` with x 0 = z and x (l + 1) = c_l.
-/

open MvPolynomial

/-- The weight (0, 0, 1, …, 1) on (Z, X, Y_0, …, Y_r); its weighted total degree is
deg^tot_Y. -/
def yWeight3 (r : ℕ) : Fin (r + 3) → ℕ := fun i => if (i : ℕ) < 2 then 0 else 1

/-- The jet variable c_l (`0` if l > d). -/
noncomputable def cVar {F : Type*} [Field F] (d l : ℕ) : MvPolynomial (Fin (d + 2)) F :=
  if h : l ≤ d then X ⟨l + 1, by omega⟩ else 0

/-- The variable Y_j (j ≤ r) of F[Z, X, Y_0, …, Y_r]. -/
def yVar3 {r : ℕ} (j : Fin (r + 1)) : Fin (r + 3) := j.succ.succ

/-- P^{[i]}(α + U) = ∑_{l=i}^{d} C(l, i) c_l U^{l−i} for the generic P of degree ≤ d,
as a polynomial in U over F[Z, c_0, …, c_d] (Equation (14)). -/
noncomputable def jetHasse {F : Type*} [Field F] (d i : ℕ) :
    Polynomial (MvPolynomial (Fin (d + 2)) F) :=
  ∑ l ∈ Finset.range (d + 1),
    if i ≤ l then Polynomial.C (C ((l.choose i : ℕ) : F) * cVar d l) * Polynomial.X ^ (l - i)
    else 0

/-- The substitution of (60): Z ↦ Z, X ↦ α + U, Y_i ↦ P^{[i]}(α + U). -/
noncomputable def jetSubstMap {F : Type*} [Field F] (r d : ℕ) (α : F) :
    Fin (r + 3) → Polynomial (MvPolynomial (Fin (d + 2)) F) :=
  fun i =>
    if (i : ℕ) = 0 then Polynomial.C (X 0)
    else if (i : ℕ) = 1 then Polynomial.C (C α) + Polynomial.X
    else jetHasse d ((i : ℕ) - 2)

/-- F_{α,t}: the coefficient of U^t in Q(Z, α + U, P(α + U), P^{[1]}(α + U), …) (Equation (60)). -/
noncomputable def jetCoeff {F : Type*} [Field F] (r d : ℕ) (α : F)
    (Q : MvPolynomial (Fin (r + 3)) F) (t : ℕ) : MvPolynomial (Fin (d + 2)) F :=
  (aeval (jetSubstMap r d α) Q).coeff t

/-- H_α(Z, c_0, …, c_s) = ∂Q/∂Y_s (Z, α, c_0, …, c_s) (Equation (59)). -/
noncomputable def Halpha {F : Type*} [Field F] (r d : ℕ) (α : F) (s : Fin (r + 1))
    (Q : MvPolynomial (Fin (r + 3)) F) : MvPolynomial (Fin (d + 2)) F :=
  aeval (fun i : Fin (r + 3) =>
      if (i : ℕ) = 0 then X 0 else if (i : ℕ) = 1 then C α else cVar d ((i : ℕ) - 2))
    (pderiv (yVar3 s) Q)

/-- The recursion (62) of Lemma 6.7, p.26: at every point x = (z, c_0, …, c_d) with
H_α(x) ≠ 0, the equations F_{α,t}(x) = 0 for 1 ≤ t ≤ d − s hold exactly when
c_{s+t} = N_t(x) / H_α(x)^{2t−1} for 1 ≤ t ≤ d − s. -/
def IsLiftedJet {F : Type*} [Field F] (r d : ℕ) (α : F) (s : Fin (r + 1))
    (Q : MvPolynomial (Fin (r + 3)) F) (N : ℕ → MvPolynomial (Fin (d + 2)) F) : Prop :=
  ∀ x : Fin (d + 2) → F, eval x (Halpha r d α s Q) ≠ 0 →
    ((∀ t : ℕ, 1 ≤ t → (s : ℕ) + t ≤ d → eval x (jetCoeff r d α Q t) = 0) ↔
      ∀ t : ℕ, 1 ≤ t → (s : ℕ) + t ≤ d →
        eval x (cVar d ((s : ℕ) + t)) = eval x (N t) / eval x (Halpha r d α s Q) ^ (2 * t - 1))

end RSCapacity


