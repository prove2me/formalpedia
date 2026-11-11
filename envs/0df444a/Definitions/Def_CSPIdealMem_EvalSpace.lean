-- Prove2me | Definitions.Def_CSPIdealMem_EvalSpace
-- name    : CSPIdealMem_EvalSpace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:28:41.089571+00:00
-- url     : https://prove2.me/theorems/affb77ca-9c16-4ef7-b9b7-09f6bb0525a4
-- title:
--   Evaluation vectors $\nu_d$, $W_d(P)$, $U_d$, the span condition and the CSP ideal $I(P)$
-- statement:
--   Fix a nonempty finite $D\subseteq\mathbb Q$ and $d\ge0$. Let $M_d(X)$ be the set of monomials in the variables $X$ of total degree at most $d$, including $1$. For an assignment $\varphi:X\to D$,
--   $$
--   \nu_d(\varphi)=\bigl(m(\varphi)\bigr)_{m\in M_d(X)}\in\mathbb Q^{M_d(X)},\qquad W_d(P)=\mathrm{span}_{\mathbb Q}\{\nu_d(\varphi)\mid\varphi\in\mathrm{Sol}(P)\}.
--   $$
--   With variables $Z=\{z_a\mid a\in D\}$, a map $e:D\to D$ is the assignment $z_a=e(a)$, giving $\nu_d(e)\in\mathbb Q^{M_d(Z)}$, and
--   $$
--   U_d=\mathrm{span}_{\mathbb Q}\{\nu_d(e)\mid e\in E\}\subseteq\mathbb Q^{M_d(Z)},
--   $$
--   where $E$ is the set of covered endomorphisms of $\Gamma$. The **finite span condition** at degree $d$ is $\nu_d(\mathrm{id}_D)\in U_d$. The **CSP ideal** is
--   $$
--   I(P)=\{f\in\mathbb Q[X]\mid f(\varphi)=0\text{ for every }\varphi\in\mathrm{Sol}(P)\},
--   $$
--   and $I(P)\cap\mathbb Q[X]_{\le d}$ is its subspace of polynomials of total degree at most $d$.
--
--   These spaces state the dichotomy criterion and the outputs of the tractable case.
--
--   **Formalization Note** Monomials of degree $\le d$ are exponent vectors $m$ with $\deg m\le d$; vectors in $\mathbb Q^{M_d}$ are functions on this type. Polynomials are evaluated at the rational labels of the values. $I(P)$ is Mathlib's `vanishingIdeal` of the solution set, so it is the whole ring when $P$ is unsatisfiable.
-- source:
--   Rafiey–Soleymani–Jaillet, A Dichotomy Theorem for CSP-Based Ideal Membership, STOC 2027 submission manuscript (held version, sha256 c7140009133170c893c7b31cf2279f3dda0264d867825a8beb7cc6963f50f109), I(P), p.3 (PDF 3); M_d, ν_d, W_d(P), ν_d(e), U_d, span condition, p.4 (PDF 4); I(P) ∩ Q[X]≤d, p.5 (PDF 5) and pp.11–12

import Mathlib
import Definitions.Def_CSPIdealMem_Polymorphism

namespace CSPIdealMem

/-! # Evaluation vectors, the spaces `W_d(P)` and `U_d`, the span condition, and the CSP ideal

Rafiey–Soleymani–Jaillet, *A Dichotomy Theorem for CSP-Based Ideal Membership*, STOC 2027
submission manuscript (held version, sha256 c7140009…f50f109): the CSP ideal `I(P)`, p.3
(PDF 3); `M_d(X)`, `ν_d(φ)`, `W_d(P)`, `ν_d(e)`, `U_d` and the finite span condition, p.4 (PDF 4);
`I(P) ∩ ℚ[X]_{≤d}`, p.5 and p.11–12.

**Formalization Note.** The domain is `D : Finset ℚ` with values in the subtype `↥D`;
polynomials are evaluated at the rational labels `(φ x : ℚ)`. The monomials of total degree at
most `d` in the variables `σ` are the exponent vectors `m : σ →₀ ℕ` with `m.degree ≤ d` (the
constant monomial `1` is `m = 0`); a vector in `ℚ^{M_d}` is a function on this type. For maps
`e : D → D` the variables are `Z = {z_a | a ∈ D}`, indexed by `↥D`, with `z_a := e(a)`. `I(P)` is
Mathlib's `vanishingIdeal` of the set of solutions (as points of `ℚ^n`); for an unsatisfiable
instance it is the whole ring. -/

/-- `M_d(σ)` (p.4): the monomials in the variables `σ` of total degree at most `d`, including the
constant monomial, as exponent vectors. -/
def Mon (σ : Type) (d : ℕ) : Type := {m : σ →₀ ℕ // m.degree ≤ d}

/-- The degree-`d` evaluation vector `ν_d(v) = (m(v))_{m ∈ M_d(σ)} ∈ ℚ^{M_d(σ)}` of a point
`v : σ → ℚ` (p.4): the values of all monomials of total degree at most `d`. -/
noncomputable def evalVec {σ : Type} (d : ℕ) (v : σ → ℚ) : Mon σ d → ℚ :=
  fun m => MvPolynomial.eval v (MvPolynomial.monomial m.1 (1 : ℚ))

variable {D : Finset ℚ}

/-- `ν_d(φ)` for an assignment `φ : X → D` (p.4), evaluated at the rational labels. -/
noncomputable def assignVec {σ : Type} (d : ℕ) (φ : σ → D) : Mon σ d → ℚ :=
  evalVec d (fun x => ((φ x : D) : ℚ))

/-- `ν_d(e)` for a map `e : D → D` (p.4): the evaluation vector of the assignment `z_a := e(a)`
to the variables `Z = {z_a | a ∈ D}`, indexed by `M_d(Z)`. -/
noncomputable def mapVec (d : ℕ) (e : D → D) : Mon D d → ℚ :=
  assignVec d e

/-- `U_d := span_ℚ {ν_d(e) | e ∈ E}` (p.4), where `E` is the set of covered endomorphisms of `Γ`. -/
noncomputable def U (Γ : ConstraintLanguage D) (d : ℕ) : Submodule ℚ (Mon D d → ℚ) :=
  Submodule.span ℚ (mapVec d '' {e | IsCovered Γ e})

/-- The finite span condition at degree `d` (p.4): `ν_d(id_D) ∈ U_d`. -/
def SpanCondition (Γ : ConstraintLanguage D) (d : ℕ) : Prop :=
  mapVec d id ∈ U Γ d

/-- The solution evaluation space `W_d(P) := span_ℚ {ν_d(φ) | φ ∈ Sol(P)}` (p.4). -/
noncomputable def W {Γ : ConstraintLanguage D} (P : Instance Γ) (d : ℕ) :
    Submodule ℚ (Mon (Fin P.n) d → ℚ) :=
  Submodule.span ℚ (assignVec d '' Sol P)

/-- The CSP ideal `I(P) := {f ∈ ℚ[X] | f(φ) = 0 for every φ ∈ Sol(P)}` (p.3), the vanishing ideal
of the solutions viewed as points `x ↦ φ(x)` of `ℚ^X`. -/
noncomputable def idealOf {Γ : ConstraintLanguage D} (P : Instance Γ) :
    Ideal (MvPolynomial (Fin P.n) ℚ) :=
  MvPolynomial.vanishingIdeal ℚ ((fun φ x => ((φ x : D) : ℚ)) '' Sol P)

/-- `I(P) ∩ ℚ[X]_{≤d}` (p.5): the polynomials of total degree at most `d` in the CSP ideal, as a
`ℚ`-subspace of `ℚ[X]`. -/
noncomputable def idealDeg {Γ : ConstraintLanguage D} (P : Instance Γ) (d : ℕ) :
    Submodule ℚ (MvPolynomial (Fin P.n) ℚ) :=
  (idealOf P).restrictScalars ℚ ⊓ MvPolynomial.restrictTotalDegree (Fin P.n) ℚ d

end CSPIdealMem


