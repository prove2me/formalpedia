-- Prove2me | Definitions.Def_ChowFormsCH_IsGeneralProjection
-- name    : ChowFormsCH_IsGeneralProjection
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:57:25.075457+00:00
-- url     : https://prove2.me/theorems/1de5ec84-f8c2-4c21-a1c0-d35ad08b4619
-- title:
--   General projection $Q$ of $V$ and the geometric resolution $q, r_2,\dots,r_n$ of eq. (1)
-- statement:
--   Let $V\subseteq K^{m+n}$ and $\ell=u_1y_1+\dots+u_ny_n$. A polynomial $Q\in K[u,x][T]$ **defines the general projection of $V$** if $Q$ is monic in $T$ and a polynomial $f\in K[u,x][T]$ vanishes at every point $(\mu,\alpha,\sum_j\mu_j\beta_j)$ with $\mu\in K^n$ and $(\alpha,\beta)\in V$ if and only if $Q$ divides $f$. With $\nu_0=(1,0,\dots,0)$, eq. (1) sets
--   $$
--   q:=Q(\nu_0,x,y_1),\qquad r_j:=-\frac{\partial Q}{\partial u_j}(\nu_0,x,y_1),\quad j=1,\dots,n,
--   $$
--   polynomials in $K[x][y_1]$; $q'$ denotes the derivative of $q$ in $y_1$, and $q,r_j,q'$ are embedded in $K[x,y]$ with $y_1$ the polynomial variable.
--
--   Lemmas 3.8, 3.10, 3.11 show that $q,r_2,\dots,r_n$ form a geometric resolution of $V$ (Definition 3.3); Lemma 3.12 computes $Q$ from a Chow form.
--
--   **Formalization Note** The paper constructs $Q=Q_1\cdots Q_t$ over the algebraic closure of $K(u)$, monic in $T$, squarefree, defining the image of $V$ under $(p,q)\mapsto(p,\ell(q))$ (Lemmas 3.5–3.6). The characterization here stays over $K$: the image has the hypersurface $Q=0$ as Zariski closure and $Q$ is squarefree, so the vanishing ideal of the image is $(Q)$; with monicity in $T$ this determines $Q$. For $V=\emptyset$ it gives $Q=1$.
-- source:
--   Andrews, Garg, Oliveira, Schost, Some algebraic and geometric computations in CH via Chow forms, arXiv:2611.05289 (held version, sha256 75e796c6…), §3.2, pp.24–25, eq. (1)

import Mathlib
import Definitions.Def_ChowFormsCH_AffSp

set_option autoImplicit false

namespace ChowFormsCH

/-- `Q ∈ K[u, x][T]` defines the general projection of `V ⊆ K^{m+n}` (Andrews–Garg–Oliveira–Schost,
*Some algebraic and geometric computations in CH via Chow forms*, arXiv:2611.05289, held version,
sha256 75e796c6…, §3.2, pp.24–25: with `ℓ = u₁y₁ + ⋯ + uₙyₙ`, `Q = Q₁ ⋯ Q_t` defines the image of
`V` under `(p, q) ↦ (p, ℓ(q))`, "The polynomial Q has total degree deg V in x and T and is monic in
T. We say that the polynomial Q defines the general projection of the variety V"): `Q` is monic in
`T`, and a polynomial `f ∈ K[u, x][T]` vanishes at every point `(μ, α, Σ_j μ_j β_j)` with
`μ ∈ K^n`, `(α, β) ∈ V` iff `Q` divides `f`.

**Formalization Note** The paper constructs `Q` over the algebraic closure of `K(u)`
(Lemmas 3.5–3.6). The characterization used here stays over `K`: the image set
`{(μ, α, ⟨μ, β⟩)}` has the hypersurface `Q = 0` as Zariski closure, and `Q` is squarefree, so the
vanishing ideal of the image is `(Q)`; together with monicity in `T` this determines `Q`. For
`V = ∅` it gives `Q = 1`. The variables of the coefficient ring are `u₁, …, uₙ` (`Sum.inl`) and
`x₁, …, x_m` (`Sum.inr`); `T` is the polynomial variable. -/
def IsGeneralProjection {m n : ℕ} {K : Type*} [Field K] (V : Set (AffSp (Fin m ⊕ Fin n) K))
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) : Prop :=
  Q.Monic ∧
    ∀ f : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K),
      (∀ (μ : Fin n → K) (v : AffSp (Fin m ⊕ Fin n) K), v ∈ V →
        Polynomial.eval (∑ j : Fin n, μ j * (show Fin m ⊕ Fin n → K from v) (Sum.inr j))
          (f.map (MvPolynomial.eval
            (Sum.elim μ (fun j : Fin m => (show Fin m ⊕ Fin n → K from v) (Sum.inl j))))) = 0)
      ↔ Q ∣ f

/-- The point `ν₀ = (1, 0, …, 0) ∈ K^n` (eq. (1), p.25). -/
def nu0 {n : ℕ} {K : Type*} [Field K] : Fin n → K := fun j => if j.val = 0 then 1 else 0

/-- Specialization `u ↦ ν₀` from `K[u, x]` to `K[x]` (eq. (1), p.25). -/
noncomputable def specNu0 {m n : ℕ} {K : Type*} [Field K] :
    MvPolynomial (Fin n ⊕ Fin m) K →+* MvPolynomial (Fin m) K :=
  (MvPolynomial.aeval (Sum.elim (fun j : Fin n => MvPolynomial.C (nu0 j))
    (fun j : Fin m => MvPolynomial.X j))).toRingHom

/-- `q := Q(ν₀, x, y₁) ∈ K[x][y₁]` (eq. (1), p.25), with `y₁` as the polynomial variable. -/
noncomputable def resQ {m n : ℕ} {K : Type*} [Field K]
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) : Polynomial (MvPolynomial (Fin m) K) :=
  Q.map specNu0

/-- `r_j := −∂Q/∂u_j (ν₀, x, y₁) ∈ K[x][y₁]` (eq. (1), p.25): the partial derivative is taken
coefficientwise in `K[u, x]`, then `u ↦ ν₀`; `y₁` is the polynomial variable. -/
noncomputable def resR {m n : ℕ} {K : Type*} [Field K]
    (Q : Polynomial (MvPolynomial (Fin n ⊕ Fin m) K)) (j : Fin n) :
    Polynomial (MvPolynomial (Fin m) K) :=
  -((Q.sum fun i a => Polynomial.monomial i (MvPolynomial.pderiv (Sum.inl j) a)).map specNu0)

/-- The embedding `K[x][y₁] → K[x, y]` sending the polynomial variable to `y₁` (§3.2, p.26). -/
noncomputable def embXY1 {m n : ℕ} [NeZero n] {K : Type*} [Field K] :
    Polynomial (MvPolynomial (Fin m) K) →+* MvPolynomial (Fin m ⊕ Fin n) K :=
  Polynomial.eval₂RingHom (MvPolynomial.rename Sum.inl).toRingHom (MvPolynomial.X (Sum.inr 0))

/-- The value `p(α, β₁)` of `p ∈ K[x][y₁]` at the projection of a point `(α, β) ∈ K^{m+n}`. -/
noncomputable def evalXY1 {m n : ℕ} [NeZero n] {K : Type*} [Field K]
    (p : Polynomial (MvPolynomial (Fin m) K)) (v : AffSp (Fin m ⊕ Fin n) K) : K :=
  Polynomial.eval ((show Fin m ⊕ Fin n → K from v) (Sum.inr 0))
    (p.map (MvPolynomial.eval fun j : Fin m => (show Fin m ⊕ Fin n → K from v) (Sum.inl j)))

end ChowFormsCH


