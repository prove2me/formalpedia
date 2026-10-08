-- Prove2me | Definitions.Def_AlgebraicPCSP_BLP_LP
-- name    : AlgebraicPCSP_BLP_LP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:23:27.239992+00:00
-- url     : https://prove2.me/theorems/17c3d241-39e5-44f5-b6df-4de6e6f5f2cb
-- title:
--   BLP solvability, the structures LP(A) and LP_ℓ(A) (Definitions 7.6, 7.7, 7.10; proof of Theorem 7.9)
-- statement:
--   Let $\mathbf A$ be a finite relational structure.
--
--   **BLP solves (Definitions 7.6, 7.7).** For an instance $\mathbf I$ (a finite structure similar to $\mathbf A$), the basic LP relaxation has variables $\mu_v(a)\in[0,1]$ for every element $v$ and $a\in A$, and $\mu_{\mathbf v,R}(\mathbf a)\in[0,1]$ for every constraint $(\mathbf v,R)$, $\mathbf v\in R^{\mathbf I}$, and $\mathbf a\in A^{\mathrm{ar}(R)}$, subject to
--   $$\sum_{a\in A}\mu_v(a)=1,\qquad \sum_{\mathbf a\in A^{\mathrm{ar}(R)},\,\mathbf a(i)=a}\mu_{\mathbf v,R}(\mathbf a)=\mu_{\mathbf v(i)}(a).\tag{7.1, 7.2}$$
--   $\mathrm{BLP}_{\mathbf A}(\mathbf I)=1$ holds exactly when this system has a solution with $\mu_{\mathbf v,R}(\mathbf a)=0$ for every constraint and every $\mathbf a\notin R^{\mathbf A}$ (the remark after Definition 7.7). For a PCSP template $(\mathbf A,\mathbf B)$, *BLP solves* $\mathrm{PCSP}(\mathbf A,\mathbf B)$ if every instance $\mathbf I$ with $\mathrm{BLP}_{\mathbf A}(\mathbf I)=1$ maps homomorphically to $\mathbf B$.
--
--   **The structure $\mathrm{LP}(\mathbf A)$ (Definition 7.10).** It is similar to $\mathbf A$; its universe consists of the rational probability distributions $\phi:A\to\mathbb Q\cap[0,1]$, $\sum_{a\in A}\phi(a)=1$. A $k$-tuple $(\phi_1,\dots,\phi_k)$ lies in $R^{\mathrm{LP}(\mathbf A)}$ iff there is a rational probability distribution $\gamma$ on $R^{\mathbf A}$ with
--   $$\sum_{\mathbf a\in R^{\mathbf A},\,\mathbf a(i)=a}\gamma(\mathbf a)=\phi_i(a)\qquad\text{for all } i\in[k],\ a\in A.\tag{$\blacklozenge$}$$
--
--   **The structure $\mathrm{LP}_\ell(\mathbf A)$ (proof of Theorem 7.9).** Its universe consists of the distributions $\phi$ with $\phi(a)=q/\ell$ for some $q\in\{0,1,\dots,\ell\}$ and $\sum_a\phi(a)=1$, and its relations are defined by ($\blacklozenge$) with witnesses $\gamma$ that also have all values in $\{0,1/\ell,\dots,1\}$. It is not an induced substructure of $\mathrm{LP}(\mathbf A)$.
--
--   $\mathrm{LP}(\mathbf A)$ is the bridge between the LP and the algebra: an instance has $\mathrm{BLP}_{\mathbf A}(\mathbf I)=1$ iff it maps to $\mathrm{LP}(\mathbf A)$, and $\mathrm{LP}(\mathbf A)$ is isomorphic to the free structure of $\mathcal Q_{\mathrm{conv}}$.
--
--   **Formalization Note** An instance is the referenced `Instance` (variables $\mathrm{Fin}\,n$, a list of constraints; repeating a constraint changes neither side of the definition), and the feasibility system is the referenced `IsLPSol` over $\mathbb Q$, which includes the vanishing condition off $R^{\mathbf A}$; an LP with rational data is feasible over $\mathbb R$ iff it is feasible over $\mathbb Q$. A distribution $\gamma$ on $R^{\mathbf A}$ is a function on $A^k$ that vanishes off $R^{\mathbf A}$. The bound $\phi(a)\le 1$ is implied by nonnegativity and the sum and is not written separately.
-- source:
--   L. Barto, J. Bulín, A. Krokhin, J. Opršal, Algebraic approach to promise constraint satisfaction, arXiv:1811.00970v3, pp. 45–48, Definitions 7.6, 7.7 (and the remark after it), 7.10, display (♦), and LP_ℓ(A) in the proof of Theorem 7.9

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace AlgebraicPCSP.BLP

open PCSPBLPAff.Symmetric

/-- "BLP solves `PCSP(𝔸, 𝔹)`" (Definition 7.7, p. 45): every instance `I` with
`BLP_𝔸(I) = 1` maps homomorphically to `𝔹`. By the remark after Definition 7.7 (p. 45),
`BLP_𝔸(I) = 1` iff the basic LP relaxation of Definition 7.6, with `µ_{v,R}(a) = 0` added for
every constraint `(v, R)` and every `a ∉ R^𝔸`, is feasible; that feasibility system is the
published `IsLPSol X 𝔸 w p` (variables `w = µ_v`, `p = µ_{v,R}`, constraints (7.1), (7.2),
nonnegativity and the vanishing condition) over `ℚ`. -/
def BLPSolves {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) : Prop :=
  ∀ X : Instance τ ar, (∃ w p, IsLPSol X 𝔸 w p) → SatIn X 𝔹

/-- The universe of `LP(𝔸)` (Definition 7.10, p. 46): rational probability distributions on
the finite set `A`, i.e. `ϕ : A → ℚ ∩ [0, 1]` with `∑_{a ∈ A} ϕ(a) = 1` (the bound
`ϕ(a) ≤ 1` follows from nonnegativity and the sum). -/
def LPDist (A : Type) [Fintype A] : Type :=
  {ϕ : A → ℚ // (∀ a, 0 ≤ ϕ a) ∧ ∑ a, ϕ a = 1}

/-- The structure `LP(𝔸)` (Definition 7.10, pp. 46–47), similar to `𝔸`. A `k`-tuple
`(ϕ₁, …, ϕ_k)` lies in `R^{LP(𝔸)}` iff there is a rational probability distribution `γ` on
`R^𝔸` with `∑_{a ∈ R^𝔸, a(i) = a} γ(a) = ϕᵢ(a)` for all `i ∈ [k]` and `a ∈ A` (display (♦)).
A distribution on `R^𝔸` is encoded as a function on all of `A^k` that vanishes off `R^𝔸`. -/
def LP {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) : RelStruct τ ar (LPDist A) where
  rel R := {t | ∃ γ : (Fin (ar R) → A) → ℚ,
    (∀ r, 0 ≤ γ r) ∧ (∀ r, r ∉ 𝔸.rel R → γ r = 0) ∧ ∑ r, γ r = 1 ∧
    ∀ (i : Fin (ar R)) (a : A),
      ∑ r ∈ Finset.univ.filter (fun r : Fin (ar R) → A => r i = a), γ r = (t i).val a}

/-- The universe of `LP_ℓ(𝔸)` (proof of Theorem 7.9, p. 48): rational probability
distributions on `A` with denominators dividing `ℓ`, i.e. `ϕ : A → ℚ` with
`ϕ(a) = q/ℓ` for some `q ∈ {0, 1, …, ℓ}` for each `a`, and `∑_{a ∈ A} ϕ(a) = 1`. -/
def LPellDist (A : Type) [Fintype A] (ℓ : ℕ) : Type :=
  {ϕ : A → ℚ // (∀ a, ∃ q : ℕ, q ≤ ℓ ∧ ϕ a = (q : ℚ) / ℓ) ∧ ∑ a, ϕ a = 1}

/-- The structure `LP_ℓ(𝔸)` (proof of Theorem 7.9, p. 48), similar to `𝔸`: the relations are
defined as in `LP(𝔸)`, but the witnessing distribution `γ` on `R^𝔸` must also have
denominators dividing `ℓ`. It is not an induced substructure of `LP(𝔸)`. -/
def LPell {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (ℓ : ℕ) : RelStruct τ ar (LPellDist A ℓ) where
  rel R := {t | ∃ γ : (Fin (ar R) → A) → ℚ,
    (∀ r, ∃ q : ℕ, q ≤ ℓ ∧ γ r = (q : ℚ) / ℓ) ∧ (∀ r, r ∉ 𝔸.rel R → γ r = 0) ∧
    ∑ r, γ r = 1 ∧
    ∀ (i : Fin (ar R)) (a : A),
      ∑ r ∈ Finset.univ.filter (fun r : Fin (ar R) → A => r i = a), γ r = (t i).val a}

end AlgebraicPCSP.BLP


