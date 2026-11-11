-- Prove2me | Definitions.Def_GoldProxGap_label
-- name    : GoldProxGap_label
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:46.520346+00:00
-- url     : https://prove2.me/theorems/8614b343-1e66-432b-8acf-52dd76909da3
-- title:
--   Canonical representatives, polynomials $\ell_\varphi$ and labels $\omega$ of linear functions, the label space $\hat D$, and $\Lambda,\eta,R$
-- statement:
--   Let $\mathbb B$ be a finite field of characteristic two and $D\subseteq\mathbb B$ a binary additive domain of dimension $d$, $N=2^d$, with locator $L_D$ and $\lambda_0=L_D'\neq0$.
--
--   The **canonical representative** of a function $u:D\to\mathbb B$ is the unique polynomial of degree $<N$ agreeing with $u$ on $D$. For an $\mathbb F_2$-linear function $\varphi:D\to\mathbb F_2$ let $\ell_\varphi$ be the canonical representative of $\varphi$ (with values $0,1\in\mathbb B$); its **label** is the square root $\omega$ of the coefficient of $X$ in $\ell_\varphi$, and the **label space** $\hat D\subseteq\mathbb B$ is the set of all labels. A family $\varphi_1,\dots,\varphi_d$ is a **coordinate basis** if $x\mapsto(\varphi_1(x),\dots,\varphi_d(x))$ is a bijection $D\to\mathbb F_2^d$. Finally
--   $$
--   \Lambda=L_D/\lambda_0,\qquad \eta=\lambda_0^{-1/2},\qquad R=\sqrt{L_D-\lambda_0X}.
--   $$
--
--   These are the standing objects of the Gold construction: linear and quadratic Boolean functions on $D$ are represented by polynomials built from the $\ell_\varphi$, and $R$ is the common high part of the polynomials with many roots.
--
--   **Formalization Note** Linear functions are additive maps `D →+ ZMod 2`. The paper writes $\ell_\omega$ and indexes everything by labels; here labels are handled through their linear functions, and "a basis $\omega_1,\dots,\omega_d$ of the label space" is a coordinate basis $\varphi_1,\dots,\varphi_d$ with $\omega_i=\mathrm{label}(\varphi_i)$. By Lemma 5.5(2) the label map is an $\mathbb F_2$-linear bijection, so this is the same data. That $\ell_\varphi$ is a combination of $X,X^2,\dots,X^{N/2}$ is Lemma 5.5, not part of the definition. Square roots are inverse Frobenius.
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Definition 3.6, p.19; §5.3, p.37; Lemma 5.5, pp.37–38

import Mathlib
import Definitions.Def_GoldProxGap_domainFinset
import Definitions.Def_GoldProxGap_locator

open Polynomial

open scoped Classical

namespace GoldProxGap

/-!
# Canonical representatives, labels of linear functions, and the normalized locator

Dao, Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary
Fields*, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Definition 3.6
(p.19), the standing setup of §5.3 (p.37), and Lemma 5.5 (pp.37–38).

Throughout, `B` is a finite field of characteristic two and `D : AddSubgroup B` is a binary
additive domain (§5.3: "D ⊆ B is binary additive of dimension d, with N = 2^d and monic locator
L_D = Σ_{i=0}^{d} λ_i X^{2^i}, λ_d = 1, λ_0 ≠ 0").

**Formalization Note.**
* `canonicalRep S u` is the canonical representative of Definition 3.6: the unique polynomial of
  degree `< |S|` agreeing with `u` on `S`, computed as Lagrange interpolation on `S`.
* A linear function `φ : D → F₂` is an additive map `D →+ ZMod 2` (every additive map to `F₂` is
  `F₂`-linear). `ellPoly D φ` is the canonical representative of `φ` (values `0, 1 ∈ B`); Lemma 5.5
  asserts that this is the unique polynomial in `span{X, X², …, X^{N/2}}` agreeing with `φ` on `D`,
  so it is the paper's `ℓ_φ`. The uniqueness is a milestone, not part of this definition.
* `label D φ` is the square root (`frobRoot B 2 1`) of the coefficient of `X` in `ellPoly D φ`,
  the paper's label `ω`; `labelSpace D` is the set of all labels, the paper's `D̂`.
* Labels are handled through their linear functions: "a basis `ω₁, …, ω_d` of the label space" is
  encoded as a family `φs : Fin d → (D →+ ZMod 2)` that is a coordinate basis (`IsCoordBasis`:
  `x ↦ (φs i x)_i` is a bijection `D → F₂^d`), with `ω_i = label D (φs i)`. By Lemma 5.5(2) the
  label map is an `F₂`-linear bijection, so this is the same data.
* `lam0 D` is `λ₀ = L_D′` (the coefficient of `X` in `L_D`), `normLocator D = Λ = L_D/λ₀`,
  `eta D = η = λ₀^{−1/2}`, and `Rpoly D = R = √(L_D − λ₀X)` (§5.3, p.37; Lemma 5.12, p.41).
-/

variable {B : Type*} [Field B] [Fintype B] [CharP B 2]

/-- Definition 3.6: the canonical representative of `u` on `S`, the unique polynomial of degree
`< |S|` agreeing with `u` on `S` (Lagrange interpolation). -/
noncomputable def canonicalRep (S : Finset B) (u : B → B) : B[X] :=
  Lagrange.interpolate S id u

/-- The polynomial `ℓ_φ` of a linear function `φ : D → F₂`: its canonical representative. -/
noncomputable def ellPoly (D : AddSubgroup B) (φ : D →+ ZMod 2) : B[X] :=
  canonicalRep (domainFinset D) (fun x => if h : x ∈ D then ((φ ⟨x, h⟩).val : B) else 0)

/-- Lemma 5.5: the label `ω` of `φ`, the square root of the coefficient of `X` in `ℓ_φ`. -/
noncomputable def label (D : AddSubgroup B) (φ : D →+ ZMod 2) : B :=
  frobRoot B 2 1 ((ellPoly D φ).coeff 1)

/-- The label space `D̂ ⊆ B`: the set of labels of all linear functions `D → F₂`. -/
def labelSpace (D : AddSubgroup B) : Set B :=
  Set.range (label D)

/-- `φs` is a basis of the linear functions `D → F₂`: the coordinates `x ↦ (φs i x)_i` are a
bijection `D → F₂^d`. -/
def IsCoordBasis {d : ℕ} (D : AddSubgroup B) (φs : Fin d → (D →+ ZMod 2)) : Prop :=
  Function.Bijective (fun x : D => fun i => φs i x)

/-- `λ₀ = L_D′`, the coefficient of `X` in the locator of `D`. -/
noncomputable def lam0 (D : AddSubgroup B) : B :=
  locLam (domainFinset D)

/-- The normalized locator `Λ = L_D / λ₀`. -/
noncomputable def normLocator (D : AddSubgroup B) : B[X] :=
  C (lam0 D)⁻¹ * locator (domainFinset D)

/-- `η = λ₀^{−1/2}`. -/
noncomputable def eta (D : AddSubgroup B) : B :=
  frobRoot B 2 1 (lam0 D)⁻¹

/-- `R = √(L_D − λ₀ X)` (§5.3, Lemma 5.12). -/
noncomputable def Rpoly (D : AddSubgroup B) : B[X] :=
  polyRoot 2 1 (locator (domainFinset D) - C (lam0 D) * X)

end GoldProxGap


