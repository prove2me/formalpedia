-- Prove2me | Definitions.Def_PathRecording_Supplement_CGPair
-- name    : PathRecording_Supplement_CGPair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:29:57.8946+00:00
-- url     : https://prove2.me/theorems/0ff5b0cc-2149-4e1a-ae11-84cba3f4e438
-- title:
--   Clebsch–Gordan and dual Clebsch–Gordan transforms, compatibility (3.13), and the tableau update coefficients
-- statement:
--   Let $\widehat G$ be the complete catalogue of irreducible representations of $G$. A **Clebsch–Gordan transform** is a family of unitary $G$-respecting isomorphisms
--   $$C_{\lambda,\mu}:V^\lambda_G\otimes V^\mu_G\to\bigoplus_{\lambda^+}M^{\lambda^+}_{\lambda,\mu}\otimes V^{\lambda^+}_G,\qquad C_{\lambda,\mu}\big(\rho_\lambda(g)\otimes\rho_\mu(g)\big)C_{\lambda,\mu}^\dagger=\bigoplus_{\lambda^+}I\otimes\rho_{\lambda^+}(g),$$
--   with multiplicities $m^{\lambda^+}_{\lambda,\mu}=\dim M^{\lambda^+}_{\lambda,\mu}$, nonzero for finitely many $\lambda^+$, and coefficients $\langle\lambda,\mu,\lambda^+,r,X^+|C|\lambda,\mu,X,x\rangle$. A **dual Clebsch–Gordan transform** is a family of unitary isomorphisms $dC_{\lambda^+,\mu}:V^{\lambda^+}_G\otimes(V^\mu_G)^*\to\bigoplus_\lambda M\otimes V^\lambda_G$ with $dC\big(\rho_{\lambda^+}(g)\otimes\rho_\mu(g)^*\big)dC^\dagger=\bigoplus_\lambda I\otimes\rho_\lambda(g)$, where $\rho_\mu(g)^*$ (the action on the dual basis) is the entrywise conjugate; the multiplicity of $\lambda$ is again indexed by $r\in\{1,\dots,m^{\lambda^+}_{\lambda,\mu}\}$. The pair is **compatible** when, for all indices,
--   $$\langle\lambda^+,\mu,X^+,x|\,dC^\dagger\,|\lambda^+,\mu,\lambda,r,X\rangle=\sqrt{\frac{\dim V^\lambda_G}{\dim V^{\lambda^+}_G}}\;\overline{\langle\lambda,\mu,\lambda^+,r,X^+|\,C\,|\lambda,\mu,X,x\rangle}.\qquad(3.13)$$
--   The **tableau update coefficient** of $|\mu,m,x\rangle\otimes|\lambda,X,Y\rangle\mapsto|\mu,m,y\rangle\otimes|\lambda^+,X^+,Y^+\rangle$ through $r$ is
--   $$\langle\lambda^+,\mu,Y^+,y|\,dC^\dagger\,|\lambda^+,\mu,\lambda,r,Y\rangle\cdot\langle\lambda,\mu,\lambda^+,r,X^+|\,C\,|\lambda,\mu,X,x\rangle .$$
--   Finally, for a finite family of labels $\mu_1,\dots,\mu_k$, the block-diagonal representation $\rho=\bigoplus_i\rho_{\mu_i}$ acts on $V=\bigoplus_iV^{\mu_i}_G$ (repeated labels form the multiplicity spaces $M_\mu$ of Eq. (4.3)).
--
--   These objects define the tableau recording oracle, whose update is a Clebsch–Gordan transform followed by an inverse dual Clebsch–Gordan transform.
--
--   **Formalization Note** Both transforms are arbitrary unitary intertwiners (no real or Gelfand–Tsetlin basis is assumed). Finite sets of labels containing every $\lambda^+$ with $m^{\lambda^+}_{\lambda,\mu}\neq0$, and every $\lambda$ with $m^{\lambda^+}_{\lambda,\mu}\ne0$, index the outputs of $C_{\lambda,\mu}$ and $dC_{\lambda^+,\mu}$. That the multiplicity of $\lambda$ in $\lambda^+\otimes\mu^*$ equals $m^{\lambda^+}_{\lambda,\mu}$ is Frobenius reciprocity; (3.13) uses the same index $r$ on both sides.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Definitions 3.19–3.20 and Lemma 3.21 (3.13), pp.38–39; Eq. (4.3), p.48; Eqs. (4.19)–(4.21), pp.50–51

import Mathlib
import Definitions.Def_PathRecording_Supplement_GHat

set_option autoImplicit false

namespace PathRecording.Supplement

/-!
# Clebsch–Gordan and dual Clebsch–Gordan transforms, compatibility (3.13), and the tableau update

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2:
* Definition 3.19, p.38: a Clebsch–Gordan transform is any family of unitary isomorphisms
  `C_{λ,µ} : V^λ_G ⊗ V^µ_G → ⨁_{λ⁺} (M^{λ⁺}_{λ,µ} ⊗ V^{λ⁺}_G)` with
  `C_{λ,µ}(ρ_λ(g) ⊗ ρ_µ(g))C†_{λ,µ} = ⨁_{λ⁺} (I ⊗ ρ_{λ⁺}(g))`; its matrix elements
  `⟨λ, µ, λ⁺, r, X⁺| C |λ, µ, X, x⟩` are the Clebsch–Gordan coefficients.
* Definition 3.20, p.39: a dual Clebsch–Gordan transform is any family of unitary isomorphisms
  `dC_{λ,µ} : V^λ_G ⊗ (V^µ_G)* → ⨁_{λ⁻} (M^{λ⁻}_{λ,µ,*} ⊗ V^{λ⁻}_G)` with
  `dC_{λ,µ}(ρ_λ(g) ⊗ ρ*_µ(g))dC†_{λ,µ} = ⨁_{λ⁻} (I ⊗ ρ_{λ⁻}(g))`.
* Lemma 3.21, Eq. (3.13), p.39 (compatibility):
  `⟨λ⁺, µ, X⁺, x| dC† |λ⁺, µ, λ, r, X⟩ = √(dim V^λ_G / dim V^{λ⁺}_G) · \overline{⟨λ, µ, λ⁺, r, X⁺| C |λ, µ, X, x⟩}`.
* §4.1, Eq. (4.3), p.48: `V ≃ ⨁_µ M_µ ⊗ V^µ_G`, `ρ` block diagonal in the basis `|µ⟩ ⊗ |m⟩ ⊗ |x⟩`.
* §4.2, pp.48–51, Eqs. (4.19)–(4.21): the tableau recording update.

**Formalization Note.**
* All labels are labels of the complete catalogue `Ĝ`. For labels `λ, µ, λ⁺`, `mult λ µ λ⁺` is
  `m^{λ⁺}_{λ,µ} = dim M^{λ⁺}_{λ,µ}`; `supp λ µ` is a finite set of labels containing every `λ⁺` with
  `m^{λ⁺}_{λ,µ} ≠ 0`, and `dsupp λ⁺ µ` a finite set containing every `λ` with `m^{λ⁺}_{λ,µ} ≠ 0`.
* `cg λ µ` is the matrix of `C_{λ,µ}` from the basis `|X, x⟩` (`Fin d_λ × Fin d_µ`) to the basis
  `|λ⁺, r, X⁺⟩` (`Σ λ⁺ ∈ supp λ µ, Fin m^{λ⁺}_{λ,µ} × Fin d_{λ⁺}`).
* `dcg λ⁺ µ` is the matrix of `dC_{λ⁺,µ}` in the dual-space form of Definition 3.20: from the basis
  `|Y⁺, y*⟩` of `V^{λ⁺}_G ⊗ (V^µ_G)*` (where `ρ*_µ(g)` acts by the entrywise conjugate matrix, p.38) to
  `|λ, r, Y⟩` (`Σ λ ∈ dsupp λ⁺ µ, Fin m^{λ⁺}_{λ,µ} × Fin d_λ`). The multiplicity of `λ` in
  `λ⁺ ⊗ µ*` is `m^{λ⁺}_{λ,µ}` (Frobenius reciprocity), and its basis is indexed by the same `r` as in
  `C`, as (3.13) requires.
* Both transforms are arbitrary (any unitary intertwiners): no particular basis (real,
  Gelfand–Tsetlin) is assumed. `Compatible` is (3.13) for all indices.
-/

open Matrix
open scoped Kronecker

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A Clebsch–Gordan transform `C` and a dual Clebsch–Gordan transform `dC` for the catalogue `Ĝ`
(arXiv:2606.30281v2, Definitions 3.19–3.20, pp.38–39). -/
structure CGPair (Ĝ : GHat.{u, v} G) where
  /-- `mult λ µ λ⁺ = m^{λ⁺}_{λ,µ}`, the multiplicity of `λ⁺` in `λ ⊗ µ`. -/
  mult : Ĝ.Charge → Ĝ.Charge → Ĝ.Charge → ℕ
  /-- A finite set of labels containing every `λ⁺` occurring in `λ ⊗ µ`. -/
  supp : Ĝ.Charge → Ĝ.Charge → Finset Ĝ.Charge
  mem_supp : ∀ a c b, mult a c b ≠ 0 → b ∈ supp a c
  /-- A finite set of labels containing every `λ` occurring in `λ⁺ ⊗ µ*`. -/
  dsupp : Ĝ.Charge → Ĝ.Charge → Finset Ĝ.Charge
  mem_dsupp : ∀ a c b, mult a c b ≠ 0 → a ∈ dsupp b c
  /-- The Clebsch–Gordan transform `C_{λ,µ}` as a matrix. -/
  cg : (a c : Ĝ.Charge) →
    Matrix (Σ b : supp a c, Fin (mult a c b) × Fin (Ĝ.dim b)) (Fin (Ĝ.dim a) × Fin (Ĝ.dim c)) ℂ
  cg_isometry : ∀ a c, (cg a c)ᴴ * cg a c = 1
  cg_coisometry : ∀ a c, cg a c * (cg a c)ᴴ = 1
  /-- `C_{λ,µ}(ρ_λ(g) ⊗ ρ_µ(g))C†_{λ,µ} = ⨁_{λ⁺} I ⊗ ρ_{λ⁺}(g)`. -/
  cg_intertwines : ∀ a c (g : G),
    cg a c * ((Ĝ.urep a).mat g ⊗ₖ (Ĝ.urep c).mat g) * (cg a c)ᴴ =
      blockDiagonal' fun b : supp a c =>
        (1 : Matrix (Fin (mult a c b)) (Fin (mult a c b)) ℂ) ⊗ₖ (Ĝ.urep b).mat g
  /-- The dual Clebsch–Gordan transform `dC_{λ⁺,µ}` as a matrix. -/
  dcg : (b c : Ĝ.Charge) →
    Matrix (Σ a : dsupp b c, Fin (mult a c b) × Fin (Ĝ.dim a)) (Fin (Ĝ.dim b) × Fin (Ĝ.dim c)) ℂ
  dcg_isometry : ∀ b c, (dcg b c)ᴴ * dcg b c = 1
  dcg_coisometry : ∀ b c, dcg b c * (dcg b c)ᴴ = 1
  /-- `dC_{λ⁺,µ}(ρ_{λ⁺}(g) ⊗ ρ*_µ(g))dC†_{λ⁺,µ} = ⨁_λ I ⊗ ρ_λ(g)`, with `ρ*_µ(g)` the entrywise
  conjugate. -/
  dcg_intertwines : ∀ b c (g : G),
    dcg b c * ((Ĝ.urep b).mat g ⊗ₖ ((Ĝ.urep c).mat g).map star) * (dcg b c)ᴴ =
      blockDiagonal' fun a : dsupp b c =>
        (1 : Matrix (Fin (mult a c b)) (Fin (mult a c b)) ℂ) ⊗ₖ (Ĝ.urep a).mat g

namespace CGPair

variable {Ĝ : GHat.{u, v} G}

/-- Compatibility (3.13): `⟨λ⁺, µ, X⁺, x| dC† |λ⁺, µ, λ, r, X⟩ =
√(d_λ / d_{λ⁺}) · \overline{⟨λ, µ, λ⁺, r, X⁺| C |λ, µ, X, x⟩}` for all indices
(arXiv:2606.30281v2, Lemma 3.21, Eq. (3.13), p.39; footnote 44, p.48). -/
def Compatible (P : CGPair Ĝ) : Prop :=
  ∀ (a c b : Ĝ.Charge) (h₁ : b ∈ P.supp a c) (h₂ : a ∈ P.dsupp b c) (r : Fin (P.mult a c b))
    (Xp : Fin (Ĝ.dim b)) (x : Fin (Ĝ.dim c)) (X : Fin (Ĝ.dim a)),
    (P.dcg b c)ᴴ (Xp, x) ⟨⟨a, h₂⟩, (r, X)⟩ =
      ((Real.sqrt ((Ĝ.dim a : ℝ) / (Ĝ.dim b : ℝ)) : ℝ) : ℂ) * star (P.cg a c ⟨⟨b, h₁⟩, (r, Xp)⟩ (X, x))

/-- The coefficient of `|µ, m, y⟩ ⊗ |λ⁺, X⁺, Y⁺⟩` in the tableau update of `|µ, m, x⟩ ⊗ |λ, X, Y⟩`
through the multiplicity index `r`:
`⟨λ⁺, µ, Y⁺, y| dC† |λ⁺, µ, λ, r, Y⟩ · ⟨λ, µ, λ⁺, r, X⁺| C |λ, µ, X, x⟩`
(arXiv:2606.30281v2, Eqs. (4.19)–(4.21), pp.50–51). Here `a = λ`, `c = µ`, `b = λ⁺`. -/
def updateCoeff (P : CGPair Ĝ) (a c : Ĝ.Charge) (X Y : Fin (Ĝ.dim a)) (x y : Fin (Ĝ.dim c))
    (b : P.supp a c) (r : Fin (P.mult a c b)) (Xp Yp : Fin (Ĝ.dim b)) : ℂ :=
  (if h : a ∈ P.dsupp b c then (P.dcg b c)ᴴ (Yp, y) ⟨⟨a, h⟩, (r, Y)⟩ else 0) *
    P.cg a c ⟨b, (r, Xp)⟩ (X, x)

end CGPair

/-- The block-diagonal representation `ρ(g) = ⨁_i ρ_{µ_i}(g)` on `V = ⨁_i V^{µ_i}_G`, for a finite
family of catalogue labels `µ_i` (repetitions give the multiplicity spaces `M_µ`):
the basis `|µ, m, x⟩` of (4.3) is `⟨i, x⟩` with `µ_i = µ` (arXiv:2606.30281v2, Eq. (4.3), p.48). -/
def blockRep (Ĝ : GHat.{u, v} G) {κ : Type*} [Fintype κ] [DecidableEq κ] (lab : κ → Ĝ.Charge) :
    C(G, Matrix (Σ i, Fin (Ĝ.dim (lab i))) (Σ i, Fin (Ĝ.dim (lab i))) ℂ) :=
  ⟨fun g => blockDiagonal' fun i => (Ĝ.urep (lab i)).mat g,
    Continuous.matrix_blockDiagonal' (continuous_pi fun i =>
      continuous_subtype_val.comp (Ĝ.urep (lab i)).continuous_toHom)⟩

end PathRecording.Supplement


