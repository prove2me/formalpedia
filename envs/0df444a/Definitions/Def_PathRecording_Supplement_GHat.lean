-- Prove2me | Definitions.Def_PathRecording_Supplement_GHat
-- name    : PathRecording_Supplement_GHat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T04:28:58.858687+00:00
-- url     : https://prove2.me/theorems/c9c36f11-2241-4bcf-940f-c21b18eb6291
-- title:
--   The complete catalogue $\widehat G$ of irreps and the Fourier basis $F^{-1}|\lambda,X,Y\rangle$
-- statement:
--   Let $G$ be a topological group. The **dual object** $\widehat G$ is a list of labels $\lambda$ together with, for each label, a continuous irreducible unitary representation $\rho_\lambda:G\to U(d_\lambda)$ written in a fixed orthonormal basis $\{|X\rangle\}$ of $V_\lambda=\mathbb C^{d_\lambda}$, such that distinct labels carry inequivalent representations and every continuous irreducible unitary representation of $G$ is equivalent to some $\rho_\lambda$. Thus the labels are exactly the isomorphism classes of irreducible representations.
--
--   The **tableau space** $\mathrm{Tab}(\widehat G)=\bigoplus_{\lambda\in\widehat G}V_\lambda\otimes V_\lambda^*$ has the basis $|\lambda,X,Y\rangle=|X,Y^*\rangle$; its vectors are square-summable families of coefficients. For a finite Borel measure on a compact group $G$, the **inverse Fourier transform** sends basis vectors to normalized matrix coefficients,
--   $$F^{-1}|\lambda,X,Y\rangle=\sqrt{d_\lambda}\int_G\langle Y|\rho_\lambda(g)|X\rangle\,|g\rangle\,dg\in L^2(G),$$
--   and a square-summable family $w$ to $F^{-1}w=\sum_{\lambda,X,Y}w_{\lambda XY}\,F^{-1}|\lambda,X,Y\rangle$.
--
--   By the Peter–Weyl theorem $F^{-1}$ is unitary for the normalized Haar measure; it identifies the uncompressed recording register $L^2(G)$ with the tableau recording register.
--
--   **Formalization Note** The catalogue extends the published `SymTensorNet.IrrepCatalogue` by continuity and completeness; the label type may be infinite. Peter–Weyl is not formalized: only $F^{-1}$ is defined, as a series, which converges on square-summable inputs because the matrix coefficients are orthonormal (Lemma 3.8, `PathRecording.lemma_3_8`); Lean's series value on a non-summable family (zero) never arises there.
-- source:
--   Foxman, Lombardi, Ma, Nehoran, Wright, Quantum Lazy Sampling and Path Recording for Any Group, arXiv:2606.30281v2, Theorem 3.6 and Definition 3.7, p.32; footnote 10, p.9

import Mathlib
import Definitions.Def_PathRecording_UnitaryRep
import Definitions.Def_SymTensorNet_IrrepCatalogue

set_option autoImplicit false

namespace PathRecording.Supplement

/-!
# `Ĝ`, the complete catalogue of irreducible representations, and the Fourier basis `|λ, X, Y⟩`

Foxman, Lombardi, Ma, Nehoran, Wright, *Quantum Lazy Sampling and Path Recording for Any Group*,
arXiv:2606.30281v2, Theorem 3.6 and Definition 3.7, p.32: "`Ĝ` refers to the set of isomorphism
classes of irreducible representations of `G`"; "For every irreducible representation `λ`, choose an
orthonormal basis `{|X⟩ : X ∈ I_λ}` of `V_λ`, with dual basis `{|Y*⟩}` of `V_λ*` … This leads to a
basis `|λ, X, Y⟩ = |X, Y*⟩` of `⨁_{λ∈Ĝ} V_λ ⊗ V_λ*` … `F⁻¹|λ, X, Y⟩ = √d_λ ∫_G ⟨Y|ρ_λ(g)|X⟩ |g⟩ dg`."

**Formalization Note.**
* `Ĝ` is the published `SymTensorNet.IrrepCatalogue` (labels `λ`, dimensions `d_λ`, irreducible
  unitary matrix representations `ρ_λ` in a fixed orthonormal basis, distinct labels inequivalent)
  together with two conditions: every `ρ_λ` is continuous, and the catalogue is **complete**: every
  continuous irreducible unitary matrix representation of `G` is equivalent to some `ρ_λ`. So the
  labels are exactly the isomorphism classes of finite-dimensional irreducible (continuous unitary)
  representations. The label type may be infinite (as for `U(1)` or `SU(2)`).
* `Tab(Ĝ) = ⨁_λ V_λ ⊗ V_λ*` has the basis `|λ, X, Y⟩` indexed by `TabIdx Ĝ = Σ λ, Fin d_λ × Fin d_λ`;
  its vectors are the square-summable coefficient functions `TabIdx Ĝ → ℂ` (`Memℓp · 2`).
* Peter–Weyl's `F` is not formalized; its inverse is used instead. `coeffFn μ Ĝ ⟨λ, X, Y⟩` is
  `F⁻¹|λ, X, Y⟩ = √d_λ · ⟨Y|ρ_λ(·)|X⟩ ∈ L²(G)`, and `fourierInv μ Ĝ w = Σ'_{b} w_b · F⁻¹|b⟩`. For
  square-summable `w` this series converges, since the `F⁻¹|b⟩` are orthonormal for the normalized
  Haar measure (Lemma 3.8, published as `PathRecording.lemma_3_8`); the Lean `tsum` is `0` on a
  non-summable family, a case that does not occur on `ℓ²` inputs.
-/

open MeasureTheory

universe u v

/-- The complete catalogue `Ĝ` of irreducible representations of a topological group `G`: a
catalogue of pairwise inequivalent irreducible unitary matrix representations, each continuous,
such that every continuous irreducible unitary representation of `G` is equivalent to one of them
(arXiv:2606.30281v2, Theorem 3.6 and Definition 3.7, p.32; footnote 10, p.9). -/
structure GHat (G : Type u) [Group G] [TopologicalSpace G] extends
    SymTensorNet.IrrepCatalogue.{u, v} G where
  /-- Every `ρ_λ` is continuous. -/
  continuous_rep : ∀ a, Continuous (rep a)
  /-- Completeness: every continuous irreducible unitary representation occurs in `Ĝ`. -/
  complete : ∀ (k : ℕ) (σ : UnitaryRep G k), SymTensorNet.IsIrrep σ.toHom →
    ∃ a, SymTensorNet.RepEquiv σ.toHom (rep a)

namespace GHat

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- `ρ_λ` as a continuous unitary representation. -/
def urep (Ĝ : GHat.{u, v} G) (a : Ĝ.Charge) : UnitaryRep G (Ĝ.dim a) :=
  ⟨Ĝ.rep a, Ĝ.continuous_rep a⟩

/-- The basis index `|λ, X, Y⟩` of `Tab(Ĝ) = ⨁_{λ∈Ĝ} V_λ ⊗ V_λ*` (Definition 3.7, p.32). -/
abbrev TabIdx (Ĝ : GHat.{u, v} G) := Σ a : Ĝ.Charge, Fin (Ĝ.dim a) × Fin (Ĝ.dim a)

end GHat

variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G] [MeasurableSpace G]
  [BorelSpace G] (μ : Measure G) [IsFiniteMeasure μ]

/-- The Fourier basis function `F⁻¹|λ, X, Y⟩ = √d_λ · ⟨Y|ρ_λ(·)|X⟩ ∈ L²(G)`
(arXiv:2606.30281v2, Definition 3.7, p.32). -/
noncomputable def coeffFn (Ĝ : GHat.{u, v} G) (b : Ĝ.TabIdx) : Lp ℂ 2 μ :=
  ContinuousMap.toLp 2 μ ℂ
    ⟨fun g => ((Real.sqrt (Ĝ.dim b.1 : ℝ) : ℝ) : ℂ) * (Ĝ.urep b.1).mat g b.2.2 b.2.1,
      continuous_const.mul ((Ĝ.urep b.1).continuous_mat_apply b.2.2 b.2.1)⟩

/-- The inverse Fourier transform `F⁻¹ : Tab(Ĝ) → L²(G)`, `F⁻¹ w = Σ'_{λ,X,Y} w_{λXY} F⁻¹|λ,X,Y⟩`
(arXiv:2606.30281v2, Definition 3.7, p.32), applied to coefficient functions `w : TabIdx Ĝ → ℂ`. -/
noncomputable def fourierInv (Ĝ : GHat.{u, v} G) (w : Ĝ.TabIdx → ℂ) : Lp ℂ 2 μ :=
  ∑' b, w b • coeffFn μ Ĝ b

end PathRecording.Supplement


