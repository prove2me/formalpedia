-- Prove2me | Definitions.Def_CatSymplectic_Hemistrict_Basic
-- name    : CatSymplectic_Hemistrict_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:38:57.308982+00:00
-- url     : https://prove2.me/theorems/e0cd6ca7-c6a6-4110-9c50-0a65dabdc616
-- title:
--   Definitions 2.1, 3.1, 3.3–3.4, 4.1–4.2 — 2-plectic forms and Lie 2-algebras
-- statement:
--   On a real normed vector space \(E\), a differential \(k\)-form is a family of continuous alternating \(k\)-linear forms. A 2-plectic three-form \(\omega\) is smooth, closed, and nondegenerate in its first slot. A smooth one-form \(F\) is Hamiltonian if a smooth vector field \(v_F\) satisfies
--
--   $$
--   dF=-\iota_{v_F}\omega.
--   $$
--
--   The definitions supply interior products, Lie derivatives, the Hamiltonian vector field, the hemi-bracket \(\{F,G\}_h=\mathcal L_{v_F}G\), the semi-bracket \(\{F,G\}_s=\iota_{v_G}\iota_{v_F}\omega\), and the alternator \(S_{F,G}=-(\iota_{v_F}G+\iota_{v_G}F)\). A two-term Lie 2-algebra carries a differential, three bracket components, an alternator, a Jacobiator, their chain-map and homotopy equations, and four coherence equations. Hemistrict means that the Jacobiator is zero. This is the common interface for Theorem 4.3.
--
--   **Formalization Note** The paper's manifold is represented by a normed vector space; later theorems assume finite dimension. The Lean name for \(\omega\) is Ω. Interior product inserts in the first slot, and the exterior derivative uses Mathlib's normalization. The first coherence diagram follows the printed edges despite their right-Leibniz labels; the second uses the source/target-consistent equation. The printed “antisymmetric” adjective for the Jacobiator is not a separate field, and the goal has \(J=0\).
-- source:
--   Baez, Hoffnung, Rogers, Categorified Symplectic Geometry and the Classical String, arXiv:0808.0246v1, pp. 6, 11, 14–17, Definitions 2.1, 3.1, 3.3–3.4, 4.1–4.2

import Mathlib
import Definitions.Def_ContWeatherall_defs

open ContinuousAlternatingMap

namespace CatSymplectic.Hemistrict

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `C∞` smoothness degree. -/
abbrev smooth : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- Differential forms on a normed real vector space. -/
abbrev Form (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) :=
  E → E [⋀^Fin k]→L[ℝ] ℝ

/-- Interior product, inserting the vector in the first slot. -/
noncomputable def interior {k : ℕ} (v : E → E) (α : Form E (k + 1)) : Form E k :=
  fun x => (α x).curryLeft (v x)

/-- The pairing of a vector field and a one-form. -/
def pair (v : E → E) (F : Form E 1) : E → ℝ := fun x => F x ![v x]

/-- An `n`-plectic form is smooth, closed, and nondegenerate in its first slot. -/
def IsNPlectic (n : ℕ) (Ω : Form E (n + 1)) : Prop :=
  ContDiff ℝ smooth Ω ∧ extDeriv Ω = 0 ∧
    ∀ x v : E, (Ω x).curryLeft v = 0 → v = 0

/-- Lie derivative of a smooth real function along a vector field. -/
noncomputable def lieDerivFn (v : E → E) (f : E → ℝ) : E → ℝ :=
  fun x => fderiv ℝ f x (v x)

/-- Lie derivative of a one-form, defined by ordinary derivatives. -/
noncomputable def lieDeriv1 (v : E → E) (α : Form E 1) : Form E 1 :=
  fun x => fderiv ℝ α x (v x) + (α x).compContinuousLinearMap (fderiv ℝ v x)

/-- Evaluation of the Lie derivative of a higher form. -/
noncomputable def lieDerivEval {k : ℕ} (v : E → E) (α : Form E k)
    (x : E) (w : Fin k → E) : ℝ :=
  fderiv ℝ α x (v x) w +
    ∑ i : Fin k, α x (Function.update w i (fderiv ℝ v x (w i)))

/-- Equation (5), with a smooth Hamiltonian vector field. -/
def IsHamVF (Ω : Form E 3) (F : Form E 1) (v : E → E) : Prop :=
  ContDiff ℝ smooth v ∧
    ∀ x, extDeriv F x = -((Ω x).curryLeft (v x))

/-- A smooth one-form with a Hamiltonian vector field. -/
def IsHamiltonian (Ω : Form E 3) (F : Form E 1) : Prop :=
  ContDiff ℝ smooth F ∧ ∃ v, IsHamVF Ω F v

/-- The unique Hamiltonian vector field on Hamiltonian inputs; zero elsewhere. -/
noncomputable def hamVF (Ω : Form E 3) (F : Form E 1) : E → E := by
  classical
  exact if h : ∃ v, IsHamVF Ω F v then h.choose else 0

/-- The vector space of Hamiltonian one-forms. -/
noncomputable def hamSubmodule (Ω : Form E 3) : Submodule ℝ (Form E 1) where
  carrier := {F | IsHamiltonian Ω F}
  zero_mem' := by
    constructor
    · exact contDiff_const
    · refine ⟨0, contDiff_const, ?_⟩
      intro x
      have hzero : extDeriv (0 : Form E 1) x = 0 := by
        simpa using (extDeriv_smul (0 : ℝ) (0 : Form E 1) (x := x))
      simpa using hzero
  add_mem' := by
    intro F G hF hG
    rcases hF with ⟨hFs, v, hvs, hv⟩
    rcases hG with ⟨hGs, w, hws, hw⟩
    constructor
    · exact hFs.add hGs
    · refine ⟨v + w, hvs.add hws, ?_⟩
      intro x
      rw [extDeriv_add (hFs.differentiable (by simp) x)
        (hGs.differentiable (by simp) x), hv x, hw x]
      simp only [Pi.add_apply, ContinuousLinearMap.map_add]
      abel
  smul_mem' := by
    intro c F hF
    rcases hF with ⟨hFs, v, hvs, hv⟩
    constructor
    · exact hFs.const_smul c
    · refine ⟨c • v, hvs.const_smul c, ?_⟩
      intro x
      rw [extDeriv_smul, hv x]
      simp

/-- Smooth real functions, the degree-one chains. -/
def smoothFns (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (E → ℝ) where
  carrier := {f | ContDiff ℝ smooth f}
  zero_mem' := by
    change ContDiff ℝ smooth (0 : E → ℝ)
    exact contDiff_const
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ smooth f at hf
    change ContDiff ℝ smooth g at hg
    change ContDiff ℝ smooth (f + g)
    exact hf.add hg
  smul_mem' := by
    intro c f hf
    change ContDiff ℝ smooth f at hf
    change ContDiff ℝ smooth (c • f)
    exact hf.const_smul c

/-- Definition 3.3: the hemi-bracket of Hamiltonian one-forms. -/
noncomputable def hemi (Ω : Form E 3) (F G : Form E 1) : Form E 1 :=
  lieDeriv1 (hamVF Ω F) G

/-- The degree-one left hemi-bracket. -/
noncomputable def hemiFn (Ω : Form E 3) (F : Form E 1) (f : E → ℝ) : E → ℝ :=
  lieDerivFn (hamVF Ω F) f

/-- Definition 3.4: the semi-bracket. -/
noncomputable def semi (Ω : Form E 3) (F G : Form E 1) : Form E 1 :=
  fun x => ((Ω x).curryLeft (hamVF Ω F x)).curryLeft (hamVF Ω G x)

/-- The alternator of Theorem 4.3. -/
noncomputable def alt (Ω : Form E 3) (F G : Form E 1) : E → ℝ :=
  fun x => -(G x ![hamVF Ω F x] + F x ![hamVF Ω G x])

/-- Definition 4.1, expanded into the nonzero components of a two-term complex.
The four coherence diagrams are equations between the summed one-chains on their paths. -/
structure Lie2Algebra (L₀ L₁ : Type*) [AddCommGroup L₀] [Module ℝ L₀]
    [AddCommGroup L₁] [Module ℝ L₁] where
  d : L₁ →ₗ[ℝ] L₀
  br : L₀ →ₗ[ℝ] L₀ →ₗ[ℝ] L₀
  brL : L₀ →ₗ[ℝ] L₁ →ₗ[ℝ] L₁
  brR : L₁ →ₗ[ℝ] L₀ →ₗ[ℝ] L₁
  S : L₀ →ₗ[ℝ] L₀ →ₗ[ℝ] L₁
  J : L₀ →ₗ[ℝ] L₀ →ₗ[ℝ] L₀ →ₗ[ℝ] L₁
  chain_L : ∀ x f, d (brL x f) = br x (d f)
  chain_R : ∀ f x, d (brR f x) = br (d f) x
  chain_2 : ∀ f g, brL (d f) g = brR f (d g)
  S_0 : ∀ x y, br x y + d (S x y) = -(br y x)
  S_L : ∀ x f, brL x f + S x (d f) = -(brR f x)
  S_R : ∀ f x, brR f x + S (d f) x = -(brL x f)
  J_0 : ∀ x y z, br x (br y z) + d (J x y z) = br (br x y) z + br y (br x z)
  J_1 : ∀ x y f, brL x (brL y f) + J x y (d f) =
    brL (br x y) f + brL y (brL x f)
  J_2 : ∀ x f z, brL x (brR f z) + J x (d f) z =
    brR (brL x f) z + brR f (br x z)
  J_3 : ∀ f y z, brR f (br y z) + J (d f) y z =
    brR (brR f y) z + brL y (brR f z)
  diagram_1 : ∀ w x y z,
    brR (J w x y) z + (J (br w y) x z + J w (br x y) z) +
      brR (J w y z) x + brL w (J x y z) =
    J (br w x) y z + brR (J w x z) y +
      (J w (br x z) y + J (br w z) x y + J w x (br y z))
  diagram_2 : ∀ x y z, brR (S x y) z = -(J x y z) - J y x z
  diagram_3 : ∀ x y z,
    brL x (S y z) - J x z y = J x y z + S (br x y) z + S y (br x z)
  diagram_4 : ∀ x y z, S x (br y z) - S (br y z) x = 0

/-- Definition 4.2: the Jacobiator is the identity homotopy. -/
def Lie2Algebra.IsHemistrict {L₀ L₁ : Type*} [AddCommGroup L₀] [Module ℝ L₀]
    [AddCommGroup L₁] [Module ℝ L₁] (L : Lie2Algebra L₀ L₁) : Prop :=
  L.J = 0

end CatSymplectic.Hemistrict


