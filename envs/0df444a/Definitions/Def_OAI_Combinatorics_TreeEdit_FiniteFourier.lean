-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteFourier
-- name    : OAI_Combinatorics_TreeEdit_FiniteFourier
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:25:45.551976+00:00
-- url     : https://prove2.me/theorems/b8d8f032-6ba4-4fe8-bbc4-e912816a8344
-- title:
--   Fourier coefficients, displacement multipliers and spectral weights on finite abelian groups
-- statement:
--   Let $A$ and $B$ be finite abelian groups, written additively, and let $\widehat{A}$ be the group of additive characters $\chi:A\to\mathbb{C}$, i.e. maps with $\chi(x+y)=\chi(x)\chi(y)$ and $\chi(0)=1$; the trivial character is denoted $\mathbf{1}$. Weights are real functions $H:\widehat{A}\to\mathbb{R}$.
--
--   1. **Fourier coefficients.** The characters form a basis of the space of functions $A\to\mathbb{C}$; for $f:A\to\mathbb{C}$ the coefficients $\widehat{f}(\chi)$ are its coordinates in this basis, $f=\sum_{\chi\in\widehat{A}}\widehat{f}(\chi)\,\chi$.
--
--   2. **Multiplier.** For $\chi\in\widehat{A}$ and $z\in A$, $\mu_\chi(z)=|1-\chi(z)|^2$; the trivial character has $\mu_{\mathbf{1}}(z)=0$.
--
--   3. **Average.** For $f:A\to\mathbb{R}$, $\operatorname{avg}(f)=|A|^{-1}\sum_{x\in A}f(x)$.
--
--   4. **Spectral representation.** A function $V:A\to\mathbb{R}$ *has a spectrum* if there are weights $H$ with $H(\chi)\ge0$ for all $\chi$ and $H(\mathbf{1})=0$ such that
--
--      $$V(z)=\sum_{\chi\in\widehat{A}}|1-\chi(z)|^2\,H(\chi)\qquad\text{for all } z\in A.$$
--
--   5. **Energy.** For weights $H$ and $z\in A$, $E_H(z)=\sum_{\chi\in\widehat{A}}|1-\chi(z)|^2H(\chi)$.
--
--   6. **Pushforward of weights.** For a homomorphism $f:B\to A$ and $\eta\in\widehat{B}$,
--
--      $$(f_*H)(\eta)=\sum_{\chi\in\widehat{A}:\ \chi\circ f=\eta}H(\chi).$$
--
--   7. **Active mass.** For $v\in A$, $\operatorname{act}_\chi(v)$ is $0$ if $\chi(v)=1$ and $1$ otherwise, and the active mass $\sum_{\chi}\operatorname{act}_\chi(v)H(\chi)$ is the total weight of the characters that are nontrivial at $v$.
--
--   Averaged displacements $z\mapsto\operatorname{avg}_x\|F(x+z)-F(x)\|_1$ of maps $F$ from $A$ into the real sequence space $\ell_1$ have spectral representations, and the energy of the representing weights recovers the displacement. Pushforwards describe displacements along subgroups such as the subtree of one child, and active masses record the weight that a shift by $v$ can detect, bounded by averages of energies. This is the finite-group Fourier toolkit for the obstruction showing that every embedding of the circle-tree words into $\ell_1$ has large distortion.
--
--   **Formalization Note** Characters are `AddChar A ℂ`, a group written additively in Lean, so the trivial character is `0`. The Lean names are `coefficient` (namely `(AddChar.complexBasis A).repr f χ`), `multiplier` (with the simp lemma `multiplier_zero`), `average`, `HasSpectrum`, `energy`, `pushSpectrum`, `active` and `activeMass`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/FiniteFourier.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison
import Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
import Definitions.Def_OAI_Combinatorics_TreeEdit_TreeArithmetic
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleTree
import Definitions.Def_OAI_Combinatorics_TreeEdit_CircleSeparation
import Definitions.Def_OAI_Combinatorics_TreeEdit_RandomCircle

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace FiniteFourier

open scoped ComplexConjugate
open RCLike

variable {A : Type*} [Fintype A] [AddCommGroup A]

noncomputable def coefficient (f : A → ℂ) (χ : AddChar A ℂ) : ℂ :=
  (AddChar.complexBasis A).repr f χ

noncomputable def multiplier (χ : AddChar A ℂ) (z : A) : ℝ := ‖1 - χ z‖ ^ 2

omit [Fintype A] in
@[simp] lemma multiplier_zero (z : A) : multiplier (0 : AddChar A ℂ) z = 0 := by
  simp [multiplier]

noncomputable def average (f : A → ℝ) : ℝ := (Fintype.card A : ℝ)⁻¹ * ∑ x, f x

def HasSpectrum (V : A → ℝ) : Prop :=
  ∃ H : AddChar A ℂ → ℝ, (∀ χ, 0 ≤ H χ) ∧ H 0 = 0 ∧
    ∀ z, V z = ∑ χ, multiplier χ z * H χ

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

noncomputable def energy (H : AddChar A ℂ → ℝ) (z : A) : ℝ :=
  ∑ χ, multiplier χ z * H χ

noncomputable def pushSpectrum (H : AddChar A ℂ → ℝ) (f : B →+ A) (η : AddChar B ℂ) : ℝ :=
  ∑ χ, if χ.compAddMonoidHom f = η then H χ else 0

end FiniteFourier

namespace FiniteFourier

variable {A B : Type*} [Fintype A] [Fintype B] [AddCommGroup A] [AddCommGroup B]

noncomputable def active (χ : AddChar A ℂ) (v : A) : ℝ := if χ v = 1 then 0 else 1

noncomputable def activeMass (H : AddChar A ℂ → ℝ) (v : A) : ℝ :=
  ∑ χ, active χ v * H χ

end FiniteFourier

namespace FiniteFourier

variable {A : Type*} [Fintype A] [AddCommGroup A]

end FiniteFourier

end TreeEdit

end OAI


