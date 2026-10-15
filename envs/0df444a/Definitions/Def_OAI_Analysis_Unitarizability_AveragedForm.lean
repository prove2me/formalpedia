-- Prove2me | Definitions.Def_OAI_Analysis_Unitarizability_AveragedForm
-- name    : OAI_Analysis_Unitarizability_AveragedForm
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T07:41:59.65039+00:00
-- url     : https://prove2.me/theorems/6ddacfa2-d9e8-4af8-8a84-aadd9032b9b8
-- title:
--   Matrix coefficients of a bounded representation and the averaged sesquilinear form
-- statement:
--   Let $G$ be a group with the discrete topology, let $H$ be a complex inner product space (completeness is not assumed) whose inner product $\langle\cdot,\cdot\rangle$ is conjugate-linear in the first argument, and let $\pi:G\to B(H)$ be a group homomorphism into the bounded linear operators on $H$. Let $M\ge0$ be a real number with $\|\pi(g)\|\le M$ for all $g\in G$, and write $\ell^\infty(G)$ for the bounded functions $G\to\mathbb{C}$.
--
--   1. **Matrix coefficients.** For $x,y\in H$, the function $c_{x,y}:G\to\mathbb{C}$,
--   $$c_{x,y}(g)=\bigl\langle\pi(g^{-1})x,\ \pi(g^{-1})y\bigr\rangle ,$$
--   regarded as an element of $\ell^\infty(G)$: by the Cauchy–Schwarz inequality $|c_{x,y}(g)|\le M^2\|x\|\|y\|$ for every $g$. The file records that $c_{x,y}$ is additive in $x$ and in $y$, and that $c_{\alpha x,y}=\overline{\alpha}\,c_{x,y}$ and $c_{x,\alpha y}=\alpha\,c_{x,y}$ for $\alpha\in\mathbb{C}$.
--   2. **Averaged form.** For a $\mathbb{C}$-linear functional $m$ on $\ell^\infty(G)$, the sesquilinear form
--   $$B_m(x,y)=m\bigl(c_{x,y}\bigr)\qquad(x,y\in H),$$
--   which is conjugate-linear in $x$ and linear in $y$.
--
--   When $m$ is invariant under left translations, $B_m$ is $\pi$-invariant, since replacing $x,y$ by $\pi(h)x,\pi(h)y$ left-translates $c_{x,y}$ by $h$. If moreover $m(\mathbf 1)=1$, $m$ is positive and $H$ is complete, then $B_m$ is a bounded inner product equivalent to the original one, and the positive square root of the operator representing $B_m$ conjugates $\pi$ to a unitary representation. This is the averaging construction behind the Day–Dixmier theorem for amenable groups.
--
--   **Formalization Note** `DayDixmier.coefficient π hM hπ x y` is a bounded continuous function `G →ᵇ ℂ`; the proofs `hM : 0 ≤ M` and `hπ` enter only through the bound $M^2\|x\|\|y\|$. The identities listed in item 1 are `coefficient_apply`, `coefficient_add_left`, `coefficient_add_right`, `coefficient_smul_left` and `coefficient_smul_right`. `averagedForm π hM hπ m` is an algebraic sesquilinear map `H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ`; its continuity is proved separately from a bound on $m$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Unitarizability/AveragedForm.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/AveragedForm.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DixmierAllDiscrete mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseMask__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_EndpointAssignment__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SparseSplitting__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Regular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_VectorMean__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSigns__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FiniteSynthesis__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SignMatrix__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Parameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_FrameParameters__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_ComplexFrames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Frames__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Masked__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MaskAlgebra__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_LocalBounds__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_UniverseTransport__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_MeanBounds

namespace OAI

noncomputable section
namespace Dixmier
namespace DayDixmier
open scoped BoundedContinuousFunction ComplexConjugate
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

section Form
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (π : G →* (H →L[ℂ] H)) {M : ℝ} (hM : 0 ≤ M) (hπ : ∀ g, ‖π g‖ ≤ M)

def coefficient (x y : H) : G →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroupDiscrete
    (fun g => inner ℂ (π g⁻¹ x) (π g⁻¹ y)) (M^2 * ‖x‖ * ‖y‖) (fun g => by
      calc
        ‖inner ℂ (π g⁻¹ x) (π g⁻¹ y)‖ ≤ ‖π g⁻¹ x‖ * ‖π g⁻¹ y‖ := norm_inner_le_norm _ _
        _ ≤ (M * ‖x‖) * (M * ‖y‖) := mul_le_mul
          ((π g⁻¹).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right (hπ _) (norm_nonneg _)))
          ((π g⁻¹).le_opNorm y |>.trans (mul_le_mul_of_nonneg_right (hπ _) (norm_nonneg _)))
          (norm_nonneg _) (mul_nonneg hM (norm_nonneg _))
        _ = M^2 * ‖x‖ * ‖y‖ := by ring)

@[simp] lemma coefficient_apply (x y : H) (g : G) :
    coefficient π hM hπ x y g = inner ℂ (π g⁻¹ x) (π g⁻¹ y) := rfl

lemma coefficient_add_left (x y z : H) :
    coefficient π hM hπ (x + y) z = coefficient π hM hπ x z + coefficient π hM hπ y z := by
  ext g
  simp

lemma coefficient_add_right (x y z : H) :
    coefficient π hM hπ x (y + z) = coefficient π hM hπ x y + coefficient π hM hπ x z := by
  ext g
  simp

lemma coefficient_smul_left (c : ℂ) (x y : H) :
    coefficient π hM hπ (c • x) y = (starRingEnd ℂ c) • coefficient π hM hπ x y := by
  ext g
  simp [mul_comm]

lemma coefficient_smul_right (c : ℂ) (x y : H) :
    coefficient π hM hπ x (c • y) = c • coefficient π hM hπ x y := by
  ext g
  simp

def averagedForm (m : (G →ᵇ ℂ) →ₗ[ℂ] ℂ) : H →ₗ⋆[ℂ] H →ₗ[ℂ] ℂ where
  toFun x :=
    { toFun y := m (coefficient π hM hπ x y)
      map_add' y z := by rw [coefficient_add_right, map_add]
      map_smul' c y := by rw [coefficient_smul_right, map_smul]; rfl }
  map_add' x y := by
    ext z
    change m (coefficient π hM hπ (x + y) z) = _
    rw [coefficient_add_left, map_add]
    rfl
  map_smul' c x := by
    ext y
    change m (coefficient π hM hπ (c • x) y) = _
    rw [coefficient_smul_left, map_smul]
    rfl

end Form

end DayDixmier
end Dixmier
end

end OAI


