-- Prove2me | Definitions.Def_CondGeoVerif_IsRotInvStiefelLaw
-- name    : CondGeoVerif_IsRotInvStiefelLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:20:22.902194+00:00
-- url     : https://prove2.me/theorems/02269fb8-8fd5-46cd-9757-0f00fa99b2c6
-- title:
--   Uniform law on the Stiefel manifold, likelihood cross-moment $K(V,W)$, $\chi^2$, random-frame mixture
-- statement:
--   A probability measure $\nu$ on $\mathbb R^{D\times k}$ is the **uniform law on the Stiefel manifold** if it is carried by $\{V:V^\top V=I_k\}$ and invariant under every rotation $V\mapsto OV$, $O\in O(D)$. For laws $P_V,P_W$ and a reference law $Q$ the **likelihood cross-moment** is
--   $$K(V,W)=\mathbb E_Q\Big[\frac{dP_V}{dQ}\frac{dP_W}{dQ}\Big],$$
--   the **$\chi^2$-divergence** is $\chi^2(\mu\|\nu)=\mathbb E_\nu[(d\mu/d\nu)^2]-1$, and the **random-frame mixture** is $P^n=\mathbb E_VP_V^{\otimes n}$, with the same random frame shared by all $n$ observations.
--
--   These are the quantities of the indistinguishability argument (§B.3–B.4).
--
--   **Formalization Note** Real $D\times k$ matrices carry the product (Borel) σ-algebra. Rotation invariance characterizes the uniform (Haar) law, since $O(D)$ acts transitively on the Stiefel manifold and the invariant probability measure is unique. Densities are Radon–Nikodym derivatives. The mixture is the bind of the frame law with $V\mapsto P_V^{\otimes n}$.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §B.3–B.4, pp.26–27 (PDF pp.29–30)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

/-- The measurable structure on real `D × k` matrices: the product σ-algebra of the entries
(the Borel σ-algebra of `ℝ^{D×k}`). -/
instance instMeasurableSpaceMatrix (D k : ℕ) : MeasurableSpace (Matrix (Fin D) (Fin k) ℝ) :=
  inferInstanceAs (MeasurableSpace (Fin D → Fin k → ℝ))

/-- `ν` is the **uniform law on the Stiefel manifold** of orthonormal `k`-frames in `ℝᴰ` (Chen,
*The Conditional Geometry of Statistical Verification*, manuscript, October 2026, sha256
07a66d18…, §B.4, p.26 = PDF p.29: "independent uniform elements of the Stiefel manifold"): the
measure on `ℝ^{D×k}` is carried by `{V | VᵀV = I_k}` and is invariant under every rotation
`V ↦ OV`, `O ∈ O(D)`.

**Formalization Note** The predicate is applied to probability measures (`ProbabilityMeasure`).
Rotation invariance characterizes the uniform (Haar) law: `O(D)` acts transitively on the Stiefel
manifold, and the invariant probability measure on it is unique. -/
def IsRotInvStiefelLaw {D k : ℕ} (ν : Measure (Matrix (Fin D) (Fin k) ℝ)) : Prop :=
  ν (stiefel D k)ᶜ = 0 ∧
    ∀ O ∈ Matrix.orthogonalGroup (Fin D) ℝ, ν.map (fun V => O * V) = ν

/-- The **one-observation likelihood cross-moment** `K(V, W) = E_Q[(dP_V/dQ)(dP_W/dQ)]` of (B.3)
(§B.3, p.26), for two laws `P_V, P_W` and a reference law `Q`, with Radon–Nikodym derivatives. -/
noncomputable def likKernel {α : Type*} [MeasurableSpace α] (Q PV PW : Measure α) : ℝ :=
  ∫ q, (PV.rnDeriv Q q).toReal * (PW.rnDeriv Q q).toReal ∂Q

/-- The **χ²-divergence** `χ²(μ ‖ ν) = E_ν[(dμ/dν)²] − 1` (§B.4, p.27), for `μ ≪ ν`. -/
noncomputable def chiSq {α : Type*} [MeasurableSpace α] (μ ν : Measure α) : ℝ :=
  ∫ x, ((μ.rnDeriv ν x).toReal) ^ 2 ∂ν - 1

/-- The **random-frame mixture** `Pⁿ = E_V P_V^{⊗n}` (§B.4, p.27: "the same random frame is shared
across all observations"), for a frame law `ν` and a family of laws `V ↦ P_V`. -/
noncomputable def frameMixture {D k : ℕ} {α : Type*} [MeasurableSpace α]
    (ν : Measure (Matrix (Fin D) (Fin k) ℝ)) (PV : Matrix (Fin D) (Fin k) ℝ → Measure α) (n : ℕ) :
    Measure (Fin n → α) :=
  ν.bind (fun V => Measure.pi (fun _ : Fin n => PV V))

end CondGeoVerif


