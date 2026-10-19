-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Quotient
-- name    : OAI_Geometry_Arnold_Quotient
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T09:06:31.383985+00:00
-- url     : https://prove2.me/theorems/bff06056-3041-48be-add6-3c8f13574db5
-- title:
--   Descending phase-equivariant maps of the unit quadric to the projective quadric $Q_3$
-- statement:
--   On $\mathbb{C}^5$ write $q(z)=\sum_jz_j^2$, $|z|^2=\sum_j|z_j|^2$, $B(z,w)=\sum_jz_jw_j$ and $\omega(u,v)=2\operatorname{Im}\sum_j\bar u_jv_j$. The unit quadric is $S=\{z:|z|^2=1,\ q(z)=0\}$, and $Q_3=S/U(1)$ is the projective quadric. Let $\pi:S\to Q_3$ be the projection $z\mapsto[z]$.
--
--   1. **Fibres.** For $z,w\in S$, $\pi(z)=\pi(w)$ if and only if $z=cw$ for some $c\in\mathbb{C}$ with $|c|=1$.
--   2. **Unit representatives.** Each $p\in Q_3$ has a chosen representative $r(p)\in S$ with $\pi(r(p))=p$.
--   3. **Descent.** Let $F:\mathbb{C}^5\to\mathbb{C}^5$ map $S$ into $S$ and satisfy $F(cz)=cF(z)$ for $|c|=1$ and $z\in S$. Then $\pi(F(z))$ depends only on $\pi(z)$. The descended map
--   $$
--   \bar F(p)=\pi\bigl(F(r(p))\bigr)
--   $$
--   satisfies $\bar F(\pi z)=\pi(Fz)$.
--   4. **Descended bijections.** If $F$ and $G$ are two such maps that are mutually inverse on $S$, then $\bar F$ and $\bar G$ are mutually inverse bijections of $Q_3$.
--
--   This is the bridge from explicit maps on $\mathbb{C}^5$ to self-maps of $Q_3$. It is used to turn the forward and backward maps of the Hamiltonian isotopy into a bijection of the quadric.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Quotient.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Quotient.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField
import Definitions.Def_OAI_Geometry_Arnold_Midpoint
import Definitions.Def_OAI_Geometry_Arnold_MidpointGeometry
import Definitions.Def_OAI_Geometry_Arnold_Parameter

namespace OAI

noncomputable section
open scoped BigOperators ContDiff
open scoped Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Quadric
open scoped ContDiff Topology

lemma project_eq_iff_phase (z w : UnitQuadric) : project z = project w ↔
    ∃ c : ℂ, Complex.normSq c = 1 ∧ c • (w:CV) = (z:CV) := by
  constructor
  · intro h
    have he := congrArg Subtype.val h
    change Projectivization.mk ℂ (z:CV) _ = Projectivization.mk ℂ (w:CV) _ at he
    obtain ⟨c, hc⟩ := (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp he
    refine ⟨c, ?_, hc⟩
    have hn := congrArg normSquared hc
    simpa only [normSquared_smul, z.property.1, w.property.1, mul_one] using hn
  · rintro ⟨c, _, hc⟩
    apply Subtype.ext
    change Projectivization.mk ℂ (z:CV) _ = Projectivization.mk ℂ (w:CV) _
    exact (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr ⟨c,hc⟩

def unitRepresentative (q : Q3) : UnitQuadric := project_surjective q |>.choose
lemma project_unitRepresentative (q : Q3) : project (unitRepresentative q) = q :=
  (project_surjective q).choose_spec

lemma phase_map_respects (F : CV → CV) (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z))
    (hphase : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → F (c • (z:CV)) = c • F z)
    (z w : UnitQuadric) (hzw : project z = project w) :
    project ⟨F z,hF z⟩ = project ⟨F w,hF w⟩ := by
  obtain ⟨c,hc,he⟩ := (project_eq_iff_phase z w).mp hzw
  apply (project_eq_iff_phase _ _).mpr
  exact ⟨c,hc, (hphase w c hc).symm.trans (congrArg F he)⟩

/-- Descent through the actual circle quotient, proved from its actual fibers. -/
def descend (F : CV → CV) (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z)) (q : Q3) : Q3 :=
  project ⟨F (unitRepresentative q),hF _⟩

lemma descend_project (F : CV → CV) (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z))
    (hphase : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → F (c • (z:CV)) = c • F z)
    (z : UnitQuadric) : descend F hF (project z) = project ⟨F z,hF z⟩ :=
  phase_map_respects F hF hphase _ z (project_unitRepresentative (project z))

def descendEquiv (F G : CV → CV)
    (hF : ∀ z : UnitQuadric, IsUnitQuadric (F z))
    (hG : ∀ z : UnitQuadric, IsUnitQuadric (G z))
    (hFp : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → F (c • (z:CV)) = c • F z)
    (hGp : ∀ (z : UnitQuadric) (c : ℂ), Complex.normSq c = 1 → G (c • (z:CV)) = c • G z)
    (hGF : ∀ z : UnitQuadric, G (F z) = z) (hFG : ∀ z : UnitQuadric, F (G z) = z) : Q3 ≃ Q3 where
  toFun := descend F hF
  invFun := descend G hG
  left_inv q := by
    obtain ⟨z,rfl⟩ := project_surjective q
    rw [descend_project F hF hFp, descend_project G hG hGp]
    exact congrArg project (Subtype.ext (hGF z))
  right_inv q := by
    obtain ⟨z,rfl⟩ := project_surjective q
    rw [descend_project G hG hGp, descend_project F hF hFp]
    exact congrArg project (Subtype.ext (hFG z))

end ArnoldCounterexample.Quadric

end

end OAI


