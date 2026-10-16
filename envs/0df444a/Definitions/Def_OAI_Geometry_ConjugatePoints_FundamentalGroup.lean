-- Prove2me | Definitions.Def_OAI_Geometry_ConjugatePoints_FundamentalGroup
-- name    : OAI_Geometry_ConjugatePoints_FundamentalGroup
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T21:28:50.73769+00:00
-- url     : https://prove2.me/theorems/00f6938b-9670-4948-bfa9-3420e3be7bcf
-- title:
--   Peripheral loops, circle fibres and block maps into the fundamental group of the glued three-manifold
-- statement:
--   This file fixes the base points, loops and homomorphisms used to compute in the fundamental group of the glued three-manifold $M$: a peripheral (horocyclic) loop of the cusped surface, a circle-fibre loop, and the two maps of $\Sigma\times S^1$ into $M$ coming from the two halves of the gluing, together with the relation the gluing imposes on the boundary torus.
--
--   **Setting.** Let $\mathbb{H}=\{z\in\mathbb{C}:\operatorname{Im}z>0\}$ with the Möbius action of $SL(2,\mathbb{Z})$, let $\varphi=\begin{pmatrix}1&1\\1&2\end{pmatrix}$, $\psi=\begin{pmatrix}1&-1\\-1&2\end{pmatrix}$, $T=\begin{pmatrix}1&1\\0&1\end{pmatrix}$ and $\Gamma=\langle\varphi,\psi,-I\rangle\le SL(2,\mathbb{Z})$. Write $\bar\Gamma$ for the group of transformations of $\mathbb{H}$ induced by $\Gamma$, $\Sigma=\mathbb{H}/\bar\Gamma$ for the quotient surface with projection $\pi:\mathbb{H}\to\Sigma$, and $h:\Sigma\to\mathbb{R}$ for the height $h(\pi(z))=\log\max_{g\in SL(2,\mathbb{Z})}\operatorname{Im}(g\cdot z)$. On the cusp region $\Sigma_{>2}=\pi(\{\operatorname{Im}z>2\})$ the cusp coordinates are $\pi(z)\mapsto(\operatorname{Im}z,\ \operatorname{Re}z \bmod 6)\in(2,\infty)\times\mathbb{R}/6\mathbb{Z}$. Put $S^1=\mathbb{R}/6\mathbb{Z}$, the piece $X=\{x\in\Sigma:h(x)<\log 8\}\times S^1$, and the collar $C=\{(x,u)\in X:x\in\Sigma_{>2}\}$ with collar coordinates $(x,u)\mapsto(y,(\theta,u))\in(2,8)\times(S^1\times S^1)$, where $(y,\theta)$ are the cusp coordinates of $x$. The manifold $M$ is obtained from two copies $X_0,X_1$ of $X$ by identifying $c\in C\subset X_0$ with $\Phi(c)\in C\subset X_1$, where in collar coordinates $\Phi(y,(\theta_1,\theta_2))=(16/y,(\theta_2,\theta_1-\theta_2))$; $\iota_0,\iota_1:X\to M$ denote the two inclusions.
--
--   1. **Generators.** $g_0=\varphi$ and $g_1=\psi$ (both lie in $\Gamma$), and $\bar g_0,\bar g_1\in\bar\Gamma$ are their images. For every $z\in\mathbb{H}$, the covering $\pi$ gives a group isomorphism $\pi_1(\Sigma,\pi(z))\cong\bar\Gamma^{\mathrm{op}}$ onto the opposite group of $\bar\Gamma$.
--
--   2. **Peripheral loop.** For $a>0$ and $t\in\mathbb{R}$ let $\eta_a(t)=6t+ia\in\mathbb{H}$. It is continuous in $t$ and $\eta_a(1)=T^6\cdot\eta_a(0)$; since $T^6\in\Gamma$, the path $t\mapsto\pi(\eta_a(t))$, $t\in[0,1]$, is a loop in $\Sigma$ at $\pi(ia)$. Its class is $\beta_a\in\pi_1(\Sigma,\pi(ia))$.
--
--   3. **Product classes.** For spaces $Y,Z$ with base points $y,z$ and classes $\alpha\in\pi_1(Y,y)$, $\gamma\in\pi_1(Z,z)$, $\langle\alpha,\gamma\rangle\in\pi_1(Y\times Z,(y,z))$ is the class of the product loop. It satisfies $\langle\alpha\alpha',\gamma\gamma'\rangle=\langle\alpha,\gamma\rangle\langle\alpha',\gamma'\rangle$ and $\langle1,1\rangle=1$, so $\lambda_z(\alpha)=\langle\alpha,1\rangle$ is a homomorphism $\pi_1(Y,y)\to\pi_1(Y\times Z,(y,z))$.
--
--   4. **Block maps.** The clipping map $c:\Sigma\to\Sigma$ fixes every point outside $\Sigma_{>2}$ and acts in cusp coordinates by $(y,\theta)\mapsto(\min(y,4),\theta)$; every value $c(x)$ has height $h(c(x))\le\log 4$. The clipped map $\kappa(x,u)=(c(x),u)$ is a continuous map $\Sigma\times S^1\to X$ with $\kappa(x,u)=(x,u)$ whenever $h(x)\le\log4$, and the block maps are the continuous maps $B_i=\iota_i\circ\kappa:\Sigma\times S^1\to M$, $i=0,1$.
--
--   5. **Boundary torus.** $\sigma(u)\in\Sigma$ is the point with cusp coordinates $(4,u)$; it has $h(\sigma(u))=\log4$ and $\sigma(6t\bmod 6)=\pi(\eta_4(t))$. For $z=(z_1,z_2)\in S^1\times S^1$, $\tau(z)\in C$ is the point with collar coordinates $(4,z)$. Then $B_i(\sigma(z_1),z_2)=\iota_i(\tau(z))$, $\Phi^{-1}(\tau(z))=\tau(z_1+z_2,z_1)$, and consequently
--   $$
--   B_1(\sigma(z_1),z_2)=B_0(\sigma(z_1+z_2),z_1)\qquad\text{for all }z_1,z_2\in S^1 .
--   $$
--
--   6. **Base points.** $\sigma_0=\pi(4i)$, $w_0=(\sigma_0,0)\in\Sigma\times S^1$ and $m_0=B_0(w_0)\in M$; also $B_1(w_0)=m_0$ and $\sigma(0)=\sigma_0$.
--
--   7. **Classes in $\pi_1(M,m_0)$.** The circle loop $t\mapsto 6t\bmod 6$ has class $\zeta\in\pi_1(S^1,0)$. For $i=0,1$, $(B_i)_*:\pi_1(\Sigma\times S^1,w_0)\to\pi_1(M,m_0)$ is the induced homomorphism, $s_i=(B_i)_*\circ\lambda_0:\pi_1(\Sigma,\sigma_0)\to\pi_1(M,m_0)$, the fibre class is $f_i=(B_i)_*\langle1,\zeta\rangle$ and the boundary image is $b_i=s_i(\beta_4)$.
--
--   The displayed shear relation is the topological content of the gluing: it identifies, on the common boundary torus at height $\log 4$, the fibre direction of one block with the peripheral direction of the other. The classes $f_i$ and $b_i$ are the elements whose relations and nontriviality are studied in the fundamental-group part of the argument.
--
--   **Formalization Note** Booleans index the two copies (`false` is $0$, `true` is $1$). The isomorphism in item 1 is `projection_cover.fundamentalGroupEquiv`; the induced maps $(B_i)_*$ use `FundamentalGroup.mapOfEq` with the proof $B_i(w_0)=m_0$. Several members (`horoline_one`, `blockMap_torus`, `gluing_torus`, `blockMap_base`, …) are the lemmas recorded above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/ConjugatePoints/FundamentalGroup.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/ConjugatePoints/FundamentalGroup.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ConjugatePoints mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ConjugatePoints
import Definitions.Def_OAI_Geometry_ConjugatePoints_Quotient
import Definitions.Def_OAI_Geometry_ConjugatePoints_Gluing
import Definitions.Def_OAI_Geometry_ConjugatePoints_Metric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Cometric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Neck
import Definitions.Def_OAI_Geometry_ConjugatePoints_Coordinates
import Definitions.Def_OAI_Geometry_ConjugatePoints_Returning
import Definitions.Def_OAI_Geometry_ConjugatePoints_Index
import Definitions.Def_OAI_Geometry_ConjugatePoints_CompactMetric
import Definitions.Def_OAI_Geometry_ConjugatePoints_Curvature
import Definitions.Def_OAI_Geometry_ConjugatePoints_Geodesics
import Definitions.Def_OAI_Geometry_ConjugatePoints_Continuation
import Definitions.Def_OAI_Geometry_ConjugatePoints_Distance
import Definitions.Def_OAI_Geometry_ConjugatePoints_Convexity

namespace OAI

noncomputable section

/-!
# Fundamental-group relations and nontrivial fiber classes.
-/

section

open Matrix Set Pointwise
open scoped MatrixGroups UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

def pairingGenerator : Bool → SL(2,ℤ) | false => phi | true => psi
lemma pairingGenerator_mem (i : Bool) : pairingGenerator i ∈ Γ := by
  cases i
  · exact phi_mem
  · exact psi_mem

def effectiveGenerator (i : Bool) : effective := effect ⟨pairingGenerator i,pairingGenerator_mem i⟩
def surfaceFundamentalGroupEquiv (z : ℍ) :
    FundamentalGroup Surface (projection z) ≃* effectiveᵐᵒᵖ :=
  projection_cover.fundamentalGroupEquiv ⟨z,rfl⟩

end ThreeManifold.HyperbolicCore
end

section
open Set Filter Topology ModularGroup
open scoped UpperHalfPlane
namespace ThreeManifold.HyperbolicCore

def horoline (a t : ℝ) (ha : 0 < a) : ℍ := ⟨(6*t:ℂ) + a*Complex.I, by simpa using ha⟩
lemma horoline_continuous (a : ℝ) (ha : 0 < a) : Continuous (fun t => horoline a t ha) := by
  apply continuous_induced_rng.mpr
  change Continuous (fun t : ℝ => ((6*t:ℂ) + a*Complex.I))
  fun_prop
lemma horoline_one (a : ℝ) (ha : 0 < a) : horoline a 1 ha = T^6 • horoline a 0 ha := by
  apply UpperHalfPlane.ext
  rw [show (T ^ (6:ℕ)) = T ^ (6:ℤ) by norm_cast, ModularGroup.coe_T_zpow_smul_eq]
  simp [horoline]
  ring

def boundaryPath (a : ℝ) (ha : 0 < a) : Path (projection (horoline a 0 ha)) (projection (horoline a 0 ha)) where
  toFun t := projection (horoline a t ha)
  continuous_toFun := projection_cover.continuous.comp ((horoline_continuous a ha).comp continuous_subtype_val)
  source' := rfl
  target' := by change projection (horoline a 1 ha) = _; rw [horoline_one,projection_smul _ T_six_mem]

def boundaryClass (a : ℝ) (ha : 0 < a) : FundamentalGroup Surface (projection (horoline a 0 ha)) :=
  FundamentalGroup.fromPath (.mk (boundaryPath a ha))

end ThreeManifold.HyperbolicCore
end

section
open Set Topology
namespace ThreeManifold.LoopTopology
open Path.Homotopic
variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {x : X} {y : Y}
def pair (a : FundamentalGroup X x) (b : FundamentalGroup Y y) :
    FundamentalGroup (X×Y) (x,y) := prod a b
lemma pair_mul (a c : FundamentalGroup X x) (b d : FundamentalGroup Y y) :
    pair (a*c) (b*d) = pair a b * pair c d :=
  (comp_prod_eq_prod_comp c d a b).symm
lemma pair_one : pair (1 : FundamentalGroup X x) (1 : FundamentalGroup Y y) =
    (1 : FundamentalGroup (X×Y) (x,y)) := by
  change Path.Homotopic.Quotient.mk ((Path.refl x).prod (Path.refl y)) = Path.Homotopic.Quotient.mk (Path.refl (x,y))
  congr
def leftHom (y : Y) : FundamentalGroup X x →* FundamentalGroup (X×Y) (x,y) where
  toFun a := pair a 1
  map_one' := pair_one
  map_mul' a b := by simpa using pair_mul a b (1 : FundamentalGroup Y y) 1

end ThreeManifold.LoopTopology
end

section
open Set Filter Topology
open scoped UpperHalfPlane
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology

def clippedPiece (x : Surface×Circle) : Piece :=
  (⟨clipCusp 2 4 (by norm_num) (by norm_num) x.1,
    (clipCusp_height_le 2 4 (by norm_num) (by norm_num) x.1).trans_lt
      (Real.log_lt_log (by norm_num) (by norm_num : (4:ℝ)<8))⟩,x.2)
lemma clippedPiece_continuous : Continuous clippedPiece :=
  (((clipCusp_continuous 2 4 (by norm_num) (by norm_num)).comp continuous_fst).subtype_mk _).prodMk continuous_snd

def blockMap (i : Bool) : C(Surface×Circle,Manifold) :=
  ⟨inclusion i ∘ clippedPiece,(TwoGluing.inclusion_openEmbedding collar gluingMap i).continuous.comp clippedPiece_continuous⟩
lemma clippedPiece_fixed (x : Surface) (hx : height x ≤ Real.log 4) (u : Circle) :
    clippedPiece (x,u) = (⟨x,hx.trans_lt (Real.log_lt_log (by norm_num) (by norm_num : (4:ℝ)<8))⟩,u) := by
  apply Prod.ext
  · apply Subtype.ext; exact clipCusp_eq_self 2 4 (by norm_num) (by norm_num) hx
  · rfl

def boundarySurface (u : Circle) : Surface :=
  ((cuspCoordinates 2 (by norm_num)).symm (⟨4,by norm_num⟩,u)).1
lemma boundarySurface_height (u : Circle) : height (boundarySurface u) = Real.log 4 := by
  unfold boundarySurface
  rw [height_cuspCoordinates 2 (by norm_num),Homeomorph.apply_symm_apply]
lemma boundarySurface_horoline (t : ℝ) :
    boundarySurface ((6*t : ℝ) : Circle) = projection (horoline 4 t (by norm_num)) := by
  have hh := cuspCoordinates_apply 2 (by norm_num) (horoline 4 t (by norm_num)) (by norm_num [horoline])
  have he : (cuspCoordinates 2 (by norm_num))
      ⟨projection (horoline 4 t (by norm_num)),⟨horoline 4 t (by norm_num),by norm_num [horoline],rfl⟩⟩ =
      (⟨4,by norm_num⟩,((6*t : ℝ) : Circle)) := by simpa [horoline] using hh
  change ((cuspCoordinates 2 (by norm_num)).symm (⟨4,by norm_num⟩,((6*t:ℝ):Circle))).1 = _
  rw [← he,Homeomorph.symm_apply_apply]

def torusPoint (z : Circle×Circle) : collar :=
  collarCoordinates.symm (⟨4,by norm_num,by norm_num⟩,z)
lemma blockMap_torus (i : Bool) (z : Circle×Circle) :
    blockMap i (boundarySurface z.1,z.2) = inclusion i (torusPoint z).1 := by
  change inclusion i (clippedPiece (boundarySurface z.1,z.2)) = _
  rw [clippedPiece_fixed _ (by rw [boundarySurface_height])]
  rfl
lemma gluing_torus (z : Circle×Circle) : gluingMap.symm (torusPoint z) = torusPoint (torusShear z) := by
  change collarCoordinates.symm ((collarFlip.prodCongr torusShear.symm).symm
    (collarCoordinates (collarCoordinates.symm (⟨4,by norm_num,by norm_num⟩,z)))) = _
  rw [Homeomorph.apply_symm_apply]
  apply congrArg collarCoordinates.symm
  apply Prod.ext
  · apply Subtype.ext
    norm_num [collarFlip]
  · rfl
lemma blockMap_torus_shear (z : Circle×Circle) :
    blockMap true (boundarySurface z.1,z.2) =
      blockMap false (boundarySurface (z.1+z.2),z.1) := by
  change blockMap true (boundarySurface z.1,z.2) =
    blockMap false (boundarySurface (torusShear z).1,(torusShear z).2)
  rw [blockMap_torus true z,blockMap_torus false (torusShear z)]
  have h := TwoGluing.inclusion_symm_transition collar gluingMap (torusPoint z)
  rw [gluing_torus] at h
  exact h

abbrev baseSurface : Surface := projection (horoline 4 0 (by norm_num))
abbrev wholeBase : Surface×Circle := (baseSurface,0)
def basePoint : Manifold := blockMap false wholeBase
lemma boundarySurface_zero : boundarySurface 0 = baseSurface := by simpa using boundarySurface_horoline 0
lemma blockMap_base (i : Bool) : blockMap i wholeBase = basePoint := by
  cases i
  · rfl
  · have h := blockMap_torus_shear (0,0)
    change blockMap true (baseSurface,0) = blockMap false (baseSurface,0)
    simpa only [zero_add,boundarySurface_zero] using h

def circlePath : Path (0 : Circle) 0 where
  toFun t := ((6*(t : ℝ) : ℝ) : Circle)
  continuous_toFun := (AddCircle.continuous_mk' 6).comp (continuous_const.mul continuous_subtype_val)
  source' := by simp
  target' := by change ((6*(1:ℝ) : ℝ) : Circle) = 0; simp

def circleClass : FundamentalGroup Circle 0 := Path.Homotopic.Quotient.mk circlePath

def blockHom (i : Bool) : FundamentalGroup (Surface×Circle) wholeBase →* FundamentalGroup Manifold basePoint :=
  FundamentalGroup.mapOfEq (blockMap i) (blockMap_base i)
def surfaceHom (i : Bool) : FundamentalGroup Surface baseSurface →* FundamentalGroup Manifold basePoint :=
  (blockHom i).comp (leftHom (0 : Circle))
def fiberClass (i : Bool) : FundamentalGroup Manifold basePoint :=
  blockHom i (pair 1 circleClass)
def boundaryImage (i : Bool) : FundamentalGroup Manifold basePoint :=
  surfaceHom i (boundaryClass 4 (by norm_num))
end ThreeManifold.GluedConstruction
end

open Set Filter Topology
namespace ThreeManifold.GluedConstruction
open HyperbolicCore LoopTopology
end ThreeManifold.GluedConstruction

end

end OAI


