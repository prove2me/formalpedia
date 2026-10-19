-- Prove2me | Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
-- name    : OAI_MathematicalPhysics_NavierStokes_BalancedTransport_TimeRegularity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T02:44:20.849989+00:00
-- url     : https://prove2.me/theorems/2343f1a6-d16f-47b9-b31f-221690d62453
-- title:
--   Moving boxes and their velocity fields
-- statement:
--   This is part of the construction of smooth forced incompressible Navier–Stokes flows on $\mathbb R^3$ whose fluid particles simulate a Turing machine: a fixed particle enters a fixed box exactly when the machine halts. A field is a function $v(t,x)$ of time $t\in\mathbb R$ and position $x\in\mathbb R^3$, and a velocity is a field with values in $\mathbb R^3$.
--
--   1. **Joint smoothness.** A field is jointly smooth when $(t,x)\mapsto v(t,x)$ is $C^\infty$. Its time derivative is $\partial_tv$.
--   2. **Moving boxes.** Given a reference box $[a,b]$ and smooth curves $c(t)\in\mathbb R^3$ and $d(t)\in(0,\infty)^3$, the moving box at time $t$ has lower corner $c(t)+d(t)a$ and upper corner $c(t)+d(t)b$, products taken coordinatewise.
--   3. **Velocity.** The moving-box velocity is the localized affine field of this box with centre $c(t)$, translation velocity $c'(t)$ and logarithmic rates $d_i'(t)/d_i(t)$.
--   4. **Affine paths.** $t\mapsto c(t)+d(t)z$, the trajectory of the label $z$ under this velocity, since
--   $$
--   \frac{d}{dt}\bigl(c+dz\bigr)=c'+\frac{d'}{d}\,(dz).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/TimeRegularity.lean

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/TimeRegularity.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedThreeStack mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveExp
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RecorderRules
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_PrefixCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_BoxCoding
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_Work

namespace OAI

noncomputable section
namespace BalancedTransport.Geometry
open scoped Topology
open Filter Set
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

def JointSmooth (f : Field F) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry f)

theorem JointSmooth.slice {f : Field F} (hf : JointSmooth f) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (f t) := hf.comp (contDiff_const.prodMk contDiff_id)

def fullTimeD (f : Field F) : Field F := fun t x => deriv (fun s => f s x) t

theorem JointSmooth.fullTimeD {f : Field F} (hf : JointSmooth f) :
    JointSmooth (fullTimeD f) := by
  have hh : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : (ℝ × Space) × ℝ => f z.2 z.1.2) :=
    hf.comp (contDiff_snd.prodMk contDiff_fst.snd)
  exact ContDiff.fderiv_apply (f := fun z : ℝ × Space => fun s => f s z.2)
    hh contDiff_fst contDiff_const (by simp)

def lowerEndpoint (a : Space) (c d : ℝ → Space) (t : ℝ) : Space :=
  fun i => c t i + d t i * a i

def logarithmicRate (d : ℝ → Space) (t : ℝ) : Space :=
  fun i => deriv (fun s => d s i) t / d t i

def movingBoxVelocity (a b : Space) (c d : ℝ → Space) (η : ℝ) : Velocity :=
  fun t => localizedAffine (lowerEndpoint a c d t) (lowerEndpoint b c d t)
    (c t) (deriv c t) (logarithmicRate d t) η

def affinePath (c d : ℝ → Space) (z : Space) (t : ℝ) : Space :=
  fun i => c t i + d t i * z i

@[simp] lemma affinePotential_zero (c : Space) : affinePotential c 0 0 = 0 := by
  ext x i
  fin_cases i <;> simp [affinePotential]

@[simp] lemma localizedAffine_zero (a b c : Space) (η : ℝ) :
    localizedAffine a b c 0 0 η = 0 := by
  unfold localizedAffine
  have he : (fun x => boxCutoff a b η x • affinePotential c 0 0 x) = 0 := by
    ext x i
    fin_cases i <;> simp [affinePotential]
  rw [he]
  exact curl_zero

end BalancedTransport.Geometry
end

end OAI


