-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P42
-- name    : QAlgorithms_Papers_Independent_Intake100_P42
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T12:20:56.392021+00:00
-- url     : https://prove2.me/theorems/f667fe16-0471-44da-b2cd-e1881c58318e
-- title:
--   Definitions for Restriction of Uniform Crossnorms
-- statement:
--   The objects the formalized statements of *Restriction of Uniform Crossnorms* (arXiv:2212.10780) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `CrossnormFamily`: PDF pp.2--3: one assignment of reasonable norms to every normed pair in an arbitrary common universe, including pairs of bounded-map spaces.
--   - `IsUniform`: PDF p.3: the metric mapping property of ONE reasonable crossnorm family. The finite bound also gives boundedness of the algebraic tensor map.
--   - `BoundedIn`: PDF pp.3--4: boundedness of a linear map for explicit domain/range norms. For genuine norms this is exactly continuity of the map between those spaces.
--   - `extendedOperatorNorm`: PDF pp.6--8: the actual possibly infinite induced norm. Only nonzero vectors enter the ratios; on a zero domain the supremum is zero.
--   - `algebraicMapNorm`: PDF pp.3--8: the finite induced norm on bounded linear maps, computed from the preceding supremum. Used as a norm only when boundedness is proved or assumed as in the source. Finiteness guards accompany the conclusions.
--   - `ratioSup`: PDF pp.7--8: supremum of norm ratios on the common nonzero carrier. Unbounded ratios give infinity; the empty set gives zero.
--   - `ratioInf`: PDF pp.7--8: the analogous infimum; the empty set gives infinity.
--   - `NormEquivalent`: PDF p.8: equivalence via positive finite constants, also meaningful on a zero space; these bounds give continuous identity maps in both directions.
--   - `operatorAction`: PDF pp.2,4: canonical operator-tensor action, independent of every choice of finite representation. It is linear in the operator tensor and its input.
--   - `restrictedOperatorNorm`: PDF pp.4--8: actual induced operator norm pulled back along operatorAction. This is not the family's norm on the pair of operator spaces.
--   - `MixedBounded`: PDF p.8, Remark 4.5: additional mixed boundedness for every pair A,B. This assumes no upper metric mapping bound for the two distinct families.
-- source:
--   Restriction of Uniform Crossnorms, arXiv:2212.10780v2, https://arxiv.org/abs/2212.10780v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P02

/-!
Kubrusly, Restriction of Uniform Crossnorms, arXiv:2212.10780v2.
All tensor products in this module are algebraic. A normed algebraic space is
represented by its actual carrier together with its explicit norm function.
BoundedIn is the usual bounded-linear-map criterion in these norms, so an
inclusion of bounded maps preserves the underlying linear map literally.
The induced norm is computed from that map, never supplied as independent data.
No theorem below requires complete or nonzero factors.

The accepted Next46.P02 definitions are imported directly: NormOn (on the
whole carrier), banachTensorEval, dualTensorPairing, injectiveNorm,
algebraicProjectiveNorm and ReasonableCrossnorm. Their definition bodies do
not depend on completeness. The bundled background theorem does require
completeness and is not reused. The explicit algebraicMapNorm below concerns
arbitrary algebraic linear maps with specified norms, unlike the accepted
Information100.P23.operatorNorm for real matrices in a Euclidean norm.
-/

noncomputable section

namespace QAlgorithms.Papers.Independent.Intake100.P42

open scoped TensorProduct ENNReal

open QAlgorithms.Papers.Independent.Next46.P02

universe u

variable {F : Type u} [RCLike F]

section Pair

variable {X Y : Type u}
variable [NormedAddCommGroup X] [NormedSpace F X]
variable [NormedAddCommGroup Y] [NormedSpace F Y]

example (f : X →L[F] F) (g : Y →L[F] F) (x : X) (y : Y) :
    banachTensorEval f g (x ⊗ₜ[F] y) = f x * g y := by
  simp [banachTensorEval]

example (f : X →L[F] F) (g : Y →L[F] F) (x : X) (y : Y) :
    dualTensorPairing (f ⊗ₜ[F] g) (x ⊗ₜ[F] y) = f x * g y := by
  simp [dualTensorPairing, banachTensorEval]

end Pair

/-- PDF pp.2--3: one assignment of reasonable norms to every normed pair
in an arbitrary common universe, including pairs of bounded-map spaces. -/
structure CrossnormFamily (F : Type u) [RCLike F] where
  norm : ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace F X]
    (Y : Type u) [NormedAddCommGroup Y] [NormedSpace F Y],
      TensorProduct F X Y → ℝ
  reasonable : ∀ (X : Type u) [NormedAddCommGroup X] [NormedSpace F X]
    (Y : Type u) [NormedAddCommGroup Y] [NormedSpace F Y],
      ReasonableCrossnorm (norm X Y)

/-- PDF p.3: the metric mapping property of ONE reasonable crossnorm family.
The finite bound also gives boundedness of the algebraic tensor map. -/
def IsUniform (a : CrossnormFamily F) : Prop :=
  ∀ (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W]
    (A : X →L[F] V) (B : Y →L[F] W) (t : TensorProduct F X Y),
    a.norm V W (TensorProduct.map A.toLinearMap B.toLinearMap t) ≤
      ‖A‖ * ‖B‖ * a.norm X Y t

section ExplicitNorms

variable {E G : Type*} [AddCommGroup E] [Module F E]
variable [AddCommGroup G] [Module F G]

/-- PDF pp.3--4: boundedness of a linear map for explicit domain/range norms.
For genuine norms this is exactly continuity of the map between those spaces. -/
def BoundedIn (p : E → ℝ) (q : G → ℝ) (T : E →ₗ[F] G) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ t, q (T t) ≤ C * p t

/-- PDF pp.6--8: the actual possibly infinite induced norm. Only nonzero
vectors enter the ratios; on a zero domain the supremum is zero. -/
def extendedOperatorNorm (p : E → ℝ) (q : G → ℝ) (T : E →ₗ[F] G) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ t : E, t ≠ 0 ∧
    r = ENNReal.ofReal (q (T t)) / ENNReal.ofReal (p t)}

/-- PDF pp.3--8: the finite induced norm on bounded linear maps, computed
from the preceding supremum. Used as a norm only when boundedness is proved
or assumed as in the source. Finiteness guards accompany the conclusions. -/
def algebraicMapNorm (p : E → ℝ) (q : G → ℝ) (T : E →ₗ[F] G) : ℝ :=
  (extendedOperatorNorm p q T).toReal

example (p : E → ℝ) (q : G → ℝ) (hq : q 0 = 0) :
    extendedOperatorNorm p q (0 : E →ₗ[F] G) = 0 := by
  apply le_antisymm _ bot_le
  apply sSup_le
  rintro r ⟨t, ht, rfl⟩
  simp [hq]

example (p : E → ℝ) (q : G → ℝ) (hq : q 0 = 0) :
    BoundedIn p q (0 : E →ₗ[F] G) := by
  refine ⟨0, le_rfl, ?_⟩
  intro t
  simp [hq]

end ExplicitNorms

/-- PDF pp.7--8: supremum of norm ratios on the common nonzero carrier.
Unbounded ratios give infinity; the empty set gives zero. -/
def ratioSup {E : Type*} [Zero E] (p q : E → ℝ) : ℝ≥0∞ :=
  sSup {r : ℝ≥0∞ | ∃ t : E, t ≠ 0 ∧
    r = ENNReal.ofReal (p t) / ENNReal.ofReal (q t)}

/-- PDF pp.7--8: the analogous infimum; the empty set gives infinity. -/
def ratioInf {E : Type*} [Zero E] (p q : E → ℝ) : ℝ≥0∞ :=
  sInf {r : ℝ≥0∞ | ∃ t : E, t ≠ 0 ∧
    r = ENNReal.ofReal (p t) / ENNReal.ofReal (q t)}

/-- PDF p.8: equivalence via positive finite constants, also meaningful on
a zero space; these bounds give continuous identity maps in both directions. -/
def NormEquivalent {E : Type*} (p q : E → ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ t, c * p t ≤ q t ∧ q t ≤ C * p t

example {E : Type*} [Zero E] [Subsingleton E] (p q : E → ℝ) :
    ratioSup p q = 0 := by
  apply le_antisymm _ bot_le
  apply sSup_le
  rintro r ⟨t, ht, hr⟩
  exact (ht (Subsingleton.elim t 0)).elim

example {E : Type*} [Zero E] [Subsingleton E] (p q : E → ℝ) :
    ratioInf p q = ⊤ := by
  apply top_unique
  apply le_sInf
  rintro r ⟨t, ht, hr⟩
  exact (ht (Subsingleton.elim t 0)).elim

example {E : Type*} (p : E → ℝ) : NormEquivalent p p := by
  refine ⟨1, 1, zero_lt_one, zero_lt_one, ?_⟩
  intro t
  simp

section FourSpaces

variable {X Y V W : Type u}
variable [NormedAddCommGroup X] [NormedSpace F X]
variable [NormedAddCommGroup Y] [NormedSpace F Y]
variable [NormedAddCommGroup V] [NormedSpace F V]
variable [NormedAddCommGroup W] [NormedSpace F W]

/-- PDF pp.2,4: canonical operator-tensor action, independent of every choice
of finite representation. It is linear in the operator tensor and its input. -/
def operatorAction :
    TensorProduct F (X →L[F] V) (Y →L[F] W) →ₗ[F]
      (TensorProduct F X Y →ₗ[F] TensorProduct F V W) :=
  (TensorProduct.homTensorHomMap (RingHom.id F) X Y V W).comp
    (TensorProduct.map (ContinuousLinearMap.coeLM F) (ContinuousLinearMap.coeLM F))

/-- PDF pp.4--8: actual induced operator norm pulled back along operatorAction.
This is not the family's norm on the pair of operator spaces. -/
def restrictedOperatorNorm
    (p : TensorProduct F X Y → ℝ) (q : TensorProduct F V W → ℝ)
    (L : TensorProduct F (X →L[F] V) (Y →L[F] W)) : ℝ :=
  algebraicMapNorm p q (operatorAction L)

example (A : X →L[F] V) (B : Y →L[F] W) (x : X) (y : Y) :
    operatorAction (A ⊗ₜ[F] B) (x ⊗ₜ[F] y) = A x ⊗ₜ[F] B y := by
  simp [operatorAction]

example : operatorAction (0 : TensorProduct F (X →L[F] V) (Y →L[F] W)) = 0 := by
  exact map_zero operatorAction

end FourSpaces

/-- PDF p.8, Remark 4.5: additional mixed boundedness for every pair A,B.
This assumes no upper metric mapping bound for the two distinct families. -/
def MixedBounded (a b : CrossnormFamily F) : Prop :=
  ∀ (X Y V W : Type u)
    [NormedAddCommGroup X] [NormedSpace F X]
    [NormedAddCommGroup Y] [NormedSpace F Y]
    [NormedAddCommGroup V] [NormedSpace F V]
    [NormedAddCommGroup W] [NormedSpace F W]
    (A : X →L[F] V) (B : Y →L[F] W),
    BoundedIn (a.norm X Y) (b.norm V W)
      (TensorProduct.map A.toLinearMap B.toLinearMap)

end QAlgorithms.Papers.Independent.Intake100.P42


