-- Prove2me | Definitions.Def_OAIQ079A002
-- name    : OAIQ079A002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-28T15:35:45.886429+00:00
-- url     : https://prove2.me/theorems/5cbcc402-0288-467f-aff6-2d1e26b25dd4
-- title:
--   Definitions bundle OAIQ079A002 of the split of OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354)
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.CubicTorus.unit_cubic_isoperimetric`, carved from OpenAI's openai/math development (OpenAI, *The isoperimetric conjecture for the cubic flat three-torus (result family 354)*, OpenAI Math Release, September 24, 2026, result family 354, [github.com/openai/math](https://github.com/openai/math) at commit 1581d4c, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 50 declarations of OpenAI's Lean: 38 definitions, 8 instances and 4 theorems. The definitions and types are `OAI.CubicTorus.phi`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e3189`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e3193`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e3238`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e3242`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e3287`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e3291`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e337`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e342`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e484`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e489`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e777`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e782`, `OAI.ReusedScalar205.CubicTorus.Scalar.Cert.e938`, `OAI.ReusedScalar205.CubicTorus.Scalar.C₀`, `OAI.ReusedScalar205.CubicTorus.Scalar.J₁`, `OAI.ReusedScalar205.CubicTorus.Scalar.J₂`, `OAI.ReusedScalar205.CubicTorus.Scalar.P`, `OAI.ReusedScalar205.CubicTorus.Scalar.Q`, `OAI.ReusedScalar205.CubicTorus.Scalar.QRad`, `OAI.ReusedScalar205.CubicTorus.Scalar.R`, `OAI.ReusedScalar205.CubicTorus.Scalar.RSlope`, `OAI.ReusedScalar205.CubicTorus.Scalar.beta`, `OAI.ReusedScalar205.CubicTorus.Scalar.cappedEnergy`, `OAI.ReusedScalar205.CubicTorus.Scalar.cappedInf`, `OAI.ReusedScalar205.CubicTorus.Scalar.critical`, `OAI.ReusedScalar205.CubicTorus.Scalar.density`, `OAI.ReusedScalar205.CubicTorus.Scalar.fluxArgument`, `OAI.ReusedScalar205.CubicTorus.Scalar.planarProfile`, `OAI.ReusedScalar205.CubicTorus.Scalar.rho`, `OAI.ReusedScalar205.CubicTorus.Scalar.rhoChord`, `OAI.ReusedScalar205.CubicTorus.Scalar.rhoDen`, `OAI.ReusedScalar205.CubicTorus.Scalar.rhoRoot`, `OAI.ReusedScalar205.CubicTorus.Scalar.rhoSlope`, `OAI.ReusedScalar205.CubicTorus.Scalar.sectionLength`, `OAI.ReusedScalar205.CubicTorus.Shape.dm`, `OAI.ReusedScalar205.CubicTorus.Shape.t`, `OAI.ReusedScalar205.CubicTorus.Shape.u`.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry, in whole or in part: [`CubicTorus_Profiles_AtanPoly`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/AtanPoly.lean), [`CubicTorus_Profiles_GainBounds`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/GainBounds.lean), [`CubicTorus_Profiles_NestingBaseline`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/NestingBaseline.lean), [`CubicTorus_Profiles_PlanarProfile`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/PlanarProfile.lean), [`CubicTorus_Profiles_ProfileBounds`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/ProfileBounds.lean), [`CubicTorus_Profiles_ValueEnclosures289To507`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/ValueEnclosures289To507.lean), [`CubicTorus_Profiles_ValueEnclosures3143To3335`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/ValueEnclosures3143To3335.lean), [`CubicTorus_Profiles_ValueEnclosures726To944`](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/CubicTorus/Profiles/ValueEnclosures726To944.lean).
--
--   **Imports.** It imports no bundle or statement, only Mathlib.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ079A003`; the statement `OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_sectionLength_corrected`; the proof of `OAI.ReusedScalar205.CubicTorus.Scalar.concaveOn_sectionLength_corrected`.
-- source:
--   OpenAI, The isoperimetric conjecture for the cubic flat three-torus (result family 354), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 354; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry at commit 1581d4c

import Mathlib

section
-- module Solutions.OAIQ079_CT.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434

/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- The first projection of a probability measure on a product: found by instance search in d13f23b
(total `Measure.map`), here a measurable map. -/
instance isProbabilityMeasure_map_fst {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.fst) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
instance isProbabilityMeasure_map_snd {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : MeasureTheory.Measure (α × β)} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Prod.snd) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
instance isProbabilityMeasure_map_subtype_val {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ : MeasureTheory.Measure {a // p a}} [MeasureTheory.IsProbabilityMeasure μ] :
    MeasureTheory.IsProbabilityMeasure (μ.map Subtype.val) :=
  MeasureTheory.Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable
/-- Mathlib d13f23b's `YoungDiagram.card_transpose`. -/
@[simp]
theorem _root_.YoungDiagram.card_transpose (μ : YoungDiagram) : μ.transpose.card = μ.card := by
  unfold YoungDiagram.card
  apply Finset.card_bij (fun c _ => c.swap)
  · intro c hc
    have : c ∈ μ.transpose := hc
    rw [YoungDiagram.mem_transpose] at this
    exact this
  · intro a _ b _ h
    simpa using h
  · intro b hb
    refine ⟨b.swap, ?_, by simp⟩
    show b.swap ∈ μ.transpose
    rw [YoungDiagram.mem_transpose]
    simpa using hb
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
/-- `simp` closes `2 ≤ ∞` in `WithTop ℕ∞` (the smoothness order) in Mathlib d13f23b; ours has the
lemma only for `1` and casts (AffineBernstein, `isSymmSndFDerivAt (by simp)`, 2026-10-26). -/
@[simp]
theorem ofNat_le_infty (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  ENat.LEInfty.out
section Y
instance closedSubmoduleNormedAddCommGroup {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedAddCommGroup K :=
  inferInstanceAs (NormedAddCommGroup K.toSubmodule)
instance closedSubmoduleNormedSpace {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : NormedSpace 𝕜 K :=
  inferInstanceAs (NormedSpace 𝕜 K.toSubmodule)
instance closedSubmoduleInner {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (K : ClosedSubmodule 𝕜 E) : InnerProductSpace 𝕜 K :=
  inferInstanceAs (InnerProductSpace 𝕜 K.toSubmodule)
end Y

/-- The underlying ⋆-subalgebra of a von Neumann algebra is norm closed, found by instance search in
d13f23b (Kadison similarity, oaiq-075). -/
instance vonNeumannToStarSubalgebraIsClosed {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (P : VonNeumannAlgebra H) : IsClosed (P.toStarSubalgebra : Set (H →L[ℂ] H)) := by
  have := Set.isClosed_centralizer (Set.centralizer (P.carrier))
  rw [P.centralizer_centralizer'] at this
  exact this
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingBaseline
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set
namespace CubicTorus

def phi (s : ℝ) : ℝ := s^2*(1-s)*(1+s)^2

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_AtanPoly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

namespace ReusedScalar205

noncomputable section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

def t (h : ℝ) : ℝ := 2 / (1 + Real.sqrt (1 + 4 * h ^ 2 / Real.pi))
def dm : ℝ := 21 / 100
def u (h : ℝ) : ℝ := min (1 - 1 / Real.pi) ((24 / 25 : ℝ) / h)

end CubicTorus.Shape
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_PlanarProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set MeasureTheory
open _root_.OAI.ReusedScalar205.CubicTorus.Shape

def planarProfile (v : ℝ) : ℝ :=
  min (Real.sqrt (Real.pi * v)) (min 1 (Real.sqrt (Real.pi * (1 - v))))

def P (h : ℝ) : ℝ := u h - 1 + 2 * h * t h / Real.pi

def Q (h : ℝ) : ℝ := 2 / Real.pi * Real.sqrt (Real.pi + 2 * h ^ 2 * t h)

def C₀ (h : ℝ) : ℝ := min ((67 / 500 : ℝ) * h ^ 3) (9 / 25)

def cappedEnergy (l a d p q y : ℝ) : ℝ :=
  l * y ^ 2 + a * min d (max (p - q * y) 0) ^ 3

def cappedInf (l a d p q : ℝ) : ℝ :=
  sInf ((cappedEnergy l a d p q) '' Ici 0)

def critical (l a p q : ℝ) : ℝ :=
  2 * p / (1 + Real.sqrt (1 + 6 * a * q ^ 2 * p / l))

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Shape

def rho (k : ℝ) : ℝ :=
  Real.sqrt Real.pi * k * Real.sqrt (1 + (Real.pi / 4) * k ^ 2) - (Real.pi / 2) * k ^ 2

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Shape

def fluxArgument (h v : ℝ) : ℝ := h * v / planarProfile v

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Shape

def density (X : ℝ) : ℝ := X * (48 - 49 * X ^ 2) / (50 * Real.sqrt (1 - X ^ 2) ^ 3)

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory Filter _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

def rhoRoot (k : ℝ) : ℝ := Real.sqrt (Real.pi * k ^ 2 + 4)
def rhoDen (k : ℝ) : ℝ := rhoRoot k + Real.sqrt Real.pi * k
def rhoSlope (k : ℝ) : ℝ := 8 * Real.sqrt Real.pi / (rhoRoot k * rhoDen k ^ 2)

end CubicTorus.Scalar
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ProfileBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

def sectionLength (X h : ℝ) : ℝ :=
  min (Real.pi * (X / h) ^ 2) (min (X / h) (rho (X / h)))

open MeasureTheory

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set Filter _root_.OAI.ReusedScalar205.CubicTorus.Shape
open scoped Topology

def R (h : ℝ) : ℝ := 2 * h * t h / Real.pi

def RSlope (h : ℝ) : ℝ := 2 * t h ^ 2 / (Real.pi * (2 - t h))

def QRad (h : ℝ) : ℝ := Real.pi + 4 * h ^ 2

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_GainBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Shape

def beta (x : ℝ) : ℝ := Real.sqrt (1 - x ^ 2)
def J₁ (x : ℝ) : ℝ := (51 / 100 : ℝ) * Real.arcsin x - (49 / 100 : ℝ) * x * beta x - x / (50 * beta x)
def J₂ (x : ℝ) : ℝ := (49 / 50 : ℝ) * (2 / 3 - beta x + beta x ^ 3 / 3) -
  (x ^ 2 / beta x - 2 + 2 * beta x) / 50

end CubicTorus.Scalar

namespace CubicTorus.Scalar
open Set MeasureTheory _root_.OAI.ReusedScalar205.CubicTorus.Shape

def rhoChord (h a b x : ℝ) : ℝ :=
  ((b - x) * rho (a / h) + (x - a) * rho (b / h)) / (b - a)

end CubicTorus.Scalar

end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures289To507
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e337 : ℝ := (21 / 25 : ℝ)

def e342 : ℝ := e337 ^ 2

def e484 : ℝ := (23 / 25 : ℝ)

def e489 : ℝ := e484 ^ 2

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures726To944
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e777 : ℝ := (51 / 50 : ℝ)

def e782 : ℝ := e777 ^ 2

def e938 : ℝ := e777 ^ 3

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_ValueEnclosures3143To3335
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace ReusedScalar205
noncomputable section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Scalar.Cert
open _root_.OAI.ReusedScalar205.CubicTorus.Shape

def e3189 : ℝ := (17 / 10 : ℝ)

def e3193 : ℝ := e3189 ^ 2

def e3238 : ℝ := (19 / 10 : ℝ)

def e3242 : ℝ := e3238 ^ 2

def e3287 : ℝ := (9 / 4 : ℝ)

def e3291 : ℝ := e3287 ^ 2

end CubicTorus.Scalar.Cert
end
end
end
end ReusedScalar205
end
end

end OAI
end


