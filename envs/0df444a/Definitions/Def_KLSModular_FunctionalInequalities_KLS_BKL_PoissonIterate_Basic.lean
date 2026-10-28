-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
-- name    : KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T17:13:43.64682+00:00
-- url     : https://prove2.me/theorems/d0bc548e-fc90-4f87-b06a-cf2208a1d375
-- title:
--   Poisson iterates and tensor-field energies
-- statement:
--   For a probability measure $ν$ on a finite-dimensional real inner-product space and a linear partial map $T:L^2(ν)\to L^2(ν;V)$, `Field ν k` is the family of $L^2(ν)$ components indexed by $k$ tensor slots, and `normSq` is their squared Hilbert–Schmidt norm. The bundle defines totalized weak gradients, generators, centered inverses, componentwise gradients and iterates, together with `energy`, `meanGradSq`, `defect`, permutation and symmetrization operations, scaling, and Taylor coefficient fields; domain-dependent operators return $0$ outside their domains.
--
--   **Original module imports**
--
--   ```lean
--   import FunctionalInequalities.KLS.LogConcave.HeatSemigroup.Inverse
--   import FunctionalInequalities.Analysis.BakryEmery.Tilt.Basic
--   import FunctionalInequalities.Analysis.Tensor.Coefficients
--   import FunctionalInequalities.Analysis.Tensor.Symmetrization
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   abbrev Field (ν : ProbabilityMeasure V) (k : ℕ) : Type _ :=
--     (Fin k → Fin (Module.finrank ℝ V)) → Lp ℝ 2 (ν : Measure V)
--   ```
--
--   **Module navigation**
--
--   Direct project imports: [`KLS/LogConcave/HeatSemigroup/Inverse`](https://prove2.me/theorems/fb0b02c9-17f0-4cad-9390-4ccd11bc29f3), [`Analysis/BakryEmery/Tilt/Basic`](https://prove2.me/theorems/5a944547-1394-433f-9c0c-8efcf1f0d48a), [`Analysis/Tensor/Coefficients`](https://prove2.me/theorems/88ad50f9-51e6-4e95-905e-5bcdc077739f), [`Analysis/Tensor/Symmetrization`](https://prove2.me/theorems/8547f114-355c-49be-8989-b3003d84814f).
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Basic.lean) · `FunctionalInequalities.KLS.BKL.PoissonIterate.Basic` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/PoissonIterate/Basic.lean#L42-L133 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.PoissonIterate.Basic`, definition bundle `KLSModular_FunctionalInequalities_KLS_BKL_PoissonIterate_Basic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_HeatSemigroup_Inverse
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Tilt_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Coefficients
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Tensor_Symmetrization

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis.Semigroup FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace Classical
namespace FunctionalInequalities
namespace KLS
namespace LogConcave
namespace PoissonIterate
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
/-- A tensor field with `k` indices over `Fin (finrank ℝ V)`, as the family of its components in
`L²(ν)`. -/
abbrev Field (ν : ProbabilityMeasure V) (k : ℕ) : Type _ :=
  (Fin k → Fin (Module.finrank ℝ V)) → Lp ℝ 2 (ν : Measure V)
variable {ν : ProbabilityMeasure V} (T : Lp ℝ 2 (ν : Measure V) →ₗ.[ℝ] Lp V 2 (ν : Measure V))
/-- The squared Hilbert–Schmidt `L²` norm `Σ_I ‖u_I‖²` of a tensor field. -/
def normSq {k : ℕ} (u : Field ν k) : ℝ :=
  ∑ I, ‖u I‖ ^ 2
/-- The gradient `T u` on the domain of `T`, and `0` elsewhere. -/
def weakGrad (u : Lp ℝ 2 (ν : Measure V)) : Lp V 2 (ν : Measure V) :=
  if h : u ∈ T.domain then T ⟨u, h⟩ else 0
/-- The generator `T†T u` (`= -ℒ u` in the heat model) on its domain, and `0` elsewhere. -/
def gen (u : Lp ℝ 2 (ν : Measure V)) : Lp ℝ 2 (ν : Measure V) :=
  if h : u ∈ (adjointComp T).domain then adjointComp T ⟨u, h⟩ else 0
/-- The weak partial derivative `∂_j u = ⟪e_j, T u⟫` in the standard orthonormal basis. -/
def partialDeriv (j : Fin (Module.finrank ℝ V)) (u : Lp ℝ 2 (ν : Measure V)) :
    Lp ℝ 2 (ν : Measure V) :=
  (innerSL ℝ (stdOrthonormalBasis ℝ V j)).compLp (weakGrad T u)
/-- The centered inverse `(-L)⁻¹ g`: the centered `u ∈ D(T†T)` with `T†T u = g` when one exists
(it is unique when `T` is the closed heat-model gradient), and `0` otherwise. -/
def centeredInv (g : Lp ℝ 2 (ν : Measure V)) : Lp ℝ 2 (ν : Measure V) :=
  if h : ∃ u : (adjointComp T).domain,
      L2.mean ν (u : Lp ℝ 2 (ν : Measure V)) = 0 ∧ adjointComp T u = g then
    (h.choose : Lp ℝ 2 (ν : Measure V))
  else 0
/-- The gradient `∇u` of a tensor field: a new first index. -/
def gradField {k : ℕ} (u : Field ν k) : Field ν (k + 1) :=
  fun J => partialDeriv T (J 0) (u (Fin.tail J))
/-- The centered gradient `∇₀u = ∇u - ∫ ∇u dν` (BKL (22)), componentwise. -/
def grad0 {k : ℕ} (u : Field ν k) : Field ν (k + 1) :=
  fun J => L2.center ν (gradField T u J)
/-- The generator applied componentwise, `-L u`. -/
def genField {k : ℕ} (u : Field ν k) : Field ν k :=
  fun I => gen T (u I)
/-- The centered inverse applied componentwise, `(-L)⁻¹ g`. -/
def invField {k : ℕ} (g : Field ν k) : Field ν k :=
  fun I => centeredInv T (g I)
/-- The normalizing coefficient `α` of BKL (31) for the step from `h`:
`‖∇₀h‖ / ‖∇(-L)⁻¹∇₀h‖`, and `0` when the denominator vanishes (in particular when `∇₀h = 0`,
the source's linear case). -/
def scale {k : ℕ} (h : Field ν k) : ℝ :=
  if normSq (gradField T (invField T (grad0 T h))) = 0 then 0
  else Real.sqrt (normSq (grad0 T h) / normSq (gradField T (invField T (grad0 T h))))
/-- One step of BKL (30): `h ↦ α (-L)⁻¹ ∇₀ h`. -/
def step {k : ℕ} (h : Field ν k) : Field ν (k + 1) :=
  scale T h • invField T (grad0 T h)
/-- The iterates: `iter T f k` is the source's `h_{k+1}`, with `h₁ = f`. -/
def iter (f : Lp ℝ 2 (ν : Measure V)) : (k : ℕ) → Field ν k
  | 0 => fun _ => f
  | k + 1 => step T (iter f k)
/-- The Dirichlet energy `v = ‖∇h‖²` (BKL (34)). -/
def energy {k : ℕ} (h : Field ν k) : ℝ :=
  normSq (gradField T h)
/-- The energy drop `p = |∫ ∇h dν|²` (BKL (35)), as the sum of the squared means of the
components of `∇h`. -/
def meanGradSq {k : ℕ} (h : Field ν k) : ℝ :=
  ∑ J, L2.mean ν (gradField T h J) ^ 2
/-- The defect `χ = ‖∇²h - α ∇h'‖²` of BKL (37) for `h' = step h` and `α = scale h`. -/
def defect {k : ℕ} (h : Field ν k) : ℝ :=
  normSq (gradField T (gradField T h) - scale T h • gradField T (step T h))
/-- Permuting the index positions of a tensor field: `(permField σ u) I = u (I ∘ σ)`. -/
def permField {k : ℕ} (σ : Equiv.Perm (Fin k)) (u : Field ν k) : Field ν k :=
  fun I => u (I ∘ σ)
/-- `S_q u`: the average of `u` over the permutations of its first `q` index positions. -/
def symField {k : ℕ} (q : ℕ) (u : Field ν k) : Field ν k :=
  ((fixingOutside (slots k 0 q)).card : ℝ)⁻¹ •
    ∑ σ ∈ fixingOutside (slots k 0 q), permField σ u
/-- The Taylor coefficient array `T_d u` of a tensor field (BKL (28), componentwise): the `d`
Taylor indices come first, followed by the `k` indices of `u`; the norm is Hilbert–Schmidt. -/
def taylorField (d : ℕ) {k : ℕ} (u : Field ν k) : Coord (Module.finrank ℝ V) (d + k) :=
  WithLp.toLp 2 fun J =>
    taylorTensor (ν : Measure V) (⇑(u fun i => J (Fin.natAdd d i))) d
      (fun i => stdOrthonormalBasis ℝ V (J (Fin.castAdd k i)))
end PoissonIterate
end LogConcave
end KLS
end FunctionalInequalities


