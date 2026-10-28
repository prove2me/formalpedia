-- Prove2me | Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
-- name    : KLSModular_FunctionalInequalities_Analysis_Convex_Legendre
-- status  : Definition
-- author  : @Lazyfill
-- created : 2026-10-25T16:49:18.739524+00:00
-- url     : https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81
-- title:
--   Extended-real convex potentials and Legendre transforms
-- statement:
--   For a real inner-product space $E$ and $\varphi:E\to\overline{\mathbb{R}}$, `ConvexPotential φ` means that $\varphi$ never equals $-\infty$ and that its real epigraph is convex, while `ProperPotential φ` additionally requires at least one finite value. `legendre φ y` is the extended-real supremum $\sup_x(\langle x,y\rangle-\varphi(x))$, and `lowerTruncate φ M` is $\max(\varphi(x),-M)$ pointwise; the module includes order, convexity, semicontinuity, and truncation auxiliary results.
--
--   **Original module imports**
--
--   ```lean
--   import Mathlib.Analysis.Convex.Topology
--   import Mathlib.Analysis.InnerProductSpace.Continuous
--   import Mathlib.Data.EReal.Operations
--   import Mathlib.Topology.Semicontinuity.Basic
--   import Mathlib.Topology.Instances.EReal.Lemmas
--   import Mathlib.Analysis.Normed.Module.Convex
--   ```
--
--   **Original declaration excerpt**
--
--   Shown in the original module context.
--
--   ```lean
--   def ConvexPotential (φ : E → EReal) : Prop :=
--     (∀ x, φ x ≠ ⊥) ∧ Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}
--   ```
--
--   **Module navigation**
--
--   Theorems in source order:
--
--   - [`convex_epigraph_legendre`](https://prove2.me/theorems/ae6b66c7-c45b-4b02-ba8a-8dcdbef9e183)
--   - [`legendre_ne_bot_iff`](https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1)
--   - [`lowerTruncate_convexification`](https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6)
--   - [`legendre_eq_interior_sup`](https://prove2.me/theorems/fb27a67d-8a39-4dbc-904c-e8977c7bb3af)
--   - [`legendre_norm`](https://prove2.me/theorems/7eb3b3f3-e05d-4ad0-a70e-b08de926b3ea)
--
--   Project result: [The KLS conjecture](https://prove2.me/theorems/c4e9e57c-586c-4945-927e-7f33933f1111).
--
--   [Original module](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean) · `FunctionalInequalities.Analysis.Convex.Legendre` · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L35-L105 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, definition bundle `KLSModular_FunctionalInequalities_Analysis_Convex_Legendre`; the repository is private at upload time).

import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Analysis.Normed.Module.Convex

noncomputable section
namespace FunctionalInequalities
namespace Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Convexity of an extended-real potential, expressed through its real epigraph. -/
def ConvexPotential (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}
/-- The actual extended-real Legendre transform; no selected maximizers are assumed. -/
def legendre (φ : E → EReal) (y : E) : EReal :=
  ⨆ x : E, (inner ℝ x y : EReal) - φ x
/-- A finite-value witness as well as exclusion of `-∞`, rather than a desired conclusion. -/
def ProperPotential (φ : E → EReal) : Prop :=
  (∀ x, φ x ≠ ⊥) ∧ ∃ x, φ x ≠ ⊤
/-- The actual lower truncation in CEK equation (61). -/
def lowerTruncate (φ : E → EReal) (M : ℝ) : E → EReal :=
  fun x => max (φ x) ((-M : ℝ) : EReal)
end Analysis
end FunctionalInequalities


