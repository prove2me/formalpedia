-- Prove2me | Definitions.Def_HunterPDE_Regularity_Sobolev
-- name    : HunterPDE_Regularity_Sobolev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T19:11:40.382911+00:00
-- url     : https://prove2.me/theorems/0fc31269-e09d-4047-b5c5-e51200dd020e
-- title:
--   Sobolev spaces W^{k,p}(Ω), their norm and W^{k,p}_0(Ω) (Definition 3.23)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, $k \in \mathbb{N}$ and $1 \le p \le \infty$. The **Sobolev space** $W^{k,p}(\Omega)$ consists of the functions $f \in L^1_{\mathrm{loc}}(\Omega)$ whose weak derivatives $\partial^\alpha f$ exist for every multi-index with $|\alpha| \le k$ and belong to $L^p(\Omega)$. Its norm is
--   $$\|f\|_{W^{k,p}(\Omega)} = \Big(\sum_{|\alpha| \le k} \int_\Omega |\partial^\alpha f|^p \, dx\Big)^{1/p} \quad (p < \infty), \qquad \|f\|_{W^{k,\infty}(\Omega)} = \max_{|\alpha|\le k} \operatorname*{ess\,sup}_\Omega |\partial^\alpha f|.$$
--   We write $H^k(\Omega) = W^{k,2}(\Omega)$. The space $W^{k,p}_0(\Omega)$ is the closure of $C_c^\infty(\Omega)$ in $W^{k,p}(\Omega)$; in particular $H^1_0(\Omega) = W^{1,2}_0(\Omega)$.
--
--   **Formalization Note.** Membership is the predicate `MemW k p Ω f` on functions $\mathbb{R}^n \to \mathbb{R}$ (with `p : ℝ≥0∞`); the norm `sobolevNorm k p Ω f` takes values in `ℝ≥0∞` and is meaningful only when `MemW k p Ω f` holds, which every statement assumes. `MemW0 k p Ω f` says $f \in W^{k,p}(\Omega)$ and $f$ is a $W^{k,p}(\Omega)$-norm limit of test functions. This module is identical, up to the namespace, to the one of mission IV of this series (without the Sobolev conjugate).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 58, Definition 3.23; p. 59 (W^{k,p}_0)

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- The finite set of multi-indices `α ∈ ℕⁿ` of order `|α| = ∑ i, α i ≤ k`. -/
def multiIndicesLe (n k : ℕ) : Finset (Fin n → ℕ) :=
  (Fintype.piFinset (fun _ : Fin n => Finset.range (k + 1))).filter (fun α => ∑ i, α i ≤ k)

/-- Definition 3.23 of Hunter, *Notes on PDEs*: `f ∈ W^{k,p}(Ω)`. For every multi-index `α` with
`|α| ≤ k` the weak derivative `∂^α f` exists on `Ω` (in particular `f` is locally integrable on
`Ω`) and lies in `Lᵖ(Ω)`. Here `p : ℝ≥0∞`; the book allows `1 ≤ p ≤ ∞`, and each theorem states
its own range of `p`. -/
def MemW {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ α ∈ multiIndicesLe n k, ∃ g, Shared.HasWeakDeriv Ω α f g ∧ MemLp g p (volume.restrict Ω)

/-- The Sobolev norm of Definition 3.23, with values in `ℝ≥0∞`:
`‖f‖_{W^{k,p}(Ω)} = (∑_{|α| ≤ k} ∫_Ω |∂^α f|ᵖ dx)^{1/p}` for `p < ∞`, and
`‖f‖_{W^{k,∞}(Ω)} = max_{|α| ≤ k} ess sup_Ω |∂^α f|` for `p = ∞`. The weak derivatives are the
chosen representatives `weakDeriv`; the norm is meaningful only for `f ∈ W^{k,p}(Ω)`
(`MemW k p Ω f`), and every statement using it assumes that. -/
noncomputable def sobolevNorm {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : ℝ≥0∞ :=
  if p = ∞ then
    (multiIndicesLe n k).sup (fun α => eLpNorm (Shared.weakDeriv Ω α f) ∞ (volume.restrict Ω))
  else
    (∑ α ∈ multiIndicesLe n k, eLpNorm (Shared.weakDeriv Ω α f) p (volume.restrict Ω) ^ p.toReal)
      ^ (1 / p.toReal)

/-- `f ∈ W^{k,p}_0(Ω)`: the closure of `C_c^∞(Ω)` in `W^{k,p}(Ω)` (Hunter p. 59; for `k = 1`,
`p = 2` this is `H¹₀(Ω)`). `f ∈ W^{k,p}(Ω)` and for every `ε > 0` there is `φ ∈ C_c^∞(Ω)` with `‖f − φ‖_{W^{k,p}(Ω)} < ε`. -/
def MemW0 {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  MemW k p Ω f ∧ ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ, Shared.IsTestFunction Ω φ ∧ sobolevNorm k p Ω (f - φ) < ε

end HunterPDE.Regularity


