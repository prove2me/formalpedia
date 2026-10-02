-- Prove2me | Definitions.Def_HunterPDE_Compactness_Sobolev
-- name    : HunterPDE_Compactness_Sobolev
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T07:39:51.173979+00:00
-- url     : https://prove2.me/theorems/f577ce53-e9a7-4b89-bb1e-6914656d8e8c
-- title:
--   Sobolev spaces W^{k,p}(Ω), their norm, W^{k,p}_0(Ω) and the Sobolev conjugate (Definitions 3.23, 3.25, 3.43)
-- statement:
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, $k \in \mathbb{N}$ and $1 \le p \le \infty$. The **Sobolev space** $W^{k,p}(\Omega)$ consists of the locally integrable $f$ whose weak derivatives $\partial^\alpha f$ exist and lie in $L^p(\Omega)$ for $0 \le |\alpha| \le k$. Its norm is
--   $$\|f\|_{W^{k,p}(\Omega)} = \Big(\sum_{|\alpha| \le k} \int_\Omega |\partial^\alpha f|^p \, dx\Big)^{1/p} \quad (1 \le p < \infty), \qquad \|f\|_{W^{k,\infty}(\Omega)} = \max_{|\alpha| \le k} \operatorname*{ess\,sup}_\Omega |\partial^\alpha f|.$$
--   The space $W^{k,p}_0(\Omega)$ is the closure of $C_c^\infty(\Omega)$ in $W^{k,p}(\Omega)$: $f \in W^{k,p}(\Omega)$ and for every $\varepsilon > 0$ there is $\phi \in C_c^\infty(\Omega)$ with $\|f - \phi\|_{W^{k,p}(\Omega)} < \varepsilon$. For $1 \le p < n$ the **Sobolev conjugate** is $p^* = np/(n - p)$.
--
--   **Formalization Note.** `MemW k p Ω f` is the membership predicate. `sobolevNorm` takes values in $[0, \infty]$ and is computed from the chosen weak-derivative representatives, so it is meaningful only for $f \in W^{k,p}(\Omega)$, and every statement that uses it assumes this. `MemW0` follows Definition 3.43, which the notes state for the half-space; §3.10 uses it on a general open $\Omega$. It is the norm closure of test functions, not "zero trace". `sobolevConjugate n p` is used only when $p < n$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 58, Definition 3.23; p. 60, Definition 3.25; p. 72, Definition 3.43

import Mathlib
import Definitions.Def_HunterPDE_Shared_WeakDeriv

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Compactness

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

/-- `f ∈ W^{k,p}_0(Ω)`: the closure of `C_c^∞(Ω)` in `W^{k,p}(Ω)` (Definition 3.43 for the
half-space, used on a general open set `Ω` in §3.10–3.11). `f ∈ W^{k,p}(Ω)` and for every
`ε > 0` there is `φ ∈ C_c^∞(Ω)` with `‖f − φ‖_{W^{k,p}(Ω)} < ε`. -/
def MemW0 {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  MemW k p Ω f ∧ ∀ ε : ℝ≥0∞, 0 < ε →
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ, Shared.IsTestFunction Ω φ ∧ sobolevNorm k p Ω (f - φ) < ε

/-- Definition 3.25: for `1 ≤ p < n`, the Sobolev conjugate `p* = np/(n − p)` of `p`. Only used
under the hypothesis `p < n`, where the denominator is positive. -/
noncomputable def sobolevConjugate (n : ℕ) (p : ℝ) : ℝ :=
  (n : ℝ) * p / ((n : ℝ) - p)

end HunterPDE.Compactness


