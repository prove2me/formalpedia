-- Prove2me | Definitions.Def_DetANN_SignChoice
-- name    : DetANN_SignChoice
-- status  : Definition
-- author  : @milia
-- created : 2026-11-15T17:39:29.09953+00:00
-- url     : https://prove2.me/theorems/8218aee8-bf9c-46d9-b5dc-c21d7371c759
-- title:
--   Choosing the signs by conditional expectation (§6.3)
-- statement:
--   Signs are $\xi\in\{\pm1\}^{L\times d}$, with $\xi^{(\ell)}_r$ the $r$-th sign of repetition $\ell$, as in the definition `DetANN_SignedBlocks`.
--
--   1. A **partial assignment** is a mask $\mu$ (which signs are fixed) together with values $u$. Its **completions** are the sign assignments that agree with $u$ on the fixed signs. The **conditional expectation** of a function of the signs is its uniform average over all completions; in particular `condPotential` is the conditional expectation of the potential $\Phi$ of (24).
--   2. For a sequence $m$, $\mathrm{EGF}(m)=\sum_k m_k t^k/k!$ is its exponential generating function. The series of $e^{ct}$ and $\cosh(at)$ are $\mathrm{EGF}(c^k)$ and $\mathrm{EGF}(a^k[k\text{ even}])$.
--   3. The **Lemma 6.2 expression** is the explicit formula of the proof of Lemma 6.2:
--      - for each $(\ell,j,v)$, split $Y=\sum_r h_{jr}v_r\xi^{(\ell)}_r$ into its known part $c$ (fixed signs) and the coefficients $a_r$ of its free signs;
--      - read the moments of $Y$ off $e^{ct}\prod_r\cosh(a_rt)$, and those of $X=Y^2-\|v\|^2$ by the binomial formula;
--      - read the $2p_0$-th moment of $\sum_\ell X_\ell$ off the product of the generating functions of the $X_\ell$;
--      - divide by $(L\tau\|v\|^2)^{2p_0}$ and sum over $(j,v)$:
--   $$\sum_{v\in\mathcal D}\sum_{j}\frac{(2p_0)!}{(L\tau\|v\|^2)^{2p_0}}\,[t^{2p_0}]\prod_{\ell}\mathrm{EGF}\Bigl(k\mapsto\sum_{i\le k}\binom ki(-\|v\|^2)^{k-i}(2i)!\,[t^{2i}]\,e^{c_{\ell jv}t}\prod_r\cosh(a_{\ell jvr}t)\Bigr).$$
--   4. The **greedy assignment** exposes the signs in the order $(\ell,r)\mapsto\ell d+r$. At each step it fixes the next sign to `true` if that does not give a larger score than `false`, and to `false` otherwise.
--
--   These are the objects of Lemma 6.2 and of the deterministic construction in the proof of Theorem 3.2.
--
--   **Formalization Note.** Generating functions are formal power series over $\mathbb R$. `prefixMask L d k` is the mask after $k$ steps, and `setSignAt k b` sets the sign at position $k$ to $b$.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.3 and Lemma 6.2, pp.15–16, and the proof of Theorem 3.2, p.16

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN

/-!
# Choosing the signs by conditional expectation (§6.3, Lemma 6.2 and the proof of Theorem 3.2)

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §6.3, pp.15–16.

**Formalization Note.**
* A partial assignment of the signs `ξ : Fin L → Fin d → Bool` is a mask `μ` (`μ ℓ r = true` when
  `ξ^(ℓ)_r` is fixed) and values `u`. Its completions are `completeSigns μ u ξ'` for all `ξ'`, and the
  conditional expectation is the uniform average over all `ξ'`.
* Exponential generating functions are formal power series `∑ₖ mₖ tᵏ / k!` over `ℝ`.
* The signs are exposed in the order `(ℓ, r) ↦ ℓ·d + r`; after `k` steps the mask is `prefixMask`.
-/

/-- The uniform average of `f` over a finite type. -/
noncomputable def avgOver {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (Fintype.card Ω : ℝ)⁻¹ * ∑ ω, f ω

/-- The exponential generating function `∑ₖ mₖ tᵏ / k!` of a sequence `m`. -/
noncomputable def egf (m : ℕ → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => m k / (k.factorial : ℝ)

/-- The series of `e^{ct}`. -/
noncomputable def expSeries (c : ℝ) : PowerSeries ℝ := egf fun k => c ^ k

/-- The series of `cosh(at)`. -/
noncomputable def coshSeries (a : ℝ) : PowerSeries ℝ := egf fun k => if Even k then a ^ k else 0

/-- The completion of the partial assignment `(μ, u)` by `ξ`: fixed signs from `u`, the others
from `ξ`. -/
def completeSigns {L d : ℕ} (μ u ξ : Fin L → Fin d → Bool) : Fin L → Fin d → Bool :=
  fun ℓ r => if μ ℓ r then u ℓ r else ξ ℓ r

/-- The conditional expectation of the potential `Φ` (24) given the partial assignment `(μ, u)`. -/
noncomputable def condPotential {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ) (τ : ℝ) (p₀ : ℕ)
    (D : Finset (EuclideanSpace ℝ (Fin d))) (μ u : Fin L → Fin d → Bool) : ℝ :=
  avgOver fun ξ : Fin L → Fin d → Bool => potential h L (completeSigns μ u ξ) τ p₀ D

/-- The known part `c = ∑_{r fixed} h_{jr} v_r ξ^(ℓ)_r` of `Y_{ℓ,j,v} = ∑_r h_{jr} v_r ξ^(ℓ)_r`. -/
noncomputable def fixedPart {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ u : Fin L → Fin d → Bool)
    (j : Fin d) (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) : ℝ :=
  ∑ r, if μ ℓ r then h j r * v r * signOf (u ℓ r) else 0

/-- The coefficient `a_r` of a free sign in `Y_{ℓ,j,v}` (zero for fixed signs). -/
noncomputable def freeCoeff {L d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (μ : Fin L → Fin d → Bool)
    (j : Fin d) (v : EuclideanSpace ℝ (Fin d)) (ℓ : Fin L) (r : Fin d) : ℝ :=
  if μ ℓ r then 0 else h j r * v r

/-- The explicit expression of Lemma 6.2. For each `(ℓ, j, v)`:
* the moments of `Y = c + ∑ a_r σ_r` are read off `e^{ct} ∏_r cosh(a_r t)`;
* the moments of `X = Y² − r_v` follow by the binomial formula;
* the `2p₀`-th moment of `∑_ℓ X_ℓ` is read off the product of the generating functions of the `X_ℓ`.

Dividing by `(Lτ r_v)^{2p₀}` and summing over `(j, v)` gives the conditional expectation of `Φ`. -/
noncomputable def lemma62Expr {d : ℕ} (h : Matrix (Fin d) (Fin d) ℝ) (L : ℕ) (τ : ℝ) (p₀ : ℕ)
    (D : Finset (EuclideanSpace ℝ (Fin d))) (μ u : Fin L → Fin d → Bool) : ℝ :=
  ∑ v ∈ D, ∑ j : Fin d, (((L : ℝ) * τ * ‖v‖ ^ 2) ^ (2 * p₀))⁻¹ * ((2 * p₀).factorial : ℝ) *
    PowerSeries.coeff (2 * p₀) (∏ ℓ : Fin L, egf fun k =>
      ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * (-‖v‖ ^ 2) ^ (k - i) *
        ((2 * i).factorial : ℝ) * PowerSeries.coeff (2 * i)
          (expSeries (fixedPart h μ u j v ℓ) * ∏ r, coshSeries (freeCoeff h μ j v ℓ r)))

/-- The mask after the first `k` signs in the order `(ℓ, r) ↦ ℓ·d + r` have been fixed. -/
def prefixMask (L d k : ℕ) : Fin L → Fin d → Bool := fun ℓ r => decide ((ℓ : ℕ) * d + r < k)

/-- `ξ` with the sign at position `k` (in the order `(ℓ, r) ↦ ℓ·d + r`) set to `b`. -/
def setSignAt {L d : ℕ} (k : ℕ) (b : Bool) (ξ : Fin L → Fin d → Bool) : Fin L → Fin d → Bool :=
  fun ℓ r => if (ℓ : ℕ) * d + r = k then b else ξ ℓ r

/-- The greedy sign choice driven by a score `F μ u`: at step `k` the sign at position `k` is set to
`true` if that does not give a larger score than `false`, and to `false` otherwise. -/
noncomputable def greedySigns {L d : ℕ}
    (F : (Fin L → Fin d → Bool) → (Fin L → Fin d → Bool) → ℝ) : ℕ → Fin L → Fin d → Bool
  | 0 => fun _ _ => false
  | k + 1 =>
    if F (prefixMask L d (k + 1)) (setSignAt k true (greedySigns F k)) ≤
        F (prefixMask L d (k + 1)) (setSignAt k false (greedySigns F k))
    then setSignAt k true (greedySigns F k) else setSignAt k false (greedySigns F k)

end DetANN


