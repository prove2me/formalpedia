-- Prove2me | Definitions.Def_MultiwayCut_Transformation
-- name    : MultiwayCut_Transformation
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T21:14:08.426578+00:00
-- url     : https://prove2.me/theorems/541a6bed-086e-41c2-a771-238aa9878a0f
-- title:
--   Feasible transformations, the quadratic transformation (5.1), the conditions of Lemma 5.1 and the order $\succeq$
-- statement:
--   1. **Feasible transformation** (Definition 3.1, p.5). $f:\Delta_k\to[0,1]^k$ is feasible if $f(e_i)=e_i$ for every $i$, and for every $\mathbf u\in\Delta_k$ with $u_{\pi(1)}\ge\dots\ge u_{\pi(k)}$ for some permutation $\pi$, also $f_{\pi(1)}(\mathbf u)\ge\dots\ge f_{\pi(k)}(\mathbf u)$.
--   2. **The vector $\mathbf u^\ell$** (§5, p.6). For sorted $u_1\ge\dots\ge u_k$, $\mathbf u^\ell=(u_\ell,\dots,u_\ell,u_{\ell+1},\dots,u_k)$, the first $\ell$ coordinates equal to $u_\ell$.
--   3. **The transformation (5.1)** (p.6). For a symmetric $A\in\mathbb R^{k\times k}$,
--   $$f_\ell(\mathbf u)=(\mathbf u^\ell)^{T}A\,\mathbf u^\ell,\qquad \ell=1,\dots,k,$$
--   for sorted $\mathbf u$; for general $\mathbf u$ the coordinates are sorted non-increasingly, transformed by position, and put back (§3.1, p.5; §4, p.6).
--   4. **Conditions of Lemma 5.1** (pp.6–7): $a_{11}=1$ and $a_{ij}\le1$; $\sum_{i=1}^\ell\sum_{j=1}^\ell a_{ij}\ge0$ for all $\ell$; $\sum_{i=1}^\ell\sum_{j=\ell+1}^r a_{ij}\ge0$ for all $\ell<r$.
--   5. **The order $\succeq$** (Definition 5.1, p.7): $\mathbf a\succeq\mathbf b$ if $\sum_{j=1}^\ell a_j\ge\sum_{j=1}^\ell b_j$ for every $\ell$.
--
--   These are the objects of §5, in which the 297/229 algorithm is built.
--
--   **Formalization Note** 0-based: `flat s ℓ` is the paper's $\mathbf u^{\ell+1}$ (so `flat s 0 = s`). The sorting permutation is Mathlib's `Tuple.sort` applied to $-\mathbf u$; the value of the transformation does not depend on how ties are sorted, since equal consecutive sorted values give equal flattened vectors (checked in a verification file). Symmetry of $A$ is a separate hypothesis where the paper requires it.
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Definition 3.1, p.5; §5, (5.1), p.6; Lemma 5.1, pp.6–7; Definition 5.1, p.7

import Mathlib

open Matrix

namespace MultiwayCut

variable {k : ℕ}

/-- **Feasible transformation**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and
the Multiway Cut Problem*, manuscript of Nov. 1, 2016, Definition 3.1, p.5: `f : Δ_k → [0, 1]ᵏ`
is feasible if (1) `f(eᵢ) = eᵢ` for every `i`, and (2) for every `u ∈ Δ_k` with
`u_{π(1)} ≥ … ≥ u_{π(k)}` for some permutation `π`: `f_{π(1)}(u) ≥ … ≥ f_{π(k)}(u)`.

**Formalization Note.** `f` is a function on `ℝᵏ`; only its values on `Δ_k` matter. The
codomain `[0, 1]ᵏ` of the paper's `f : Δ_k → [0, 1]ᵏ` is the first clause. -/
def IsFeasibleTransform (f : (Fin k → ℝ) → Fin k → ℝ) : Prop :=
  (∀ u ∈ stdSimplex ℝ (Fin k), ∀ ℓ, f u ℓ ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ i : Fin k, f (Pi.single i 1) = Pi.single i 1) ∧
    (∀ u ∈ stdSimplex ℝ (Fin k), ∀ π : Equiv.Perm (Fin k),
      Antitone (u ∘ π) → Antitone (f u ∘ π))

/-- A permutation sorting `u` non-increasingly: `u ∘ sortPerm u` is antitone (Mathlib's
`Tuple.sort` sorts `-u` increasingly). -/
noncomputable def sortPerm (u : Fin k → ℝ) : Equiv.Perm (Fin k) :=
  Tuple.sort (-u)

/-- **The vector `u^ℓ`**, manuscript of Nov. 1, 2016, §5, p.6: for a sorted `u`, the vector
obtained by replacing the first `ℓ − 1` coordinates with the value `u_ℓ`,
`u^ℓ = (u_ℓ, …, u_ℓ, u_{ℓ+1}, …, u_k)` (`ℓ` times `u_ℓ`).

**Formalization Note.** 0-based: `flat s ℓ m = s ℓ` for `m < ℓ` and `s m` otherwise, so
`flat s ℓ` is the paper's `u^{ℓ+1}`; `flat s 0 = s` is the paper's `u¹ = u`. -/
def flat (s : Fin k → ℝ) (ℓ : Fin k) : Fin k → ℝ :=
  fun m => if m < ℓ then s ℓ else s m

/-- **The transformation (5.1)**, manuscript of Nov. 1, 2016, §5, p.6 (with §3.1, p.5, and §4,
p.6): `f_ℓ(u) = (u^ℓ)ᵀ A u^ℓ` for sorted `u`, `f(u) = (f₁(u), …, f_k(u))`. For an unsorted `u`
the coordinates are first sorted non-increasingly, each sorted position `ℓ` gets
`(u^ℓ)ᵀ A u^ℓ`, and the values are placed back at the original coordinates.

**Formalization Note.** With `π = sortPerm u` and `s = u ∘ π`, coordinate `m` receives the
value of sorted position `ℓ = π⁻¹ m`: `f u m = (flat s ℓ) ⬝ᵥ (A *ᵥ flat s ℓ)`. The value does
not depend on how ties are sorted: if `s ℓ = s (ℓ + 1)` then `flat s ℓ = flat s (ℓ + 1)`. -/
noncomputable def quadTransform (A : Matrix (Fin k) (Fin k) ℝ) (u : Fin k → ℝ) : Fin k → ℝ :=
  fun m =>
    flat (u ∘ sortPerm u) ((sortPerm u).symm m) ⬝ᵥ
      (A *ᵥ flat (u ∘ sortPerm u) ((sortPerm u).symm m))

/-- **The conditions of Lemma 5.1**, manuscript of Nov. 1, 2016, pp.6–7, on `A ∈ ℝ^{k×k}`:
1. `a₁₁ = 1` and `a_ij ≤ 1` for every `i, j`;
2. `Σ_{i=1}^ℓ Σ_{j=1}^ℓ a_ij ≥ 0` for every `ℓ = 1, …, k`;
3. `Σ_{i=1}^ℓ Σ_{j=ℓ+1}^r a_ij ≥ 0` for every `ℓ = 1, …, k` and `r = ℓ + 1, …, k`.

**Formalization Note.** 0-based: `a₁₁` is `A 0 0`, `i ≤ ℓ` ranges over `Finset.Iic ℓ` and
`ℓ < j ≤ r` over `Finset.Ioc ℓ r`. Symmetry of `A` is a separate hypothesis of Lemma 5.1. -/
def Lemma51Conditions [NeZero k] (A : Matrix (Fin k) (Fin k) ℝ) : Prop :=
  (A 0 0 = 1 ∧ ∀ i j, A i j ≤ 1) ∧
    (∀ ℓ : Fin k, 0 ≤ ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Iic ℓ, A i j) ∧
    (∀ ℓ r : Fin k, ℓ < r → 0 ≤ ∑ i ∈ Finset.Iic ℓ, ∑ j ∈ Finset.Ioc ℓ r, A i j)

/-- **The order `⪰`**, manuscript of Nov. 1, 2016, Definition 5.1, p.7: for `a, b ∈ ℝᵏ`,
`a ⪰ b` if `Σ_{j=1}^ℓ a_j ≥ Σ_{j=1}^ℓ b_j` for all `ℓ = 1, …, k` (0-based prefixes `Iic ℓ`). -/
def PrefixGe (a b : Fin k → ℝ) : Prop :=
  ∀ ℓ : Fin k, ∑ j ∈ Finset.Iic ℓ, b j ≤ ∑ j ∈ Finset.Iic ℓ, a j

end MultiwayCut


