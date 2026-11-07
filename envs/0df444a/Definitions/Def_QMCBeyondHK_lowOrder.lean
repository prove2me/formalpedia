-- Prove2me | Definitions.Def_QMCBeyondHK_lowOrder
-- name    : QMCBeyondHK_lowOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:36:00.746287+00:00
-- url     : https://prove2.me/theorems/e16cf702-2b76-453a-8915-dc005b950372
-- title:
--   Low-order Haar functions $\Pi_{\le\ell}$, $N_\ell = (\ell+1)^d$, $\ell = \lceil 10\log_2 n\rceil$, and the projections $\Pi_{\le\ell} g$, $\Pi_{>\ell} g$
-- statement:
--   1. $\Pi_{\le\ell}$ is the finite collection of **non-constant** Haar functions $H_{j,k}$ with $j_i \le \ell$ for **every** $i \in [d]$ (non-constant means $j \ne 0$).
--   2. $N_\ell := (\ell+1)^d$, the number of scale vectors $j \in \{0,1,\dots,\ell\}^d$.
--   3. The algorithm's level is $\ell := \lceil 10 \log_2 n \rceil$.
--   4. The **low-order projection** of $g$ is
--   $$
--   \Pi_{\le\ell}\, g = \sum_{H \in \Pi_{\le\ell}} \frac{\langle g, H\rangle}{\|H\|_2^2}\, H .
--   $$
--   5. The **high-order projection** is $\Pi_{>\ell}\, g = g - \bar g - \Pi_{\le\ell}\, g$, the component of $g$ along the remaining non-constant Haar functions.
--
--   **Formalization Note** The paper writes $N_\ell$ both for $|\Pi_{\le\ell}|$ (§2) and for $(\ell+1)^d$ (§3.1); the value $(\ell+1)^d$ is the one used in (7), (8) and Lemma 3.4.1 and is the one defined here. $\log_2$ is `Real.logb 2` and the ceiling is `Nat.ceil`; for $n = 1$ this gives $\ell = 0$ and $\Pi_{\le 0} = \emptyset$. $\Pi_{>\ell} g$ is defined pointwise; since the Haar system is an orthogonal basis it is the orthogonal projection onto the span of the remaining non-constant Haar functions.
-- source:
--   Ezeunala, Jha, Jiang, Quasi-Monte Carlo Beyond Hardy–Krause II: (1 + ε)n Samples Suffice, arXiv:2609.10921 (sha256 bc273e88…), §2, p.6 (PDF p.8): Π≤ℓ, Π>ℓ; §3.1, p.8 (PDF p.10): ℓ := ⌈10 log2 n⌉, N_ℓ := (ℓ + 1)^d; §3.4.1, (13), p.14 (PDF p.16): Π≤ℓ g = ∑ c_H H

import Mathlib
import Definitions.Def_QMCBeyondHK_haar

set_option autoImplicit false

open MeasureTheory

namespace QMCBeyondHK

/-- Membership in `Π≤ℓ`: a non-constant Haar function `H_{j,k}` with `j_i ≤ ℓ` for every `i`
(arXiv:2609.10921, sha256 bc273e88…, §2, p.6, PDF p.8; footnote 8, p.12). -/
def IsLowOrder {d : ℕ} (ℓ : ℕ) (H : HaarIdx d) : Prop := (∃ i, H.j i ≠ 0) ∧ ∀ i, H.j i ≤ ℓ

/-- `Π≤ℓ` is finite (structural lemma used to define `lowOrder`). -/
theorem isLowOrder_finite (d ℓ : ℕ) : {H : HaarIdx d | IsLowOrder ℓ H}.Finite := by
  let F : HaarIdx d → (Fin d → ℕ × ℕ) := fun H i => (H.j i, H.k i)
  have hF : Function.Injective F := by
    intro H H' h
    have h' := fun i => congrFun h i
    ext i
    · exact (Prod.mk.inj (h' i)).1
    · exact (Prod.mk.inj (h' i)).2
  have hfin : (Set.univ.pi (fun _ : Fin d => (Set.Iic ℓ ×ˢ Set.Iio (2 ^ ℓ) : Set (ℕ × ℕ)))).Finite :=
    Set.Finite.pi (fun _ => (Set.finite_Iic ℓ).prod (Set.finite_Iio _))
  refine (hfin.preimage hF.injOn).subset ?_
  intro H hH i _
  refine ⟨hH.2 i, ?_⟩
  show H.k i < 2 ^ ℓ
  rcases H.valid i with h | h
  · rw [h.2]; exact Nat.pow_pos (by norm_num)
  · exact lt_of_lt_of_le h.2 (Nat.pow_le_pow_right (by norm_num) (by have := hH.2 i; omega))

/-- The collection `Π≤ℓ` of non-constant Haar functions `H_{j,k}` with `j_i ≤ ℓ` for every
`i ∈ [d]` (arXiv:2609.10921, sha256 bc273e88…, §2, p.6, PDF p.8). -/
noncomputable def lowOrder (d ℓ : ℕ) : Finset (HaarIdx d) := (isLowOrder_finite d ℓ).toFinset

/-- `N_ℓ := (ℓ + 1)^d`, the number of scale vectors `j ∈ {0, 1, …, ℓ}^d` (arXiv:2609.10921,
sha256 bc273e88…, §3.1, p.8, PDF p.10).

**Formalization Note** §2 also writes `N_ℓ` for `|Π≤ℓ|`; §3.1 redefines it as `(ℓ+1)^d`, the value
used in (7), (8) and Lemma 3.4.1, and that is the one taken here. -/
def Nell (d ℓ : ℕ) : ℕ := (ℓ + 1) ^ d

/-- The level `ℓ := ⌈10 log₂ n⌉` (arXiv:2609.10921, sha256 bc273e88…, §3.1, p.8, PDF p.10). -/
noncomputable def ell (n : ℕ) : ℕ := ⌈10 * Real.logb 2 n⌉₊

/-- The low-order projection `Π≤ℓ g = ∑_{H∈Π≤ℓ} (⟨g,H⟩/‖H‖₂²) H` (arXiv:2609.10921,
sha256 bc273e88…, §2, p.6, PDF p.8; (13), p.14), as a pointwise function. -/
noncomputable def lowProj (d ℓ : ℕ) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ H ∈ lowOrder d ℓ, (l2inner d g (haar H) / haarNormSq H) * haar H x

/-- The high-order projection `Π>ℓ g`, the projection onto the span of the non-constant Haar
functions outside `Π≤ℓ` (arXiv:2609.10921, sha256 bc273e88…, §2, p.6, PDF p.8).

**Formalization Note** Defined pointwise as `g − ḡ − Π≤ℓ g`; since the Haar functions form an
orthogonal basis of `L²`, this is the orthogonal projection of `g` onto the span of the remaining
non-constant Haar functions, as an everywhere-defined representative. -/
noncomputable def highProj (d ℓ : ℕ) (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  g x - cubeMean d g - lowProj d ℓ g x

end QMCBeyondHK


