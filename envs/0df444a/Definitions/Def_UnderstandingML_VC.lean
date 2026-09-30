-- Prove2me | Definitions.Def_UnderstandingML_VC
-- name    : UnderstandingML_VC
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T03:38:09.353465+00:00
-- url     : https://prove2.me/theorems/4c511509-7812-4936-9ad4-859a63d90d2a
-- title:
--   Chapter 6: restriction H_C, shattering, VC-dimension, growth function, pointwise separability, and the threshold, interval and rectangle classes
-- statement:
--   Chapter 6 of Shalev-Shwartz and Ben-David. For a class $H$ of functions $X \to \{0,1\}$ and a finite $C \subseteq X$: the **restriction** $H_C$ (Definition 6.2) is the set of functions $C \to \{0,1\}$ derived from $H$; $H$ **shatters** $C$ (Definition 6.3) if $H_C$ is the set of all functions $C \to \{0,1\}$; the **VC-dimension** (Definition 6.5) is the maximal size of a shattered set, $\infty$ if $H$ shatters arbitrarily large sets; the **growth function** (Definition 6.9) is $\tau_H(m) = \max_{|C| = m} |H_C|$, taken here over $|C| \le m$ (the same value whenever $|X| \ge m$). `PointwiseSeparable H` is the measurability assumption of Remark 3.1: a countable subclass approximates every member of $H$ pointwise. The classes of §6.3: thresholds $h_a(x) = \mathbb{1}[x < a]$, intervals $h_{a,b}(x) = \mathbb{1}[x \in (a,b)]$ with $a < b$, and axis-aligned rectangles (6.2).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §6.2 Definitions 6.2, 6.3, 6.5 (pp. 69-70), §6.3 (pp. 70-72), §6.5.1 Definition 6.9 (p. 74)

import Definitions.Def_UnderstandingML_Framework
import Mathlib.Order.Lattice.Nat
import Mathlib.Data.Nat.Log

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 6: the VC-dimension

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §6.2–§6.5.

**Restriction, shattering, VC-dimension (Definitions 6.2, 6.3, 6.5).** For a class `H` of
functions `X → {0,1}` and a finite `C ⊆ X`, the restriction `H_C` is the set of functions
`C → {0,1}` obtained by restricting members of `H`; `H` **shatters** `C` if `H_C` is the set of
all functions `C → {0,1}`; `VCdim(H)` is the maximal size of a shattered set, `∞` if `H`
shatters sets of arbitrarily large size.

**Growth function (Definition 6.9).** `τ_H(m) = max_{C ⊆ X, |C| = m} |H_C|`.

**Examples (§6.3).** Threshold functions `h_a(x) = 𝟙[x < a]` over `ℝ`, intervals
`h_{a,b}(x) = 𝟙[x ∈ (a, b)]` with `a < b`, and axis-aligned rectangles (6.2).

**Conventions.** `vcDim` takes values in `ℕ∞`, with `⊤` for infinite VC-dimension. The growth
function is taken over sets of size *at most* `m`, which agrees with Definition 6.9 whenever
`|X| ≥ m` (`|H_C|` is monotone in `C`) and makes `τ_H(2m)` the right quantity in Theorem 6.11
when the double sample has repeated points. `PointwiseSeparable` is the measurability
assumption of Remark 3.1 made explicit: a countable subclass approximates every member of `H`
pointwise (rational parameters do this for the classes of §6.3), so the uniform-convergence
events are measurable; without such an assumption the "finite VC-dimension ⇒ uniform
convergence" direction of the fundamental theorem is false (Durst and Dudley, 1981).
-/

open MeasureTheory

namespace UnderstandingML

section VC

variable {X : Type*}

/-- **Definition 6.2.** The restriction `H_C` of `H` to the finite set `C`: the functions
`C → {0,1}` that can be derived from `H`. -/
def restriction (H : Set (X → Bool)) (C : Finset X) : Set (C → Bool) :=
  {g | ∃ h ∈ H, ∀ c : C, g c = h c}

/-- **Definition 6.3.** `H` **shatters** the finite set `C` if the restriction of `H` to `C` is the
set of all functions from `C` to `{0,1}`. -/
def Shatters (H : Set (X → Bool)) (C : Finset X) : Prop :=
  ∀ g : C → Bool, ∃ h ∈ H, ∀ c : C, h c = g c

/-- **Definition 6.5.** The **VC-dimension** of `H`: the maximal size of a set `C ⊆ X` shattered
by `H`, and `⊤` if `H` shatters sets of arbitrarily large size. -/
noncomputable def vcDim (H : Set (X → Bool)) : ℕ∞ :=
  ⨆ (C : Finset X) (_ : Shatters H C), (C.card : ℕ∞)

/-- **Definition 6.9.** The **growth function** `τ_H(m)`: the maximal number of distinct
functions from a set `C` of (at most) `m` points to `{0,1}` obtained by restricting `H` to `C`. -/
noncomputable def growth (H : Set (X → Bool)) (m : ℕ) : ℕ :=
  sSup {n | ∃ C : Finset X, C.card ≤ m ∧ (restriction H C).ncard = n}

/-- The measurability assumption of Remark 3.1: `H` has a countable subclass `H₀` such that every
`h ∈ H` is the pointwise limit of a sequence in `H₀` (on a discrete codomain, eventually equal at
every point). -/
def PointwiseSeparable (H : Set (X → Bool)) : Prop :=
  ∃ H₀ ⊆ H, H₀.Countable ∧ ∀ h ∈ H, ∃ u : ℕ → (X → Bool), (∀ n, u n ∈ H₀) ∧
    ∀ x, ∃ N, ∀ n, N ≤ n → u n x = h x

end VC

/-! ### The examples of §6.3 -/

section Examples

/-- The **threshold function** `h_a(x) = 𝟙[x < a]` (Example 6.1). -/
noncomputable def threshold (a : ℝ) : ℝ → Bool := fun x ↦ decide (x < a)

/-- The class of threshold functions over `ℝ` (Example 6.1, §6.3.1). -/
def thresholds : Set (ℝ → Bool) := Set.range threshold

/-- The **interval function** `h_{a,b}(x) = 𝟙[x ∈ (a, b)]` (§6.3.2). -/
noncomputable def interval (a b : ℝ) : ℝ → Bool := fun x ↦ decide (a < x ∧ x < b)

/-- The class of intervals over `ℝ`, `{h_{a,b} : a < b}` (§6.3.2). -/
def intervals : Set (ℝ → Bool) := {h | ∃ a b : ℝ, a < b ∧ h = interval a b}

/-- The **axis-aligned rectangle** `h_{(a₁,a₂,b₁,b₂)}` (6.2). -/
noncomputable def rect (a₁ a₂ b₁ b₂ : ℝ) : ℝ × ℝ → Bool :=
  fun p ↦ decide (a₁ ≤ p.1 ∧ p.1 ≤ a₂ ∧ b₁ ≤ p.2 ∧ p.2 ≤ b₂)

/-- The class of axis-aligned rectangles, `{h_{(a₁,a₂,b₁,b₂)} : a₁ ≤ a₂ ∧ b₁ ≤ b₂}` (§6.3.3). -/
def rectangles : Set (ℝ × ℝ → Bool) :=
  {h | ∃ a₁ a₂ b₁ b₂ : ℝ, a₁ ≤ a₂ ∧ b₁ ≤ b₂ ∧ h = rect a₁ a₂ b₁ b₂}

end Examples

end UnderstandingML


