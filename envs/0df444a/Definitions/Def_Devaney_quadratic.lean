-- Prove2me | Definitions.Def_Devaney_quadratic
-- name    : Devaney_quadratic
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T10:10:24.597741+00:00
-- url     : https://prove2.me/theorems/f2099906-bfe4-48d6-bfbb-095998e3fdcc
-- title:
--   The quadratic family $F_\mu$, its invariant set $\Lambda$, and itineraries
-- statement:
--   **The family.** $F_\mu(x) = \mu x (1-x)$, the quadratic family the book analyses throughout Chapter 1, together with the unit interval $I = [0,1]$, where all its interesting dynamics take place.
--
--   **Escape sets.** $A_0 = \{x \in I : F_\mu(x) > 1\}$ is the set of points that leave $I$ after one iteration (nonempty precisely when $\mu > 4$), and $A_n = \{x \in I : F_\mu^{\,n}(x) \in A_0\}$ is the set of points that escape at the $(n+1)$-st iteration. The complement $I \setminus A_0$ splits into a left piece $I_0$ and a right piece $I_1$, separated by the midpoint $1/2$.
--
--   **The invariant set.** $\Lambda$ is the set of points whose entire forward orbit stays in $I$; equivalently, $I$ minus the union of all the $A_n$. It is forward invariant, so $F_\mu$ restricts to a map $\Lambda \to \Lambda$.
--
--   **Itineraries (Definition 7.1).** The itinerary of $x$ is the sequence $S(x) \in \Sigma_2$ whose $n$-th entry records which of the two pieces the $n$-th iterate lands in: $0$ when $F_\mu^{\,n}(x)$ lies in the left piece, $1$ when it lies in the right piece. Since the two pieces are separated by $1/2$, the entry is determined by the test $F_\mu^{\,n}(x) \le 1/2$; for $\mu > 4$ the midpoint itself belongs to the gap $A_0$ and so never occurs along an orbit in $\Lambda$.
-- source:
--   Robert L. Devaney, An Introduction to Chaotic Dynamical Systems, 2nd edition, Westview Press, 2003, ISBN 0-8133-4085-3, §1.5, pp. 31–36 (the sets $A_0$, $A_n$, $I_0$, $I_1$, $\Lambda$); §1.7, p. 44, Definition 7.1 (itinerary)

import Mathlib
import Definitions.Def_Devaney_sigma2

namespace Devaney

/-- The quadratic family `Fμ(x) = μ x (1 - x)` of Devaney, §1.1 and §1.5. -/
def quadratic (μ x : ℝ) : ℝ := μ * x * (1 - x)

/-- The unit interval `I = [0,1]`, where all the interesting dynamics of `Fμ` takes place. -/
def unitI : Set ℝ := Set.Icc (0 : ℝ) 1

/-- Devaney, §1.5: `A₀`, the set of points of `I` that leave `I` after one iteration. -/
def escapeStep (μ : ℝ) : Set ℝ := {x ∈ unitI | 1 < quadratic μ x}

/-- Devaney, §1.5: `Aₙ = {x ∈ I | Fμⁿ(x) ∈ A₀}`, the points that escape from `I` at the
`(n+1)`-st iteration. -/
def escapeAfter (μ : ℝ) (n : ℕ) : Set ℝ := {x ∈ unitI | (quadratic μ)^[n] x ∈ escapeStep μ}

/-- Devaney, §1.5: `I₀`, the left component of `I - A₀`. -/
def leftPiece (μ : ℝ) : Set ℝ := {x ∈ unitI | x ≤ 1 / 2 ∧ quadratic μ x ≤ 1}

/-- Devaney, §1.5: `I₁`, the right component of `I - A₀`. -/
def rightPiece (μ : ℝ) : Set ℝ := {x ∈ unitI | 1 / 2 ≤ x ∧ quadratic μ x ≤ 1}

/-- Devaney, §1.5: `Λ`, the set of points whose entire forward orbit stays in the unit
interval; equivalently `I` minus the union of the escape sets `Aₙ`. -/
def Lambda (μ : ℝ) : Set ℝ := {x | ∀ n : ℕ, (quadratic μ)^[n] x ∈ unitI}

lemma mapsTo_Lambda (μ : ℝ) : Set.MapsTo (quadratic μ) (Lambda μ) (Lambda μ) := by
  intro x hx n
  have := hx (n + 1)
  rwa [Function.iterate_succ_apply] at this

/-- The restriction of `Fμ` to its invariant set `Λ`. -/
def lambdaMap (μ : ℝ) : Lambda μ → Lambda μ :=
  fun x => ⟨quadratic μ x.1, mapsTo_Lambda μ x.2⟩

/-- Devaney, Definition 7.1: the itinerary of `x`, the sequence recording for each `n`
whether `Fμⁿ(x)` lies in the left piece `I₀` (entry `0`) or the right piece `I₁` (entry `1`).
The two pieces are separated by the midpoint `1/2`, so the test is `Fμⁿ(x) ≤ 1/2`. -/
noncomputable def itinerary (μ : ℝ) (x : ℝ) : Sigma2 :=
  fun n => if (quadratic μ)^[n] x ≤ 1 / 2 then 0 else 1

end Devaney


