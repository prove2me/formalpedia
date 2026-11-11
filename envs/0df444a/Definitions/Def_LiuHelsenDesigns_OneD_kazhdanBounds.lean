-- Prove2me | Definitions.Def_LiuHelsenDesigns_OneD_kazhdanBounds
-- name    : LiuHelsenDesigns_OneD_kazhdanBounds
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T11:05:55.429408+00:00
-- url     : https://prove2.me/theorems/b53cb52e-32db-4e3e-ad90-9230ee81eb37
-- title:
--   Vector-first and average Kazhdan lower bounds (corrected Definition 4)
-- statement:
--   A Kazhdan lower bound requires that every unit vector in every Hilbert-space representation without invariant vectors is displaced by at least κ by some generator; the generator may depend on the vector. The average lower bound uses uniform average squared displacement on the actual finite set.
--
--   $$\forall\rho,v,\quad\|v\|=1\Longrightarrow\exists s\in S:\|\rho(s)v-v\|\ge\kappa.$$
--
--   This corrects the quantifier order of printed Definition 4. For $(\mathbb Z/2)^2$ and its three nontrivial characters, the printed constant is zero, although the vector-first constant is $\sqrt2$ and the average constant is 2. Lower-bound predicates avoid empty-real-infimum defaults at the trivial group. The orbit of a kernel set is computed by actual conjugation in the extension.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), pp.11–13, Definitions 4–5, Eqs.(20)–(28). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Mathlib

universe u

namespace LiuHelsenDesigns.OneD

/-- Vector-first Kazhdan lower-bound predicate, for arbitrary Hilbert representations.
Using lower bounds avoids imposing a real-valued empty-infimum convention at the
trivial group. Finite-dimensional specializations agree with DepthOneQExp.kazhdan. -/
def KazhdanLower (G : Type u) [Group G] (S : Set G) (κ : ℝ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    ∀ ρ : G →* (E ≃ₗᵢ[ℂ] E),
      (∀ v : E, (∀ g : G, ρ g v = v) → v = 0) →
      ∀ v : E, ‖v‖ = 1 → ∃ s ∈ S, κ ≤ ‖ρ s v - v‖

/-- Squared displacement, with uniform weights on the actual set. -/
def AverageKazhdanLower (G : Type u) [Group G] (S : Finset G) (κ : ℝ) : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E],
    ∀ ρ : G →* (E ≃ₗᵢ[ℂ] E),
      (∀ v : E, (∀ g : G, ρ g v = v) → v = 0) →
      ∀ v : E, ‖v‖ = 1 → κ ≤ (∑ s ∈ S, ‖ρ s v - v‖^2) / S.card

def InverseClosed {G : Type u} [Group G] (S : Set G) : Prop :=
  ∀ g ∈ S, g⁻¹ ∈ S

def BoundedProducts {G : Type u} [Group G] (S : Set G) (M : ℕ) : Prop :=
  ∀ g : G, ∃ xs : List G, xs.length ≤ M ∧ (∀ x ∈ xs, x ∈ S) ∧ xs.prod = g

noncomputable def kernelOrbit {A Γ : Type u} [CommGroup A] [Group Γ] [Fintype A]
    (i : A →* Γ) (B : Finset A) : Finset A :=
  open Classical in
  Finset.univ.filter fun a => ∃ b ∈ B, ∃ γ : Γ, i a = γ * i b * γ⁻¹

end LiuHelsenDesigns.OneD


