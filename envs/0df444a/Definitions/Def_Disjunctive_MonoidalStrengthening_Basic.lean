-- Prove2me | Definitions.Def_Disjunctive_MonoidalStrengthening_Basic
-- name    : Disjunctive_MonoidalStrengthening_Basic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:02:00.65873+00:00
-- url     : https://prove2.me/theorems/e4091a14-f314-4274-b00b-8542c04be46d
-- title:
--   The cut monoid, disjunctive-cut coefficients, and Theorem 11.26's piecewise coefficients
-- statement:
--   This definition sets up the algebraic apparatus of monoidal cut strengthening.
--
--   The **cut monoid** $M := \{\mu \in \mathbb{Z}^q : \sum_h \mu_h \ge 0\}$ is the chapter's
--   central algebraic object. For a $q$-term disjunctive-cut situation with per-term coefficients
--   $a^h_j$, right-hand sides $a^h_0$, and multipliers $\theta_h$, `AlphaJUnstrengthened`/`Alpha0`
--   give the ordinary disjunctive-cut coefficients (Chapter 1's construction), and
--   `AlphaJStrengthened` gives the monoidally-strengthened coefficient $\alpha_j = \inf_{\mu^j\in
--   M} \max_h \theta_h[a^h_j+\mu^j_h(a^h_0-b^h_0)]$ using a background lower bound $b^h_0$.
--   `BetaJUnstrengthened` is the normalized ($a_i0=1$-scaled) version of the same unstrengthened
--   coefficient used from §11.9 onward. `AlphaPlus`/`AlphaMinus` are Theorem 11.26's two piecewise
--   cut coefficients, each split over three index sets with a different formula per set.
--
--   **Formalization Note.** `AlphaJStrengthened` uses `sInf` over the (generally infinite) monoid
--   `M`, matching the book's own `inf_{μ^j∈M}`; `AlphaPlus`/`AlphaMinus` use nested `if`-`then`-
--   `else` matching the three cases of (11.55)/(11.56) exactly, deliberately not collapsed into a
--   single closed-form expression, per `BRIEF.md`'s explicit warning that the piecewise structure
--   is the theorem's actual content.
-- source:
--   Balas, Disjunctive Programming, Springer 2018, DOI 10.1007/978-3-030-00148-3, p. 173, 176, 179, 187, Sections 11.8-11.9

import Mathlib

namespace Disjunctive.MonoidalStrengthening

/-- The monoid `M := {μ ∈ ℤ^q : Σ_h μ_h ≥ 0}` (Balas §11.8, p. 176, eq. (11.28)/(11.40)), the
central algebraic object of monoidal cut strengthening. -/
def CutMonoid (q : ℕ) : Set (Fin q → ℤ) :=
  {mu | 0 ≤ ∑ h, mu h}

/-- The unstrengthened disjunctive-cut coefficient `α_j = max_{h∈Q} θ_h a^h_j` (Balas §11.8,
p. 173, eq. (11.27)/(11.30)'s `j ∈ J₂` case). -/
noncomputable def AlphaJUnstrengthened {q n : ℕ} [Nonempty (Fin q)] (theta : Fin q → ℝ)
    (acoef : Fin q → Fin n → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun h => theta h * acoef h j)

/-- The disjunctive-cut right-hand side `α_0 = min_{h∈Q} θ_h a^h_0` (Balas §11.8, p. 176, eq.
(11.31)). -/
noncomputable def Alpha0 {q : ℕ} [Nonempty (Fin q)] (theta a0 : Fin q → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun h => theta h * a0 h)

/-- The monoidally-strengthened cut coefficient `α_j = inf_{μ^j∈M} max_{h∈Q} θ_h[a^h_j +
μ^j_h(a^h_0-b^h_0)]` (Balas §11.8, p. 176, eq. (11.30)'s `j ∈ J₁` case), the goal of Theorem
11.19. -/
noncomputable def AlphaJStrengthened {q n : ℕ} [Nonempty (Fin q)] (theta a0 b0 : Fin q → ℝ)
    (acoef : Fin q → Fin n → ℝ) (j : Fin n) : ℝ :=
  sInf {v : ℝ | ∃ mu : Fin q → ℤ, mu ∈ CutMonoid q ∧
    v = Finset.univ.sup' Finset.univ_nonempty
      (fun h => theta h * (acoef h j + (mu h : ℝ) * (a0 h - b0 h)))}

/-- The unstrengthened, normalized disjunctive-cut coefficient `β_j = max_{i∈Q} a_ij/a_i0`
(Balas §11.9, p. 179, eq. (11.39)), for the `q`-term disjunction (11.38). -/
noncomputable def BetaJUnstrengthened {q n : ℕ} [Nonempty (Fin q)] (a : Fin q → Fin n → ℝ)
    (a0 : Fin q → ℝ) (j : Fin n) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => a i j / a0 i)

/-- `α⁺_j`, Theorem 11.26's piecewise cut coefficient (Balas §11.9.1, p. 187, eq. (11.55)):
`(1-a_j)/(1-a_0)` on `J⁺₁ := {j∈J₁ : a_j>1}`; the monoidally-strengthened GMI coefficient on
`J^{>}₁ := {j∈J₁ : a_0-1≤a_j≤1}`; and the plain GMI coefficient `max{a_j/a_0,-a_j/(1-a_0)}`
elsewhere. -/
noncomputable def AlphaPlus {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n)) (j : Fin n) : ℝ :=
  if j ∈ J1 ∧ 1 < a j then (-(a j) + 1) / (1 - a0)
  else if j ∈ J1 ∧ a0 - 1 ≤ a j ∧ a j ≤ 1 then
    min ((a j - (⌊a j⌋ : ℝ)) / a0) ((-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0))
  else max (a j / a0) (-(a j) / (1 - a0))

/-- `α⁻_j`, Theorem 11.26's piecewise cut coefficient (Balas §11.9.1, p. 187, eq. (11.56)):
`(a_j+1)/a_0` on `J⁻₁ := {j∈J₁ : a_j<-1}`; the monoidally-strengthened GMI coefficient on
`J^{<}₁ := {j∈J₁ : -1≤a_j≤a_0}`; and the plain GMI coefficient elsewhere. -/
noncomputable def AlphaMinus {n : ℕ} (a0 : ℝ) (a : Fin n → ℝ) (J1 : Finset (Fin n)) (j : Fin n) : ℝ :=
  if j ∈ J1 ∧ a j < -1 then (a j + 1) / a0
  else if j ∈ J1 ∧ -1 ≤ a j ∧ a j ≤ a0 then
    min ((a j - (⌊a j⌋ : ℝ)) / a0) ((-(a j) + (⌈a j⌉ : ℝ)) / (1 - a0))
  else max (a j / a0) (-(a j) / (1 - a0))

end Disjunctive.MonoidalStrengthening


