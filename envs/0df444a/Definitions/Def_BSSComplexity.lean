-- Prove2me | Definitions.Def_BSSComplexity
-- name    : BSSComplexity
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-14T14:55:43.247878+00:00
-- url     : https://prove2.me/theorems/0b6fd50c-a7e2-4e2c-8a0c-9142da76f170
-- title:
--   $P$, $NP$ and $NP$-completeness over $\mathbb{R}$ (§§5-6)
-- statement:
--   Size, the classes $P$ and $NP$, polynomial-time reductions and $NP$-completeness over
--   $\mathbb{R}$, from §5 (pp. 23–26) and §6 (p. 26).
--
--   Over $\mathbb{R}$ the height of every element is $1$, so the size of $y \in \mathbb{R}^\infty$ is
--   its length plus one, and the standard cost function $C_M(y)$ coincides with the halting time
--   $T_M(y)$. A machine is in class $P$ on a space of admissible inputs $Y$ when it halts on every
--   $y \in Y$ within $c \cdot \mathrm{size}(y)^q$ steps for fixed $c, q$. A machine solves
--   $(Y, Y_{\mathrm{yes}})$ when on each admissible input it halts with answer $1$ or $0$ and answers
--   $1$ exactly on $Y_{\mathrm{yes}}$. The pairing of guesses with instances places the instance in
--   the even coordinates and the guess in the odd ones.
--
--   $NP$ follows the three clauses of the definition on p. 25: the values are $0$ and $1$; an answer
--   of $1$ occurs only at members of $Y_{\mathrm{yes}}$; and each member of $Y_{\mathrm{yes}}$ has
--   *some* guess on which the answer is $1$ within $c \cdot \mathrm{size}(y)^q$ steps. A polynomial
--   time reduction of $(Z, Z_{\mathrm{yes}})$ to $(Y, Y_{\mathrm{yes}})$ is a map computed on $Z$ by a
--   machine in class $P$, landing in $Y$, whose value lies in $Y_{\mathrm{yes}}$ exactly on
--   $Z_{\mathrm{yes}}$; and $(Y, Y_{\mathrm{yes}})$ is $NP$-complete over $\mathbb{R}$ when it is in
--   $NP$ and everything in $NP$ so reduces to it.
-- source:
--   L. Blum, M. Shub, S. Smale, On a theory of computation and complexity over the real numbers: NP-completeness, recursive functions and universal machines, Bull. Amer. Math. Soc. (N.S.) 21 (1989), no. 1, 1-46, https://doi.org/10.1090/S0273-0979-1989-15750-9, §5, pp. 23-26; §6, p. 26

import Definitions.Def_BSSMachine

/-!
# Complexity of machines over the reals (Blum–Shub–Smale, §§5–6)

Formalization of size, the classes `P` and `NP`, polynomial time reductions and
`NP`-completeness over `ℝ`, following

  L. Blum, M. Shub, S. Smale, *On a theory of computation and complexity over the
  real numbers: NP-completeness, recursive functions and universal machines*,
  Bull. Amer. Math. Soc. **21** (1989), no. 1, 1–46, §5 (pp. 23–26) and §6 (p. 26).

Over `ℝ` the height of every element is `1` (BSS §5, p. 24), so the size of a
point of `ℝ^∞` is its length plus one and the standard cost function `C_M(y)`
equals the halting time `T_M(y)`.
-/

namespace BSS

/-- The size over `ℝ` of a point of `ℝ^∞`: its length plus its height, the height
over `ℝ` of a real number being `1` (BSS §5, p. 24). -/
noncomputable def sizeR (x : Rinf ℝ) : ℕ := lengthInf x + 1

/-- The pairing `ℝ^∞ × ℝ^∞ → ℝ^∞` used for the input space `Y × I` of a
nondeterministic machine (BSS §2, p. 13: `R^∞ = R^∞ + ⋯ + R^∞`): `y` is placed in
the even coordinates and `y'` in the odd ones. -/
noncomputable def pairInf (y y' : Rinf ℝ) : Rinf ℝ :=
  Finsupp.onFinset (α := ℕ) (M := ℝ) ((y.support.image (fun i => 2 * i)) ∪ (y'.support.image (fun i => 2 * i + 1)))
    (fun i : ℕ => if i % 2 = 0 then y (i / 2) else y' (i / 2))
    (by
      intro a ha
      by_cases h : a % 2 = 0
      · simp only [if_pos h] at ha
        refine Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a / 2, ?_, ?_⟩)
        · exact Finsupp.mem_support_iff.mpr ha
        · omega
      · simp only [if_neg h] at ha
        refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a / 2, ?_, ?_⟩)
        · exact Finsupp.mem_support_iff.mpr ha
        · omega)

/-- The machine `M` is in class `P` on the space of admissible inputs `Y`:
its cost on every admissible input is bounded by a fixed polynomial in the size of
the input (BSS §5, p. 24). Over `ℝ` the cost is the halting time. -/
def InClassP (M : Machine ℝ) (Y : Set (Rinf ℝ)) : Prop :=
  ∃ c q : ℕ, ∀ y ∈ Y, M.Halts y ∧ M.haltingTime y ≤ c * (sizeR y) ^ q

/-- `M` solves the decision problem `(Y, Yyes)`: on every admissible input it halts
with answer `1` (yes) or `0` (no), and answers `1` exactly on `Yyes`
(BSS §5, p. 25). -/
def Solves (M : Machine ℝ) (Y Yyes : Set (Rinf ℝ)) : Prop :=
  ∀ y ∈ Y, M.Halts y ∧ (M.outputVal y = 1 ∨ M.outputVal y = 0) ∧
    (M.outputVal y = 1 ↔ y ∈ Yyes)

/-- The decision problem `(Y, Yyes)` over `ℝ` is in class `P` (BSS §5, p. 25). -/
def DecisionInP (Y Yyes : Set (Rinf ℝ)) : Prop :=
  ∃ M : Machine ℝ, Solves M Y Yyes ∧ InClassP M Y

/-- The decision problem `(Y, Yyes)` over `ℝ` is in class `NP` (BSS §5, p. 25):
there is a machine on `Y × ℝ^∞` whose values are `0` and `1`, which answers `1`
only at members of `Yyes`, and which for every member of `Yyes` answers `1` on
some guess within time polynomial in the size of the instance. -/
def DecisionInNP (Y Yyes : Set (Rinf ℝ)) : Prop :=
  ∃ (M : Machine ℝ) (c q : ℕ),
    (∀ y ∈ Y, ∀ y' : Rinf ℝ, M.Halts (pairInf y y') →
        (M.outputVal (pairInf y y') = 1 ∨ M.outputVal (pairInf y y') = 0)) ∧
    (∀ y ∈ Y, ∀ y' : Rinf ℝ, M.Halts (pairInf y y') →
        M.outputVal (pairInf y y') = 1 → y ∈ Yyes) ∧
    (∀ y ∈ Yyes, ∃ y' : Rinf ℝ, M.Halts (pairInf y y') ∧
        M.outputVal (pairInf y y') = 1 ∧
        M.haltingTime (pairInf y y') ≤ c * (sizeR y) ^ q)

/-- A polynomial time reduction of `(Z, Zyes)` to `(Y, Yyes)` (BSS §6, p. 26):
a map `ψ : Z → Y`, computed on `Z` by a machine in class `P`, with
`ψ z ∈ Yyes` if and only if `z ∈ Zyes`. -/
def PolyTimeReduces (Z Zyes Y Yyes : Set (Rinf ℝ)) : Prop :=
  ∃ M : Machine ℝ, InClassP M Z ∧ (∀ z ∈ Z, M.output z ∈ Y) ∧
    (∀ z ∈ Z, M.output z ∈ Yyes ↔ z ∈ Zyes)

/-- The decision problem `(Y, Yyes)` is `NP`-complete over `ℝ` (BSS §6, p. 26):
it lies in `NP`, and every decision problem in `NP` over `ℝ` reduces to it in
polynomial time. -/
def NPCompleteOverReal (Y Yyes : Set (Rinf ℝ)) : Prop :=
  DecisionInNP Y Yyes ∧
    ∀ Z Zyes : Set (Rinf ℝ), Zyes ⊆ Z → DecisionInNP Z Zyes →
      PolyTimeReduces Z Zyes Y Yyes

end BSS


