-- Prove2me | Definitions.Def_HypercliqueAC0_FixedDepth_Switching
-- name    : HypercliqueAC0_FixedDepth_Switching
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-27T00:58:10.64203+00:00
-- url     : https://prove2.me/theorems/e76e51e8-e910-5fd4-a58e-dc335f3cbf25
-- title:
--   Random restrictions, decision-tree depth and DNFs
-- statement:
--   Basic objects for the switching-lemma route to Fourier tails of constant-depth circuits, on the cube $\{0,1\}^X$ for a finite set $X$.
--
--   1. A **restriction** is a map $\rho\colon X\to\{0,1,*\}$, written `X → Option Bool` with `none` for a star. The restricted function $f|_\rho$ is again a function on the whole cube: it substitutes $\rho(e)$ for every fixed coordinate and reads the remaining coordinates from its argument, so it ignores the fixed coordinates.
--   2. $\mathrm{DT}(f)\le t$ (`DTDepthLE t f`) means that $f$ is computed by a decision tree of depth at most $t$: either $f$ is constant, or for some variable $x_i$ both subfunctions $f|_{x_i=0}$ and $f|_{x_i=1}$ have decision-tree depth at most $t-1$.
--   3. The **$p$-random restriction** $\mathcal R_p$ makes every coordinate independently a star with probability $p$ and each of the constants $0,1$ with probability $(1-p)/2$; `restrictionWeight` is its product weight and `restrictionProb p E` is the probability of the event $E$.
--   4. A **term** is a finite set of literals $x_e=b$, satisfied when all of them hold, and a **DNF** is a finite set of terms, satisfied when some term is; the width of a term is its number of literals.
--
--   **Formalization Note** Restricted functions are kept on the full cube rather than on the subcube of free coordinates, so that restrictions compose by substitution.
-- source:
--   Håstad, Almost optimal lower bounds for small depth circuits (STOC 1986); Beame, A switching lemma primer (1994), §1–2; O'Donnell, Analysis of Boolean Functions (2014), §3.3 and §4.3 (random restrictions, decision trees).

import Mathlib

noncomputable section
namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Apply a restriction `ρ : X → Option Bool` to a Boolean function: a coordinate with
`ρ e = some b` is fixed to `b`, and a coordinate with `ρ e = none` (a star) stays free.
The result is again a function on the full cube that ignores the fixed coordinates. -/
def restrictFn {X : Type} (ρ : X → Option Bool) (f : (X → Bool) → Bool) :
    (X → Bool) → Bool :=
  fun x => f (fun e => (ρ e).getD (x e))

/-- `DTDepthLE t f`: the Boolean function `f` is computed by a decision tree of depth at most `t`. -/
inductive DTDepthLE {X : Type} : ℕ → ((X → Bool) → Bool) → Prop
  | const (t : ℕ) (b : Bool) : DTDepthLE t (fun _ => b)
  | query (t : ℕ) (i : X) (f : (X → Bool) → Bool)
      (h0 : DTDepthLE t (fun x => f (Function.update x i false)))
      (h1 : DTDepthLE t (fun x => f (Function.update x i true))) :
      DTDepthLE (t + 1) f

/-- The probability of a single coordinate of a `p`-random restriction: a star with
probability `p`, and each of the two constants with probability `(1 - p)/2`. -/
def starWeight (p : ℝ) : Option Bool → ℝ
  | none => p
  | some _ => (1 - p) / 2

/-- The product weight of a restriction under the `p`-random restriction distribution. -/
def restrictionWeight {X : Type} [Fintype X] (p : ℝ) (ρ : X → Option Bool) : ℝ :=
  ∏ e, starWeight p (ρ e)

/-- The probability of an event under the `p`-random restriction distribution. -/
def restrictionProb {X : Type} [Fintype X] (p : ℝ) (E : (X → Option Bool) → Prop) : ℝ :=
  ∑ ρ : X → Option Bool, if E ρ then restrictionWeight p ρ else 0

/-- A term is a finite set of literals `(e, b)`, read as `x_e = b`; it is satisfied when
all its literals hold. -/
def termValue {X : Type} (T : Finset (X × Bool)) (x : X → Bool) : Bool :=
  decide (∀ l ∈ T, x l.1 = l.2)

/-- The value of a DNF, given as a finite set of terms. -/
def dnfValue {X : Type} (F : Finset (Finset (X × Bool))) (x : X → Bool) : Bool :=
  decide (∃ T ∈ F, termValue T x = true)

end HypercliqueAC0.FixedDepth


