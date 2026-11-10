-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_SetFunctions
-- name    : SFLOracleLowerBound_Hardness_SetFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:25:21.204772+00:00
-- url     : https://prove2.me/theorems/51af41d9-9c82-44dd-a664-3bad12c3466c
-- title:
--   Set functions, matroid rank and the cube Lovász extension
-- statement:
--   For a finite ground set $E$, normalization means $r(\varnothing)=0$, monotonicity means $r(A)\le r(B)$ whenever $A\subseteq B$, and integer valued means that every $r(A)$ is an integer. A facility cost is nonnegative, normalized, monotone and submodular. A matroid rank is the rank of an actual finite matroid whose ground set is all of $E$; loops are allowed. The published pure submodularity predicate supplies the lattice inequality.
--
--   For real set functions, define the two minima of Lemma 6 and the cube Lovász extension by
--   $$
--   h_1(S)=\min_{A\subseteq W}H(S\sqcup A),\qquad h_2(S)=\min_{A\subseteq W}(|S\setminus\varphi^{-1}(A)|+r(A)),\qquad
--   \widehat r(x)=\int_{(0,1]}r(\{e:x_e\ge t\})\,dt.
--   $$
--   The minimum ranges are finite and nonempty. The threshold integrand is a bounded finite-step function, even for unnormalized real $r$. These definitions support the minimization and symmetry facts without adding monotonicity or sign assumptions to the real-valued lemmas.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), §2.1, pp.5–6; Lemma 6, p.7; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- §2.1, pp.5–6. Sign, normalization and monotonicity are independent properties. -/
def Normalized {E : Type} [Fintype E] [DecidableEq E] (r : Finset E → ℝ) : Prop := r ∅ = 0

def SetMonotone {E : Type} [Fintype E] [DecidableEq E] (r : Finset E → ℝ) : Prop :=
  ∀ A B, A ⊆ B → r A ≤ r B

def IntegerValued {E : Type} (r : Finset E → ℝ) : Prop := ∀ A, ∃ z : ℤ, r A = z

def FacilityCost {E : Type} [Fintype E] [DecidableEq E] (g : Finset E → ℝ) : Prop :=
  (∀ A, 0 ≤ g A) ∧ Normalized g ∧ SetMonotone g ∧ NonmonotoneSubmod.Shared.Submodular g

/-- Genuine matroid on the full carrier, not a real polymatroid. Loops are allowed. -/
def MatroidRank {E : Type} [Fintype E] (r : Finset E → ℝ) : Prop :=
  ∃ M : Matroid E, M.E = Set.univ ∧ ∀ A, r A = (M.eRk (A : Set E)).toNat

/-- Minima are over the nonempty finite power set. -/
def partialMinimum {E W : Type} [Fintype E] [Fintype W] [DecidableEq E] [DecidableEq W]
    (H : Finset (Sum E W) → ℝ) (S : Finset E) : ℝ :=
  ⨅ A : Finset W, H (S.image Sum.inl ∪ A.image Sum.inr)

def pullbackMinimum {E W : Type} [Fintype E] [Fintype W] [DecidableEq E] [DecidableEq W]
    (φ : E → W) (r : Finset W → ℝ) (S : Finset E) : ℝ :=
  ⨅ A : Finset W, ((S.filter (fun e => φ e ∉ A)).card : ℝ) + r A

/-- §2.1 p.6: the threshold integral over (0,1], even when r(∅) ≠ 0. -/
def lovasz {E : Type} [Fintype E] [DecidableEq E]
    (r : Finset E → ℝ) (x : E → ℝ) : ℝ :=
  ∫ t in Set.Ioc (0 : ℝ) 1, r (univ.filter (fun e => t ≤ x e))

end SFLOracleLowerBound.Hardness


