-- Prove2me | Definitions.Def_SFLOracleLowerBound_Hardness_SparseRank
-- name    : SFLOracleLowerBound_Hardness_SparseRank
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T02:27:07.611696+00:00
-- url     : https://prove2.me/theorems/ef4fa52e-39da-43c5-8c2c-c4d01c197ea8
-- title:
--   Cyclic lift, sparse witnesses and the lifted allocation instance
-- statement:
--   Lift every matching edge $M_a(v)=u$ to edges from $(v,t)$ to $(u,t+a)$, with cyclic coordinates modulo $d$. Write $N_{\widetilde G}$ for the resulting neighborhood map and $U\times\mathbb Z_d$ for a union of fibers. A witness $V$ is admissible when $|V|\le2K$. Define
--   $$
--   \Phi(U,V)=|U\cup N_{\widetilde G}(V)|-(d-3)|V|,\qquad
--   \rho(U)=\min\left\{K,\min_{|V|\le2K}\Phi(U,V)\right\}.
--   $$
--   The subtraction is signed integer subtraction; nonnegativity is a theorem, not an input certificate. Shifts send $(u,t)$ to $(u,t+a)$. Facilities are the base right vertices, and a lifted client $(u,t)$ has the connection distances of $u$. The first-copy assignment sends $(u,a)$ to the unique vertex matched to $u$ in $M_a$. Whole-orbit assignments are those constant on each fiber.
--
--   This computes the precise rank and assignment construction used in Lemmas 22–25. Lifted right vertices supply rank witnesses and are not the facilities.
-- source:
--   Adam N. Elmachtoub, Bento Natura, Meike Neuwohner, Settling the Approximability of Submodular Facility Location, STOC 2027 submission #1249 (October 2026), Definitions 20–21, pp.20–22, equation (18); Definition 24, pp.23–24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1249.pdf

import Mathlib
import Definitions.Def_SFLOracleLowerBound_Hardness_MatchingGraph
import Definitions.Def_SFLOracleLowerBound_Hardness_Allocation

set_option autoImplicit false

noncomputable section

namespace SFLOracleLowerBound.Hardness

open Classical Finset MeasureTheory
open scoped ENNReal

/-- Addition in ℤ_d, using Fin d as its concrete finite carrier. -/
def cyclicAdd {d : ℕ} (t a : Fin d) : Fin d :=
  ⟨(t.val+a.val)%d, Nat.mod_lt _ (Nat.zero_lt_of_lt t.isLt)⟩

/-- Definition 20, p.20: M_a(v) at coordinate t+a is joined to (v,t). -/
def liftNeighbors {d m : ℕ} (M : MatchingGraph d m)
    (V : Finset (Fin m × Fin d)) : Finset (Fin m × Fin d) :=
  V.biUnion (fun v => univ.image (fun a : Fin d => (M a v.1, cyclicAdd v.2 a)))

def LiftExpansion {d m : ℕ} (M : MatchingGraph d m) (K : ℕ) : Prop :=
  ∀ V : Finset (Fin m × Fin d), V.card ≤ 2*K →
    ((d : ℤ)-2) * V.card ≤ (liftNeighbors M V).card

def fibers {d m : ℕ} (U : Finset (Fin m)) : Finset (Fin m × Fin d) := U ×ˢ univ

/-- Definition 21 (18), signed integer subtraction before minimization. -/
def witnessCost {d m : ℕ} (M : MatchingGraph d m)
    (U V : Finset (Fin m × Fin d)) : ℤ :=
  ((U ∪ liftNeighbors M V).card : ℤ) - ((d : ℤ)-3) * V.card

def sparseRank {d m : ℕ} (M : MatchingGraph d m) (K : ℕ)
    (U : Finset (Fin m × Fin d)) : ℤ :=
  min (K : ℤ) (sInf {z : ℤ | ∃ V : Finset (Fin m × Fin d), V.card ≤ 2*K ∧ z = witnessCost M U V})

def sparseRankReal {d m : ℕ} (M : MatchingGraph d m) (K : ℕ)
    (U : Finset (Fin m × Fin d)) : ℝ := sparseRank M K U

def shiftSet {d m : ℕ} (U : Finset (Fin m × Fin d)) (a : Fin d) : Finset (Fin m × Fin d) :=
  U.image (fun u => (u.1, cyclicAdd u.2 a))

def liftedData {d m : ℕ} (M : MatchingGraph d m) : PublicData (Fin m × Fin d) (Fin m) :=
  fun u v => baseDistance M (Sum.inl u.1) (Sum.inr v)

/-- The first-copy neighborhoods partition the clients; no choice of a partition is assumed. -/
def firstCopyAssignment {d m : ℕ} (M : MatchingGraph d m) : (Fin m × Fin d) → Fin m :=
  fun u => (M u.2).symm u.1

def FiberConstant {d m : ℕ} (σ : (Fin m × Fin d) → Fin m) : Prop :=
  ∀ u t s, σ (u,t) = σ (u,s)

/-- The concrete shift permutations and their finite image group, Definition 20. -/
def shiftPermutation {d m : ℕ} [NeZero d] (a : Fin d) : Equiv.Perm (Fin m × Fin d) :=
  Equiv.prodCongr (Equiv.refl (Fin m)) (Equiv.addRight a)

def shiftGroup (d m : ℕ) [NeZero d] : Finset (Equiv.Perm (Fin m × Fin d)) :=
  univ.image (fun a : Fin d => shiftPermutation (m := m) a)

end SFLOracleLowerBound.Hardness


