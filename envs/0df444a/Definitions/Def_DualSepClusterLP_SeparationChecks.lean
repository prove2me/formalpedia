-- Prove2me | Definitions.Def_DualSepClusterLP_SeparationChecks
-- name    : DualSepClusterLP_SeparationChecks
-- status  : Definition
-- author  : @hypercube
-- created : 2026-11-19T14:47:09.618155+00:00
-- url     : https://prove2.me/theorems/bee907d0-916e-4801-8948-d1f408bcc32c
-- title:
--   Local tests for approximate dual feasibility
-- statement:
--   Given a signed graph and rational vertex prices, test singleton constraints, sets recovered by ordering near-clique deletion scores, and lower bounds for the cost minus price on small universes constructed from two pivot neighborhoods. The last test permits an additive error quadratic in the size of the tested universe. The inverse accuracy and both constants governing this error are specified explicitly.
-- source:
--   David García-Soriano and Antoine Schohn, Approximate Dual Separation for the Cluster LP, Theorem 2.1, the large/small/intermediate cost regimes, and the dense quadratic subroutine. https://arxiv.org/abs/2607.27829. The two-pivot localization is an alternative proof for the application.

import Definitions.Def_DualSepClusterLP_LinearProgram

namespace DualSepClusterLP.SepStructure
open Finset
def edge {n : ℕ} (G : Graph n) (i j : Fin n) : Bool :=
  if i < j then G i j else if j < i then G j i else false
def neighbors {n : ℕ} (G : Graph n) (v : Fin n) := univ.filter (fun j => edge G v j)
def closed {n : ℕ} (G : Graph n) (v : Fin n) := insert v (neighbors G v)
def degree {n : ℕ} (G : Graph n) (A : Finset (Fin n)) (v : Fin n) := ((neighbors G v) ∩ A).card
end DualSepClusterLP.SepStructure

namespace DualSepClusterLP.SepStructure
open Finset
def eligible {n : ℕ} (G : Graph n) (t s : ℕ) :=
  univ.filter (fun v => (closed G v).card ≤ (100*(t+1)+1)*s)
end DualSepClusterLP.SepStructure

namespace DualSepClusterLP.TwoPivot
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
def window (N : α → Finset α) (P : Finset α) (s : ℕ) (v w : α) : Finset α :=
  univ.filter fun u => s ≤ 10*(N u ∩ ((N v ∪ N w) ∩ P)).card
end DualSepClusterLP.TwoPivot

namespace DualSepClusterLP.Near
open Finset
variable {n : ℕ}
def top (U : Finset (Fin n)) (f : Fin n → ℚ) (h : Fin n) :=
  U.filter (fun i => f h < f i ∨ f i = f h ∧ i.val ≤ h.val)
end DualSepClusterLP.Near

namespace DualSepClusterLP.Near
open Finset SepStructure
variable {n : ℕ} (G : Graph n)
def count (A : Finset (Fin n)) (u : Fin n) := ((closed G u)∩A).card
def zone (s : ℕ) (v : Fin n) := univ.filter (fun u => s ≤ 3*count G (closed G v) u)
end DualSepClusterLP.Near

namespace DualSepClusterLP.Near
open Finset SepStructure
variable {n : ℕ} (G : Graph n) (q : Fin n → ℚ)
def score (U : Finset (Fin n)) (i : Fin n) : ℚ :=
  2*(degree G U i : ℚ) - (degree G univ i : ℚ)/2 + q i
def candidate (s : ℕ) (v h : Fin n) := top (zone G s v) (score G q (zone G s v)) h
noncomputable def lag (S : Finset (Fin n)) : ℝ := subsetCost G S-∑ i∈S,(q i:ℝ)
end DualSepClusterLP.Near

namespace DualSepClusterLP.SepCheck
open Finset
def scale (t : ℕ) := 100*(t+1)+1
def growth (t : ℕ) := 20*(scale t)^2
def accuracy (t : ℕ) := 25600*(t+1)^2*(growth t)^2
def localize {n : ℕ} (t : ℕ) (G : Graph n) (s : ℕ) (v w : Fin n) :=
  TwoPivot.window (SepStructure.closed G) (SepStructure.eligible G t s) s v w
def Checks {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) : Prop :=
  (∀ v, (q v:ℝ) ≤ subsetCost G {v}) ∧
  (∀ s ≤ n, ∀ v h : Fin n, 0 ≤ Near.lag G q (Near.candidate G q s v h)) ∧
  ∀ s ≤ n, ∀ v w : Fin n, ∀ X ⊆ localize t G s v w,
    0 ≤ (accuracy t:ℝ)*Near.lag G q X + 2*((localize t G s v w).card:ℝ)^2
end DualSepClusterLP.SepCheck


