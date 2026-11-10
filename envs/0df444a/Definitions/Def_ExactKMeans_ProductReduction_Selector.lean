-- Prove2me | Definitions.Def_ExactKMeans_ProductReduction_Selector
-- name    : ExactKMeans_ProductReduction_Selector
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T19:15:52.125121+00:00
-- url     : https://prove2.me/theorems/9cabfe3f-8368-4637-8d50-3e08508fd642
-- title:
--   Selectors, prefix–suffix partitions and squared-distance costs
-- statement:
--   Let a,b be positive integers with ab≥2, and let t≥3 be odd. Write N=abt and λ=N¹²−t+1. Choose the positive angle α with 1/2<αλ<1 and λ sin α=cos((t−1)α), and put r=1/(√b N¹² sin α), δ=N⁻⁵ and γ=αrδ/√b. The additional constants are β=arcsin(1/(4a²√b)) and θᵢ=arcsin(i/a²).
--
--   The b orthogonal coordinate planes have basis vectors eⱼ,eⱼ⊥; their normalized averages are ē,ē⊥. Rotation through 2sα defines eⱼ(s) and eⱼ⊥(s). A selector consists of the two arcs ±eⱼ⊥(ℓ), ℓ=1−t/2,…,t/2−1, and bλ occurrences at each heavy position ±ē/√b. A state s chooses one of the t centered integer cutoffs in every plane. Its positive cluster contains the positive heavy occurrences, the positive-arc prefix ℓ<sⱼ, and the negative-arc suffix ℓ>sⱼ. Its other cluster is the complement. The reference displacement is μ̂(s)=(r/√b)Σⱼeⱼ(sⱼ).
--
--   Means and cluster costs count occurrences. Two-cluster partitions are unordered, represented by the part containing a fixed positive heavy occurrence; both parts must be nonempty. B₁=2(N¹²+(b−1)(t−1)), and B₂=B₁−2bN¹²r². General nearest-center cost is the sum of minimum squared distances. OPT is the published weighted k-means optimum with every weight equal to one, over nonempty families of at most k unrestricted centers. The selector occupies the first 2b coordinates of ℝ^(2b+1), an isometric embedding. Indexed occurrences and zero-based states preserve multiplicities and all centered source states; no geometric conclusion is assumed in the parameter structure.
-- source:
--   Bai, Fomin, Xu (2026), Exact Euclidean k-Means: Faster in the Plane, Hard Beyond It, held STOC 2027 submission; SHA-256 89f18334320ba73627305c6f8870ae70fef423ca012f8b71a3052e407c7e62ec, printed pp. 7, 28–31 (PDF 8, 29–32), Definitions 3–4

import Mathlib
import Definitions.Def_FairKMeans_WeightedKMeans

noncomputable section
open scoped Classical
open scoped BigOperators
open Finset

namespace ExactKMeans.ProductReduction

abbrev E := FairKMeans.E
/-- Section 5 normalization, before any geometric conclusions. -/
structure Parameters where
  a : ℕ
  b : ℕ
  t : ℕ
  a_pos : 0 < a
  b_pos : 0 < b
  q_ge : 2 ≤ a * b
  t_ge : 3 ≤ t
  t_odd : Odd t

def Parameters.N (p : Parameters) : ℕ := p.a * p.b * p.t
def Parameters.lam (p : Parameters) : ℕ := p.N ^ 12 - p.t + 1
def Parameters.alpha (p : Parameters) : ℝ := Classical.epsilon fun x : ℝ =>
  0 < x ∧ (1 / 2 : ℝ) < x * p.lam ∧ x * p.lam < 1 ∧
    (p.lam : ℝ) * Real.sin x = Real.cos (((p.t : ℝ) - 1) * x)
def Parameters.r (p : Parameters) : ℝ :=
  1 / (Real.sqrt p.b * (p.N : ℝ)^12 * Real.sin p.alpha)
def Parameters.delta (p : Parameters) : ℝ := 1 / (p.N : ℝ)^5
def Parameters.gamma (p : Parameters) : ℝ := p.alpha * p.r * p.delta / Real.sqrt p.b
def Parameters.beta (p : Parameters) : ℝ := Real.arcsin (1 / (4 * (p.a : ℝ)^2 * Real.sqrt p.b))
def Parameters.theta (p : Parameters) (i : Fin p.a) : ℝ :=
  Real.arcsin (((i.val : ℝ) + 1) / (p.a : ℝ)^2)
def Parameters.d (p : Parameters) : ℕ := 2 * p.b + 1
abbrev State (p : Parameters) := Fin p.b → Fin p.t
abbrev States (p : Parameters) := Fin p.a → State p
def stateValue (p : Parameters) (s : Fin p.t) : ℝ := (s.val : ℝ) - ((p.t : ℝ) - 1) / 2
def zeroState (p : Parameters) : State p := fun _ => ⟨p.t / 2, by have := p.t_ge; omega⟩
def arcValue (p : Parameters) (l : Fin (p.t - 1)) : ℝ := (l.val : ℝ) + 1 - (p.t : ℝ) / 2

def unit (d : ℕ) (j : ℕ) : E d := WithLp.toLp 2 (fun i => if i.val = j then 1 else 0)
def e (p : Parameters) (j : Fin p.b) : E p.d := unit p.d (2 * j.val)
def ep (p : Parameters) (j : Fin p.b) : E p.d := unit p.d (2 * j.val + 1)
def axis (p : Parameters) : E p.d := unit p.d (2 * p.b)
def ebar (p : Parameters) : E p.d := (1 / Real.sqrt p.b) • ∑ j, e p j
def epbar (p : Parameters) : E p.d := (1 / Real.sqrt p.b) • ∑ j, ep p j
def rot (α s : ℝ) {d : ℕ} (u v : E d) : E d :=
  Real.cos (2 * s * α) • u + Real.sin (2 * s * α) • v
def rotp (α s : ℝ) {d : ℕ} (u v : E d) : E d :=
  (-Real.sin (2 * s * α)) • u + Real.cos (2 * s * α) • v
def sign (s : Bool) : ℝ := if s then 1 else -1
abbrev Occ (p : Parameters) := (Bool × Fin (p.b * p.lam)) ⊕ (Bool × Fin p.b × Fin (p.t - 1))
def selectorPoint (p : Parameters) : Occ p → E p.d
  | .inl (s, _) => (sign s / Real.sqrt p.b) • ebar p
  | .inr (s, j, l) => sign s • rotp p.alpha (arcValue p l) (e p j) (ep p j)
def prefixSet (p : Parameters) (s : State p) : Finset (Occ p) :=
  univ.filter fun o => match o with
    | .inl (sg, _) => sg = true
    | .inr (sg, j, l) => if sg then arcValue p l < stateValue p (s j)
      else stateValue p (s j) < arcValue p l

def mean {ι : Type} [Fintype ι] {d : ℕ} (X : ι → E d) (C : Finset ι) : E d :=
  (1 / (C.card : ℝ)) • ∑ x ∈ C, X x
def clusterCost {ι : Type} [Fintype ι] {d : ℕ} (X : ι → E d) (C : Finset ι) : ℝ :=
  ∑ x ∈ C, ‖X x - mean X C‖^2
def partitionCost (p : Parameters) (C : Finset (Occ p)) : ℝ :=
  clusterCost (selectorPoint p) C + clusterCost (selectorPoint p) (univ \ C)
/-- Representative of an unordered nonempty two-part partition, oriented at a positive heavy occurrence. -/
def TwoPartition (p : Parameters) (C : Finset (Occ p)) : Prop :=
  C.Nonempty ∧ (univ \ C).Nonempty ∧
    ∃ j : Fin (p.b * p.lam), Sum.inl (true, j) ∈ C ∧ j.val = 0
def OptimalPartition (p : Parameters) (C : Finset (Occ p)) : Prop :=
  TwoPartition p C ∧ ∀ D, TwoPartition p D → partitionCost p C ≤ partitionCost p D
def mu0 (p : Parameters) (s : State p) : E p.d :=
  (p.r / Real.sqrt p.b) • ∑ j, rot p.alpha (stateValue p (s j)) (e p j) (ep p j)
def B1 (p : Parameters) : ℝ := 2 * ((p.N : ℝ)^12 + ((p.b : ℝ) - 1) * ((p.t : ℝ) - 1))
def B2 (p : Parameters) : ℝ := B1 p - 2 * p.b * (p.N : ℝ)^12 * p.r^2
/-- Indexed occurrences, including duplicates, with the published unit-weight objective. -/
def opt {d : ℕ} (X : List (E d)) (k : ℕ) : ℝ :=
  FairKMeans.kmOpt (fun i : Fin X.length => X[i]) (fun _ => 1) k

def cost {ι : Type} [Fintype ι] {d : ℕ} (X : List (E d)) (M : ι → E d) : ℝ :=
  (X.map fun x => ⨅ i, ‖x - M i‖^2).sum
def Served {ι : Type} {d : ℕ} (M : ι → E d) (x : E d) (i : ι) : Prop :=
  ∀ j, ‖x - M i‖^2 ≤ ‖x - M j‖^2
end ExactKMeans.ProductReduction


