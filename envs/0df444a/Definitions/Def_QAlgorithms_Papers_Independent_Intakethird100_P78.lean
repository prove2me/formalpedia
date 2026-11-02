-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P78
-- name    : QAlgorithms_Papers_Independent_Intakethird100_P78
-- status  : Definition
-- author  : @Gohan
-- created : 2026-11-01T06:14:13.369077+00:00
-- url     : https://prove2.me/theorems/9cc2e518-3c64-4d2c-835a-aab4c18959dc
-- title:
--   Definitions for Bipartite Units of Non-Locality
-- statement:
--   The objects the formalized statements of *Bipartite Units of Non-Locality* (arXiv:0808.0651) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `BipartiteConditionalArray`: PDF p.2: a conditional array, before imposing probability and no-signaling conditions. The two input and two output alphabets may differ.
--   - `BipartiteSystem`: PDF pp.2–3: the finite bipartite systems considered in this paper. Nonempty alphabets are imposed at each theorem using this structure. The two marginal equalities express no-signaling for both proper subsets.
--   - `simulationDistance`: PDF p.2, Definition 1: worst-input total variation. The range whose supremum is taken is finite and nonempty, hence bounded and nonempty; there is no default empty/unbounded real supremum in the stated domain.
--   - `graphKernel`: PDF p.3, Definition 3: uniform graph law of a family of maps. This raw array belongs to D precisely when d > 1 and the maps are permutations; that condition is stated by IsPermutationSystem below.
--   - `IsPermutationSystem`: PDF p.3, Definition 3: membership in D, without presupposing that a constructed candidate map is bijective.
--   - `liftLabel`: PDF p.4, (8): zero-based form of r_hat, which exchanges the omitted label with the last label. Here d = m + 1.
--   - `dropLabel`: PDF p.4, inverse of (8), on the complement of hat. Modulo gives a specified total extension off that complement. For a valid complement label the swapped value is less than m, so modulo does not change it. All uses in the reduction have this valid-complement property as a consequence of the given permutation, rather than an extra hypothesis.
--   - `reducedMap`: PDF p.4, corrected (7): set u = r_ahat(a), replace f(u) by f(ahat) exactly when f(u) = bhat, then apply r_bhat inverse. Printed (7) instead tests f(a) = bhat, a != ahat; this fails when f(last) = bhat and ahat is not last. This definition implements the deletion-and-splicing construction described in the text and Figures 4–5.
--   - `reducedKernel`: PDF pp.4–5: the computed smaller resource has augmented local inputs (x,ahat) and (y,bhat), and m outputs on each side.
--   - `roundKernel`: PDF p.5, four-step round: a fresh shared coin, independent of the resource, keeps (ahat,bhat) with mass 1/(m+1). Otherwise, the smaller resource's outputs are relabeled separately. The sum explicitly uses that resource; no unconstrained transition probability is supplied.
--   - `finiteRoundKernel`: PDF pp.5,7, exact-resource experiment: start from independent uniform local labels and apply n rounds. The convolution uses a fresh coin and an independent exact resource copy in each round. This specifies this particular synchronous construction, not the general wiring model.
--   - `relabeledKernel`: PDF p.8, Lemma 5 proof: one permutation resource followed by local relabelings depending solely on the corresponding test input.
--   - `IsRational`: PDF p.8: entirely rational probabilities; zeros and ones are allowed.
--   - `HasCommonProbabilityDenominator`: PDF p.8: a padded common denominator d, not necessarily the least one. Nonnegative integer numerators are appropriate because these are probabilities. Padding to d >= 2 retains deterministic target systems in Definition 3.
-- source:
--   Bipartite Units of Non-Locality, arXiv:0808.0651v4, https://arxiv.org/abs/0808.0651v4

import Mathlib

/-!
# Bipartite Units of Nonlocality (arXiv:0808.0651v4)

Finite-law statements from PDF pp.4–8. Equation (7) is corrected by testing
f(r_hat(a)) rather than f(a); the deleted edge is spliced as described in the
plan. The printed R in the rational-case paragraph on p.8 is corrected to D.
Both corrections require independent moderation. General wiring results and
the disputed adaptive lemmas are explicitly deferred in the unit artifacts.
No unreviewed module or paper-specific quantum-information predicate is used.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intakethird100.P78

attribute [local instance] Classical.propDecidable Classical.decEq

/-- PDF p.2: a conditional array, before imposing probability and no-signaling
conditions. The two input and two output alphabets may differ. -/
abbrev BipartiteConditionalArray (X Y A B : Type) := X → Y → A → B → ℝ

/-- PDF pp.2–3: the finite bipartite systems considered in this paper.
Nonempty alphabets are imposed at each theorem using this structure.
The two marginal equalities express no-signaling for both proper subsets. -/
structure BipartiteSystem (X Y A B : Type) [Fintype A] [Fintype B] where
  prob : BipartiteConditionalArray X Y A B
  nonnegative : ∀ x y a b, 0 ≤ prob x y a b
  normalized : ∀ x y, ∑ a, ∑ b, prob x y a b = 1
  aliceNS : ∀ x y z a, ∑ b, prob x y a b = ∑ b, prob x z a b
  bobNS : ∀ x z y b, ∑ a, prob x y a b = ∑ a, prob z y a b

/-- PDF p.2, Definition 1: worst-input total variation. The range whose
supremum is taken is finite and nonempty, hence bounded and nonempty;
there is no default empty/unbounded real supremum in the stated domain. -/
def simulationDistance {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Nonempty X] [Nonempty Y]
    (S T : BipartiteConditionalArray X Y A B) : ℝ :=
  sSup (Set.range fun xy : X × Y =>
    (∑ a, ∑ b, |S xy.1 xy.2 a b - T xy.1 xy.2 a b|) / 2)

/-- PDF p.3, Definition 3: uniform graph law of a family of maps.
This raw array belongs to D precisely when d > 1 and the maps are
permutations; that condition is stated by IsPermutationSystem below. -/
def graphKernel {X Y : Type} {d : ℕ}
    (F : X → Y → Fin d → Fin d) : BipartiteConditionalArray X Y (Fin d) (Fin d) :=
  fun x y a b => if F x y a = b then 1 / (d : ℝ) else 0

/-- PDF p.3, Definition 3: membership in D, without presupposing that a
constructed candidate map is bijective. -/
def IsPermutationSystem {X Y : Type} {d : ℕ}
    (P : BipartiteConditionalArray X Y (Fin d) (Fin d)) : Prop :=
  1 < d ∧ ∃ F : X → Y → Fin d → Fin d,
    (∀ x y, Function.Bijective (F x y)) ∧ P = graphKernel F

/-- PDF p.4, (8): zero-based form of r_hat, which exchanges the omitted
label with the last label. Here d = m + 1. -/
def liftLabel {m : ℕ} (hat : Fin (m + 1)) (a : Fin m) : Fin (m + 1) :=
  Equiv.swap hat (Fin.last m) a.castSucc

/-- PDF p.4, inverse of (8), on the complement of hat. Modulo gives a
specified total extension off that complement. For a valid complement
label the swapped value is less than m, so modulo does not change it.
All uses in the reduction have this valid-complement property as a
consequence of the given permutation, rather than an extra hypothesis. -/
def dropLabel {m : ℕ} (hm : 0 < m)
    (hat v : Fin (m + 1)) : Fin m :=
  ⟨(Equiv.swap hat (Fin.last m) v).val % m, Nat.mod_lt _ hm⟩

/-- PDF p.4, corrected (7): set u = r_ahat(a), replace f(u) by f(ahat)
exactly when f(u) = bhat, then apply r_bhat inverse. Printed (7) instead
tests f(a) = bhat, a != ahat; this fails when f(last) = bhat and ahat
is not last. This definition implements the deletion-and-splicing
construction described in the text and Figures 4–5. -/
def reducedMap {m : ℕ} (hm : 0 < m)
    (f : Equiv.Perm (Fin (m + 1)))
    (ahat bhat : Fin (m + 1)) (a : Fin m) : Fin m :=
  let u := liftLabel ahat a
  dropLabel hm bhat (if f u = bhat then f ahat else f u)

/-- PDF pp.4–5: the computed smaller resource has augmented local inputs
(x,ahat) and (y,bhat), and m outputs on each side. -/
def reducedKernel {X Y : Type} {m : ℕ} (hm : 0 < m)
    (F : X → Y → Equiv.Perm (Fin (m + 1))) :
    BipartiteConditionalArray (X × Fin (m + 1)) (Y × Fin (m + 1)) (Fin m) (Fin m) :=
  graphKernel (fun xa yb => reducedMap hm (F xa.1 yb.1) xa.2 yb.2)

/-- PDF p.5, four-step round: a fresh shared coin, independent of the
resource, keeps (ahat,bhat) with mass 1/(m+1). Otherwise, the smaller
resource's outputs are relabeled separately. The sum explicitly uses
that resource; no unconstrained transition probability is supplied. -/
def roundKernel {m : ℕ} (hm : 0 < m)
    (f : Equiv.Perm (Fin (m + 1)))
    (ahat bhat a b : Fin (m + 1)) : ℝ :=
  (if a = ahat ∧ b = bhat then 1 / ((m + 1 : ℕ) : ℝ) else 0) +
    (m : ℝ) / ((m + 1 : ℕ) : ℝ) *
      ∑ u : Fin m, ∑ v : Fin m,
        if liftLabel ahat u = a ∧ liftLabel bhat v = b then
          (if reducedMap hm f ahat bhat u = v then 1 / (m : ℝ) else 0)
        else 0

/-- PDF pp.5,7, exact-resource experiment: start from independent uniform
local labels and apply n rounds. The convolution uses a fresh coin and
an independent exact resource copy in each round. This specifies this
particular synchronous construction, not the general wiring model. -/
def finiteRoundKernel {X Y : Type} {m : ℕ} (hm : 0 < m)
    (F : X → Y → Equiv.Perm (Fin (m + 1))) :
    ℕ → BipartiteConditionalArray X Y (Fin (m + 1)) (Fin (m + 1))
  | 0 => fun _ _ _ _ => 1 / (((m + 1 : ℕ) : ℝ) ^ 2)
  | n + 1 => fun x y a b =>
      ∑ ahat, ∑ bhat,
        finiteRoundKernel hm F n x y ahat bhat *
          roundKernel hm (F x y) ahat bhat a b

/-- PDF p.8, Lemma 5 proof: one permutation resource followed by local
relabelings depending solely on the corresponding test input. -/
def relabeledKernel {X Y A B : Type} {d : ℕ}
    (F : X → Y → Equiv.Perm (Fin d))
    (alice : X → Fin d → A) (bob : Y → Fin d → B) : BipartiteConditionalArray X Y A B :=
  fun x y a b => ∑ u : Fin d,
    if alice x u = a ∧ bob y (F x y u) = b then 1 / (d : ℝ) else 0

/-- PDF p.8: entirely rational probabilities; zeros and ones are allowed. -/
def IsRational {X Y A B : Type} (P : BipartiteConditionalArray X Y A B) : Prop :=
  ∀ x y a b, ∃ q : ℚ, (q : ℝ) = P x y a b

/-- PDF p.8: a padded common denominator d, not necessarily the least one.
Nonnegative integer numerators are appropriate because these are probabilities.
Padding to d >= 2 retains deterministic target systems in Definition 3. -/
def HasCommonProbabilityDenominator {X Y A B : Type} (P : BipartiteConditionalArray X Y A B) (d : ℕ) : Prop :=
  ∀ x y a b, ∃ k : ℕ, P x y a b = (k : ℝ) / (d : ℝ)

-- Sanity: a deterministic singleton-output law is a legitimate no-signaling
-- system; the target alphabets need not have two distinct outputs.
example : BipartiteSystem Unit Unit Unit Unit where
  prob := fun _ _ _ _ => 1
  nonnegative := by intros; norm_num
  normalized := by intros; simp
  aliceNS := by intros; rfl
  bobNS := by intros; rfl

-- Sanity for (8): deleting the last label leaves the remaining labels fixed.
example {m : ℕ} (a : Fin m) : liftLabel (Fin.last m) a = a.castSucc := by
  simp [liftLabel]

-- Sanity for the total inverse on its valid domain.
example {m : ℕ} (hm : 0 < m) (a : Fin m) :
    dropLabel hm (Fin.last m) a.castSucc = a := by
  apply Fin.ext
  simp [dropLabel, Nat.mod_eq_of_lt a.isLt]

-- Sanity for the resource normalization constant, without enumeration.
example {d : ℕ} (F : Unit → Unit → Fin d → Fin d) (a : Fin d) :
    graphKernel F () () a (F () () a) = 1 / (d : ℝ) := by
  simp [graphKernel]

-- Sanity: n = 0 is an independent-uniform law, before any resource use.
example {X Y : Type} {m : ℕ} (hm : 0 < m)
    (F : X → Y → Equiv.Perm (Fin (m + 1))) (x : X) (y : Y)
    (a b : Fin (m + 1)) :
    finiteRoundKernel hm F 0 x y a b = 1 / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  rfl

-- Sanity: relabeling all labels to the singleton output retains all d atoms.
example {d : ℕ} (F : Unit → Unit → Equiv.Perm (Fin d)) :
    relabeledKernel F (fun _ _ => ()) (fun _ _ => ()) () () () () =
      (d : ℝ) * (1 / (d : ℝ)) := by
  simp [relabeledKernel]

-- Sanity: arbitrary permutations on at least two labels satisfy the D predicate.
example {X Y : Type} {d : ℕ} (hd : 1 < d)
    (F : X → Y → Equiv.Perm (Fin d)) :
    IsPermutationSystem (graphKernel (fun x y => F x y)) := by
  exact ⟨hd, (fun x y => F x y), (fun x y => (F x y).bijective), rfl⟩

-- Sanity: the constant deterministic law is rational, including denominator one.
example : IsRational (fun (_ _ _ _ : Unit) => (1 : ℝ)) := by
  intro x y a b
  exact ⟨1, by norm_num⟩

-- Sanity: padding a deterministic probability to denominator two is allowed.
example : HasCommonProbabilityDenominator (fun (_ _ _ _ : Unit) => (1 : ℝ)) 2 := by
  intro x y a b
  exact ⟨2, by norm_num⟩

-- Sanity: worst-input distance vanishes for identical singleton laws.
example : simulationDistance (fun (_ _ _ _ : Unit) => (1 : ℝ))
    (fun (_ _ _ _ : Unit) => (1 : ℝ)) = 0 := by
  simp [simulationDistance]

end QAlgorithms.Papers.Independent.Intakethird100.P78


