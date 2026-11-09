-- Prove2me | Definitions.Def_RandOnlineSetCover_InfoLB_Model
-- name    : RandOnlineSetCover_InfoLB_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:38:33.465487+00:00
-- url     : https://prove2.me/theorems/bacc58d9-025c-4b7e-a459-1fc716bd2b98
-- title:
--   Unknown-instance online set cover: instances, strategies, cost and optimum
-- statement:
--   There are $m$ labeled sets and exactly $n$ arriving elements. An instance is an ordered sequence $(E_1,\ldots,E_n)$ of nonempty subsets of $[m]$, where $E_t$ lists the sets containing the element arriving at time $t$. Distinct labels may have identical contents. A deterministic algorithm chooses an arbitrary subset of labels after each observed incidence prefix. Purchases accumulate by union, and each coverable arrival must be covered immediately. No future incidences, element names, tree vertices or hidden indices are inputs to the rule. The cost counts distinct purchased labels.
--
--   For a request sequence $\sigma$, write $\mathcal C_A(\sigma)$ for the union of purchases. The offline optimum and mixed-strategy cost are
--
--   $$
--   \operatorname{Opt}(I)=\min\{|C|: C\cap E_t\ne\varnothing\text{ for every }t\},\qquad
--   \mathbb E_R[|A(I)|]=\sum_A R(A)|\mathcal C_A(I)|.
--   $$
--
--   Distributions over instances and their expected costs are also finite probability distributions. The predicate $\operatorname{OptBound}(D,L)$ asserts $\operatorname{Opt}(I)\le L$ at every instance of positive probability. Finally, write $r(m,n)=\log_2 m\log_2 n/(\log_2\log_2 m+\log_2\log_2 n)$.
--
--   This interface supplies the information model shared by all distributional and randomized lower bounds.
--
--   **Formalization Note** Histories and decision tables have finite types at fixed $m,n$, so a PMF over valid tables includes every randomized strategy. Coverage is required only for nonempty incidences; the rule that buys all labels is valid. A list interface permits shorter sequences within the fixed horizon. The raw-list optimum uses $\mathbb N\cup\{+\infty\}$, assigning $+\infty$ to an uncoverable list and zero to the empty list. For valid instances it is finite, and `Opt` converts that finite natural value to $\mathbb N$. No theorem assumes finiteness in place of proving it.
-- source:
--   Roie Levin, STOC 2027 submission #400 (October 2026), §1 and footnote 1, p. 2; binary logarithm convention, §2, p. 3. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/400.pdf

import Mathlib

namespace RandOnlineSetCover.InfoLB

/-- §1 and footnote 1, p. 2: m set labels, exactly n arrivals, all coverable. -/
abbrev Instance (m n : ℕ) :=
  {x : Fin n → Finset (Fin m) // ∀ i, (x i).Nonempty}

noncomputable instance instanceFintype (m n : ℕ) : Fintype (Instance m n) :=
  Fintype.ofFinite _

/-- An ordered observation history of length at most n, with no element identifiers. -/
abbrev History (m n : ℕ) := Σ t : Fin (n + 1), Fin t.val → Finset (Fin m)

/-- Arbitrary sets may be added after each nonempty observation history. -/
abbrev Rule (m n : ℕ) :=
  (t : Fin n) → (Fin (t.val + 1) → Finset (Fin m)) → Finset (Fin m)

/-- Distinct purchases, taking the union over all steps. The list interface also serves §3. -/
def chosen {m n : ℕ} (A : Rule m n) (σ : List (Finset (Fin m))) : Finset (Fin m) :=
  Finset.univ.biUnion fun t : Fin n =>
    if t.val < σ.length then A t (fun i => σ[i.val]?.getD ∅) else ∅

/-- Coverage is required only for nonempty incidence lists, at their arrival time. -/
def IsValid {m n : ℕ} (A : Rule m n) : Prop :=
  ∀ h : History m n, ∀ t : Fin h.1.val, (h.2 t).Nonempty →
    (chosen A ((List.ofFn h.2).take (t.val + 1)) ∩ h.2 t).Nonempty

abbrev DetAlg (m n : ℕ) := {A : Rule m n // IsValid A}

noncomputable instance detAlgFintype (m n : ℕ) : Fintype (DetAlg m n) :=
  Fintype.ofFinite _

/-- The all-labels rule witnesses that the validity predicate is satisfiable. -/
def buyAll (m n : ℕ) : Rule m n := fun _ _ => Finset.univ

/-- Cost counts each label once, regardless of repeated selections. -/
def listCost {m n : ℕ} (A : DetAlg m n) (σ : List (Finset (Fin m))) : ℕ :=
  (chosen A.val σ).card

def cost {m n : ℕ} (A : DetAlg m n) (I : Instance m n) : ℕ :=
  listCost A (List.ofFn I.val)

/-- All offline covers, including the full family whenever every incidence is nonempty. -/
def Covers {m : ℕ} (σ : List (Finset (Fin m))) (C : Finset (Fin m)) : Prop :=
  ∀ e ∈ σ, (C ∩ e).Nonempty

/-- Extended natural value: an uncoverable raw list has optimum +∞, never a junk zero. -/
noncomputable def listOpt {m : ℕ} (σ : List (Finset (Fin m))) : ℕ∞ :=
  ⨅ C : {C : Finset (Fin m) // Covers σ C}, (C.val.card : ℕ∞)

noncomputable def Opt {m n : ℕ} (I : Instance m n) : ℕ :=
  (listOpt (List.ofFn I.val)).toNat

/-- Finite mixed strategies capture every randomized algorithm at this horizon. -/
abbrev RandAlg (m n : ℕ) := PMF (DetAlg m n)

noncomputable def expectedCost {m n : ℕ} (R : RandAlg m n) (I : Instance m n) : ℝ :=
  ∑ A : DetAlg m n, (R A).toReal * (cost A I : ℝ)

abbrev InstanceDistribution (m n : ℕ) := PMF (Instance m n)

noncomputable def distributionCost {m n : ℕ} (D : InstanceDistribution m n)
    (A : DetAlg m n) : ℝ :=
  ∑ I : Instance m n, (D I).toReal * (cost A I : ℝ)

/-- Probability one, equivalently every point in the finite PMF support. -/
def OptBound {m n : ℕ} (D : InstanceDistribution m n) (L : ℕ) : Prop :=
  ∀ I : Instance m n, D I ≠ 0 → Opt I ≤ L

/-- All logarithms in the paper are binary (§2, p. 3). -/
noncomputable def logRatio (m n : ℕ) : ℝ :=
  (Real.logb 2 m * Real.logb 2 n) /
    (Real.logb 2 (Real.logb 2 m) + Real.logb 2 (Real.logb 2 n))

end RandOnlineSetCover.InfoLB


