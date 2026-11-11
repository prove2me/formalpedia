-- Prove2me | Definitions.Def_PermanentStars_Counting_Gadgets
-- name    : PermanentStars_Counting_Gadgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:53:14.907111+00:00
-- url     : https://prove2.me/theorems/8e5dd2ef-7375-4499-86fb-5b24cb4084c4
-- title:
--   Signed star-formation coefficients and literal gadgets
-- statement:
--   For disjoint clusters $U_j$ of sizes $d_j$, the formation coefficient is
--   $$C_r(d)=\sum_{\rho:r(\rho)=r}\mu(\rho),$$
--   where every block has size greater than $r$ and lies in one cluster. The definition exposes this sum for arbitrary clusters as well as canonical consecutive clusters. Independence of cluster labels is a theorem obligation in Lemma 4.4, not an assumption.
--
--   A component state $(a;k,\nu)$ stores unused leaves, open-star size and counters. Begin decreases $a$ and opens size one with label one. Grow decreases $a$, increases $k$, increments the counter at the old size when that size is a selected cutoff at least $r$, and has $a$ distinct parallel transitions labelled $-1$. Close requires $k>r$. Components process the clusters in order, carrying counters unchanged. Acceptance requires $\nu_r\le\alpha_r n$ and $\nu_s>\alpha_s n$ for every larger selected cutoff. The empty nursery and $n=0$ use the same assignment rule.
--
--   The gadget is a concrete rule graph. Its output and polynomial size are not part of its data.
-- source:
--   Radu Curticapean, STOC 2027 submission #1331 (October 2026), Definition 4.3 and equations (14)–(17), p.9

import Definitions.Def_PermanentStars_Counting_Nursery

namespace PermanentStars.Counting

abbrev Counters (P : Cutoffs) (n : ℕ) := P.R → Fin (n + 1)
abbrev ClusterState (P : Cutoffs) (n : ℕ) :=
  Fin n × Fin (n + 1) × Fin (n + 1) × Counters P n
abbrev GadgetVertex (P : Cutoffs) (n : ℕ) := Unit ⊕ (ClusterState P n ⊕ Unit)

def zeroCounters (P : Cutoffs) (n : ℕ) : Counters P n := fun _ => 0

def accepts (P : Cutoffs) (n r : ℕ) (nu : Counters P n) : Prop :=
  (∀ s : P.R, s.val = r → ((nu s).val : ℚ) ≤ P.alpha r * n) ∧
  (∀ s : P.R, r < s.val → P.alpha s.val * n < ((nu s).val : ℚ))

/-- Canonical disjoint clusters of sizes d_j: consecutive intervals of the ordered leaves. -/
def cluster {n : ℕ} (d : Nursery n) (j : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    (∑ k ∈ Finset.univ.filter (fun k : Fin n => k < j), (d k).val) ≤ i.val ∧
    i.val < (∑ k ∈ Finset.univ.filter (fun k : Fin n => k ≤ j), (d k).val))

/-- Definition 4.3, eq.(14). This is a partition sum, not an assumed gadget output. -/
noncomputable def formationCoefficientOn {n : ℕ} (P : Cutoffs) (r : ℕ)
    (clusters : Fin n → Finset (Fin n)) : ℤ := by
  classical
  let U := Finset.univ.biUnion clusters
  exact ∑ rho : Finpartition U,
    if (∀ B ∈ rho.parts, r < B.card ∧ ∃ j : Fin n, B ⊆ clusters j) ∧
        assigned P n rho.parts = some r then mobius rho.parts else 0

noncomputable def formationCoefficient {n : ℕ} (P : Cutoffs) (r : ℕ) (d : Nursery n) : ℤ :=
  formationCoefficientOn P r (cluster d)

/-- Equations (15)--(17), including a separate slot for each of the a parallel Grow edges. -/
def gadgetRule {n : ℕ} (P : Cutoffs) (r : ℕ) (d : Nursery n)
    (s t : GadgetVertex P n) (l : Label n) (slot : Fin (n + 1)) : Prop :=
  ((slot.val = 0 ∧ l = .one) ∧
    ((n = 0 ∧ s = .inl () ∧ t = .inr (.inr ()) ∧
        assigned P n ∅ = some r) ∨
     (∃ j : Fin n, j.val = 0 ∧ s = .inl () ∧
        t = .inr (.inl (j, d j, 0, zeroCounters P n))) ∨
     (∃ j a k nu a' k', s = .inr (.inl (j, a, k, nu)) ∧
        0 < a.val ∧ k.val = 0 ∧ a'.val + 1 = a.val ∧ k'.val = 1 ∧
        t = .inr (.inl (j, a', k', nu))) ∨
     (∃ j a k nu, s = .inr (.inl (j, a, k, nu)) ∧ r < k.val ∧
        t = .inr (.inl (j, a, 0, nu))) ∨
     (∃ j j' nu, s = .inr (.inl (j, 0, 0, nu)) ∧ j'.val = j.val + 1 ∧
        t = .inr (.inl (j', d j', 0, nu))) ∨
     (∃ j nu, s = .inr (.inl (j, 0, 0, nu)) ∧ j.val + 1 = n ∧ accepts P n r nu ∧
        t = .inr (.inr ())))) ∨
  (l = .negOne ∧ ∃ j a k nu a' k' nu', s = .inr (.inl (j, a, k, nu)) ∧
    0 < a.val ∧ 0 < k.val ∧ slot.val < a.val ∧ a'.val + 1 = a.val ∧ k'.val = k.val + 1 ∧
    (∀ s : P.R, (nu' s).val = (nu s).val + if s.val = k.val ∧ r ≤ k.val then 1 else 0) ∧
    t = .inr (.inl (j, a', k', nu')))

noncomputable def formationABP {n : ℕ} (P : Cutoffs) (r : ℕ) (d : Nursery n) :
    Graph (GadgetVertex P n) (Label n) :=
  ruleGraph _ _ (.inl ()) (.inr (.inr ())) (n + 1) (gadgetRule P r d)

end PermanentStars.Counting


