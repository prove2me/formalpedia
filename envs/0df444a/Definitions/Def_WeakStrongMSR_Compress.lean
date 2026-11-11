-- Prove2me | Definitions.Def_WeakStrongMSR_Compress
-- name    : WeakStrongMSR_Compress
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:29:57.283379+00:00
-- url     : https://prove2.me/theorems/fc9ae48d-324c-47db-abac-89e083fd509e
-- title:
--   MSR on a subset, offline routines, and compression (§3.4, Algorithm 4)
-- statement:
--   1. For a set $S$ of points, $\mathrm{opt}_S$ is the least $\sum_j \mathrm{rad}_S(C_j)$ over partitions of $S$ into at most $k$ clusters. Here $\mathrm{rad}_S(C)=\min_{p\in S}\max_{q\in C}d(p,q)$, the centres are restricted to $S$, and an empty cluster costs $0$ (Lemma 3.32).
--   2. An **offline routine** returns a $k$-slot solution for every strong set $S$. It is **good with parameter $\varepsilon$** if for every $S$ its radii are nonnegative, its balls cover $S$, and its cost is at most $(3+\varepsilon)\,\mathrm{opt}_S$. This is the guarantee of the routine of [BERW24].
--   3. **Compression** runs the offline routine on the final strong set. Each nonempty repaired list goes to the slot of its root; a point on several lists uses the list of least root index. Each slot's radius grows by $\max(\{3R_J : X_J \text{ assigned to the slot}\}\cup\{0\})$.
--
--   **Formalization Note** The offline routine is a parameter. Centres outside $S$ are not excluded, which admits more routines.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §3.4, pp.25–26 (PDF 26–27), Algorithm 4, p.26 (PDF 27); Lemma 3.32, p.26 (PDF 27)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Rounding
import Definitions.Def_WeakStrongMSR_Repair

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# MSR on a subset and the compression step (§3.4, Algorithm 4)

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), §3.4, pp.25–26, Algorithm 4, p.26: "Run the
polynomial-time (3 + ϵ)-approximation of [BERW24] on the exact metric restricted to S, obtaining at
most k balls B; Assign every point of S to a ball of B covering it; for each nonempty list X_J: Let
B(z, r) ∈ B be the ball to which its root c_J was assigned; assign all points of X_J to that ball;
for each B(z, r) ∈ B do Increase its radius by max({3R_J : X_J was assigned to this ball} ∪ {0})";
"If a point belongs to several repaired lists, assign it via any one of them." Lemma 3.32, p.26
("the optimum minimum-sum-of-radii cost on the metric induced by S, with centres restricted to S").

This module bundles the solution type, the subset optimum, the offline routine interface and the
compression map.

**Formalization Note.**
* A solution has `k` slots (R6): labels `σ`, centres `ctr`, radii `rad`.
* `optOn d k S` is the least `∑_j rad_S(σ⁻¹(j) ∩ S)` over labellings `σ`, with
  `rad_S(C) = min_{p ∈ S} max_{q ∈ C} d(p, q)` (centres restricted to `S`) and `rad_S(∅) = 0`; it is
  `0` for `S = ∅`.
* The offline routine of [BERW24] (R11) is a parameter: any map returning, for each `S`, a solution
  whose balls cover `S` with nonnegative radii and total radius at most `(3 + ε) · optOn d k S`
  (`GoodOffline`). Centres are not required to lie in `S` (more routines qualify).
* A point on several lists is assigned through the component of least root index (R12). -/

/-- A solution with `k` slots. -/
structure Sol (n k : ℕ) where
  /-- The slot label of each point. -/
  σ : Fin n → Fin k
  /-- The centre of each slot. -/
  ctr : Fin k → Fin n
  /-- The radius of each slot. -/
  rad : Fin k → ℝ

/-- `rad_S(C) = min_{p ∈ S} max_{q ∈ C} d(p, q)`, and `0` if `C` or `S` is empty. -/
noncomputable def radOn {n : ℕ} (d : Fin n → Fin n → ℝ) (S C : Finset (Fin n)) : ℝ :=
  if h : C.Nonempty ∧ S.Nonempty then S.inf' h.2 (fun p => C.sup' h.1 (fun q => d p q)) else 0

/-- The MSR optimum of `S` with centres restricted to `S` (Lemma 3.32). -/
noncomputable def optOn {n : ℕ} (d : Fin n → Fin n → ℝ) (k : ℕ) (S : Finset (Fin n)) : ℝ :=
  if h : (Finset.univ : Finset (Fin n → Fin k)).Nonempty then
    (Finset.univ : Finset (Fin n → Fin k)).inf' h
      (fun σ => ∑ j : Fin k, radOn d S (S.filter (fun v => σ v = j)))
  else 0

/-- An offline MSR routine: a solution for each strong set `S`. -/
abbrev OfflineRoutine (n k : ℕ) : Type := Finset (Fin n) → Sol n k

/-- The routine covers `S` with nonnegative radii and total radius at most `(3 + ε) · optOn d k S`,
for every `S`. -/
def GoodOffline {n k : ℕ} (d : Fin n → Fin n → ℝ) (ε : ℝ) (off : OfflineRoutine n k) : Prop :=
  ∀ S : Finset (Fin n), (∀ j, 0 ≤ (off S).rad j) ∧
    (∀ x ∈ S, d ((off S).ctr ((off S).σ x)) x ≤ (off S).rad ((off S).σ x)) ∧
    solCost (off S).rad ≤ (3 + ε) * optOn d k S

/-- Compression (Algorithm 4) of the repaired lists `rp` of the rounding output `r`, with the
offline routine `off`. -/
noncomputable def compress {n k : ℕ} (r : RoundOut n) (rp : RepairOut n r.m)
    (off : OfflineRoutine n k) : Sol n k :=
  let B := off rp.S
  let nonempty := r.roots.filter (fun j => (rp.lists j).Nonempty)
  let slotOf : Fin r.m → Fin k := fun j => B.σ (r.ctr j)
  { σ := fun v =>
      if v ∈ rp.S then B.σ v else
        if hv : (nonempty.filter (fun j => v ∈ rp.lists j)).Nonempty then
          slotOf ((nonempty.filter (fun j => v ∈ rp.lists j)).min' hv)
        else B.σ v
    ctr := B.ctr
    rad := fun t =>
      B.rad t + (nonempty.filter (fun j => slotOf j = t)).fold max 0 (fun j => 3 * r.radiusJ j) }

end WeakStrongMSR


