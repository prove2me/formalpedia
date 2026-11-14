-- Prove2me | Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_Triangularization
-- name    : ConsistentSubmodular_Deterministic_Certificates_Triangularization
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:10:42.772928+00:00
-- url     : https://prove2.me/theorems/56a58461-84ed-492e-b8d8-14ddb8ed131e
-- title:
--   Triangularization of a compatible profile: raw and triangular length arrays
-- statement:
--   Let $P$ be a compatible profile on $m+1$ types: a family of nonnegative monotone submodular objectives $f_t$ ($t\in\mathbb N$) on subsets of the types, with $f_t(I)$ nondecreasing in $t$ and every marginal $f_t(J)-f_t(I)$ ($I\subseteq J$) nonincreasing in $t$. Its residual at time $t$ of type $i$ is $\rho_t(i)=f_t(\{i\})-f_t(\emptyset)$, and its loss is $\rho_t(i)-\rho_{t+1}(i)\ge0$.
--
--   - `rawLength` $i\,j$: $\ell^{\rm raw}_{i,j}=\rho_m(i)$ if $j=m$, and the loss $\rho_j(i)-\rho_{j+1}(i)$ if $j<m$. Its tail sum from $t$ telescopes to $\rho_t(i)$.
--   - `triangularLength` $i\,j$: $\ell_{i,j}=\ell^{\rm raw}_{i,j}$ if $i\le j$ and $0$ if $j<i$, so only the part of the loss at stages not before $i$ is kept.
--   - `toTriangularArray`: under the hypotheses $\rho_0(0)=1$ and $\rho_t(i)\le\rho_t(t)$ for all $t,i$, the array $\ell_{i,j}$ is a `TriangularArray m`. Nonnegativity and triangularity are immediate, the tail from $t$ of row $t$ equals $\rho_t(t)$, and the tail of any row $i$ from $t$ is at most $\rho_t(i)\le\rho_t(t)$, which gives domination; for $t=0$ this also yields the normalization. Labels keep their prescribed stage identities even when distinct types have the same physical core.
--
--   The file also proves the telescoping identity for finite tail sums over $\mathrm{Fin}(m+1)$, nonnegativity of both length arrays, $\ell_{i,j}\le\ell^{\rm raw}_{i,j}$, the tail-sum formula $\sum_{j\ge t}\ell^{\rm raw}_{i,j}=\rho_t(i)$, and the tail bounds of the triangular array.
--
--   In the proof of Theorem 7 (Appendix B) these constructions reduce a compatible profile arising from a window instance to a canonical triangular array, which is then atomized and handed to the finite checkpoint theorem.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/Triangularization.lean (definitions and supporting lemmas of this module, ported from Lean v4.30.0-rc1 to Lean v4.33.1)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_ArrayCompletion

noncomputable section

open scoped BigOperators

namespace ConsistentSubmodular

theorem fin_tail_step {m : ℕ} (a : Fin (m + 1) → ℝ) (t : Fin m) :
    (∑ j, if t.castSucc ≤ j then a j else 0) =
      a t.castSucc + ∑ j, if t.succ ≤ j then a j else 0 := by
  have hpoint (j : Fin (m + 1)) :
      (if t.castSucc ≤ j then a j else 0) =
        (if j = t.castSucc then a j else 0) + (if t.succ ≤ j then a j else 0) := by
    by_cases heq : j = t.castSucc
    · subst j
      simp
    · have hiff : t.castSucc ≤ j ↔ t.succ ≤ j := by
        have hne : j.val ≠ t.val := by intro h; exact heq (Fin.ext h)
        simp only [Fin.le_def, Fin.val_castSucc, Fin.val_succ]
        omega
      simp [heq, hiff]
  simp_rw [hpoint]
  rw [Finset.sum_add_distrib]
  simp

namespace CompatibleProfile

variable {m : ℕ} (P : CompatibleProfile (m + 1))

def rawLength (i j : Fin (m + 1)) : ℝ :=
  if j = Fin.last m then P.residual m i else P.loss j.val i

def triangularLength (i j : Fin (m + 1)) : ℝ :=
  if i ≤ j then P.rawLength i j else 0

theorem rawLength_nonnegative (i j : Fin (m + 1)) : 0 ≤ P.rawLength i j := by
  unfold rawLength
  split_ifs
  · exact P.residualOn_nonnegative m {i}
  · exact P.loss_nonnegative j.val i

theorem triangularLength_nonnegative (i j : Fin (m + 1)) : 0 ≤ P.triangularLength i j := by
  unfold triangularLength
  split_ifs
  · exact P.rawLength_nonnegative i j
  · rfl

theorem triangularLength_le_raw (i j : Fin (m + 1)) :
    P.triangularLength i j ≤ P.rawLength i j := by
  unfold triangularLength
  split_ifs
  · rfl
  · exact P.rawLength_nonnegative i j

theorem rawLength_tail (i t : Fin (m + 1)) :
    (∑ j, if t ≤ j then P.rawLength i j else 0) = P.residual t.val i := by
  induction t using Fin.reverseInduction with
  | last => simp [rawLength]
  | cast t ih =>
    rw [fin_tail_step, ih]
    simp only [rawLength, Fin.castSucc_ne_last, ite_false, Fin.val_castSucc, Fin.val_succ, loss]
    ring

theorem triangularLength_designated (t : Fin (m + 1)) :
    (∑ j, if t ≤ j then P.triangularLength t j else 0) = P.residual t.val t := by
  calc
    _ = ∑ j, if t ≤ j then P.rawLength t j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : t ≤ j <;> simp [triangularLength, hj]
    _ = _ := P.rawLength_tail t t

theorem triangularLength_tail_le (i t : Fin (m + 1)) :
    (∑ j, if t ≤ j then P.triangularLength i j else 0) ≤ P.residual t.val i := by
  rw [← P.rawLength_tail i t]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact P.triangularLength_le_raw i j
  · rfl

/-- Labels remain their prescribed stage labels, even when physical cores
coincide. Only already-buffered coverage is removed from each label. -/
def toTriangularArray (hinit : P.residual 0 0 = 1)
    (hopt : ∀ t : Fin (m + 1), ∀ i, P.residual t.val i ≤ P.residual t.val t) :
    TriangularArray m where
  length := P.triangularLength
  nonnegative := P.triangularLength_nonnegative
  triangular i j hij := by simp [triangularLength, not_le.mpr hij]
  initial := by
    have h := P.triangularLength_designated 0
    simpa [hinit] using h
  dominated i t := by
    rw [P.triangularLength_designated]
    exact (P.triangularLength_tail_le i t).trans (hopt t i)

end CompatibleProfile

end ConsistentSubmodular

end


