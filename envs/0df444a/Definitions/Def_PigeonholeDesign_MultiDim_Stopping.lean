-- Prove2me | Definitions.Def_PigeonholeDesign_MultiDim_Stopping
-- name    : PigeonholeDesign_MultiDim_Stopping
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:36:21.565407+00:00
-- url     : https://prove2.me/theorems/61026a13-570d-4e00-8dd1-9f3ca5d2b63b
-- title:
--   pp. ec21–ec22 — the stopping time τ, matched subjects 𝒯_M, unmatched subjects 𝒯_U, and H⁰_τ, H¹_τ
-- statement:
--   These are the objects of the proof of Theorem 9, defined for one run of a design: the pigeonhole of each subject and the realised assignment.
--
--   **Counts.** $n^0_n$ and $n^1_n$ are the numbers of control and treated subjects among the first $n$ subjects.
--
--   **Stopping time.**
--   $$\tau=\min\Big\{n\in[T] : n^0_n=\tfrac T2\ \text{or}\ n^1_n=\tfrac T2\Big\},$$
--   the number of subjects assigned when one group first reaches $T/2$.
--
--   **Matched and unmatched subjects.** Within each pigeonhole, the subjects among the first $\tau$ are paired in arrival order: the first with the second, the third with the fourth, and so on. The paired subjects form $\mathcal T_M$. A subject among the first $\tau$ is unmatched (in $\mathcal T_U$) iff its pigeonhole contains an odd number of the first $\tau$ subjects and it is the last of them; so each pigeonhole has at most one unmatched subject.
--
--   **$H^0_\tau$, $H^1_\tau$.** The numbers of unmatched subjects in control and in treatment, i.e. the numbers of pigeonholes whose single unmatched subject is in control, respectively in treatment.
--
--   Component 1 of the proof bounds the discrepancy of $\mathcal T_M$; Component 2 bounds that of the remaining subjects, $\mathcal T_U$ together with the last $T-\tau$.
--
--   **Formalization Note** Subjects are indexed from $0$, so "the first $n$ subjects" are those with index $<n$. If no $n\in[1,T]$ has a full group, $\tau$ is set to $T$; for even $T\ge2$ the pigeonhole design is balanced, so $n^0_T=n^1_T=T/2$ and this default is never used. The paper's pairing "inside a pigeonhole" is made explicit as pairing in arrival order, which is how the design's Step 2 alternates within a pigeonhole before $\tau$.
-- source:
--   Zhao and Zhou, Pigeonhole Design: Balancing Sequential Experiments from an Online Matching Perspective, arXiv:2201.12936v6, pp. ec21–ec22, proof of Theorem 9 (τ, 𝒯_M, 𝒯_U, H⁰_τ, H¹_τ)

import Mathlib
import Definitions.Def_PigeonholeDesign_MultiDim_Setting

namespace PigeonholeDesign.MultiDim

/-!
Zhao and Zhou, arXiv:2201.12936v6, proof of Theorem 9 (pp. ec21–ec22): the stopping time `τ`, the
matched subjects `𝒯_M`, the unmatched subjects `𝒯_U`, and `H⁰_τ`, `H¹_τ`. Every object is a
function of a run: the pigeonhole `cell t` of each subject and the realised assignment `w`
(`false` = control, `true` = treated). Subjects are indexed from 0.
-/

/-- `n⁰_n`: the number of control subjects among the first `n` subjects. -/
def nCtrl {T : ℕ} (w : Fin T → Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ w t = false)).card

/-- `n¹_n`: the number of treated subjects among the first `n` subjects. -/
def nTrt {T : ℕ} (w : Fin T → Bool) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun t : Fin T => (t : ℕ) < n ∧ w t = true)).card

/-- `τ = min {n ∈ [T] | n⁰_n = T/2 or n¹_n = T/2}` (p. ec21), the number of subjects assigned when
one group first reaches `T/2`. If no such `n` exists the value is `T`; for even `T ≥ 2` and a
balanced run (`n⁰_T = n¹_T = T/2`) the set is nonempty and this default is never used. -/
def tau {T : ℕ} (w : Fin T → Bool) : ℕ :=
  (((List.range T).map (· + 1)).find? (fun n => nCtrl w n = T / 2 ∨ nTrt w n = T / 2)).getD T

/-- `𝒯_M`: the matched subjects among the first `τ`. Within each pigeonhole the subjects among the
first `τ` are paired in arrival order (1st with 2nd, 3rd with 4th, …); a subject is unmatched iff
its pigeonhole holds an odd number of the first `τ` subjects and it is the last of them. -/
def matched {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (w : Fin T → Bool) :
    Finset (Fin T) :=
  Finset.univ.filter (fun s => (s : ℕ) < tau w ∧
    (Even (Finset.univ.filter (fun s' : Fin T => (s' : ℕ) < tau w ∧ cell s' = cell s)).card ∨
      ∃ s' : Fin T, s < s' ∧ (s' : ℕ) < tau w ∧ cell s' = cell s))

/-- `𝒯_U`: the unmatched subjects among the first `τ`. -/
def unmatched {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (w : Fin T → Bool) :
    Finset (Fin T) :=
  Finset.univ.filter (fun s : Fin T => (s : ℕ) < tau w) \ matched cell w

/-- `H⁰_τ`: the number of unmatched control subjects among the first `τ` (equivalently, of
pigeonholes whose single unmatched subject is in control). -/
def H0 {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (w : Fin T → Bool) : ℕ :=
  ((unmatched cell w).filter (fun s => w s = false)).card

/-- `H¹_τ`: the number of unmatched treated subjects among the first `τ`. -/
def H1 {ι : Type*} [DecidableEq ι] {T : ℕ} (cell : Fin T → ι) (w : Fin T → Bool) : ℕ :=
  ((unmatched cell w).filter (fun s => w s = true)).card

end PigeonholeDesign.MultiDim


