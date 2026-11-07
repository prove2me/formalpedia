-- Prove2me | Definitions.Def_CFLOutliers_assignChange
-- name    : CFLOutliers_assignChange
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:38:08.246796+00:00
-- url     : https://prove2.me/theorems/b6fa5839-6a8e-44f0-b06e-737b8fd38eb6
-- title:
--   Assignment improvements $A_t(b)$ and the certificates (9), (10)
-- statement:
--   Let $S$ be the current solution, $w_i$ its load at $i$ ($0$ if $i$ is closed), $v_i=u_i-w_i$ the unused capacity, $f'_i=0$ for $i\in F_S$ and $f'_i=f_i$ otherwise, and $f(K)=\sum_{i\in K}f_i$.
--
--   1. For a recipient $t$ and an integer $0\le b\le v_t$, $A_t(b)$ is the **minimum change** in $c_s+\lambda r$ when the facilities of $F_S\cup\{t\}$ are available, the load at $t$ is at most $w_t+b$ and every other facility $i$ has load at most $w_i$; opening costs are excluded.
--   2. An **open operation** $\mathrm{open}(t,K)$ has $K\subseteq F_S\setminus\{t\}$ with $W_K=\sum_{s\in K}w_s\le v_t$; its certificate is
--   $$\widehat\Delta_{\mathrm{open}}(t,K)=f'_t-f(K)+\sum_{s\in K}w_sc_{st}+A_t(v_t-W_K).\tag{9}$$
--   3. A **close operation** $\mathrm{close}(s,T)$ has $s\in F_S$, recipients $T\subseteq F\setminus\{s\}$, integers $0\le a_i\le v_i$ ($i\in T$) with $\sum_{i\in T}a_i\le w_s$, and $h=w_s-\sum_{i\in T}a_i$; its certificate is
--   $$\widehat\Delta_{\mathrm{close}}(s,T,a)=-f_s+\sum_{i\in T}f'_i+\sum_{i\in T}a_ic_{si}+\lambda h+\min\bigl(\{0\}\cup\{A_t(v_t-a_t):t\in T\}\bigr),\tag{10}$$
--   the minimum being $0$ when $T=\emptyset$.
--
--   Recipients may be closed or already open. These values are what the local search evaluates in place of exact potential changes.
--
--   **Formalization Note** $A_t(b)$ is a change relative to the current assignment; the properties (8) ($A_t(0)=0$, monotone, $\le 0$) hold when the current assignment is optimal and are not built in.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §3.1, p.8, displays (8)–(10)

import Mathlib
import Definitions.Def_CFLOutliers_Phi

namespace CFLOutliers

open Finset

/-- Unused capacity `v_i = u_i − w_i` of the current solution (§3.1, p.8). -/
def vfree {I : Inst} (S : Sol I) (i : Fin I.m) : ℕ := I.u i - load S i

/-- Additional opening cost `f'_i` (§3.1, p.8): `0` if `i ∈ F_S`, `f_i` otherwise. -/
def fprime {I : Inst} (S : Sol I) (i : Fin I.m) : ℝ := if i ∈ S.openSet then 0 else I.f i

open Classical in
/-- The assignments admitted by `A_t(b)`: they use only facilities of `F_S ∪ {t}`, put at most
`w_t + b` clients at `t` and at most `w_i` clients at every other facility `i`. -/
noncomputable def assignChangeSet {I : Inst} (S : Sol I) (t : Fin I.m) (b : ℕ) :
    Finset (Fin I.n → Option (Fin I.m)) :=
  univ.filter (fun σ' => AssignInto (insert t S.openSet) σ' ∧
    aload σ' t ≤ load S t + b ∧ ∀ i, i ≠ t → aload σ' i ≤ load S i)

theorem reject_all_mem_assignChangeSet {I : Inst} (S : Sol I) (t : Fin I.m) (b : ℕ) :
    (fun _ => none) ∈ assignChangeSet S t b := by
  classical
  unfold assignChangeSet
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j i h => ?_, ?_, fun i _ => ?_⟩
  · simp at h
  · simp [aload]
  · simp [aload]

/-- **Assignment-improvement value** `A_t(b)` (§3.1, p.8): "the minimum change in c_s + λr when
facilities in F_S ∪ {t} are available, the load at t is at most w_t + b, and every other current
facility i has load at most w_i. Opening costs are excluded."

**Formalization Note.** It is a *change*: the minimum of `c_s + λ r` over `assignChangeSet S t b`
minus the value `(c_s + λ r)(S)` of the current assignment. It is used with `0 ≤ b ≤ v_t`; the
properties (8) (`A_t(0) = 0`, monotone, `≤ 0`) hold at an optimal penalty assignment and are not
built in. -/
noncomputable def assignChange {I : Inst} (lam : ℝ) (S : Sol I) (t : Fin I.m) (b : ℕ) : ℝ :=
  (assignChangeSet S t b).inf' ⟨_, reject_all_mem_assignChangeSet S t b⟩ (penCost I lam) -
    penCost I lam S.σ

/-- Admissible open operation `open(t, K)` (§3.1, p.8): `K ⊆ F_S \ {t}` and
`W_K = Σ_{s ∈ K} w_s ≤ v_t`. The recipient `t` may be closed or already open. -/
def OpenAdm {I : Inst} (S : Sol I) (t : Fin I.m) (K : Finset (Fin I.m)) : Prop :=
  K ⊆ S.openSet.erase t ∧ ∑ s ∈ K, load S s ≤ vfree S t

/-- **Open certificate** (9), p.8:
`Δ̂_open(t, K) = f'_t − f(K) + Σ_{s ∈ K} w_s c_{st} + A_t(v_t − W_K)`. -/
noncomputable def DeltaOpen {I : Inst} (lam : ℝ) (S : Sol I) (t : Fin I.m)
    (K : Finset (Fin I.m)) : ℝ :=
  fprime S t - ∑ s ∈ K, I.f s + ∑ s ∈ K, (load S s : ℝ) * I.cFF s t +
    assignChange lam S t (vfree S t - ∑ s ∈ K, load S s)

/-- Admissible close operation `close(s, T)` with transfer amounts `a` (§3.1, p.8): `s ∈ F_S`,
the recipients `T ⊆ F \ {s}` (closed or already open), integers `0 ≤ a_i ≤ v_i` for `i ∈ T` and
`Σ_{i ∈ T} a_i ≤ w_s`. -/
def CloseAdm {I : Inst} (S : Sol I) (s : Fin I.m) (T : Finset (Fin I.m)) (a : Fin I.m → ℕ) :
    Prop :=
  s ∈ S.openSet ∧ s ∉ T ∧ (∀ i ∈ T, a i ≤ vfree S i) ∧ ∑ i ∈ T, a i ≤ load S s

/-- **Close certificate** (10), p.8: with `h = w_s − Σ_{i ∈ T} a_i`,
`Δ̂_close(s, T, a) = −f_s + Σ_{i ∈ T} f'_i + Σ_{i ∈ T} a_i c_{si} + λ h
  + min({0} ∪ {A_t(v_t − a_t) : t ∈ T})`; the minimum is `0` when `T = ∅`. -/
noncomputable def DeltaClose {I : Inst} (lam : ℝ) (S : Sol I) (s : Fin I.m)
    (T : Finset (Fin I.m)) (a : Fin I.m → ℕ) : ℝ :=
  -I.f s + ∑ i ∈ T, fprime S i + ∑ i ∈ T, (a i : ℝ) * I.cFF s i +
    lam * ((load S s - ∑ i ∈ T, a i : ℕ) : ℝ) +
    (insert (0 : ℝ) (T.image (fun t => assignChange lam S t (vfree S t - a t)))).min'
      (insert_nonempty _ _)

end CFLOutliers


