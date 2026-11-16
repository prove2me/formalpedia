-- Prove2me | Definitions.Def_MeanCertificates1424_Hardness_Supplement_Detection
-- name    : MeanCertificates1424_Hardness_Supplement_Detection
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T08:55:02.931986+00:00
-- url     : https://prove2.me/theorems/63705efd-b155-4174-a4bf-aa5898b55be4
-- title:
--   Adaptive randomized detectors, hitting games and impact capacity
-- statement:
--   In Appendix B the actual field $x$ and the report $y$ are fixed before the detector's private randomness. A **deterministic adaptive detector** chooses, from the history of audited vertices and their exact values, the next vertex to audit or stops, and finally decides whether to alarm; it performs at most $q$ audits. A **randomized detector** is a probability distribution over deterministic ones. It has **no false alarm** if it alarms with probability $0$ when $x=y$. For a set of alternatives $\mathcal A$, the optimal worst-case miss probability is
--
--   $$
--   \beta_q=\inf_{\pi\ \text{no false alarm}}\ \sup_{x\in\mathcal A}\ \Pr_{\sigma\sim\pi}(\sigma\ \text{does not alarm on}\ x),
--   $$
--
--   which is $0$ when $\mathcal A=\emptyset$. For a known class $\mathcal H$ of fields, $S_b(y)=\{\operatorname{supp}(x-y):x\in\mathcal H,\ 0<\|x-y\|_0\le b\}$. Distributions $\pi$ over audit sets of size at most $q$ give avoidance probabilities $\Pr_{Q\sim\pi}(Q\cap S=\emptyset)$. The file defines the least number of audits of a deterministic detector with zero miss probability and the minimum hitting-set size of a family of sets.
--
--   For impact-sensitive detection with uniform mean $\mu$, the alternatives are the $L$-Lipschitz $x$ with $|\operatorname{supp}(x-y)|\le b$ and $|\mu(x)-\mu(y)|\ge\tau$. For a proper $S\subsetneq V$, $U^S_v=\min_{u\notin S}(y_u+Ld_G(u,v))$, $\Lambda^S_v=\max_{u\notin S}(y_u-Ld_G(u,v))$, the **impact capacity** is
--
--   $$
--   a_y(S)=\frac1n\max\Big\{\sum_v(U^S_v-y_v),\ \sum_v(y_v-\Lambda^S_v)\Big\},
--   $$
--
--   $A_{b,\tau}(y)=\{S:1\le|S|\le b,\ a_y(S)\ge\tau\}$ and $D_G(S)=\sum_{v\in S}d_G(v,V\setminus S)$. The nonadaptive detector of an audit set audits it and alarms at the first mismatch; sampling a uniformly random $q$-set gives the uniform detector.
--
--   These objects state Proposition B.1 and Theorems B.2 and B.4.
--
--   **Formalization Note** Randomized detectors are probability mass functions over deterministic adaptive strategies; probabilities are outer measures in $[0,\infty]$.
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Appendix B (printed pp.24–26, PDF pp.26–28)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_General

set_option autoImplicit false

namespace MeanCertificates1424.Hardness.Supplement

/-! # Detection at a prescribed scale (Appendix B, printed pp.24–26, PDF pp.26–28)

The adversary fixes the actual field `x` and the report `y` before the detector's private
randomness. A detector audits coordinates exactly, possibly adaptively, at most `q` of them,
and must never raise an alarm when `x = y`. -/

/-- A deterministic adaptive detector: from the history of (audited vertex, exact value)
pairs it chooses the next vertex to audit (`none` = stop) and finally decides to alarm. -/
structure Strategy (n : ℕ) where
  next : List (Fin n × ℝ) → Option (Fin n)
  alarm : List (Fin n × ℝ) → Bool

/-- The history after at most `q` audits on the true field `x`. -/
def Strategy.history {n : ℕ} (σ : Strategy n) (x : Fin n → ℝ) :
    ℕ → List (Fin n × ℝ) → List (Fin n × ℝ)
  | 0, h => h
  | q + 1, h =>
    match σ.next h with
    | none => h
    | some v => σ.history x q (h ++ [(v, x v)])

/-- Whether `σ`, with at most `q` audits, raises an alarm when the true field is `x`. -/
def Strategy.alarms {n : ℕ} (σ : Strategy n) (q : ℕ) (x : Fin n → ℝ) : Bool :=
  σ.alarm (σ.history x q [])

/-- A randomized detector: a probability distribution over deterministic adaptive
detectors (the private randomness). -/
abbrev Policy (n : ℕ) := PMF (Strategy n)

/-- No false alarm: under `x = y` the alarm probability is zero. -/
def NoFalseAlarm {n : ℕ} (π : Policy n) (q : ℕ) (y : Fin n → ℝ) : Prop :=
  π.toOuterMeasure {σ | σ.alarms q y = true} = 0

/-- Miss probability against the alternative `x`. -/
noncomputable def missProb {n : ℕ} (π : Policy n) (q : ℕ) (x : Fin n → ℝ) : ENNReal :=
  π.toOuterMeasure {σ | σ.alarms q x = false}

/-- Optimal worst-case miss probability over a set `Alt` of alternatives, allowing
randomization and adaptivity, with no false positives at `y`. It is `0` if `Alt = ∅`. -/
noncomputable def optMiss {n : ℕ} (q : ℕ) (y : Fin n → ℝ) (Alt : Set (Fin n → ℝ)) : ENNReal :=
  ⨅ (π : Policy n) (_ : NoFalseAlarm π q y), ⨆ x ∈ Alt, missProb π q x

/-- Distributions over audit sets of size at most `q`. -/
def AuditDist {n : ℕ} (q : ℕ) (π : PMF (Finset (Fin n))) : Prop :=
  ∀ Q ∈ π.support, Q.card ≤ q

/-- `Pr_{Q∼π}(Q ∩ S = ∅)`. -/
noncomputable def avoidProb {n : ℕ} (π : PMF (Finset (Fin n))) (S : Finset (Fin n)) : ENNReal :=
  π.toOuterMeasure {Q | Disjoint Q S}

/-- Support of a deviation. -/
noncomputable def supp {n : ℕ} (x y : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun v => x v ≠ y v

/-- `S_b(y) = {supp(x − y) : x ∈ H, 0 < ‖x − y‖₀ ≤ b}` for a known class `H`. -/
noncomputable def supportFamily {n : ℕ} (H : Set (Fin n → ℝ)) (b : ℕ) (y : Fin n → ℝ) :
    Set (Finset (Fin n)) :=
  {S | ∃ x ∈ H, S = supp x y ∧ 0 < (supp x y).card ∧ (supp x y).card ≤ b}

/-- Alternatives of `H`: `x ∈ H` with `0 < ‖x − y‖₀ ≤ b`. -/
def altOf {n : ℕ} (H : Set (Fin n → ℝ)) (b : ℕ) (y : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ H ∧ 0 < (supp x y).card ∧ (supp x y).card ≤ b}

/-- Smallest number of audits of a deterministic adaptive detector with no false alarm and
zero miss probability on every alternative. -/
noncomputable def detAudits {n : ℕ} (y : Fin n → ℝ) (Alt : Set (Fin n → ℝ)) : ℕ :=
  sInf {q | ∃ σ : Strategy n, σ.alarms q y = false ∧ ∀ x ∈ Alt, σ.alarms q x = true}

/-- Minimum hitting-set size of a family of vertex sets. -/
noncomputable def minHitting {n : ℕ} (F : Set (Finset (Fin n))) : ℕ :=
  sInf {k | ∃ Q : Finset (Fin n), Q.card = k ∧ ∀ S ∈ F, ¬ Disjoint Q S}

/-! ## Impact capacity (B.1) -/

/-- Uniform mean `µ(x) = n⁻¹ ∑ x_v`. -/
noncomputable def umean {n : ℕ} (x : Fin n → ℝ) : ℝ := (∑ v, x v) / n

def LipOn {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ u v, G.Adj u v → |x u - x v| ≤ L

/-- Impact alternatives: `L`-Lipschitz `x` with `|supp(x − y)| ≤ b` and `|µ(x) − µ(y)| ≥ τ`. -/
def impactAlt {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (b : ℕ) (τ : ℝ) (y : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  {x | LipOn G L x ∧ (supp x y).card ≤ b ∧ τ ≤ |umean x - umean y|}

/-- `U^S_v = min_{u ∉ S} (y_u + L d_G(u, v))` (proper `S`). -/
noncomputable def capUp {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (y : Fin n → ℝ)
    (S : Finset (Fin n)) (v : Fin n) : ℝ :=
  sInf ((Sᶜ.image fun u => y u + L * (G.dist u v : ℝ) : Finset ℝ) : Set ℝ)

/-- `Λ^S_v = max_{u ∉ S} (y_u − L d_G(u, v))` (proper `S`). -/
noncomputable def capLow {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (y : Fin n → ℝ)
    (S : Finset (Fin n)) (v : Fin n) : ℝ :=
  sSup ((Sᶜ.image fun u => y u - L * (G.dist u v : ℝ) : Finset ℝ) : Set ℝ)

/-- Impact capacity `a_y(S) = n⁻¹ max{∑_v (U^S_v − y_v), ∑_v (y_v − Λ^S_v)}`. -/
noncomputable def impactCap {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (y : Fin n → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  max (∑ v, (capUp G L y S v - y v)) (∑ v, (y v - capLow G L y S v)) / n

/-- `A_{b,τ}(y) = {S : 1 ≤ |S| ≤ b, a_y(S) ≥ τ}`. -/
noncomputable def capFamily {n : ℕ} (G : SimpleGraph (Fin n)) (L : ℝ) (b : ℕ) (τ : ℝ)
    (y : Fin n → ℝ) : Set (Finset (Fin n)) :=
  {S | 1 ≤ S.card ∧ S.card ≤ b ∧ τ ≤ impactCap G L y S}

/-- `D_G(S) = ∑_{v∈S} d_G(v, V ∖ S)` for proper `S` (real valued). -/
noncomputable def depthReal {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : ℝ :=
  ((depthSum G S).toNat : ℝ)

/-- The uniformly random `q`-subset of `Fin n`. -/
noncomputable def uniformQSet (n q : ℕ) (h : q ≤ n) : PMF (Finset (Fin n)) :=
  haveI : Nonempty {Q : Finset (Fin n) // Q.card = q} := by
    obtain ⟨Q, -, hQ⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset (Fin n)))
      (by simpa using h)
    exact ⟨⟨Q, hQ⟩⟩
  (PMF.uniformOfFintype {Q : Finset (Fin n) // Q.card = q}).map Subtype.val

/-- The nonadaptive detector of a fixed audit set `Q`: audit the vertices of `Q` in increasing
order and alarm iff some audited value differs from the report. -/
noncomputable def setStrategy {n : ℕ} (Q : Finset (Fin n)) (y : Fin n → ℝ) : Strategy n where
  next h := (Q.sort (· ≤ ·))[h.length]?
  alarm h := decide (∃ p ∈ h, p.2 ≠ y p.1)

/-- Sample `Q ∼ π`, then run `setStrategy Q y`. -/
noncomputable def setPolicy {n : ℕ} (π : PMF (Finset (Fin n))) (y : Fin n → ℝ) : Policy n :=
  π.map fun Q => setStrategy Q y

end MeanCertificates1424.Hardness.Supplement


