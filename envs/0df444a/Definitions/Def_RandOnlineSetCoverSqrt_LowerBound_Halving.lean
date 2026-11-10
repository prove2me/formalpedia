-- Prove2me | Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Halving
-- name    : RandOnlineSetCoverSqrt_LowerBound_Halving
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T19:34:33.996069+00:00
-- url     : https://prove2.me/theorems/f271b154-280d-4d05-b4d8-c9f62481609a
-- title:
--   Joint-history uniform halving and terminal expectation
-- statement:
--   Fix nonnegative integers $m,T$. A trajectory records candidate families $C^{(t)}$ and purchased label sets $X_t$ for all $0\le t\le T$. A probability mass function $p$ on the finite trajectory space is their joint law, with arbitrary real probabilities and arbitrary correlations. For an event $E$, its mass is the sum of $p(z)$ over trajectories $z\in E$.
--
--   A halving process with initial family $C_0$ has $C^{(0)}=C_0$ and nested purchases on every positive-probability trajectory. Given any joint-history atom $h$ through time $t<T$, including every earlier candidate family and purchase and also $X_t$, the next family is uniform over all halves of the current family. Explicitly, for any family $D$,
--
--   $$\Pr[h,\ C^{(t+1)}=D]=\begin{cases}\Pr[h]/\binom{|C^{(t)}|}{\lfloor|C^{(t)}|/2\rfloor},&D\subseteq C^{(t)},\ |D|=\lfloor|C^{(t)}|/2\rfloor,\\0,&\text{otherwise}.\end{cases}$$
--
--   This multiplication form includes zero-probability histories without dividing by their probability. The binomial denominator is positive for every family size. On the power-of-two initial families used in Lemma 4.1, every preterminal size is even, so these are exact halves. No independence of discard indicators, deterministic purchase rule, or cost bound is part of the definition.
--
--   The terminal expectation is the finite real sum
--
--   $$\mathbb E_p|X_T|=\sum_z p(z)|X_T(z)|.$$
--
--   Finite pushforward laws capture the source's arbitrary measurable finite-valued random trajectories; no restriction on the underlying randomness or memory is introduced.
-- source:
--   Ilan Doron-Arad, Joseph (Seffi) Naor, STOC 2027 submission #1160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1160.pdf, §4 standing setup and Lemma 4.1, printed p. 10 / PDF p. 11

import Definitions.Def_RandOnlineSetCoverSqrt_LowerBound_Candidates

open scoped ENNReal

namespace RandOnlineSetCoverSqrt.LowerBound

/-- Complete finite-valued joint trajectories (C^t, X_t), t = 0,...,T. -/
abbrev Trajectory (m T : ℕ) :=
  (Fin (T + 1) → Family m) × (Fin (T + 1) → Candidate m)

/-- Mass of an event under the joint law, without conditional-probability division. -/
noncomputable def eventMass {m T : ℕ} (p : PMF (Trajectory m T))
    (E : Trajectory m T → Prop) : ℝ≥0∞ := by
  classical
  exact ∑ z, if E z then p z else 0

/-- Agreement on the entire observed joint history through t, including X_t. -/
def sameHistory {m T : ℕ} (t : Fin T) (z h : Trajectory m T) : Prop :=
  ∀ s : Fin (T + 1), s.val ≤ t.val → z.1 s = h.1 s ∧ z.2 s = h.2 s

/-- §4 standing setup, printed p. 10 / PDF p. 11.
On each joint-history atom the next family has uniform mass among all halves.
The equation also holds on zero-mass histories; choose(n,n/2) is always positive.
No independence of derived discard indicators is assumed. -/
def HalvingProcess {m T : ℕ} (p : PMF (Trajectory m T)) (C₀ : Family m) : Prop :=
  (∀ z, p z ≠ 0 → z.1 0 = C₀) ∧
  (∀ z, p z ≠ 0 → ∀ t : Fin T, z.2 t.castSucc ⊆ z.2 t.succ) ∧
  ∀ (t : Fin T) (h : Trajectory m T) (D : Family m),
    eventMass p (fun z => sameHistory t z h ∧ z.1 t.succ = D) =
      if D ⊆ h.1 t.castSucc ∧ D.card = (h.1 t.castSucc).card / 2 then
        eventMass p (fun z => sameHistory t z h) /
          (Nat.choose (h.1 t.castSucc).card ((h.1 t.castSucc).card / 2) : ℝ≥0∞)
      else 0

/-- Real expectation of the bounded terminal purchase count. -/
noncomputable def terminalExpectation {m T : ℕ} (p : PMF (Trajectory m T)) : ℝ :=
  ∑ z, (p z).toReal * ((z.2 (Fin.last T)).card : ℝ)

end RandOnlineSetCoverSqrt.LowerBound


