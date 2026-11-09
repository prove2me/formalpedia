-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Prepared
-- name    : SublinearChoresMMS_Disposal_Prepared
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:31:40.584907+00:00
-- url     : https://prove2.me/theorems/c17a773e-4bbc-4fbd-ae81-3779eb8faf74
-- title:
--   The prepared fractional bundles and coordinated coefficient constraints
-- statement:
--   Fix a reserved set $R$ and let $N_o=N\setminus R$. Starting from actual representative labels for each ordinary agent, merge the optional fractional bin into the last unit bin and expand representatives to their $q$-chore blocks $G_{i,t}$. Let $d_t=q$ except for the last bin, where $d_L=q+h$, and put $\eta_{i,t}=d_t/n$. Exclude the first block, all excluded blocks, and the first $\min(d_L,|G_{i,L}|)$ chores of the last bin. These operations compute $Z_i$.
--
--   Set $K=\max_{i\in N_o}|Z_i|$ and $H=\{e_1,\ldots,e_K\}$. Survivor $j$ in the ordered complement of $Z_i$ shifts to $e_{K+j}$, disappearing if that index exceeds $m$. The shifted base fraction is $1/d_t$ on surviving shifted members of $G_{i,t}$. Complete it by the actual restoration formula
--
--   $$\tau_{i,t}=\frac{1-c_i(y_{i,t})}{n(1-\mathrm{PROP}_i)+c_i(H)},\qquad x_{i,t}(e)=\begin{cases}\tau_{i,t}&e\in H,\\y_{i,t}(e)&e\notin H.\end{cases}$$
--
--   The normalized positive regime and the nonempty first block ensure a positive denominator in the statements using it. A coefficient vector is in the product simplex if its entries are nonnegative and each ordinary agent's entries sum to one. An ordinary agent is pure exactly when one coefficient is one and all others vanish; all other ordinary agents are mixed.
--
--   The coordination predicate consists only of the simplex, chore-capacity inequalities, and the $|R|$ reserved-agent cost equations. It contains no probability law. The realized fractional allocation gives an ordinary agent the indicated convex combination and each reserved agent $1/|R|$ of the residual of every chore. The number of distinct full chore profiles is computed from these completed bundles, rather than supplied as unrelated data.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), §§3.1–3.2 and Appendix A.2, printed pp. 7–10, 26–27 / PDF pp. 8–11, 27–28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Packing

noncomputable section

namespace SublinearChoresMMS.Disposal

abbrev Ordinary {n : ℕ} (R : Finset (Fin n)) := {i : Fin n // i ∉ R}
abbrev Packings (n m q : ℕ) (R : Finset (Fin n)) := Ordinary R → Labels n m q
abbrev Coefficients (n q : ℕ) (R : Finset (Fin n)) := Ordinary R → Fin (n / q) → ℝ

/-- The merged bin index for a block. The fractional bin is merged into the last unit bin. -/
def mergedLabel {n m q : ℕ} (p : Labels n m q) (e : Fin m) : Option ℕ :=
  if h : e.val / q < m / q then
    (p ⟨e.val / q, h⟩).map (fun v => min v.val (n / q - 1))
  else none

def G {n m q : ℕ} (p : Labels n m q) (t : Fin (n / q)) : Finset (Fin m) :=
  Finset.univ.filter (fun e => mergedLabel p e = some t.val)

def denominator (n q : ℕ) (t : Fin (n / q)) : ℕ :=
  q + if t.val + 1 = n / q then n % q else 0

def eta (n q : ℕ) (t : Fin (n / q)) : ℝ := (denominator n q t : ℝ) / n

/-- Zero-based rank within an ordered finite set. -/
def position {m : ℕ} (S : Finset (Fin m)) (e : Fin m) : ℕ :=
  (S.filter (fun g => g.val < e.val)).card

/-- Exclude B₁, excluded blocks, and the first q+h chores of the last merged bin. -/
def Z {n m q : ℕ} (p : Labels n m q) : Finset (Fin m) :=
  Finset.univ.filter (fun e =>
    ¬∃ t : Fin (n / q), e ∈ G p t ∧
      (t.val + 1 ≠ n / q ∨ denominator n q t ≤ position (G p t) e))

def K {n m q : ℕ} {R : Finset (Fin n)} (p : Packings n m q R) : ℕ :=
  Finset.univ.sup (fun i => (Z (p i)).card)

def H {n m q : ℕ} {R : Finset (Fin n)} (p : Packings n m q R) : Finset (Fin m) :=
  Finset.univ.filter (fun e => e.val < K p)

/-- Base fraction, after the last-bin exclusion and before shifting. -/
def rawBase {n m q : ℕ} (p : Labels n m q) (t : Fin (n / q)) (g : Fin m) : ℝ :=
  if g ∉ Z p ∧ g ∈ G p t then 1 / (denominator n q t : ℝ) else 0

/-- Actual order-preserving shift: survivor number j becomes chore K+j, with zero-based j.
The finite sum selects its unique preimage; surviving positions past m-K disappear. -/
def shiftedBase {n m q : ℕ} {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) : ℝ :=
  if e.val < K p then 0 else
    ∑ g : Fin m, if g ∉ Z (p i) ∧
      position (Finset.univ \ Z (p i)) g = e.val - K p then rawBase (p i) t g else 0

def tau {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Ordinary R) (t : Fin (n / q)) : ℝ :=
  (1 - fractionalCost c i.val (shiftedBase p i t)) /
    ((n : ℝ) * (1 - propShare c i.val) + cost c i.val (H p))

/-- Completed bundle from the displayed restoration formula in §3.1. -/
def completed {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) : ℝ :=
  if e ∈ H p then tau c p i t else shiftedBase p i t e

def Simplex {n q : ℕ} {R : Finset (Fin n)} (v : Coefficients n q R) : Prop :=
  (∀ i t, 0 ≤ v i t) ∧ ∀ i, ∑ t, v i t = 1

/-- On the coefficient simplex this is exactly one nonzero coefficient, necessarily one. -/
def Pure {n q : ℕ} {R : Finset (Fin n)} (v : Coefficients n q R) (i : Ordinary R) : Prop :=
  ∃ t, ∀ u, v i u = if u = t then 1 else 0

open Classical in
def mixedCount {n q : ℕ} {R : Finset (Fin n)} (v : Coefficients n q R) : ℕ :=
  (Finset.univ.filter (fun i => ¬Pure v i)).card

def ordinaryFraction {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (v : Coefficients n q R) (e : Fin m) : ℝ :=
  ∑ i, ∑ t, v i t * completed c p i t e

/-- Equal division of the actual residual, as in §3.2. -/
def realized {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (v : Coefficients n q R) (i : Fin n) (e : Fin m) : ℝ :=
  if hi : i ∈ R then (1 - ordinaryFraction c p v e) / (R.card : ℝ)
  else ∑ t, v ⟨i, hi⟩ t * completed c p ⟨i, hi⟩ t e

/-- These are the deterministic affine constraints, not an assumed rounding law. -/
def Coordinated {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (v : Coefficients n q R) : Prop :=
  Simplex v ∧ (∀ e, ordinaryFraction c p v e ≤ 1) ∧
    ∀ j ∈ R, (∑ i, ∑ t, v i t * fractionalCost c j (completed c p i t)) =
      ((n - R.card : ℕ) : ℝ) * propShare c j

/-- Distinct full chore profiles, a computed finite set, not a free parameter. -/
def profiles {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) : ℕ :=
  (Finset.univ.image (fun e : Fin m => fun (i : Ordinary R) (t : Fin (n / q)) =>
    completed c p i t e)).card

end SublinearChoresMMS.Disposal


