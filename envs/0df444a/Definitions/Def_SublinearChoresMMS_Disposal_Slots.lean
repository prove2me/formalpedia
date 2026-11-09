-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Slots
-- name    : SublinearChoresMMS_Disposal_Slots
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:33:25.579765+00:00
-- url     : https://prove2.me/theorems/fc6f3337-824e-44aa-a8ae-0e58952d9504
-- title:
--   General and custom slots for the actual completed fractional allocation
-- statement:
--   For a fractional bundle $z$ in decreasing cost order, let $W_e$ be the total fraction before chore $e$. Its share in general slot $s$ is the published interval-intersection formula
--
--   $$\max\{0,\min(W_e+z(e),s+1)-\max(W_e,s)\}.$$
--
--   Reserved and mixed agents use these slots. A pure ordinary agent uses the actual selected prepared bundle. If $K\tau_{i,t}\le1$, the fractions in $H$ occupy one extra slot. Her other slots are the original one-per-block slots when $t<L$, or the consecutive $q+h$-chore slots of $G_{i,L}$ after deleting the first slot when $t=L$. They undergo precisely the same order-preserving shift and truncation as the base bundles. If $K\tau_{i,t}>1$, the whole bundle uses general slots instead. Equality belongs to the custom branch.
--
--   Slot fractions, ownership, loads, the bundle arising from an integral assignment, and that bundle with the first general slot omitted are computed from these definitions. A slot assignment maps each real chore to an owned slot. Injectivity means at most one chore per slot.
--
--   **Formalization Note** Each agent has a common type of $m+1$ slot labels, including unused zero-load slots. Slot zero is the first general slot; slot $m$ is the extra $H$ slot in the custom branch. Empty labels carry no real chore in a supported rounding outcome. No load-maxima bounds or rounding certificates are input fields.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), §3.3, equation (1), Lemma 3.3, printed pp. 10–12 / PDF pp. 11–13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Prepared
import Definitions.Def_ChoresEFX_IsAdmissibleMatching

noncomputable section

namespace SublinearChoresMMS.Disposal

attribute [local instance] Classical.propDecidable

/-- Extra empty slots allow one fixed finite slot type for all constructions.
Index m is the extra H slot in the custom case; index zero is the first general slot. -/
abbrev Slots (n m : ℕ) := Fin n × Fin (m + 1)
abbrev SlotAssignment (n m : ℕ) := Fin m → Slots n m

/-- Reuse the published interval-intersection slot fraction with the common IDO order.
No capped-price sorting predicate is used. -/
def generalSlot {m : ℕ} (z : Fin m → ℝ) (e : Fin m) (s : ℕ) : ℝ :=
  ChoresEFX.slotMass (fun _ : Unit => z) (fun _ e => e.val) () e s

/-- The original block-slots (t<L), or the consecutive (q+h)-chore slots (t=L).
The first last-bin slot is absent because rawBase has already deleted it. -/
def rawSlot {n m q : ℕ} (p : Labels n m q) (t : Fin (n / q))
    (g : Fin m) (s : ℕ) : ℝ :=
  if s = (if t.val + 1 = n / q then position (G p t) g / denominator n q t
          else g.val / q) then rawBase p t g else 0

def shiftedSlot {n m q : ℕ} {R : Finset (Fin n)} (p : Packings n m q R)
    (i : Ordinary R) (t : Fin (n / q)) (e : Fin m) (s : ℕ) : ℝ :=
  if e.val < K p then 0 else
    ∑ g : Fin m, if g ∉ Z (p i) ∧
      position (Finset.univ \ Z (p i)) g = e.val - K p then rawSlot (p i) t g s else 0

/-- The selected pure index, encoded as a Nat so the total definition also covers L=0.
Every statement uses it only when Pure supplies an index. -/
def selected {n q : ℕ} {R : Finset (Fin n)} (v : Coefficients n q R) (i : Ordinary R) : ℕ :=
  if h : Pure v i then (Classical.choose h).val else 0

/-- Both pure-agent cases are determined by the actual K*tau comparison. -/
def usesCustom {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (v : Coefficients n q R) (i : Ordinary R) : Prop :=
  ∃ t : Fin (n / q), selected v i = t.val ∧ Pure v i ∧ (K p : ℝ) * tau c p i t ≤ 1

/-- Slot fractions for the actual realized allocation: all general agents use consecutive
unit slots; pure ordinary agents use the shifted block/last-bin slots plus H iff K*tau≤1. -/
def slotFraction {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (v : Coefficients n q R) (s : Slots n m) (e : Fin m) : ℝ :=
  if hi : s.1 ∉ R then
    if hc : usesCustom c p v ⟨s.1, hi⟩ then
      let t := Classical.choose hc
      if e ∈ H p then (if s.2.val = m then tau c p ⟨s.1, hi⟩ t else 0)
      else shiftedSlot p ⟨s.1, hi⟩ t e s.2.val
    else generalSlot (realized c p v s.1) e s.2.val
  else generalSlot (realized c p v s.1) e s.2.val

/-- Predicate identifying the general-slot branch, including pure agents with K*tau>1. -/
def GeneralAgent {n m q : ℕ} (c : Cost n m) {R : Finset (Fin n)}
    (p : Packings n m q R) (v : Coefficients n q R) (i : Fin n) : Prop :=
  ∀ hi : i ∉ R, ¬usesCustom c p v ⟨i, hi⟩

def slotLoad {n m : ℕ} (f : Slots n m → Fin m → ℝ) (s : Slots n m) : ℝ := ∑ e, f s e

def slotBundle {n m : ℕ} (A : SlotAssignment n m) (i : Fin n) : Finset (Fin m) :=
  bundle (fun e => (A e).1) i

/-- Exact removal of the chore occupying the first general slot, if there is one. -/
def withoutFirst {n m : ℕ} (A : SlotAssignment n m) (i : Fin n) : Finset (Fin m) :=
  Finset.univ.filter (fun e => (A e).1 = i ∧ (A e).2.val ≠ 0)

end SublinearChoresMMS.Disposal


