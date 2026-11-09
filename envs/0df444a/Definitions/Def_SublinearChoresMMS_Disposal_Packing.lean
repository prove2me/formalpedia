-- Prove2me | Definitions.Def_SublinearChoresMMS_Disposal_Packing
-- name    : SublinearChoresMMS_Disposal_Packing
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:30:36.331666+00:00
-- url     : https://prove2.me/theorems/b8c7d7fe-0b47-4b0b-b04b-417a434b47bb
-- title:
--   Representative labels, copy packings, and retained-copy halving
-- statement:
--   With block size $q>0$ dividing $m$, block $r$ has representative $e_{rq+1}$ for zero-based $r$. The first representative is excluded; each remaining representative has either a bin label or an exclusion label. A valid packing has total representative cost at most the capacity of each bin. The exclusion count omits the first representative. The segment count is the number of maximal consecutive runs of constant bin or exclusion labels along representatives $2,\ldots,m/q$.
--
--   At stage $j$ with $q=2^\ell$, there are $q/2^j$ distinguished copies of every representative except the first. Their locations and a finite set of old marked copies are explicit data. Marked copies contribute zero load. The bins comprise $\lfloor n/2^j\rfloor$ unit bins, a fractional bin if needed, and an empty zero-capacity padding bin if needed to make the number even. The exceptional pair follows all four parity/fractional cases in Appendix A.1.2; the chosen unit bin is labelled zero when the unit count is odd.
--
--   A halving output consists of a retained set, a marked retained set, and a fixed-point-free involution pairing bins. It keeps exactly half the copies of each representative, retains every old mark on a retained copy, keeps the exceptional pair together, and requires
--
--   $$\text{retained unmarked load of }(u,v)\le\frac{T_u+T_v}{2},\qquad M_{j+1}\le\frac{M_j}{2}+C_3\sqrt b.$$
--
--   The output predicate describes the promised witnesses. No field of an input packing assumes their existence. Empty padding bins contain no copies.
-- source:
--   Zehan Lin, Xiaowei Wu, Shengwei Zhou, STOC 2027 submission #845 (October 2026), Lemma 3.1 and Appendix A.1.1–A.1.3, printed pp. 6, 20–26 / PDF pp. 7, 21–27; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/845.pdf

import Mathlib
import Definitions.Def_SublinearChoresMMS_Disposal_Setting

noncomputable section

namespace SublinearChoresMMS.Disposal

/-- Block index zero is the first, always excluded, representative. -/
abbrev Labels (n m q : ℕ) := Fin (m / q) → Option (Fin (binCount n q))

def representativeCost {n m : ℕ} (c : Cost n m) (i : Fin n) (q : ℕ)
    (r : Fin (m / q)) : ℝ :=
  if h : r.val * q < m then c i ⟨r.val * q, h⟩ else 0

def excludedCount {n m q : ℕ} (p : Labels n m q) : ℕ :=
  (Finset.univ.filter (fun r => 0 < r.val ∧ p r = none)).card

/-- Consecutive constant segments on representatives 2,...,m/q, including exclusion labels. -/
def segments {n m q : ℕ} (p : Labels n m q) : ℕ :=
  if m / q ≤ 1 then 0 else 1 +
    (Finset.univ.filter (fun r : Fin (m / q) =>
      ∃ h : 0 < r.val, 1 < r.val ∧ p r ≠ p ⟨r.val - 1, by omega⟩)).card

def ValidPacking {n m q : ℕ} (c : Cost n m) (i : Fin n) (p : Labels n m q) : Prop :=
  (∀ r, r.val = 0 → p r = none) ∧
  ∀ v, (∑ r, if p r = some v then representativeCost c i q r else 0) ≤ binCapacity n q v

/-- The padded bin list in A.1.2: unit bins, optional fraction, optional zero padding. -/
def stageBins (n j : ℕ) : ℕ :=
  let a := binCount n (2 ^ j)
  a + a % 2

def stageCapacity (n j : ℕ) (v : Fin (stageBins n j)) : ℝ :=
  if v.val < n / 2 ^ j then 1
  else if v.val = n / 2 ^ j then (n % 2 ^ j : ℕ) / ((2 ^ j : ℕ) : ℝ) else 0

/-- Distinguished exceptional pair, for every bin parity. The odd case chooses the first
unit bin; relabelling unit bins covers the arbitrary choice in A.1.2. -/
def ExceptionalPair (n j : ℕ) (u v : Fin (stageBins n j)) : Prop :=
  let a := n / 2 ^ j
  let r := n % 2 ^ j
  if a % 2 = 0 then r ≠ 0 ∧ u.val = a ∧ v.val = a + 1
  else u.val = 0 ∧ v.val = a

abbrev Copies (m q j : ℕ) := {r : Fin (m / q) // 0 < r.val} × Fin (q / 2 ^ j)

/-- Packing data contain only positions and old marks. No halving conclusion is a field. -/
structure CopyPacking (n m q j : ℕ) where
  location : Copies m q j → Fin (stageBins n j)
  marked : Finset (Copies m q j)

def copyLoad {n m q j : ℕ} (c : Cost n m) (i : Fin n) (P : CopyPacking n m q j)
    (v : Fin (stageBins n j)) : ℝ :=
  ∑ s, if P.location s = v ∧ s ∉ P.marked then representativeCost c i q s.1.val else 0

def CopyFeasible {n m q j : ℕ} (c : Cost n m) (i : Fin n)
    (P : CopyPacking n m q j) : Prop :=
  (∀ v, copyLoad c i P v ≤ stageCapacity n j v) ∧
  (∀ s, stageCapacity n j (P.location s) = 0 → False)

/-- A pairing is a fixed-point-free involution. -/
def IsPairing {b : ℕ} (π : Fin b → Fin b) : Prop :=
  Function.Involutive π ∧ ∀ v, π v ≠ v

/-- Retained marks include all retained old marks; nonretained old marks do not count. -/
def HalvingOutput {n m q j : ℕ} (c : Cost n m) (i : Fin n)
    (P : CopyPacking n m q j) (C₃ : ℝ) : Prop :=
  ∃ (keep marks : Finset (Copies m q j)) (π : Fin (stageBins n j) → Fin (stageBins n j)),
    IsPairing π ∧
    (∀ u v, ExceptionalPair n j u v → π u = v) ∧
    (∀ r : {r : Fin (m / q) // 0 < r.val},
      (keep.filter (fun s => s.1 = r)).card = (q / 2 ^ j) / 2) ∧
    marks ⊆ keep ∧ P.marked ∩ keep ⊆ marks ∧
    (∀ v, (∑ s ∈ keep, if s ∉ marks ∧ (P.location s = v ∨ P.location s = π v)
        then representativeCost c i q s.1.val else 0) ≤
      (stageCapacity n j v + stageCapacity n j (π v)) / 2) ∧
    (marks.card : ℝ) ≤ (P.marked.card : ℝ) / 2 + C₃ * Real.sqrt (stageBins n j)

end SublinearChoresMMS.Disposal


