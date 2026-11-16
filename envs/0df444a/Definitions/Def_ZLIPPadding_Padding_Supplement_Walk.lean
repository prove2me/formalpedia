-- Prove2me | Definitions.Def_ZLIPPadding_Padding_Supplement_Walk
-- name    : ZLIPPadding_Padding_Supplement_Walk
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:17:23.266114+00:00
-- url     : https://prove2.me/theorems/48023774-0f9c-41bd-9f69-b85bc266313a
-- title:
--   Common-shell walk laws and deterministic bucket selection
-- statement:
--   For a common increment law $\pi$, define its $K$-step endpoint as the sum of $K$ independent increments. Define shell weights $w_m$, the heavy set $H_K=\{1\le m\le M:w_m\ge1/(8M)\}$, and the explicit finite relative local estimate. The number of independent endpoints is
--
--   $$T=\left\lceil\max\{128M^2\log(2M/\beta),8MN\}\right\rceil.$$
--
--   The bucket function groups actual coordinate endpoints by exact quadratic norm, selects the largest bucket with smallest-label ties, and returns its first $N$ vectors or failure. Conditional shell laws are constructed by restriction and normalization on positive-probability shells; their unused zero-probability branch is the point mass at zero. The program input contains $K,M,N,T$ and the rational basis, never the heavy labels, shell weights, local amplitudes, or hidden factor. The theorem must establish its output law and resources.
-- source:
--   Shengmao Jiang, STOC 2027 submission #496 (October 2026), printed pp. 22–23 (PDF pp. 23–24), Theorem 5.1 and equations (5.1)–(5.6)

import Definitions.Def_ZLIPPadding_Padding_Supplement_Programs

namespace ZLIPPadding.Padding.Supplement
open scoped BigOperators ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

def endpoint {n : ℕ} (ν : PMF (ZVec n)) (K : ℕ) : PMF (ZVec n) :=
  (iid ν K).map List.sum
def shellWeight {n : ℕ} (π : PMF (ZVec n)) (K m : ℕ) : ℝ :=
  prob (endpoint π K) {z | iznorm z = m}
def heavy {n : ℕ} (π : PMF (ZVec n)) (K M : ℕ) : Finset ℕ :=
  (Finset.Icc 1 M).filter (fun m => shellWeight π K m ≥ 1/(8*M))
def LocalEstimate {n : ℕ} (π : PMF (ZVec n)) (K M : ℕ) (delta : ℝ) : Prop :=
  0 ≤ delta ∧ delta ≤ 1/32 ∧ ∀ m ∈ heavy π K M,
    ∃ a : ℝ, 0 < a ∧ ∀ z ∈ shell n m, ∃ e : ℝ,
      |e| ≤ delta ∧ ((endpoint π K) z).toReal = a*Real.exp e
def walkTrials (M N : ℕ) (beta : ℝ) : ℕ :=
  ⌈max (128*(M : ℝ)^2*Real.log (2*M/beta)) (8*(M : ℝ)*(N : ℝ))⌉₊
def bucket {n : ℕ} (G : ZMat n) (xs : List (ZVec n)) (m : ℕ) : List (ZVec n) :=
  xs.filter (fun z => qnorm G z = m)
/-- Strict replacement preserves the first (smallest) label on ties. -/
def bucketOutput {n : ℕ} (G : ZMat n) (M N : ℕ) (xs : List (ZVec n)) :
    Option (ℕ × List (ZVec n)) :=
  let best := (List.range M).foldl (fun best j =>
    if (bucket G xs (j+1)).length > (bucket G xs best).length then j+1 else best) 1
  let ys := bucket G xs best
  if N ≤ ys.length then some (best, ys.take N) else none
def bucketLaw {n : ℕ} (G : ZMat n) (ν : PMF (ZVec n)) (K M N T : ℕ) :
    PMF (Option (ℕ × List (ZVec n))) :=
  (iid (endpoint ν K) T).map (bucketOutput G M N)
def conditionalShell {n : ℕ} (ν : PMF (ZVec n)) (G : ZMat n) (K m : ℕ) : PMF (ZVec n) :=
  if h : ∃ z ∈ {z | qnorm G z = m}, z ∈ (endpoint ν K).support then
    (endpoint ν K).filter {z | qnorm G z = m} h else PMF.pure 0
def encWalkInput {n : ℕ} (B : QMat n) (K M N T : ℕ) : Bits :=
  encBasis B ++ encNat K ++ encNat M ++ encNat N ++ encNat T
def readBlocksAux : ℕ → Bits → Option (List Bits × Bits)
  | 0, w => some ([], w)
  | j+1, w => do
    let (k, r) ← readNat w
    if r.length < k then none else do
      let (bs, tail) ← readBlocksAux j (r.drop k)
      pure (r.take k :: bs, tail)
def decodeWalk (n : ℕ) (w : Bits) : Option (ℕ × List (ZVec n)) := do
  let (m, r) ← readNat w
  let (k, r) ← readNat r
  let (bs, tail) ← readBlocksAux k r
  if tail ≠ [] then none else do
    let zs ← bs.mapM (decVec n)
    pure (m, zs)
def incrementKernel {n : ℕ} (B : QMat n) (ν : PMF (ZVec n)) : Kernel :=
  fun w => if w = encBasis B then ν.map encVec else PMF.pure []
def walkRun {n : ℕ} (P : Program) (c d : ℕ) (B : QMat n) (ν : PMF (ZVec n))
    (K M N T k R : ℕ) : PMF RunState :=
  run P (incrementKernel B ν) (powerBound c d (K+M+N+k+(encBasis B).length+R))
    (encWalkInput B K M N T)

end
end ZLIPPadding.Padding.Supplement


