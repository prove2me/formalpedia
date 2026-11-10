-- Prove2me | Definitions.Def_EditGV897_Main_Patterns
-- name    : EditGV897_Main_Patterns
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T07:25:04.707923+00:00
-- url     : https://prove2.me/theorems/2489edec-261a-4bd3-b913-914a1ae92875
-- title:
--   Enumerable positioned edit patterns and explicit family bound
-- statement:
--   A positioned operation inserts a specified bit at a current position, deletes a current bit, or complements one current bit. Positions are enumerated at the current length; insertion includes both ends. Execute these operations symbolically on affine coordinate expressions, enumerate every path of length at most $2t$, retain outputs of length $n$, and extract their affine matrices and offsets. This defines the canonical family $F_{t,n}$ without deduplicating path occurrences.
--
--   An admissible family is nonempty, consists of maps induced by these legal scripts, and covers every distinct confusable pair. The coefficient and additive overhead used in the goal are
--
--   $$a_t=(2t+1)[8(t+1)]^{2t},\qquad C_t=\log_2 a_t+3.$$
--
--   The goal concludes admissibility and $|F_{t,n}|\le a_t n^{2t}$ for sufficiently large $n$. The numerical coefficient is a planning derivation from the source's script enumeration and its $M=O_t(n^{2t})$ estimate; it is not a printed constant.
--
--   **Formalization Note** Ordered list occurrences index scripts. Binary substitutions are complements, which are always proper. The logarithm is the real base-two logarithm; it is used only at positive arguments under theorem guarantees.
-- source:
--   Ryan Gabrys, Shubhransh Singhvi, Eitan Yaakobi, Making Every Edit Count: Efficient Binary Edit Correction at the Gilbert–Varshamov Bound, STOC 2027 submission #897 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §§2.1, 3.1 and proof of Theorem 1, printed pp. 3–4, 6–7, 13–14 / PDF pp. 4–5, 7–8, 14–15; planning-derived coefficient as explained

import Definitions.Def_EditGV897_Main_Affine

namespace EditGV897.Main

inductive PositionedOp where
  | insert (position : ℕ) (value : Bit)
  | delete (position : ℕ)
  | toggle (position : ℕ)

/-- Positions refer to the current word, with both boundary insertions included. -/
def legalOps (L : ℕ) : List PositionedOp :=
  (List.range (L + 1)).flatMap (fun k => [.insert k 0, .insert k 1]) ++
  (List.range L).map PositionedOp.delete ++ (List.range L).map PositionedOp.toggle

/-- Symbolic affine-coordinate execution, with complements implemented by adding 1. -/
def symbolicStep {n : ℕ} (s : List (Equation n)) : PositionedOp → List (Equation n)
  | .insert k a => s.take k ++ [(0, a)] ++ s.drop k
  | .delete k => s.take k ++ s.drop (k + 1)
  | .toggle k => s.take k ++
    ((s.drop k).take 1).map (fun e => (e.1, e.2 + 1)) ++ s.drop (k + 1)

/-- Every path of at most r operations, retaining different path occurrences. -/
def symbolicPaths {n : ℕ} : ℕ → List (Equation n) → List (List (Equation n))
  | 0, s => [s]
  | r + 1, s => s :: (legalOps s.length).flatMap (fun op => symbolicPaths r (symbolicStep s op))

def canonicalFamily (t n : ℕ) : Family n :=
  let start := List.ofFn (fun i : Fin n => (unitWord n i.val, (0 : Bit)))
  ((symbolicPaths (2 * t) start).filter (fun s => s.length == n)).map (fun s =>
    { matrix := fun i => (s[i.val]?.getD ((0, 0) : Equation n)).1
      offset := fun i => (s[i.val]?.getD ((0, 0) : Equation n)).2 })

/-- Every occurrence is a fixed legal positioned pattern, and all distinct
confusable pairs are covered. No correctness or runtime guarantee is assumed. -/
def EditFamily {n : ℕ} (t : ℕ) (F : Family n) : Prop :=
  1 ≤ F.length ∧
  (∀ x y : Word n, x ≠ y →
    DeletionHash.MixedEdit.Confusable 1 t (wordList x) (wordList y) →
      ∃ f ∈ F, f.apply x = y) ∧
  (∀ f ∈ F, ∃ g ∈ canonicalFamily t n,
    g.matrix = f.matrix ∧ g.offset = f.offset)

/-- Planning bound derived from script enumeration, not a printed numerical constant. -/
def familyCoefficient (t : ℕ) : ℕ := (2 * t + 1) * (8 * (t + 1)) ^ (2 * t)
noncomputable def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2
noncomputable def redundancyConstant (t : ℕ) : ℝ := logTwo (familyCoefficient t) + 3

end EditGV897.Main


