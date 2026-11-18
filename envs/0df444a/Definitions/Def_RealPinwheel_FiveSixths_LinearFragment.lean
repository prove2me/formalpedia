-- Prove2me | Definitions.Def_RealPinwheel_FiveSixths_LinearFragment
-- name    : RealPinwheel_FiveSixths_LinearFragment
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T04:44:54.442009+00:00
-- url     : https://prove2.me/theorems/5a77fb84-7e7e-45b8-98c4-115dfc1adf21
-- title:
--   Linear-real coverage proof fragments
-- statement:
--   A coverage proof fragment consists of exact linear-combination leaves and complementary coordinate cuts. A hole carries the obligation that its current real domain is covered by the annotated word boxes.
--
--   $$\forall d\in R_\Gamma,\quad\exists j<N:\ d\in B_j.$$
--
--   Independent coverage lemmas discharge these holes. Finite arithmetic checks validate the other leaves, keeping proof fragments separate without weakening the real-domain inclusion. In particular, a hole is an explicit proof obligation, never a certificate-success assumption on a scheduling instance.
-- source:
--   Fujiwara, Gutowski, Ouchi and Wolff, STOC 2027 submission #885, Section 3 equation (2) and its proof, printed p. 8 (PDF p. 9), Section 4 Table 1 and verification, printed pp. 9–11 (PDF pp. 10–12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/885.pdf. Exact linear-real verification of queries (4) and (5).

import Definitions.Def_RealPinwheel_FiveSixths_LinearCertificate
namespace RealPinwheel.FiveSixths
/-- Coverage proof fragments have holes discharged by independent real-domain lemmas. -/
inductive LinearFragment (n : ℕ) where
  | empty (c : LinearCombination)
  | word (j : ℕ) (cs : Fin n → LinearCombination)
  | split (i : Fin n) (p q : ℕ) (strict : Bool) (left right : LinearFragment n)
  | hole

def fragmentObligations {n : ℕ} (N : ℕ) (codes : ℕ → CycleCode)
    (Γ : List (LinearAtom n)) : LinearFragment n → Prop
  | .empty c => combinationCheck Γ c (falseAtom n) = true
  | .word j cs => linearCoverCheck N codes Γ (.word j cs) = true
  | .split i p q strict l r => 0 < q ∧
      fragmentObligations N codes (upperAtom i p q strict :: Γ) l ∧
      fragmentObligations N codes (complementAtom (upperAtom i p q strict) :: Γ) r
  | .hole => ∀ d : Fin n → ℝ, (∀ a ∈ Γ, a.Holds d) → ∃ j : Fin N, codeBox (codes j.val) d
end RealPinwheel.FiveSixths


