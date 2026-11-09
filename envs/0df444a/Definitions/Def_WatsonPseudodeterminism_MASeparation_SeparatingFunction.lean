-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_SeparatingFunction
-- name    : WatsonPseudodeterminism_MASeparation_SeparatingFunction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:36:46.415903+00:00
-- url     : https://prove2.me/theorems/8ddf4073-674d-4d82-abd5-7b9d5968cc79
-- title:
--   The separating promise problem and its bit-string family
-- statement:
--   Let $z$ have even positive length $n$, and let $L=|z_{\leftarrow}|$, $R=|z_{\rightarrow}|$ be the weights of its left and right halves. Define
--
--   $$f_n(z)=\begin{cases}1&L=n/2\text{ or }R>0,\\0&L\le n/6\text{ and }R=0,\\\bot&\text{otherwise},\end{cases}\qquad F_n(x,y)=f_n(g^n(x,y)).$$
--
--   The thresholds $n/2$ and $n/6$ are compared in the real numbers. Zero-based indices smaller than the natural number $n/2$ form the left half. The asymptotic sequence is $n_t=4(t+1)^2$, so these halves and $\sqrt{n_t}$ are integral. An explicit equivalence identifies the block input with an $N_t=n_th(n_t)$-bit string and defines the corresponding family. The auxiliary total definition at sizes outside the admissible sequence chooses the first displayed branch first; no theorem about the source's separating functions uses a zero or odd size. Growth of the explicit family is to be established as part of its class membership.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §4, p. 10 (f and F); §1.1, p. 3 (bit-string families); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Families
import Definitions.Def_WatsonPseudodeterminism_MASeparation_Gadget

namespace WatsonPseudodeterminism.MASeparation

/-- Zero-based left and right halves; the source uses even n. -/
def leftWeight {n : ℕ} (z : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => i.val < n / 2 ∧ z i = true)).card

def rightWeight {n : ℕ} (z : Fin n → Bool) : ℕ :=
  (Finset.univ.filter (fun i => n / 2 ≤ i.val ∧ z i = true)).card

/-- §4, p. 10: the promise problem, with the n/6 threshold compared in ℝ. -/
noncomputable def outerFn (n : ℕ) (z : Fin n → Bool) : Option Bool := by
  classical
  exact if (leftWeight z : ℝ) = (n : ℝ) / 2 ∨ 0 < rightWeight z then some true
    else if (leftWeight z : ℝ) ≤ (n : ℝ) / 6 ∧ rightWeight z = 0 then some false
    else none

/-- The communication problem F = f ∘ g^n. -/
noncomputable def liftedFn (n : ℕ) : PartialFn
    (BlockInput (gadgetLength n) n) (BlockInput (gadgetLength n) n) :=
  fun x y => outerFn n (gadgetPower x y)

/-- Explicit equivalence between n blocks of h bits and an n*h-bit string. -/
def blockEquiv (n h : ℕ) : Bits (n * h) ≃ BlockInput h n where
  toFun x i j := x (finProdFinEquiv (i, j))
  invFun x k := x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  left_inv x := by
    funext k
    exact congrArg x (finProdFinEquiv.apply_symm_apply k)
  right_inv x := by funext i j; simp

noncomputable def flatLiftedFn (n : ℕ) : PartialFn
    (Bits (n * gadgetLength n)) (Bits (n * gadgetLength n)) :=
  fun x y => liftedFn n (blockEquiv n (gadgetLength n) x) (blockEquiv n (gadgetLength n) y)

/-- An infinite set of positive even squares, as used for §4's asymptotic family. -/
def Admissible (n : ℕ) : Prop := ∃ s : ℕ, 1 ≤ s ∧ n = 4 * s ^ 2

def separationSize (t : ℕ) : ℕ := 4 * (t + 1) ^ 2

/-- The explicit family used by the source; growth is a class membership condition. -/
noncomputable def separationFamily : Family where
  length t := separationSize t * gadgetLength (separationSize t)
  fn t := flatLiftedFn (separationSize t)

end WatsonPseudodeterminism.MASeparation


