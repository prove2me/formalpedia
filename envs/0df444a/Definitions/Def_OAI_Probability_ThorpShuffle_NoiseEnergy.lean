-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
-- name    : OAI_Probability_ThorpShuffle_NoiseEnergy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:31:38.427648+00:00
-- url     : https://prove2.me/theorems/59ad30c5-1f23-4ff7-8c7e-94d630339d2a
-- title:
--   Bit insertion, half markers and half histories of the Thorp shuffle
-- statement:
--   Let $Q_n=\{0,1\}^n$ with coordinates indexed from $0$, and identify Booleans with bits. A coin vector for a deck of $2^{n+1}$ cards is a function $Q_n\to\{0,1\}$, and a history of length $t$ is a sequence $(\omega_0,\dots,\omega_{t-1})$ of coin vectors.
--
--   1. *Bit insertion.* For $i\in\{0,\dots,d\}$, $b\in\{0,1\}$ and $x\in Q_d$,
--   $$
--   \iota_{i,b}(x)=(x_0,\dots,x_{i-1},\,b,\,x_i,\dots,x_{d-1})\in Q_{d+1}.
--   $$
--   The map $(b,x)\mapsto\iota_{i,b}(x)$ is a bijection $\{0,1\}\times Q_d\to Q_{d+1}$. Inserting at $i=0$ prepends $b$, and inserting at $i=d$ appends $b$.
--   2. *Half markers.* For $t\in\mathbb{N}$, $m_d(t)=d+1-t\in\{0,\dots,d+1\}$ and $m'_d(t)=d-t\in\{0,\dots,d\}$, both with truncated subtraction (the value is $0$ once $t$ exceeds $d+1$, respectively $d$). In particular $m_d(0)=d+1$ and $m_d(d+1)=0$.
--   3. *Half histories.* Let $\omega=(\omega_0,\dots,\omega_{t-1})$ be a history for a deck of $2^{d+2}$ cards, so $\omega_k:Q_{d+1}\to\{0,1\}$, and let $h\in\{0,1\}$. The $h$-half history is the history for $2^{d+1}$ cards given by
--   $$
--   \omega^{(h)}_k(x)=\omega_k\bigl(\iota_{m'_d(k),h}(x)\bigr),\qquad x\in Q_d,\ 0\le k<t .
--   $$
--   It is compatible with appending a coin vector $c$: the half history of $(\omega_0,\dots,\omega_{t-1},c)$ is $(\omega^{(h)}_0,\dots,\omega^{(h)}_{t-1},\,c\circ\iota_{m'_d(t),h})$.
--
--   These objects support a halving argument for the deck of $2^{d+2}$ cards. Each Thorp step moves every coordinate except the leading one place towards the front, and sends the leading bit, modified by a coin, to the back. Hence the bit that starts in the last coordinate $d+1$ sits in coordinate $m_d(k)$ after $k\le d+1$ steps. For $k\le d$ that coordinate belongs to the coin label, at index $m'_d(k)$. The positions on which this bit equals $h$ form a half of the deck. The step driven by $\omega_k$ only pairs positions within the same half, using the coins whose label has bit $h$ at index $m'_d(k)$, and $\omega^{(h)}$ collects exactly these coins.
--
--   **Formalization Note** The definitions are `insertBit` (via `Fin.insertNth`), `halfPositionEquiv` (via `Fin.insertNthEquiv`), `halfMarker`, `coinHalfMarker` and `halfHistory`. The lemmas `insertBit_zero`, `insertBit_last`, `halfMarker_zero`, `halfMarker_end` and `halfHistory_snoc` record the special cases and the compatibility above, and `RawState.ext` is an extensionality lemma for raw states.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/NoiseEnergy.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/NoiseEnergy.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories

namespace OAI

noncomputable section

open scoped BigOperators
open Filter

namespace Thorp

namespace Conditional

def insertBit (d : ℕ) (i : Fin (d + 1)) (b : Bool) (x : Position d) : Position (d + 1) :=
  Fin.insertNth i b x

def halfPositionEquiv (d : ℕ) (i : Fin (d + 1)) : Bool × Position d ≃ Position (d + 1) :=
  Fin.insertNthEquiv (fun _ => Bool) i

@[simp] theorem halfPositionEquiv_apply (d : ℕ) (i : Fin (d + 1)) (p : Bool × Position d) :
    halfPositionEquiv d i p = insertBit d i p.1 p.2 := rfl

@[simp] theorem insertBit_zero (d : ℕ) (b : Bool) (x : Position d) :
    insertBit d 0 b x = Fin.cons b x := Fin.insertNth_zero' _ _

@[simp] theorem insertBit_last (d : ℕ) (b : Bool) (x : Position d) :
    insertBit d (Fin.last d) b x = Fin.snoc x b := Fin.insertNth_last' _ _

@[ext] theorem RawState.ext {d : ℕ} {v u : RawState d}
    (hf : v.free = u.free) (hw : v.weight = u.weight) : v = u := by
  cases v; cases u; simp_all

end Conditional

namespace Conditional

def halfMarker (d t : ℕ) : Fin (d + 2) := ⟨d + 1 - t, by omega⟩
def coinHalfMarker (d t : ℕ) : Fin (d + 1) := ⟨d - t, by omega⟩

@[simp] theorem halfMarker_zero (d : ℕ) : halfMarker d 0 = Fin.last (d + 1) := rfl
@[simp] theorem halfMarker_end (d : ℕ) : halfMarker d (d + 1) = 0 := by
  apply Fin.ext; simp [halfMarker]

def halfHistory (d t : ℕ) (h : Bool) (ω : History (d + 2) t) : History (d + 1) t :=
  fun i x => ω i (insertBit d (coinHalfMarker d i.val) h x)

@[simp] theorem halfHistory_snoc (d t : ℕ) (h : Bool)
    (ω : History (d + 2) t) (c : Coins (d + 2)) :
    halfHistory d (t + 1) h (Fin.snoc ω c) =
      Fin.snoc (halfHistory d t h ω) (fun x => c (insertBit d (coinHalfMarker d t) h x)) := by
  funext i x
  refine Fin.lastCases ?_ (fun j => ?_) i
  · change (Fin.snoc (α := fun _ => Coins (d + 2)) ω c (Fin.last t)) (insertBit d (coinHalfMarker d t) h x) =
      (Fin.snoc (α := fun _ => Coins (d + 1)) (halfHistory d t h ω)
        (fun z => c (insertBit d (coinHalfMarker d t) h z)) (Fin.last t)) x
    erw [Fin.snoc_last, Fin.snoc_last]
  · change (Fin.snoc (α := fun _ => Coins (d + 2)) ω c j.castSucc) (insertBit d (coinHalfMarker d j.val) h x) =
      (Fin.snoc (α := fun _ => Coins (d + 1)) (halfHistory d t h ω)
        (fun z => c (insertBit d (coinHalfMarker d t) h z)) j.castSucc) x
    erw [Fin.snoc_castSucc, Fin.snoc_castSucc]
    rfl

end Conditional

end Thorp

end

end OAI


