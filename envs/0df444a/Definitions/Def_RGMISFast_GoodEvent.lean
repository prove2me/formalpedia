-- Prove2me | Definitions.Def_RGMISFast_GoodEvent
-- name    : RGMISFast_GoodEvent
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:29:47.227216+00:00
-- url     : https://prove2.me/theorems/bfe037da-343f-4a0f-85ee-5597e24bd8f8
-- title:
--   The good event $E_h$: conclusions of Lemmas 3.1, 3.2 and A.1
-- statement:
--   Fix a degree bound $\Delta$, a root $u^*$ and a deviation parameter $L$. The good event is the conjunction of
--
--   1. (9): for every $0\le i<m\le M$ and every root-connected $B$ active at $a_m$, $K_{m,i}(B)\le 32c^{1+m-i}(2S_m(B)+L)$;
--   2. (10): for every $1\le m\le M$ and every root-connected $A$ active at $a_m$, $|\Gamma_m(A)|\le 2S_m(A)+L$;
--   3. (11): $|C_0|\le 1+L$;
--   4. (32): every root-connected $A$ satisfies $|\Gamma_{<a_M}(A)|\le 2(|A|\log(8e\Delta)+L+2)$.
--
--   With $h=L-8$, $E_h$ is this event at $L=h+8$.
--
--   On $E_h$ every admissible tree is small (Propositions 4.1 and 4.2), and $E_h$ fails with probability less than $e^{-h}$ (eq. (12)).
--
--   **Formalization Note** Each of the four conditions is its own predicate (`EntryEvent`, `GrowthEvent`, `TopEvent`, `LowRankEvent`), so Lemmas 3.1, 3.2 and A.1 bound exactly the conditions that enter $E_h$. $\log$ is the natural logarithm.
-- source:
--   Dalirrooyfard, Makarychev, Mitrović, Ramachandran, Randomized Greedy MIS Is Fast at Every Node, STOC 2027 submission (manuscript sha256 e93cdfecc03618969d5f2ecf8171c6f84c528edcc473b2f864299e555f823664), §3, p.14 (PDF p.16) (Lemmas 3.1, 3.2, E_h); App. A, p.29 (PDF p.31) (32)

import Mathlib
import Definitions.Def_RGMISFast_Gamma

set_option autoImplicit false

namespace RGMISFast

/-- The event of Lemma 3.1(a) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), eq. (9),
p.14): "For every 0 ≤ i < m ≤ M and every root-connected set B active at am,
Km,i(B) ≤ 32c^{1+m−i}(2Sm(B) + L)", with `M = Mof Δ`. -/
def EntryEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (u : V) (L : ℝ) (r : V → ℝ) : Prop :=
  ∀ m i : ℕ, i < m → m ≤ Mof Δ → ∀ B : Finset V, IsRootConnected G u B →
    ActiveAt G r (am m) B → (Kmi G r m i B : ℝ) ≤ 32 * c ^ (1 + m - i) * (2 * Sm r B m + L)

/-- The event of Lemma 3.1(b) (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), eq. (10),
p.14): "For every 1 ≤ m ≤ M and every root-connected set A active at am,
|Γm(A)| ≤ 2Sm(A) + L", with `M = Mof Δ`. -/
def GrowthEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (u : V) (L : ℝ) (r : V → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m → m ≤ Mof Δ → ∀ A : Finset V, IsRootConnected G u A →
    ActiveAt G r (am m) A → ((Gammam G r m A).card : ℝ) ≤ 2 * Sm r A m + L

/-- The event (11) of Lemma 3.2 (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), p.14):
`|C₀| ≤ 1 + L`. -/
def TopEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (L : ℝ) (r : V → ℝ) : Prop :=
  ((C0 G r u).card : ℝ) ≤ 1 + L

/-- The event (32) of Lemma A.1 (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized
Greedy MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), p.29):
"every root-connected set A satisfies |Γ<aM(A)| ≤ 2(|A| log(8e∆) + L + 2)" (natural logarithm). -/
def LowRankEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (Δ : ℕ) (u : V)
    (L : ℝ) (r : V → ℝ) : Prop :=
  ∀ A : Finset V, IsRootConnected G u A →
    ((GammaLow G r Δ A).card : ℝ) ≤
      2 * ((A.card : ℝ) * Real.log (8 * Real.exp 1 * Δ) + L + 2)

/-- The good event `E_h` (Dalirrooyfard, Makarychev, Mitrović, Ramachandran, *Randomized Greedy
MIS Is Fast at Every Node*, STOC 2027 submission (manuscript sha256 e93cdfec…), §3, p.14):
"Define h = L − 8, and let Eh be the event that the conclusions of Lemmas 3.1, 3.2, and A.1 all
hold." `GoodEvent G Δ u L r` is the conjunction of (9), (10), (11) and (32) at deviation
parameter `L`; `E_h` is `GoodEvent G Δ u (h + 8)`. -/
def GoodEvent {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ : ℕ) (u : V) (L : ℝ) (r : V → ℝ) : Prop :=
  EntryEvent G Δ u L r ∧ GrowthEvent G Δ u L r ∧ TopEvent G u L r ∧ LowRankEvent G Δ u L r

end RGMISFast


