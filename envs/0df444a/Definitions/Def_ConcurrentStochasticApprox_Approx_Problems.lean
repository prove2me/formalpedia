-- Prove2me | Definitions.Def_ConcurrentStochasticApprox_Approx_Problems
-- name    : ConcurrentStochasticApprox_Approx_Problems
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:44:51.569931+00:00
-- url     : https://prove2.me/theorems/6e4c5de3-791a-4eb3-937f-8bced1fb4647
-- title:
--   §2, §5.2 — encoded instances, CsgApproxValue, CsgGapValue, witnesses and Algorithm 1
-- statement:
--   **Inputs.** An instance consists of a game with nonempty state and action sets and rational transition probabilities, an objective (a target set $T$ for reachability, or a rational reward function $r$ with values in $[0,1]$ for limit-average or discounted-sum objectives), and the additive error $\varepsilon=2^{-B_\varepsilon}\in(0,1)$ with $B_\varepsilon\ge1$, given in binary with $B_\varepsilon+1$ bits. A discounted-sum instance also carries a succinct discount factor $\lambda=1-2^{-2^{B_\lambda}}$, represented by the exponent $2^{B_\lambda}$ in binary (so its encoding has length linear in $B_\lambda$). A rational number is defined using at most $B_{\mathrm{inp}}$ bits if its numerator and denominator together have at most $B_{\mathrm{inp}}$ bits.
--
--   **CsgApproxValue** asks, given an instance, for a vector $\hat v:S\to\mathbb Q$ with
--   $$|\hat v(s)-\mathrm{val}_\varphi(s)|\le\varepsilon\quad\text{for all states }s.$$
--   It is a search problem over binary strings: valid inputs are encodings of well-formed instances, and the answers are encodings of such vectors.
--
--   **CsgGapValue** additionally takes a state $s$ and a rational threshold $\alpha$. It is the promise problem whose yes-instances satisfy $\mathrm{val}_\varphi(s)\ge\alpha+\varepsilon$ and whose no-instances satisfy $\mathrm{val}_\varphi(s)\le\alpha-\varepsilon$. A promise problem is in **promise-NP** if a polynomial-time checking relation gives every yes-instance a polynomial-size certificate and accepts no certificate of a no-instance; **promise-coNP** exchanges yes and no.
--
--   **Witnesses.** For a game with reward $r$, succinct $\lambda$ and $\varepsilon=2^{-B_\varepsilon}$, a tuple $(\sigma,\tau,I_\sigma,I_\tau)$ of power-series numbers is a **witness** if
--   1. $\sigma$ and $\tau$ are stationary strategies of Players 1 and 2;
--   2. $I_\sigma=(L_\sigma,U_\sigma)$ is an $\varepsilon/2$-close shrinking interval bound of $G_\sigma$, and $I_\tau=(L_\tau,U_\tau)$ one of $G_\tau$;
--   3. $[L_\sigma(s),U_\sigma(s)]\cap[L_\tau(s),U_\tau(s)]\neq\emptyset$ for every state $s$.
--
--   Its **size** is the length of its binary encoding.
--
--   **Algorithm 1** (the verifier) checks with exact rational arithmetic that the strategies have nonnegative entries summing to one, that $L_\sigma\preceq U_\sigma$ and $L_\tau\preceq U_\tau$, and the shrinking inequalities in the expanded form of Equation (1): for $G_\sigma$,
--   $$L_\sigma(s)\le\sum_{a}\sigma(s)(a)\Big((1-\lambda)r(s,a,b)+\lambda\sum_{s'}\delta(s,a,b)(s')L_\sigma(s')\Big)$$
--   for **every** action $b$, and the reverse inequality with $U_\sigma$ for **some** $b$; for $G_\tau$ the quantifiers are exchanged. It then checks the widths $U-L\le\varepsilon/2$ and the statewise intersections.
--
--   These are the computational problems of Theorem 3.1 and Theorem 3.2 and the certificate system behind them.
--
--   **Formalization Note** Encodings use the published self-delimiting codes `encNat`, `encRat`, `encList`, `encVector`, the published `SearchProblem`, and Cook's machines. The threshold $\alpha$ is an arbitrary rational. A state is encoded as a binary natural below $n$.
-- source:
--   Ali Asadi, Krishnendu Chatterjee, The Computational Complexity of Concurrent Stochastic Games: Exact Value and Approximation, STOC 2027 submission #285 (October 2026), SHA-256 5cff187cf6b230b3bdfe540f2832f824d1ddb6acb43239fbf469d37c43b0d461, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/285.pdf, §2 "Computational problems" (printed p. 5, PDF p. 7); §5.2 "Witness" (printed p. 15, PDF p. 17); Algorithm 1 and Equation (1) (printed pp. 16–17, PDF pp. 18–19); proof of Theorem 3.2 (printed p. 17, PDF p. 19)

import Mathlib
import Definitions.Def_ConcurrentStochasticApprox_Approx_Game
import Definitions.Def_ConcurrentStochasticApprox_Approx_PowerSeries
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Complexity

/-!
# Encoded instances, witnesses, Algorithm 1, and the problems CsgApproxValue / CsgGapValue

Asadi–Chatterjee, STOC 2027 submission #285, §2 "Computational problems" (printed p. 5),
§5.2 "Witness" and "Verifier" (printed pp. 15–17).

Conventions.
* Input games have rational transition probabilities and rewards (`RatGame`, `RatReward`).
* The additive error `ε = 2^{-Bε}` is given in binary, i.e. with `Bε + 1` bits: it is encoded as
  the binary natural `2^{Bε}` (`encNat (2 ^ Bε)`, length linear in `Bε`). A succinct discount
  factor `λ = 1 - 2^{-2^{Bλ}}` is encoded by its exponent `2^{Bλ}` in binary (`encNat (2 ^ Bλ)`,
  length linear in `Bλ`); its rational denominator is never expanded.
* Encodings use the published self-delimiting binary codes `encNat`, `encRat`, `encList`,
  `encVector` (`NetworkEquilibriumCLS.LinearNash`), the published search problems,
  `InTFNP` and search reductions, and Cook's `PolyTimeComputable` / `P`.
* `CsgGapValue` is a promise problem; promise-NP and promise-coNP are defined below.
-/

open Finset NetworkEquilibriumCLS.LinearNash

noncomputable section

namespace ConcurrentStochasticApprox.Approx

/-! ### Rational input games -/

/-- A game with rational transition probabilities, as given in the input. -/
structure RatGame where
  n : ℕ
  mA : ℕ
  mB : ℕ
  δ : Fin n → Fin mA → Fin mB → Fin n → ℚ

/-- A rational game is well formed: the state and action sets are nonempty and every
`δ(s,a,b)` is a probability distribution. -/
def RatGame.Valid (G : RatGame) : Prop :=
  0 < G.mA ∧ 0 < G.mB ∧
    (∀ s a b, (∀ s', 0 ≤ G.δ s a b s') ∧ ∑ s', G.δ s a b s' = 1) ∧ 0 < G.n

/-- The game `G` denoted by a well-formed rational game. -/
def RatGame.toCSG (G : RatGame) (h : G.Valid) : CSG G.n G.mA G.mB where
  δ s a b := ⟨fun s' => (G.δ s a b s' : ℝ),
    fun s' => by simp only; exact_mod_cast (h.2.2.1 s a b).1 s', by
      have := (h.2.2.1 s a b).2
      simp only
      exact_mod_cast this⟩
  hA := h.1
  hB := h.2.1
  hN := h.2.2.2

/-- The number of states `n` and the action bound `m = max(|A|, |B|)`. -/
def RatGame.m (G : RatGame) : ℕ := max G.mA G.mB

/-- Rational rewards `r : S × A × B → ℚ`. -/
abbrev RatReward (G : RatGame) := Fin G.n → Fin G.mA → Fin G.mB → ℚ

/-- Rational rewards take values in `[0, 1]`. -/
def RatReward.Valid {G : RatGame} (r : RatReward G) : Prop := ∀ s a b, 0 ≤ r s a b ∧ r s a b ≤ 1

/-- The rewards as real numbers. -/
def RatReward.toReal {G : RatGame} (r : RatReward G) : Reward G.n G.mA G.mB :=
  fun s a b => (r s a b : ℝ)

/-- Number of bits of a rational number: bits of its numerator plus bits of its denominator. -/
def ratBits (q : ℚ) : ℕ := Nat.size q.num.natAbs + Nat.size q.den

/-- The list of transition probabilities, in lexicographic order of `(s, a, b, s')`. -/
def RatGame.entries (G : RatGame) : List ℚ :=
  (List.finRange G.n).flatMap fun s => (List.finRange G.mA).flatMap fun a =>
    (List.finRange G.mB).flatMap fun b => (List.finRange G.n).map fun s' => G.δ s a b s'

/-- The list of rewards, in lexicographic order of `(s, a, b)`. -/
def RatReward.entries {G : RatGame} (r : RatReward G) : List ℚ :=
  (List.finRange G.n).flatMap fun s => (List.finRange G.mA).flatMap fun a =>
    (List.finRange G.mB).map fun b => r s a b

/-- Binary encoding of a rational game: `n`, `|A|`, `|B|`, then all transition probabilities. -/
def RatGame.enc (G : RatGame) : List Bool :=
  encNat G.n ++ encNat G.mA ++ encNat G.mB ++ encList encRat G.entries

/-- Binary encoding of a target set, as its characteristic vector. -/
def encTarget {n : ℕ} (T : Fin n → Bool) : List Bool := encList (fun b => [b]) (List.ofFn T)

/-- The target set denoted by a characteristic vector. -/
def targetSet {n : ℕ} (T : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter fun s => T s = true

/-! ### Instances of the three objectives -/

/-- An instance with a reachability objective and additive error `ε = 2^{-Bε}`. -/
structure ReachInst where
  G : RatGame
  T : Fin G.n → Bool
  Bε : ℕ

/-- Well formed: valid game and `Bε ≥ 1`. -/
def ReachInst.Valid (I : ReachInst) : Prop := I.G.Valid ∧ 1 ≤ I.Bε

def ReachInst.enc (I : ReachInst) : List Bool := I.G.enc ++ encTarget I.T ++ encNat (2 ^ I.Bε)

/-- An instance with a limit-average objective `LimAvg(r)` and additive error `ε = 2^{-Bε}`. -/
structure LimAvgInst where
  G : RatGame
  r : RatReward G
  Bε : ℕ

def LimAvgInst.Valid (I : LimAvgInst) : Prop := I.G.Valid ∧ I.r.Valid ∧ 1 ≤ I.Bε

def LimAvgInst.enc (I : LimAvgInst) : List Bool :=
  I.G.enc ++ encList encRat I.r.entries ++ encNat (2 ^ I.Bε)

/-- An instance with a discounted-sum objective `Disc(r, λ)` for the succinct discount factor
`λ = 1 - 2^{-2^{Bλ}}`, and additive error `ε = 2^{-Bε}`. -/
structure DiscInst where
  G : RatGame
  r : RatReward G
  Blam : ℕ
  Bε : ℕ

def DiscInst.Valid (I : DiscInst) : Prop := I.G.Valid ∧ I.r.Valid ∧ 1 ≤ I.Bε

def DiscInst.enc (I : DiscInst) : List Bool :=
  I.G.enc ++ encList encRat I.r.entries ++ encNat (2 ^ I.Blam) ++ encNat (2 ^ I.Bε)

/-- All transition probabilities and rewards are rationals defined using at most `Binp` bits. -/
def DiscInst.BitsLE (I : DiscInst) (Binp : ℕ) : Prop :=
  (∀ q ∈ I.G.entries, ratBits q ≤ Binp) ∧ ∀ q ∈ I.r.entries, ratBits q ≤ Binp

/-! ### CsgApproxValue (search problems) -/

/-- **CsgApproxValue** for reachability: given `(G, T)` and `ε = 2^{-Bε}`, output `v̂ : S → ℚ`
with `|v̂(s) - val_T(s)| ≤ ε` for all states `s`. -/
def reachApproxSearch : SearchProblem where
  valid x := ∃ I : ReachInst, I.Valid ∧ I.enc = x
  answer x y := ∃ (I : ReachInst) (h : I.Valid), I.enc = x ∧
    ∃ v : Fin I.G.n → ℚ, encVector v = y ∧
      ∀ s, |(v s : ℝ) - reachValue (I.G.toCSG h.1) (targetSet I.T) s| ≤ (1 / 2 : ℝ) ^ I.Bε

/-- **CsgApproxValue** for limit-average objectives. -/
def limAvgApproxSearch : SearchProblem where
  valid x := ∃ I : LimAvgInst, I.Valid ∧ I.enc = x
  answer x y := ∃ (I : LimAvgInst) (h : I.Valid), I.enc = x ∧
    ∃ v : Fin I.G.n → ℚ, encVector v = y ∧
      ∀ s, |(v s : ℝ) - limAvgValue (I.G.toCSG h.1) I.r.toReal s| ≤ (1 / 2 : ℝ) ^ I.Bε

/-- **CsgApproxValue** for discounted-sum objectives with a succinct discount factor. -/
def discApproxSearch : SearchProblem where
  valid x := ∃ I : DiscInst, I.Valid ∧ I.enc = x
  answer x y := ∃ (I : DiscInst) (h : I.Valid), I.enc = x ∧
    ∃ v : Fin I.G.n → ℚ, encVector v = y ∧
      ∀ s, |(v s : ℝ) - discValue (I.G.toCSG h.1) I.r.toReal (succinct I.Blam) s| ≤
        (1 / 2 : ℝ) ^ I.Bε

/-! ### Promise problems, promise-NP and promise-coNP -/

/-- A promise problem over binary strings: disjoint-by-promise sets of yes- and no-instances;
strings in neither set are outside the promise. -/
structure PromiseProblem where
  yes : List Bool → Prop
  no : List Bool → Prop

/-- Promise-NP: a polynomial-time checking relation `R` (Cook's `checkLang R ∈ P`) and a uniform
polynomial bound such that every yes-instance has a certificate of polynomial length and no
no-instance has any certificate. Off the promise nothing is required. -/
def PromiseNP (Pr : PromiseProblem) : Prop :=
  ∃ (R : List Bool → List Bool → Prop) (k : ℕ),
    CookPvsNP.checkLang R ∈ CookPvsNP.P (Option (Bool ⊕ Bool)) ∧
    (∀ x, Pr.yes x → ∃ y, y.length ≤ x.length ^ k + k ∧ R x y) ∧
    (∀ x, Pr.no x → ∀ y, ¬ R x y)

/-- Promise-coNP: promise-NP with the roles of yes- and no-instances exchanged. -/
def PromiseCoNP (Pr : PromiseProblem) : Prop := PromiseNP ⟨Pr.no, Pr.yes⟩

/-! ### CsgGapValue (promise problems) -/

/-- **CsgGapValue** for reachability: input an instance, a state `s` (as a natural `< n`) and a
rational threshold `α`; yes if `val_T(s) ≥ α + ε`, no if `val_T(s) ≤ α - ε`. -/
def reachGap : PromiseProblem where
  yes x := ∃ (I : ReachInst) (h : I.Valid) (s : ℕ) (hs : s < I.G.n) (α : ℚ),
    I.enc ++ encNat s ++ encRat α = x ∧
      (α : ℝ) + (1 / 2 : ℝ) ^ I.Bε ≤ reachValue (I.G.toCSG h.1) (targetSet I.T) ⟨s, hs⟩
  no x := ∃ (I : ReachInst) (h : I.Valid) (s : ℕ) (hs : s < I.G.n) (α : ℚ),
    I.enc ++ encNat s ++ encRat α = x ∧
      reachValue (I.G.toCSG h.1) (targetSet I.T) ⟨s, hs⟩ ≤ (α : ℝ) - (1 / 2 : ℝ) ^ I.Bε

/-- **CsgGapValue** for limit-average objectives. -/
def limAvgGap : PromiseProblem where
  yes x := ∃ (I : LimAvgInst) (h : I.Valid) (s : ℕ) (hs : s < I.G.n) (α : ℚ),
    I.enc ++ encNat s ++ encRat α = x ∧
      (α : ℝ) + (1 / 2 : ℝ) ^ I.Bε ≤ limAvgValue (I.G.toCSG h.1) I.r.toReal ⟨s, hs⟩
  no x := ∃ (I : LimAvgInst) (h : I.Valid) (s : ℕ) (hs : s < I.G.n) (α : ℚ),
    I.enc ++ encNat s ++ encRat α = x ∧
      limAvgValue (I.G.toCSG h.1) I.r.toReal ⟨s, hs⟩ ≤ (α : ℝ) - (1 / 2 : ℝ) ^ I.Bε

/-- **CsgGapValue** for discounted-sum objectives with a succinct discount factor. -/
def discGap : PromiseProblem where
  yes x := ∃ (I : DiscInst) (h : I.Valid) (s : ℕ) (hs : s < I.G.n) (α : ℚ),
    I.enc ++ encNat s ++ encRat α = x ∧
      (α : ℝ) + (1 / 2 : ℝ) ^ I.Bε ≤
        discValue (I.G.toCSG h.1) I.r.toReal (succinct I.Blam) ⟨s, hs⟩
  no x := ∃ (I : DiscInst) (h : I.Valid) (s : ℕ) (hs : s < I.G.n) (α : ℚ),
    I.enc ++ encNat s ++ encRat α = x ∧
      discValue (I.G.toCSG h.1) I.r.toReal (succinct I.Blam) ⟨s, hs⟩ ≤
        (α : ℝ) - (1 / 2 : ℝ) ^ I.Bε

/-! ### Witnesses (§5.2, printed p. 15) -/

/-- A candidate tuple `(σ, τ, I_σ, I_τ)` in power-series representation: the probabilities
`σ(s)(a)`, `τ(s)(b)` and the interval endpoints `L_σ(s), U_σ(s), L_τ(s), U_τ(s)`. -/
structure WitnessData (n mA mB : ℕ) where
  σ : Fin n → Fin mA → PSNum
  τ : Fin n → Fin mB → PSNum
  Lσ : Fin n → PSNum
  Uσ : Fin n → PSNum
  Lτ : Fin n → PSNum
  Uτ : Fin n → PSNum

/-- Binary encoding of a tuple; its length is the size of the tuple. -/
def WitnessData.enc {n mA mB : ℕ} (W : WitnessData n mA mB) : List Bool :=
  encList (encList encPS) (List.ofFn fun s => List.ofFn (W.σ s)) ++
  encList (encList encPS) (List.ofFn fun s => List.ofFn (W.τ s)) ++
  encList encPS (List.ofFn W.Lσ) ++ encList encPS (List.ofFn W.Uσ) ++
  encList encPS (List.ofFn W.Lτ) ++ encList encPS (List.ofFn W.Uτ)

/-- The stationary strategy of Player 1 stored in a tuple, given that it is one. -/
def WitnessData.σStat {n mA mB : ℕ} (W : WitnessData n mA mB)
    (h : ∀ s, IsDist fun a => psVal (W.σ s a)) : Stationary₁ n mA :=
  fun s => ⟨fun a => psVal (W.σ s a), h s⟩

/-- The stationary strategy of Player 2 stored in a tuple, given that it is one. -/
def WitnessData.τStat {n mA mB : ℕ} (W : WitnessData n mA mB)
    (h : ∀ s, IsDist fun b => psVal (W.τ s b)) : Stationary₂ n mB :=
  fun s => ⟨fun b => psVal (W.τ s b), h s⟩

/-- `(σ, τ, I_σ, I_τ)` is a **witness** for the game `G`, reward `r`, succinct discount factor
`λ = 1 - 2^{-2^{Bλ}}` and additive error `ε = 2^{-Bε}`:
1. `σ, τ` are (power-series representable) stationary strategies;
2. `I_σ = (L_σ, U_σ)` (resp. `I_τ`) is an `ε/2`-close shrinking interval bound of `G_σ`
   (resp. `G_τ`);
3. `[L_σ(s), U_σ(s)] ∩ [L_τ(s), U_τ(s)] ≠ ∅` for every state `s`. -/
def IsWitness {n mA mB : ℕ} (G : CSG n mA mB) (r : Reward n mA mB) (Blam Bε : ℕ)
    (W : WitnessData n mA mB) : Prop :=
  ∃ (hσ : ∀ s, IsDist fun a => psVal (W.σ s a)) (hτ : ∀ s, IsDist fun b => psVal (W.τ s b)),
    IsShrinking₂ (fixP1 G (W.σStat hσ)) (fixP1Reward r (W.σStat hσ)) (succinct Blam)
        (fun s => psVal (W.Lσ s)) (fun s => psVal (W.Uσ s)) ∧
      IsClose ((1 / 2 : ℝ) ^ Bε / 2) (fun s => psVal (W.Lσ s)) (fun s => psVal (W.Uσ s)) ∧
    IsShrinking₁ (fixP2 G (W.τStat hτ)) (fixP2Reward r (W.τStat hτ)) (succinct Blam)
        (fun s => psVal (W.Lτ s)) (fun s => psVal (W.Uτ s)) ∧
      IsClose ((1 / 2 : ℝ) ^ Bε / 2) (fun s => psVal (W.Lτ s)) (fun s => psVal (W.Uτ s)) ∧
    ∀ s, max (psVal (W.Lσ s)) (psVal (W.Lτ s)) ≤ min (psVal (W.Uσ s)) (psVal (W.Uτ s))

/-! ### Algorithm 1 (printed p. 16) -/

/-- **Algorithm 1**, the verifier, with exact rational arithmetic. It checks
(line 2) that `σ(s)`, `τ(s)` have nonnegative entries summing to one;
(line 3) `L_σ ⪯ U_σ`, `L_τ ⪯ U_τ`;
(line 6) the shrinking inequalities in the expanded form of Equation (1), printed p. 17: for
`G_σ` the lower inequality for **every** action `b` and the upper inequality for **some** `b`;
for `G_τ` the lower inequality for **some** action `a` and the upper inequality for **every** `a`;
(line 8) `U_σ - L_σ ⪯ (ε/2)·1` and `U_τ - L_τ ⪯ (ε/2)·1`;
(line 10) `max(L_σ(s), L_τ(s)) ≤ min(U_σ(s), U_τ(s))` at every state.
(Power-series representability is syntactic: every entry is a list of signed powers of two.) -/
def algorithm1 (I : DiscInst) (W : WitnessData I.G.n I.G.mA I.G.mB) : Bool :=
  let lam : ℚ := 1 - (1 / 2 : ℚ) ^ (2 ^ I.Blam)
  let εh : ℚ := (1 / 2 : ℚ) ^ (I.Bε + 1)
  let σv := fun s a => psValQ (W.σ s a)
  let τv := fun s b => psValQ (W.τ s b)
  let Lσ := fun s => psValQ (W.Lσ s)
  let Uσ := fun s => psValQ (W.Uσ s)
  let Lτ := fun s => psValQ (W.Lτ s)
  let Uτ := fun s => psValQ (W.Uτ s)
  -- the right-hand side of Equation (1) for `G_σ` at `(s, b)`, applied to `ρ`
  let Eσ := fun (ρ : Fin I.G.n → ℚ) s b =>
    ∑ a, σv s a * ((1 - lam) * I.r s a b + lam * ∑ s', I.G.δ s a b s' * ρ s')
  -- the analogous expression for `G_τ` at `(s, a)`
  let Eτ := fun (ρ : Fin I.G.n → ℚ) s a =>
    ∑ b, τv s b * ((1 - lam) * I.r s a b + lam * ∑ s', I.G.δ s a b s' * ρ s')
  decide (
    ((∀ s, (∀ a, 0 ≤ σv s a) ∧ ∑ a, σv s a = 1) ∧
      (∀ s, (∀ b, 0 ≤ τv s b) ∧ ∑ b, τv s b = 1)) ∧
    ((∀ s, Lσ s ≤ Uσ s) ∧ (∀ s, Lτ s ≤ Uτ s)) ∧
    ((∀ s, ∀ b, Lσ s ≤ Eσ Lσ s b) ∧ (∀ s, ∃ b, Eσ Uσ s b ≤ Uσ s) ∧
      (∀ s, ∃ a, Lτ s ≤ Eτ Lτ s a) ∧ (∀ s, ∀ a, Eτ Uτ s a ≤ Uτ s)) ∧
    ((∀ s, Uσ s - Lσ s ≤ εh) ∧ (∀ s, Uτ s - Lτ s ≤ εh)) ∧
    (∀ s, max (Lσ s) (Lτ s) ≤ min (Uσ s) (Uτ s)))

end ConcurrentStochasticApprox.Approx


