-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_Kibitzer
-- name    : SparseCCE_ThreePlayer_Kibitzer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:07:48.660948+00:00
-- url     : https://prove2.me/theorems/5428c8e0-9233-4a6d-bb86-28cb24c05831
-- title:
--   The kibitzer game, its round payoffs, the profiles $y^\sigma$, profitable one-round deviations, and codes
-- statement:
--   From a Bayesian game $G$ and a horizon $H$: players $1,2$ (indices $0,1$) and the kibitzer $K$ (index $2$). In each round $K$ observes the history and chooses a challenge $(i,\theta_i,c)\in\{1,2\}\times\Theta_i\times A_i$; nature draws $\theta_{i'}\sim\rho(\cdot\mid\theta_i)$; players $1$ and $2$ observe the history and their own types and choose $a_1,a_2$. The outcome $o=(i,\theta_i,c,\theta_{i'},a_1,a_2)$ is public. Round payoffs (eq. (5)): $g_K(o)=u_i(\theta,a_{i\leftarrow c})-u_i(\theta,a)$, $g_i=-g_K$, $g_{i'}=0$; $\Gamma_j(\omega)=\frac1H\sum_hg_j(o_h)$.
--
--   In the protocol, stage 0 is $K$'s challenge, stage 1 nature's draw (only the type of the unchallenged player is available), stages 2 and 3 the actions of players 1 and 2; $K$'s signal is a dummy. `NeZero` on the type counts only makes the signal map total on unavailable move tuples.
--
--   $y^\sigma_i(\theta_i)=x_i(\cdot\mid\sigma,\theta_i)$. `IsProfitableDeviation ε₀ x x†`: for every player $j$, round and history, the round with $j$ using the pure strategy $x^\dagger_j$ and the others using $x$ gives $j$ an expected round payoff at least $\varepsilon_0$ if $j=K$ and at least $0$ otherwise.
--
--   Codes of challenges, outcomes, histories, signals, actions, queries and transcripts are fixed concretely; `IsLemma37Input` (unary $M$, $|G|$, $H$, a listing of the rational profile $x$) and `IsDeviationOutput` (flag `false` and a listing of $x^\dagger$) are the formats of Lemma 3.7.
--
--   The generic `roundLaw` uses the repeated game’s round/history-specific nature and signal fields. For `kGame` these fields default to `natureProb` and the type signals above.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §3.4, eq. (5), p. 18; App. A.4, p. 31.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_BayesGame
import Definitions.Def_SparseCCE_ThreePlayer_RepeatedGame
import Definitions.Def_SparseCCE_ThreePlayer_Transcripts
import Definitions.Def_SparseCCE_ThreePlayer_ReferenceProfile

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-! ### The kibitzer game (§3.4, eq. (5), p. 18)

Players `0, 1 : Fin 3` are the Bayesian players `1, 2` of `G`, and `2 : Fin 3` is the kibitzer
`K`. A round has four stages: `K` chooses a challenge `(i, θ_i, c)`; nature draws the type
`θ_{i'} ∼ ρ(· | θ_i)` of the other player; player `1` and then player `2` choose actions. -/

/-- A challenge `(i, θ_i, c) ∈ {1, 2} × Θ_i × A_i`: `inl (θ₁, c)` challenges player `1`,
`inr (θ₂, c)` player `2`. -/
abbrev Challenge (n : Fin 2 → ℕ) := (Fin (n 0) × Fin 2) ⊕ (Fin (n 1) × Fin 2)

/-- Nature's draw: the type of player `1` (`inl`) or of player `2` (`inr`). -/
abbrev NatureDraw (n : Fin 2 → ℕ) := Fin (n 0) ⊕ Fin (n 1)

/-- The move sets of the four stages of a round. -/
def KMv (n : Fin 2 → ℕ) : Fin 4 → Type
  | ⟨0, _⟩ => Challenge n
  | ⟨1, _⟩ => NatureDraw n
  | ⟨_, _⟩ => Fin 2

instance (n : Fin 2 → ℕ) : ∀ s, Fintype (KMv n s)
  | ⟨0, _⟩ => inferInstanceAs (Fintype (Challenge n))
  | ⟨1, _⟩ => inferInstanceAs (Fintype (NatureDraw n))
  | ⟨_ + 2, _⟩ => inferInstanceAs (Fintype (Fin 2))

instance (n : Fin 2 → ℕ) : ∀ s, DecidableEq (KMv n s)
  | ⟨0, _⟩ => inferInstanceAs (DecidableEq (Challenge n))
  | ⟨1, _⟩ => inferInstanceAs (DecidableEq (NatureDraw n))
  | ⟨_ + 2, _⟩ => inferInstanceAs (DecidableEq (Fin 2))

/-- Nature's draw is available iff it is the type of the player other than the challenged one. -/
def natureOK {n : Fin 2 → ℕ} : Challenge n → NatureDraw n → Prop
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | _, _ => False

instance natureOKDec {n : Fin 2 → ℕ} (c : Challenge n) (m : NatureDraw n) :
    Decidable (natureOK c m) := by
  cases c <;> cases m <;> simp [natureOK] <;> infer_instance

/-- The type profile `(θ₁, θ₂)`. -/
def typeProfile {n : Fin 2 → ℕ} (t₁ : Fin (n 0)) (t₂ : Fin (n 1)) : TypeProfile n
  | ⟨0, _⟩ => t₁
  | ⟨1, _⟩ => t₂

/-- `ρ(θ_{i'} | θ_i)`: the probability of nature's draw given the challenge. -/
def natureProb (G : BayesGame) : Challenge G.n → NatureDraw G.n → ℝ
  | .inl (t₁, _), .inr t₂ => G.ρ (typeProfile t₁ t₂) / G.marg 0 t₁
  | .inr (t₂, _), .inl t₁ => G.ρ (typeProfile t₁ t₂) / G.marg 1 t₂
  | _, _ => 0

/-- The type of player `1` determined by the challenge and nature's draw. -/
def type₁ {n : Fin 2 → ℕ} [NeZero (n 0)] : Challenge n → NatureDraw n → Fin (n 0)
  | .inl (t, _), _ => t
  | .inr _, .inl t => t
  | .inr _, .inr _ => default

/-- The type of player `2` determined by the challenge and nature's draw. -/
def type₂ {n : Fin 2 → ℕ} [NeZero (n 1)] : Challenge n → NatureDraw n → Fin (n 1)
  | .inr (t, _), _ => t
  | .inl _, .inr t => t
  | .inl _, .inl _ => default

/-- The signal set sizes: types of players `1, 2`, a dummy signal for `K`. -/
def kSigCard (n : Fin 2 → ℕ) : Fin 3 → ℕ := ![n 0, n 1, 1]

/-- The round protocol of the kibitzer game. -/
def kProtocol (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] : RoundProtocol (Fin 3) where
  L := 4
  Mv := KMv G.n
  mover := ![some 2, none, some 0, some 1]
  stage := ![2, 3, 0]
  allowed := fun s o m => match s, m with
    | ⟨1, _⟩, m => natureOK (o 0) m
    | _, _ => True
  allowedDec := fun s o m => match s, m with
    | ⟨0, _⟩, _ => instDecidableTrue
    | ⟨1, _⟩, m => natureOKDec (o 0) m
    | ⟨_ + 2, _⟩, _ => instDecidableTrue
  natK := fun s o m => match s, m with
    | ⟨1, _⟩, m => natureProb G (o 0) m
    | _, _ => 0
  Θ := fun j => Fin (kSigCard G.n j)
  sig := fun j o => match j with
    | ⟨0, _⟩ => type₁ (o 0) (o 1)
    | ⟨1, _⟩ => type₂ (o 0) (o 1)
    | ⟨2, _⟩ => (0 : Fin 1)

/-- The four moves of an outcome of the kibitzer round. -/
def kMoves (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (o : (kProtocol G).Outcome) :
    (s : Fin 4) → KMv G.n s := o.1

/-- The kibitzer's round payoff `g_K(o) = u_i(θ, a_{i←c}) − u_i(θ, a)` (eq. (5)): the gain of the
challenged type `θ_i` from switching to `c`; `θ = (θ₁, θ₂)`, `a = (a₁, a₂)`. -/
def kibitzerGain (G : BayesGame) (t₁ : Fin (G.n 0)) (t₂ : Fin (G.n 1)) (a : Fin 2 → Fin 2) :
    Challenge G.n → ℝ
  | .inl (_, c) => G.u 0 (typeProfile t₁ t₂) (Function.update a 0 c) - G.u 0 (typeProfile t₁ t₂) a
  | .inr (_, c) => G.u 1 (typeProfile t₁ t₂) (Function.update a 1 c) - G.u 1 (typeProfile t₁ t₂) a

/-- The round payoffs of eq. (5), p. 18: `g_K(o)` for the kibitzer, `g_i(o) = −g_K(o)` for the
challenged player `i`, `g_{i'}(o) = 0` for the other player. -/
def kRoundPayoff (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (j : Fin 3)
    (o : (kProtocol G).Outcome) : ℝ :=
  let c : Challenge G.n := kMoves G o 0
  let d : NatureDraw G.n := kMoves G o 1
  let a : Fin 2 → Fin 2 := ![(kMoves G o 2 : Fin 2), (kMoves G o 3 : Fin 2)]
  let gK := kibitzerGain G (type₁ c d) (type₂ c d) a c
  match j, c with
  | ⟨2, _⟩, _ => gK
  | ⟨0, _⟩, .inl _ => -gK
  | ⟨1, _⟩, .inr _ => -gK
  | _, _ => 0

/-- **The kibitzer game** with horizon `H` (§3.4, p. 18): the payoff of player `j` is its average
round payoff `Γ_j(ω) = (1/H) ∑_h g_j(o_h)`. -/
def kGame (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H : ℕ) : RepeatedGame (Fin 3) where
  P := kProtocol G
  H := H
  payoff := fun j ω => (1 / (H : ℝ)) * ∑ h, kRoundPayoff G j (ω h)

namespace RepeatedGame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (Γ : RepeatedGame ι)

/-- The law of the outcome of round `h` at history `σ` when every player `j` uses `x_j`. -/
def roundLaw (x : Γ.StrategyProfile) (h : Fin Γ.H) (σ : Fin h.val → Γ.P.Outcome)
    (o : Γ.P.Outcome) : ℝ :=
  Γ.natO h.val σ o * ∏ j, x j h σ (Γ.signalO h.val σ j o) (Γ.P.act j o)

/-- A pure legal strategy of player `j`: an action at every round, history and signal. -/
abbrev PureStrategy (j : ι) :=
  (h : Fin Γ.H) → (Fin h.val → Γ.P.Outcome) → Γ.P.Θ j → Γ.P.A j

/-- A pure strategy as a legal (mixed) strategy. -/
def pureToMixed {j : ι} (xd : Γ.PureStrategy j) : Γ.Strategy j :=
  fun h σ θ a => if a = xd h σ θ then 1 else 0

end RepeatedGame

/-- The Bayesian profile `y^σ` that players `1` and `2` play at the history `σ` of round `h`:
`y^σ_i(θ_i) = x_i(· | σ, θ_i)` (p. 18). -/
def ySigma (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] {H : ℕ}
    (x : (kGame G H).StrategyProfile) (h : Fin H) (σ : Fin h.val → (kProtocol G).Outcome) :
    G.Profile
  | ⟨0, _⟩ => fun t a => x 0 h σ t a
  | ⟨1, _⟩ => fun t a => x 1 h σ t a

/-- The conclusion of the second alternative of Lemma 3.7 (p. 18): at every history, a round with
player `j` using the pure legal strategy `x†_j` and its opponents using `x` gives `j` an expected
round payoff of at least `ε₀` if `j = K`, and at least `0` otherwise. -/
def IsProfitableDeviation (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] {H : ℕ} (ε₀ : ℝ)
    (x : (kGame G H).StrategyProfile) (xd : (j : Fin 3) → (kGame G H).PureStrategy j) : Prop :=
  ∀ j h σ, (if j = 2 then ε₀ else 0) ≤
    ∑ o, (kGame G H).roundLaw (Function.update x j ((kGame G H).pureToMixed (xd j))) h σ o *
      kRoundPayoff G j o

instance (G : RatBayesGame) (i : Fin 2) [h : NeZero (G.n i)] : NeZero (G.toReal.n i) := h

/-! ### Codes of the objects of the kibitzer game -/

/-- Code of a challenge: which player, then the type and the action in binary. -/
def chCode {n : Fin 2 → ℕ} : Challenge n → List Bool
  | .inl (t, c) => false :: QAlgorithms.LocalHamiltonian.encBin t ++
      QAlgorithms.LocalHamiltonian.encBin c
  | .inr (t, c) => true :: QAlgorithms.LocalHamiltonian.encBin t ++
      QAlgorithms.LocalHamiltonian.encBin c

/-- Code of an action in `{0, 1}`. -/
def encBit (a : Fin 2) : List Bool := QAlgorithms.LocalHamiltonian.encBin a.val

/-- Code of nature's draw. -/
def natCode {n : Fin 2 → ℕ} : NatureDraw n → List Bool
  | .inl t => false :: QAlgorithms.LocalHamiltonian.encBin t
  | .inr t => true :: QAlgorithms.LocalHamiltonian.encBin t

section codes

variable (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)]

/-- Code of an outcome `o = (i, θ_i, c, θ_{i'}, a₁, a₂)`. -/
def outCode (o : (kProtocol G).Outcome) : List Bool :=
  chCode (kMoves G o 0 : Challenge G.n) ++ natCode (kMoves G o 1 : NatureDraw G.n) ++
    encBit (kMoves G o 2) ++
    encBit (kMoves G o 3)

/-- Code of a history: its outcomes in order. -/
def histCode {h : ℕ} (σ : Fin h → (kProtocol G).Outcome) : List Bool :=
  (List.finRange h).flatMap (fun l => outCode G (σ l))

/-- Code of a signal. -/
def sigCode (j : Fin 3) (θ : Fin (kSigCard G.n j)) : List Bool :=
  QAlgorithms.LocalHamiltonian.encBin (θ : ℕ)

/-- Code of an action of player `j`. -/
def actCode : (j : Fin 3) → (kProtocol G).A j → List Bool
  | ⟨0, _⟩, a => encBit a
  | ⟨1, _⟩, a => encBit a
  | ⟨2, _⟩, a => chCode (a : Challenge G.n)

/-- Code of a query of player `j` in the kibitzer game with horizon `H`. -/
def kQueryCode (H : ℕ) (j : Fin 3) (q : (kGame G H).Query j) : List Bool :=
  (match q.1 with
    | none => [false]
    | some o => true :: outCode G o) ++ sigCode G j q.2

/-- Code of a transcript of player `j`. -/
def kTrCode (H : ℕ) (j : Fin 3) (z : (kGame G H).Transcript j) : List Bool :=
  (List.finRange H).flatMap (fun h => kQueryCode G H j (z.1 h).1 ++ actCode G j (z.1 h).2)

/-- The input of the algorithm of Lemma 3.7: `M` in unary, the code `|G|` of the source game,
`H`, and a listing of the rational legal profile `x`, keyed by player, round, history, signal and
action. -/
def IsLemma37Input (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H : ℕ)
    (x : (j : Fin 3) → (h : Fin H) → (Fin h.val → (kProtocol G.toReal).Outcome) →
      (kProtocol G.toReal).Θ j → (kProtocol G.toReal).A j → ℚ) (s : List Bool) : Prop :=
  ∃ xs : List Bool,
    IsLawListing (K := Σ j : Fin 3, Σ h : Fin H, (Fin h.val → (kProtocol G.toReal).Outcome) ×
        (kProtocol G.toReal).Θ j × (kProtocol G.toReal).A j)
      (fun k => QAlgorithms.LocalHamiltonian.encBin k.1 ++ QAlgorithms.LocalHamiltonian.encBin k.2.1
        ++ histCode G.toReal k.2.2.1 ++ sigCode G.toReal k.1 k.2.2.2.1 ++
        actCode G.toReal k.1 k.2.2.2.2)
      (fun k => x k.1 k.2.1 k.2.2.1 k.2.2.2.1 k.2.2.2.2) xs ∧
    s = unary (kGame G.toReal H).Mmax ++ G.code ++ QAlgorithms.LocalHamiltonian.encBin H ++ xs

/-- `s` is an output of the second kind of Lemma 3.7: the flag `false`, then a listing of the
pure legal strategies `x†`, keyed by player, round, history and signal, valued by the action. -/
def IsDeviationOutput (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H : ℕ)
    (xd : (j : Fin 3) → (kGame G.toReal H).PureStrategy j) (s : List Bool) : Prop :=
  ∃ xs : List Bool,
    IsListing (K := Σ j : Fin 3, Σ h : Fin H, (Fin h.val → (kProtocol G.toReal).Outcome) ×
        (kProtocol G.toReal).Θ j)
      (fun k => QAlgorithms.LocalHamiltonian.encBin k.1 ++ QAlgorithms.LocalHamiltonian.encBin k.2.1
        ++ histCode G.toReal k.2.2.1 ++ sigCode G.toReal k.1 k.2.2.2)
      (fun k => actCode G.toReal k.1 (xd k.1 k.2.1 k.2.2.1 k.2.2.2)) xs ∧
    s = false :: xs

end codes

end SparseCCE.ThreePlayer


