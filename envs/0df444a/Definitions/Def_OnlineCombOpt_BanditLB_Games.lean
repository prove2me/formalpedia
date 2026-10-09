-- Prove2me | Definitions.Def_OnlineCombOpt_BanditLB_Games
-- name    : OnlineCombOpt_BanditLB_Games
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T16:54:35.802982+00:00
-- url     : https://prove2.me/theorems/8d2ed1e9-2ac6-4927-947f-0df625ca9ac1
-- title:
--   App. B, pp. 16–18 — parallel games, Bernoulli adversaries and observation laws
-- statement:
--   For $m$ parallel games with $k$ choices each, an action is a function $\alpha:\{1,\ldots,m\}\to\{1,\ldots,k\}$, representing a binary matrix with one selected entry in each row. Against the $\alpha$-adversary, each coordinate loss is an independent Bernoulli variable with parameter $1/2-\epsilon$ at the selected entry and $1/2$ elsewhere. The $(-i,\alpha)$-adversary restores parameter $1/2$ throughout game $i$.
--
--   A deterministic player maps every finite history of observed scalar losses to an action. The definitions give the finite laws of the observation sequence, the probability $P_{i,\alpha}(1)$ of selecting the favoured coordinate at a uniformly chosen round, and the corresponding probability $P_{-i,\alpha}(1)$. They also give the Poisson-binomial law of a sum of independent Bernoulli variables and its finite Kullback–Leibler divergence,
--
--   $$
--   \mathrm{KL}(P,Q)=\sum_xP(x)\log\frac{P(x)}{Q(x)}.
--   $$
--
--   Finally, the regret of a deterministic player against the $\alpha$-adversary is its expected cumulative loss minus the smallest expected cumulative loss of a fixed action, as in the paper's definition of $R_n$. These objects are reused by the appendix milestones.
--
--   **Formalization Note** The $m$ games of $k=d/m$ actions are the paper's identification of $\{0,1\}^d$ with $\{0,1\}^{m\times d/m}$; the action $\alpha$ is the matrix with $\alpha(i,j)=1$ iff $\alpha_i=j$. Game and round indices are zero-based. The observation law is a finite sum over binary loss arrays and matching deterministic runs. Zero-mass KL summands contribute zero; every law compared in the milestones has common support under the stated parameter bounds.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, pp. 16–18, Appendix B; pp. 20–21, Lemmas 4–5

import Mathlib

namespace OnlineCombOpt.BanditLB

/-! The proof model of App. B (arXiv:1204.4710v2, pp. 16–18): `d = m * k` coordinates arranged as
`m` parallel games with `k = d/m` actions each. An action is `a : Fin m → Fin k` (the binary matrix
with `a(i, j) = 1` iff `a i = j`); a loss sequence is `ω : Fin n → Fin m → Fin k → Bool`
(`true` = loss one). Games, actions and rounds are 0-based. -/

/-- An action of the `m` parallel games: the chosen action `a i` of each game `i`. -/
abbrev GameAction (m k : ℕ) := Fin m → Fin k
abbrev LossSeq (n m k : ℕ) := Fin n → Fin m → Fin k → Bool
/-- A deterministic player: at round `t` it maps the real-valued observed losses of rounds
`0, …, t-1` to an action. -/
abbrev DetPlayer (m k : ℕ) := (t : ℕ) → (Fin t → ℝ) → GameAction m k

/-- Probability mass of a Bernoulli variable with success parameter `p`. -/
def bernMass (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

/-- Independent Bernoulli losses with the favored coordinate selected by `α`. -/
noncomputable def advProb {n m k : ℕ} (ε : ℝ) (α : GameAction m k)
    (ω : LossSeq n m k) : ℝ :=
  ∏ t : Fin n, ∏ i : Fin m, ∏ j : Fin k,
    bernMass (if α i = j then (1 : ℝ) / 2 - ε else 1 / 2) (ω t i j)

/-- In game `i₀`, all losses have Bernoulli parameter one half. -/
noncomputable def advProbMinus {n m k : ℕ} (ε : ℝ) (i₀ : Fin m)
    (α : GameAction m k) (ω : LossSeq n m k) : ℝ :=
  ∏ t : Fin n, ∏ i : Fin m, ∏ j : Fin k,
    bernMass (if i = i₀ then (1 : ℝ) / 2 else
      if α i = j then (1 : ℝ) / 2 - ε else 1 / 2) (ω t i j)

/-- The play after a given observed-loss prefix. -/
def playAt {n m k : ℕ} (f : DetPlayer m k)
    (W : Fin n → Fin (m + 1)) (t : Fin n) : GameAction m k :=
  f t.val (fun s : Fin t.val =>
    ((W ⟨s.val, Nat.lt_trans s.isLt t.isLt⟩).val : ℝ))

/-- The recorded observation is exactly the number of selected coordinates with loss one. -/
def IsRun {n m k : ℕ} (f : DetPlayer m k)
    (ω : LossSeq n m k) (W : Fin n → Fin (m + 1)) : Prop :=
  ∀ t : Fin n, (W t).val =
    ∑ i : Fin m, if ω t i (playAt f W t i) then 1 else 0

/-- For a fixed loss sequence exactly one observation sequence is a run (it is built round by
round); `runMass` is its indicator, so `∑ W, runMass f ω W * g W` evaluates `g` at that run. -/
noncomputable def runMass {n m k : ℕ} (f : DetPlayer m k)
    (ω : LossSeq n m k) (W : Fin n → Fin (m + 1)) : ℝ :=
  by
    classical
    exact if IsRun f ω W then 1 else 0

/-- `ℙ_{i,α}(1)`: the probability, against the α-adversary and at a round `τ` uniform on the `n`
rounds, that the player chooses the favoured action `α i` in game `i`. -/
noncomputable def pAlpha {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (α : GameAction m k) : ℝ :=
  (∑ ω : LossSeq n m k, advProb ε α ω *
    ∑ W : Fin n → Fin (m + 1), runMass f ω W *
      ∑ t : Fin n, if playAt f W t i = α i then (1 : ℝ) else 0) / (n : ℝ)

/-- `ℙ_{−i,α}(1)`: as `pAlpha`, against the `(−i,α)`-adversary. -/
noncomputable def pMinus {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (α : GameAction m k) : ℝ :=
  (∑ ω : LossSeq n m k, advProbMinus ε i α ω *
    ∑ W : Fin n → Fin (m + 1), runMass f ω W *
      ∑ t : Fin n, if playAt f W t i = α i then (1 : ℝ) else 0) / (n : ℝ)

/-- Law of the observed loss sequence against the α-adversary. -/
noncomputable def lawW {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (α : GameAction m k) (W : Fin n → Fin (m + 1)) : ℝ :=
  ∑ ω : LossSeq n m k, advProb ε α ω * runMass f ω W

/-- Law of the observed loss sequence against the `(−i,α)`-adversary. -/
noncomputable def lawWMinus {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (α : GameAction m k) (W : Fin n → Fin (m + 1)) : ℝ :=
  ∑ ω : LossSeq n m k, advProbMinus ε i α ω * runMass f ω W

/-- `ℙ_{i,α}`: the law on `Bool` of `α(i, I_{i,τ})` (`true` = the favoured action is chosen). -/
noncomputable def choiceLaw {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (α : GameAction m k) (b : Bool) : ℝ :=
  if b then pAlpha n ε f i α else 1 - pAlpha n ε f i α

/-- `ℙ_{−i,α}` as a law on `Bool`. -/
noncomputable def choiceLawMinus {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (α : GameAction m k) (b : Bool) : ℝ :=
  if b then pMinus n ε f i α else 1 - pMinus n ε f i α

/-- Kullback–Leibler divergence `KL(P, Q) = ∑ₓ P x log (P x / Q x)` of two probability vectors on a
finite type. A summand with `P x = 0` is `0`, the usual convention. In every use in this mission
(`0 < ε < 1/2`) `Q x = 0` forces `P x = 0`, so the value is the Kullback–Leibler divergence. -/
noncomputable def klFin {X : Type*} [Fintype X] (P Q : X → ℝ) : ℝ :=
  ∑ x, P x * Real.log (P x / Q x)

/-- Parameters `p,p₁,…,pₙ` from Lemma 4, with `p₁,…,pₗ=q` and the rest `r`. -/
def bernoulliParams (n ℓ : ℕ) (p q r : ℝ) (j : Fin (n + 1)) : ℝ :=
  if j.val = 0 then p else if j.val ≤ ℓ then q else r

/-- Distribution of a sum of independent, non-identically distributed Bernoulli variables. -/
noncomputable def pbLaw {r : ℕ} (p : Fin r → ℝ) (v : Fin (r + 1)) : ℝ :=
  ∑ b : Fin r → Bool,
    if (∑ j : Fin r, if b j then 1 else 0) = v.val then
      ∏ j : Fin r, bernMass (p j) (b j)
    else 0

/-- The pseudo-regret `Rₙ` (p. 2) of the deterministic player `f` against the α-adversary: its
expected cumulative loss minus the smallest expected cumulative loss of a fixed action
`a : Fin m → Fin k`. The loss of an action `a` at round `t` is the number of games `i` whose chosen
coordinate `a i` has loss one. If there is no action at all (`k = 0 < m`) the value is `0`. -/
noncomputable def gamesRegret {m k : ℕ} (n : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (α : GameAction m k) : ℝ :=
  if h : (Finset.univ : Finset (GameAction m k)).Nonempty then
    (∑ ω : LossSeq n m k, advProb ε α ω *
      ∑ W : Fin n → Fin (m + 1), runMass f ω W *
        ∑ t : Fin n, ∑ i : Fin m,
          if ω t i (playAt f W t i) then (1 : ℝ) else 0) -
    Finset.univ.inf' h (fun a : GameAction m k =>
      ∑ ω : LossSeq n m k, advProb ε α ω *
        ∑ t : Fin n, ∑ i : Fin m, if ω t i (a i) then (1 : ℝ) else 0)
  else 0

end OnlineCombOpt.BanditLB


