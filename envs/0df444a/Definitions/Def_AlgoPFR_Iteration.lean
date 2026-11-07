-- Prove2me | Definitions.Def_AlgoPFR_Iteration
-- name    : AlgoPFR_Iteration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T10:44:27.570193+00:00
-- url     : https://prove2.me/theorems/9920fa8e-1a0a-4f2d-a92f-cc09d72887fd
-- title:
--   One iteration and the trajectory law of Algorithm 2; $C_{\mathrm{fib}}$, $C_{\mathrm{access}}$, $L_0$, $\xi$, $d_{\mathrm{term}}$, $T$
-- statement:
--   A **state** is a pair of access procedures $(X,Y)$ with envelopes $(M_X,M_Y)$. One iteration of Algorithm 2 chooses one of the five families uniformly, draws its natural label, applies the protocols of Lemmas 4.4–4.6 with the envelopes they state, draws independent bucket labels $J_X,J_Y$ and passes to the two buckets.
--
--   The cost overheads are
--   $$C_{\mathrm{access}}=C_{\mathrm{fib}}+\log\frac{2^{J_X+1}}{\pi_{J_X}}+\log\frac{2^{J_Y+1}}{\pi_{J_Y}},$$
--   where $C_{\mathrm{fib}}$ is $0$ for the sum families and otherwise the sum of the logarithms of the reciprocal acceptance probabilities of the fiber rejection samplers (Eq. (43)).
--
--   The constants are $L_0=256/\eta$, $\xi=768/\eta$ and $d_{\mathrm{term}}=\max\{L_0+1,\frac{16}\eta\log\frac{64}\eta\}$. An iteration is **good**, with $d=\max\{d[X;Y],d_{\mathrm{term}}\}$, when
--   $$\Phi_{X,Y}(X_t,Y_t)\le(1-\eta/2)d,\quad\Delta[X_t],\Delta[Y_t]\le L_0,\quad C_{\mathrm{access}}\le\xi(d+1).$$
--   The **trajectory law** iterates this random kernel $T=\min\{t\ge0:(1-\eta/2)^t\log K\le d_{\mathrm{term}}\}$ times from the root state $X_0=Y_0=U_A$, recording each state and each choice.
--
--   **Formalization Note** The trajectory omits the budget checks of lines 9–11 of Algorithm 2, which belong to the running time of the composed procedure. A cross-sum gives both coordinates the envelope $M_Y$ of Lemma 4.4. The trajectory is the random kernel, never a chosen good family.
-- source:
--   Arunachalam, Dutt, Grewal, Gupte, Marton's conjecture in polynomial time, arXiv:2609.20771 (sha256 60e45066…), Algorithm 2, p.29; Eqs. (43)–(44), p.31; Claim 4.12, p.33; Eq. (57), p.35

import Mathlib
import Definitions.Def_AlgoPFR_Protocols
import Definitions.Def_AlgoPFR_Families

set_option autoImplicit false

open scoped ENNReal

namespace AlgoPFR

noncomputable section

variable {n : ℕ}

/-- A current pair `(X, Y)` together with the envelopes of the two implementations. -/
structure AccessState (n : ℕ) where
  /-- The access procedures of `X`. -/
  X : Oracle n
  /-- The access procedures of `Y`. -/
  Y : Oracle n
  /-- The envelope `M_X`. -/
  MX : ℝ
  /-- The envelope `M_Y`. -/
  MY : ℝ

/-- `d[X;Y]` of a state. -/
def AccessState.dist (s : AccessState n) : ℝ :=
  rd s.X.sample s.Y.sample

/-- `p_{X+Y}(z)` as a real number, for the laws of two oracles. -/
def sumMass (X Y : Oracle n) (z : Vec n) : ℝ :=
  (sumLaw X.sample Y.sample z).toReal

/-- Line 7 of Algorithm 2, p.29: the access procedures and envelopes of `(X′, Y′)` given by the
protocols of Lemmas 4.4–4.6, with the envelopes these lemmas state. In particular the two copies in
a cross sum both have the envelope `M_Y` of Lemma 4.4. -/
def applyFamily (f : Family) (s : AccessState n) (ℓ : Vec n × Vec n) : AccessState n :=
  match f with
  | .selfSum => ⟨sumOracle s.X s.X, sumOracle s.Y s.Y, s.MX, s.MY⟩
  | .crossSum => ⟨sumOracle s.X s.Y, sumOracle s.X s.Y, s.MY, s.MY⟩
  | .selfFiber =>
    ⟨fiberOracle s.X s.X ℓ.1, fiberOracle s.Y s.Y ℓ.2,
      s.MX * s.MX / sumMass s.X s.X ℓ.1, s.MY * s.MY / sumMass s.Y s.Y ℓ.2⟩
  | .crossFiber =>
    ⟨fiberOracle s.X s.Y ℓ.1, fiberOracle s.Y s.X ℓ.2,
      s.MX * s.MY / sumMass s.X s.Y ℓ.1, s.MY * s.MX / sumMass s.Y s.X ℓ.2⟩
  | .endgame =>
    ⟨endgameOracle s.X s.Y ℓ.1 (ℓ.1 + ℓ.2), endgameOracle s.X s.Y ℓ.1 (ℓ.1 + ℓ.2),
      s.MX * s.MY / sumMass s.X s.Y (ℓ.1 + ℓ.2), s.MX * s.MY / sumMass s.X s.Y (ℓ.1 + ℓ.2)⟩

/-- `C_fib`, Eq. (43), p.31 of arXiv:2609.20771 (sha256 60e45066…): the sum of the logarithms of the
reciprocal acceptance probabilities of the fiber rejection samplers of the family. The endgame label
is `(z, w)`, written `(w, z)` in Eq. (43). -/
def cFib (f : Family) (s : AccessState n) (ℓ : Vec n × Vec n) : ℝ :=
  match f with
  | .selfSum => 0
  | .crossSum => 0
  | .selfFiber =>
    Real.logb 2 (s.MX / sumMass s.X s.X ℓ.1) + Real.logb 2 (s.MY / sumMass s.Y s.Y ℓ.2)
  | .crossFiber =>
    Real.logb 2 (s.MY / sumMass s.X s.Y ℓ.1) + Real.logb 2 (s.MX / sumMass s.X s.Y ℓ.2)
  | .endgame =>
    Real.logb 2 (s.MY / sumMass s.X s.Y ℓ.1) + Real.logb 2 (s.MX / sumMass s.X s.Y (ℓ.2 + ℓ.1))

/-- The random choices of one iteration once the family is fixed: the fiber label and the two bucket
labels. -/
abbrev FamilyOutcome (n : ℕ) := (Vec n × Vec n) × ℕ × ℕ

/-- The law of the random choices of one iteration for a fixed family: its natural label, then
independent bucket labels `J_X`, `J_Y` for the outputs `X′`, `Y′` (lines 7–8 of Algorithm 2,
p.29). -/
def familyOutcomeLaw (f : Family) (s : AccessState n) : PMF (FamilyOutcome n) :=
  (familyLabel f s.X.sample s.Y.sample).bind fun ℓ =>
    (pairLaw (bucketLabel (applyFamily f s ℓ).X) (bucketLabel (applyFamily f s ℓ).Y)).map
      fun j => (ℓ, j)

/-- The state after line 8 of Algorithm 2, p.29: the bucket `X̂ = X′_{J_X}`, `Ŷ = Y′_{J_Y}` with the
envelopes of Lemma 4.7. -/
def nextState (f : Family) (s : AccessState n) (ω : FamilyOutcome n) : AccessState n :=
  let s' := applyFamily f s ω.1
  ⟨bucketOracle s'.X ω.2.1, bucketOracle s'.Y ω.2.2,
    bucketEnv s'.X s'.MX ω.2.1, bucketEnv s'.Y s'.MY ω.2.2⟩

/-- `C_access`, Eq. (44), p.31: `C_fib + log (2^(J_X+1) / π_{J_X}) + log (2^(J_Y+1) / π_{J_Y})`. -/
def cAccess (f : Family) (s : AccessState n) (ω : FamilyOutcome n) : ℝ :=
  let s' := applyFamily f s ω.1
  cFib f s ω.1 + Real.logb 2 (2 ^ (ω.2.1 + 1) / bucketProb s'.X ω.2.1) +
    Real.logb 2 (2 ^ (ω.2.2 + 1) / bucketProb s'.Y ω.2.2)

/-- The law of one iteration (lines 6–8 of Algorithm 2, p.29): a family chosen uniformly at random,
then `familyOutcomeLaw`. -/
def iterationLaw (s : AccessState n) : PMF (Family × FamilyOutcome n) :=
  (PMF.uniformOfFintype Family).bind fun f => (familyOutcomeLaw f s).map fun ω => (f, ω)

/-- `L₀ = 256 / η`, Claim 4.12, p.33. -/
def L0 (η : ℝ) : ℝ := 256 / η

/-- `ξ = 768 / η`, Claim 4.12, p.33. -/
def xi (η : ℝ) : ℝ := 768 / η

/-- `d_term = max {L₀ + 1, (16 / η) log (64 / η)}`, Claim 4.12, p.33. -/
def dTerm (η : ℝ) : ℝ := max (L0 η + 1) (16 / η * Real.logb 2 (64 / η))

/-- `d̃ = max {d[X;Y], d_term}`, Claims 4.12–4.13, pp.33, 35. -/
def AccessState.dTilde (s : AccessState n) (η : ℝ) : ℝ := max s.dist (dTerm η)

/-- A **good iteration** in the sense of Claim 4.12, p.33, from `s` with the choices
`(f, ω)`: `Φ_{X,Y}(X_t, Y_t) ≤ (1 − η/2) d`, `Δ[X_t], Δ[Y_t] ≤ L₀` and `C_access ≤ ξ (d + 1)`,
where `d = max {d[X;Y], d_term}`. -/
def IsGoodIteration (η : ℝ) (s : AccessState n) (e : Family × FamilyOutcome n) : Prop :=
  let t := nextState e.1 s e.2
  potential η s.X.sample s.Y.sample t.X.sample t.Y.sample ≤ (1 - η / 2) * s.dTilde η ∧
    slack t.X t.MX ≤ L0 η ∧ slack t.Y t.MY ≤ L0 η ∧
    cAccess e.1 s e.2 ≤ xi η * (s.dTilde η + 1)

/-- The trajectory law of Algorithm 2, p.29, without the budget checks of lines 9–11: `T` iterations
from `s`, recording each starting state and the random choices of the iteration. -/
def trajectoryLaw : ℕ → AccessState n → PMF (List (AccessState n × Family × FamilyOutcome n))
  | 0, _ => PMF.pure []
  | T + 1, s =>
    (iterationLaw s).bind fun e =>
      (trajectoryLaw T (nextState e.1 s e.2)).map fun τ => (s, e) :: τ

/-- The state reached from `s` after the recorded iterations. -/
def finalState (s : AccessState n) (τ : List (AccessState n × Family × FamilyOutcome n)) :
    AccessState n :=
  τ.foldl (fun _ e => nextState e.2.1 e.1 e.2.2) s

/-- The initial state of Algorithm 2, line 1, p.29: `X₀ = Y₀ = U_A` with the root access and the
envelope `1 / |A|` of p.18. -/
def rootState (A : Finset (Vec n)) (hA : A.Nonempty) : AccessState n :=
  ⟨rootOracle A hA, rootOracle A hA, 1 / (A.card : ℝ), 1 / (A.card : ℝ)⟩

/-- The number of iterations `T = min {t ≥ 0 : (1 − η/2)^t log K ≤ d_term}`, Eq. (57), p.35. -/
def iterationBound (η K : ℝ) : ℕ :=
  sInf {t : ℕ | (1 - η / 2) ^ t * Real.logb 2 K ≤ dTerm η}

end

end AlgoPFR


