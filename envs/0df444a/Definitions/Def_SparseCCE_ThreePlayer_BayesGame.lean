-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_BayesGame
-- name    : SparseCCE_ThreePlayer_BayesGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:05:16.99735+00:00
-- url     : https://prove2.me/theorems/d0a40357-9e6a-4715-bb8f-9ee5918794fd
-- title:
--   Two-player two-action Bayesian games, type regret, every-type-$\varepsilon$ BNE, ex-ante regret, and the source problems
-- statement:
--   A **two-player, two-action Bayesian game** $G$ has type sets $\Theta_i=\mathrm{Fin}\,n_i$, actions $A_1=A_2=\{0,1\}$, a prior $\rho$ on type profiles $\theta=(\theta_1,\theta_2)$ and utilities $u_i(\theta,a)$. It is **valid** if $\rho\in\Delta(\Theta_1\times\Theta_2)$ has positive marginals $\rho_i(\theta_i)=\sum_{\theta':\theta'_i=\theta_i}\rho(\theta')$ and $u_i\in[0,1]$.
--
--   A **Bayesian profile** $y$ assigns $y_i(\theta_i)\in\Delta(\{0,1\})$ to every type. The **regret** of type $t$ of player $i$ is
--   $$\mathrm{Reg}_i(y;t)=\max_{c\in\{0,1\}}\sum_{\theta:\theta_i=t}\frac{\rho(\theta)}{\rho_i(t)}\sum_a\Big(\prod_l y_l(\theta_l)(a_l)\Big)\big(u_i(\theta,a_{i\leftarrow c})-u_i(\theta,a)\big).$$
--   $y$ is an **every-type-$\varepsilon$ BNE** if it is a Bayesian profile and every type of every player has regret at most $\varepsilon$; its **ex-ante regret** is $\mathrm{Reg}(y)=\sum_i\sum_t\rho_i(t)\mathrm{Reg}_i(y;t)$.
--
--   Rational games are coded by $n_1,n_2$, the prior and the utility tables (rational vectors, canonical orders); rational profiles by the vectors $y_i(t)$. `EveryTypeBNEProblem ε₀` asks, on valid rational games, for (the code of) a rational every-type-$\varepsilon_0$ BNE; `ExAnteRegretProblem γ` for a rational Bayesian profile with $\mathrm{Reg}(y)\le\gamma$.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §2.3, p. 13; Lemma 3.1, p. 14.

import Mathlib
import Definitions.Def_TetrisHard_Rows_Search
import Definitions.Def_CardinalMatching_encRatMatrix
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-- Type profiles `θ = (θ₁, θ₂)` of a two-player Bayesian game whose player `i` has the types
`Fin (n i)` (§2.3, p. 13; players `1, 2` are `0, 1 : Fin 2`). -/
abbrev TypeProfile (n : Fin 2 → ℕ) := (i : Fin 2) → Fin (n i)

/-- **A two-player, two-action Bayesian game** (§2.3, p. 13): type sets `Θ_i = Fin (n i)`,
action sets `A₁ = A₂ = {0, 1}` (`Fin 2`), a prior `ρ` on type profiles and utilities
`u_i(θ, a)`, `a : Fin 2 → Fin 2` an action profile. -/
structure BayesGame where
  n : Fin 2 → ℕ
  ρ : TypeProfile n → ℝ
  u : Fin 2 → TypeProfile n → (Fin 2 → Fin 2) → ℝ

namespace BayesGame

variable (G : BayesGame)

/-- The marginal `ρ_i(θ_i)` of the prior. -/
def marg (i : Fin 2) (t : Fin (G.n i)) : ℝ :=
  ∑ θ : TypeProfile G.n, if θ i = t then G.ρ θ else 0

/-- The standing assumptions of §2.3: `ρ ∈ Δ(Θ₁ × Θ₂)` with positive marginals, and utilities
`u_i(θ, a) ∈ [0, 1]`. -/
def Valid : Prop :=
  IsDist G.ρ ∧ (∀ i t, 0 < G.marg i t) ∧ ∀ i θ a, 0 ≤ G.u i θ a ∧ G.u i θ a ≤ 1

/-- A Bayesian profile `y = (y₁, y₂)`: a mixed action `y_i(θ_i) ∈ Δ(A_i)` for every type. -/
abbrev Profile := (i : Fin 2) → Fin (G.n i) → Fin 2 → ℝ

/-- `y` is a Bayesian profile: every `y_i(θ_i)` is a distribution on `{0, 1}`. -/
def IsProfile (y : G.Profile) : Prop := ∀ i t, IsDist (y i t)

/-- The expected gain of type `t` of player `i` from switching to the fixed action `c`:
`E[u_i(θ, a_{i←c}) − u_i(θ, a)]`, over `θ_{i'} ∼ ρ(· | θ_i = t)` and
`a ∼ y₁(θ₁) ⊗ y₂(θ₂)` (§2.3, p. 13). -/
def switchGain (y : G.Profile) (i : Fin 2) (t : Fin (G.n i)) (c : Fin 2) : ℝ :=
  ∑ θ : TypeProfile G.n, if θ i = t then
    (G.ρ θ / G.marg i t) * ∑ a : Fin 2 → Fin 2, (∏ l, y l (θ l) (a l)) *
      (G.u i θ (Function.update a i c) - G.u i θ a)
  else 0

/-- The regret of a type, `Reg_i(y; θ_i) = max_{c ∈ A_i} E[u_i(θ, a_{i←c}) − u_i(θ, a)]`
(§2.3, p. 13). -/
def regret (y : G.Profile) (i : Fin 2) (t : Fin (G.n i)) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun c : Fin 2 => G.switchGain y i t c)

/-- `y` is an every-type-`ε` Bayesian Nash equilibrium: a Bayesian profile in which every type
of every player has regret at most `ε` (§2.3, p. 13). -/
def IsEveryTypeBNE (y : G.Profile) (ε : ℝ) : Prop :=
  G.IsProfile y ∧ ∀ i t, G.regret y i t ≤ ε

/-- The ex-ante regret `Reg(y) = ∑_{i ∈ {1,2}} E_{θ_i ∼ ρ_i}[Reg_i(y; θ_i)]` (§2.3, p. 13). -/
def exAnteRegret (y : G.Profile) : ℝ :=
  ∑ i : Fin 2, ∑ t : Fin (G.n i), G.marg i t * G.regret y i t

end BayesGame

/-- A two-player, two-action Bayesian game with rational prior and utilities (an instance of the
source problems of Lemma 3.1, p. 14). -/
structure RatBayesGame where
  n : Fin 2 → ℕ
  ρ : TypeProfile n → ℚ
  u : Fin 2 → TypeProfile n → (Fin 2 → Fin 2) → ℚ

namespace RatBayesGame

variable (G : RatBayesGame)

/-- The same game with real entries. -/
def toReal : BayesGame where
  n := G.n
  ρ θ := (G.ρ θ : ℝ)
  u i θ a := (G.u i θ a : ℝ)

/-- The binary code `|G|` of a rational Bayesian game: `n₁, n₂` in self-delimiting binary, the
prior as a rational vector over type profiles (canonical mixed-radix order `finPiFinEquiv`), then
for each player `i` and action profile `a` the table `θ ↦ u_i(θ, a)`. -/
def code : List Bool :=
  (List.finRange 2).flatMap (fun i => QAlgorithms.LocalHamiltonian.encBin (G.n i)) ++
    CardinalMatching.encRatVec (∏ i, G.n i) (fun k => G.ρ (finPiFinEquiv.symm k)) ++
    (List.finRange 2).flatMap (fun i =>
      (List.finRange (∏ _i : Fin 2, 2)).flatMap (fun a =>
        CardinalMatching.encRatVec (∏ i, G.n i)
          (fun k => G.u i (finPiFinEquiv.symm k) (finPiFinEquiv.symm a))))

/-- A rational Bayesian profile of `G`. -/
abbrev RatProfile := (i : Fin 2) → Fin (G.n i) → Fin 2 → ℚ

/-- The binary code of a rational Bayesian profile: for each player `i` and type `θ_i`, the
rational vector `(y_i(θ_i)(0), y_i(θ_i)(1))`. -/
def profileCode (y : G.RatProfile) : List Bool :=
  (List.finRange 2).flatMap (fun i =>
    (List.finRange (G.n i)).flatMap (fun t => CardinalMatching.encRatVec 2 (y i t)))

/-- The rational profile as a real one. -/
def profileToReal (y : G.RatProfile) : G.toReal.Profile := fun i t a => (y i t a : ℝ)

end RatBayesGame

/-- **Source problem (a) of Lemma 3.1** (p. 14): given a two-player, two-action Bayesian game
(rational, satisfying the standing assumptions of §2.3), compute an every-type-`ε₀` BNE. Answers
are the codes of every rational every-type-`ε₀` BNE. -/
def EveryTypeBNEProblem (ε₀ : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : RatBayesGame, G.toReal.Valid ∧ s = G.code
  answer s t := ∃ G : RatBayesGame, G.toReal.Valid ∧ s = G.code ∧
    ∃ y : G.RatProfile, t = G.profileCode y ∧
      G.toReal.IsEveryTypeBNE (G.profileToReal y) (ε₀ : ℝ)

/-- **Source problem (b) of Lemma 3.1** (p. 14): given a two-player, two-action Bayesian game,
compute a Bayesian profile `y` with ex-ante regret `Reg(y) ≤ γ`. Answers are the codes of every
rational such profile. -/
def ExAnteRegretProblem (γ : ℚ) : TetrisHard.Rows.SearchProblem where
  valid s := ∃ G : RatBayesGame, G.toReal.Valid ∧ s = G.code
  answer s t := ∃ G : RatBayesGame, G.toReal.Valid ∧ s = G.code ∧
    ∃ y : G.RatProfile, t = G.profileCode y ∧
      G.toReal.IsProfile (G.profileToReal y) ∧ G.toReal.exAnteRegret (G.profileToReal y) ≤ (γ : ℝ)

end SparseCCE.ThreePlayer


