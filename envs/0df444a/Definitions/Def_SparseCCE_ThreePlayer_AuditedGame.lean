-- Prove2me | Definitions.Def_SparseCCE_ThreePlayer_AuditedGame
-- name    : SparseCCE_ThreePlayer_AuditedGame
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:08:49.316677+00:00
-- url     : https://prove2.me/theorems/1e126c5d-45b7-4e90-a4e7-d5810c5a9e83
-- title:
--   The normal-form encoding of the kibitzer game with audits: $R_j$, $\varepsilon=\lambda\varepsilon_0/64$, $\delta=\lambda/(4M^3)$, $W=6HM^2/\delta$, normalization
-- statement:
--   Player $j$'s action is a transcript $z_j\in Z_j$ and optionally one **audit** $(i,\kappa,\tilde z,s)$: a player $i\ne j$, a test $\kappa$ of $i$, a transcript $\tilde z\in Z_k$ of the third player $k$ and a sign $s\in\{-1,1\}$; it transfers $W\cdot s\cdot f_\kappa(z_i)\cdot\mathbf 1\{z_k=\tilde z\}$ from $i$ to $j$. The utility $R_j$ is $V_j(z)$ plus the transfers $j$ receives minus those it pays. The constants are $\varepsilon=\lambda\varepsilon_0/64$, $\delta=\lambda/(4M^3)$, $W=6HM^2/\delta$, with $\lambda$, $M$ of the kibitzer game; $R_{\max}=1+3W$ and the normalized utilities are $U_j=(R_j+R_{\max})/(2R_{\max})$. The recommended transcript of an action is its first component; the cyclic partners are $k_i=i+1 \bmod 3$.
--
--   `IsProp39Input` is the input format of Proposition 3.9: $M$ in unary, $|G|$, $H$, $T$, the rational weights, and each component as a listing of actions (by `aActCode`) with rational probabilities.
--
--   `IsProp39TableInput` is the corresponding probability-table format: unary $M$, $|G|$, $H$, $T$, and a listing of all action profiles and their rational probabilities.
-- source:
--   Fan Chen, Constantinos Daskalakis, Gabriele Farina, Noah Golowich and Charalampos Platanos, "On the Computation of Sparse Equilibria in Normal-Form Games", STOC 2027 submission (citation_basis: published; PDF SHA256 796c83067187974f1685ea4343c0c56d9f89e99484824615342fb7178ee023b5; PDF page = printed page). §3.4, p. 18; §3.5, p. 19.

import Mathlib
import Definitions.Def_SparseCCE_ThreePlayer_NormalForm
import Definitions.Def_SparseCCE_ThreePlayer_Kibitzer

noncomputable section

namespace SparseCCE.ThreePlayer

open scoped BigOperators

/-! ### The normal-form encoding of the kibitzer game with audits (§3.4, p. 18; §3.5, p. 19) -/

/-- The third player `k ∉ {i, j}` of three (for `i ≠ j`). -/
def third (i j : Fin 3) : Fin 3 := ⟨(3 - i.val - j.val) % 3, Nat.mod_lt _ (by norm_num)⟩

section

variable (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H : ℕ)

/-- An audit by player `j` (p. 18): a player `i ≠ j`, a test `κ` of `i`, a transcript `z̃ ∈ Z_k`
of the third player `k`, and a sign `s ∈ {−1, 1}` (`true` is `+1`). -/
abbrev Audit (j : Fin 3) :=
  Σ i : {i : Fin 3 // i ≠ j}, (kGame G H).Test i.1 × (kGame G H).Transcript (third i.1 j) × Bool

/-- An action of player `j` in the normal-form game: a transcript `z_j ∈ Z_j` and optionally one
audit. -/
abbrev AAction (j : Fin 3) := (kGame G H).Transcript j × Option (Audit G H j)

/-- The sign `s ∈ {−1, 1}`. -/
def signVal (s : Bool) : ℝ := if s then 1 else -1

/-- `M = max_j |Z_j|` for the kibitzer game with horizon `H`. -/
def kM : ℕ := (kGame G H).Mmax

/-- `λ` for the kibitzer game with horizon `H`. -/
def kLam : ℝ := (kGame G H).lamTot

/-- `δ = λ / (4 M³)` (p. 18). -/
def auditDelta : ℝ := kLam G H / (4 * (kM G H : ℝ) ^ 3)

/-- `W = 6 H M² / δ` (p. 18). -/
def auditW : ℝ := 6 * (H : ℝ) * (kM G H : ℝ) ^ 2 / auditDelta G H

/-- `ε = λ ε₀ / 64` (p. 18). -/
def auditEps (ε₀ : ℝ) : ℝ := kLam G H * ε₀ / 64

/-- `R_max = 1 + 3W` (§3.5, p. 19). -/
def auditRmax : ℝ := 1 + 3 * auditW G H

/-- The transfer `W · s · f_κ(z_i) · 1{z_k = z̃}` of the audit `(i, κ, z̃, s)` made by player `j`,
from `i` to `j`, at the transcript profile `z`. -/
def auditTransfer {j : Fin 3} (z : (kGame G H).TProfile) (a : Audit G H j) : ℝ :=
  auditW G H * signVal a.2.2.2 * (kGame G H).testFn a.2.1 (z a.1.1) *
    (if z (third a.1.1 j) = a.2.2.1 then 1 else 0)

/-- The utility `R_j` of player `j` (p. 18): its simulation payoff `V_j(z)` plus the transfers
it receives from its own audit minus the transfers it pays to the audits of others. -/
def auditUtil (j : Fin 3) (b : (l : Fin 3) → AAction G H l) : ℝ :=
  let z : (kGame G H).TProfile := fun l => (b l).1
  (kGame G H).simValue j z +
    (match (b j).2 with
      | none => 0
      | some a => auditTransfer G H z a) -
    ∑ l : Fin 3, (match (b l).2 with
      | none => 0
      | some a => if a.1.1 = j then auditTransfer G H z a else 0)

/-- The normalized utilities `U_j = (R_j + R_max)/(2 R_max)` with values in `[0, 1]` (§3.5,
p. 19). -/
def auditUtilNorm (j : Fin 3) (b : (l : Fin 3) → AAction G H l) : ℝ :=
  (auditUtil G H j b + auditRmax G H) / (2 * auditRmax G H)

/-- The transcripts recommended to the players, `tr j (z_j, audit) = z_j`. -/
def aTr (j : Fin 3) : AAction G H j → (kGame G H).Transcript j := Prod.fst

/-- The cyclic partner choice `k_i = i + 1 (mod 3)` (p. 30). -/
def cyclicPartner : Fin 3 → Fin 3 := fun i => i + 1

end

/-! ### Codes for the computability clause of Proposition 3.9 -/

section codes

variable (G : BayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H : ℕ)

/-- Code of a test `κ = (h, v, q)` of player `i`. -/
def testCode (i : Fin 3) (κ : (kGame G H).Test i) : List Bool :=
  QAlgorithms.LocalHamiltonian.encBin κ.1.val ++
    (List.finRange κ.1.val).flatMap (fun l =>
      kQueryCode G H i (κ.2.1.1 l).1 ++ actCode G i (κ.2.1.1 l).2) ++
    kQueryCode G H i κ.2.2.1

/-- Code of an action `(z_j, audit)` of player `j` of the normal-form game. -/
def aActCode (j : Fin 3) (b : AAction G H j) : List Bool :=
  kTrCode G H j b.1 ++
    (match b.2 with
      | none => [false]
      | some a => true :: QAlgorithms.LocalHamiltonian.encBin a.1.1.val ++
          testCode G H a.1.1 a.2.1 ++ kTrCode G H (third a.1.1 j) a.2.2.1 ++ [a.2.2.2])

end codes

/-- The input of the algorithm of Proposition 3.9: `M` in unary, the code `|G|`, `H`, and the
`T`-sparse law `μ` by its rational weights `w` and components, each component `p^{(t)}_j` as a
listing of the actions of player `j` (by `aActCode`) with their probabilities. -/
def IsProp39Input (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H T : ℕ) (w : Fin T → ℚ)
    (p : Fin T → (j : Fin 3) → AAction G.toReal H j → ℚ) (s : List Bool) : Prop :=
  ∃ comp : Fin T → Fin 3 → List Bool,
    (∀ t j, IsLawListing (aActCode G.toReal H j) (p t j) (comp t j)) ∧
    s = unary (kM G.toReal H) ++ G.code ++ QAlgorithms.LocalHamiltonian.encBin H ++
      QAlgorithms.LocalHamiltonian.encBin T ++ CardinalMatching.encRatVec T w ++
      (List.finRange T).flatMap (fun t => (List.finRange 3).flatMap (fun j => comp t j))

/-- Probability-table input for Proposition 3.9 (pp. 13, 19), without a supplied
factorization: `M` in unary, `G`, `H`, `T`, then a listing of all action profiles and their
rational probabilities. Sparsity is a promise on the table, over real product laws. -/
def IsProp39TableInput (G : RatBayesGame) [NeZero (G.n 0)] [NeZero (G.n 1)] (H T : ℕ)
    (μ : ((j : Fin 3) → AAction G.toReal H j) → ℚ) (s : List Bool) : Prop :=
  ∃ tab : List Bool,
    IsLawListing (fun b => (List.finRange 3).flatMap (fun j => aActCode G.toReal H j (b j))) μ tab ∧
    s = unary (kM G.toReal H) ++ G.code ++ QAlgorithms.LocalHamiltonian.encBin H ++
      QAlgorithms.LocalHamiltonian.encBin T ++ tab

end SparseCCE.ThreePlayer


