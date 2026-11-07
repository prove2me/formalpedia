-- Prove2me | Definitions.Def_MatMulTimeLP_Sampler
-- name    : MatMulTimeLP_Sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T05:50:22.845306+00:00
-- url     : https://prove2.me/theorems/5e1b5410-4112-4c0c-80ec-62f01ba60780
-- title:
--   Algorithm 6: tree nodes, accuracy, the Sample tree and the adversary transcripts
-- statement:
--   This module writes the residual sampler of Appendix A for $n=2^D$, with $\alpha=1/(8D)$ and $k=2^\kappa$ the least power of two with $k\ge 2^{13}D^3$.
--
--   1. The **nodes** are the intervals $S_{\ell,j}$ of length $2^\ell$, for $\kappa\le\ell\le D$. For a sketch $G\in\mathbb R^{k\times n}$, a residual $r$ is **accurate** if, at every node $J$,
--
--   $$(1-\alpha)k\|r_J\|_2^2\le\|G_{:,J}r_J\|_2^2\le(1+\alpha)k\|r_J\|_2^2.\tag{17}$$
--
--   2. The estimate is $\tilde E=\|Gr\|_2^2/(k(1-\alpha))$. The **proposal probability** $\pi_i$ is the product of the branching probabilities $a_q/(a_1+a_2)$ along the path to $i$ and the final probability $r_i^2/\sum_{s}r_s^2$ inside the leaf.
--   3. **Sample(U)** is Lines 13–26 of Algorithm 6 as a finite probability tree, with answers Fail, $\bot$ or a coordinate; `sampleExp` is the expected value of a function of the answer.
--   4. An **adaptive adversary** is a function from the transcript so far to the next operation, Update or Sample. The module gives the probability of a transcript under the data structure with a fixed $G$, and under the independent sampler, which returns $i$ with probability $r_i^2/U$ and $\bot$ otherwise. It also gives the condition $U\ge 4\|r\|_2^2$ on every query.
--   5. The sketch law has independent standard Gaussian entries.
--
--   These objects state why a sketch-based sampler can answer exactly, with the sketch hidden from the caller.
--
--   **Formalization Note** Coordinates and nodes are $0$-indexed, so the paper's $S_{\ell,j}$ is `node l (j-1)`. The sketch is a function on `Fin k × Fin n`, which carries the product measure. Every value on the tree is a probability: Line 14 guards Line 15, and Line 25 guards Line 26. At $U=0$, where $\tilde E=0$, the convention $0/0=0$ rejects with probability $1$, as the proof of Lemma A.3 says. The sketch of a node is written directly as $G_{:,S}r_S$, which is identity (16).
-- source:
--   Jiang–Kyng–Zöcklein, Solving Linear Programs in Truly Matrix Multiplication Time, STOC 2027 submission (manuscript sha256 6539350a…81ffcc), Appendix A, pp.44–47; Algorithm 6 p.46; (16), (17) p.45

import Mathlib
import Definitions.Def_MatMulTimeLP_FixPoint

namespace MatMulTimeLP

open MeasureTheory ProbabilityTheory

/-!
# Algorithm 6, the residual sampler

Jiang–Kyng–Zöcklein, *Solving Linear Programs in Truly Matrix Multiplication Time*, STOC 2027
submission (manuscript sha256 6539350a…81ffcc), Appendix A, pp.44–47.

**Formalization Note** As in Appendix A, `n = 2^D`, `α = 1/(8D)` and `k = 2^κ` is the least power of two
with `k ≥ 2¹³D³`. Coordinates are `0`-indexed, so the paper's `S_{ℓ,j}` is `node ℓ (j-1)` and its children
`S_{ℓ-1,2j-1}, S_{ℓ-1,2j}` are `node (ℓ-1) (2j)`, `node (ℓ-1) (2j+1)` after the shift. The sketch `G` is a
function on `Fin k × Fin n`, because that type carries the product measure. Sample is a finite probability
tree: `sampleExp G r U φ` is the expected value of `φ` on its answer, so the probability of an answer `o` is
`sampleExp` at the indicator of `o`. All values on the tree are probabilities: Line 14 guards Line 15, and
Line 25 guards Line 26. Line 15 at `U = 0` forces `Ẽ = 0`, and there `0/0 = 0` rejects with probability `1`,
as the proof of Lemma A.3 says. The sketch `y_{ℓ,j}` is written directly as `G_{:,S}r_S`, which is identity
(16) of the page.
-/

/-- `α = 1/(8D)`, p.44. -/
noncomputable def skAlpha (D : ℕ) : ℝ := 1 / (8 * (D : ℝ))

/-- `κ`, with `2^κ` the least power of two `≥ 2¹³D³`, p.44. -/
def skKappa (D : ℕ) : ℕ := Nat.clog 2 (2 ^ 13 * D ^ 3)

/-- `k = 2^κ`, p.44. -/
def skK (D : ℕ) : ℕ := 2 ^ skKappa D

variable {k n : ℕ}

open scoped Classical in
/-- The tree node `S_{ℓ,j}` of length `2^ℓ`, `0`-indexed. -/
noncomputable def node (l j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun s => s.val / 2 ^ l = j

/-- `‖G_{:,J} r_J‖₂²` for the node `J = S_{ℓ,j}`, the left side of (17), and the `a₁, a₂` of Algorithm 6,
Line 18. -/
noncomputable def sketchSq (G : Fin k × Fin n → ℝ) (r : Fin n → ℝ) (l j : ℕ) : ℝ :=
  ∑ m, (∑ s ∈ node l j, G (m, s) * r s) ^ 2

/-- `‖r_J‖₂²` for the node `J = S_{ℓ,j}`. -/
noncomputable def energy (r : Fin n → ℝ) (l j : ℕ) : ℝ :=
  ∑ s ∈ node l j, r s ^ 2

/-- `E = ‖r‖₂²`. -/
def energyE (r : Fin n → ℝ) : ℝ := ∑ s, r s ^ 2

/-- The residual `r` is accurate for `G`, (17), p.45, at every node `S_{ℓ,j}`, `κ ≤ ℓ ≤ D`,
`j < 2^(D-ℓ)`. -/
def Accurate (D : ℕ) (G : Fin (skK D) × Fin (2 ^ D) → ℝ) (r : Fin (2 ^ D) → ℝ) : Prop :=
  ∀ l j, skKappa D ≤ l → l ≤ D → j < 2 ^ (D - l) →
    (1 - skAlpha D) * (skK D : ℝ) * energy r l j ≤ sketchSq G r l j ∧
      sketchSq G r l j ≤ (1 + skAlpha D) * (skK D : ℝ) * energy r l j

/-- The estimate `Ẽ = ‖y‖₂² / (k(1 - α))` at the root `y = Gr`, Algorithm 6, Line 13. -/
noncomputable def estE (D : ℕ) (G : Fin (skK D) × Fin (2 ^ D) → ℝ) (r : Fin (2 ^ D) → ℝ) : ℝ :=
  sketchSq G r D 0 / ((skK D : ℝ) * (1 - skAlpha D))

/-- The branching probability of the walk from level `ℓ` to `ℓ - 1` on the way to coordinate `i`. -/
noncomputable def branchProb (D : ℕ) (G : Fin (skK D) × Fin (2 ^ D) → ℝ) (r : Fin (2 ^ D) → ℝ)
    (i : Fin (2 ^ D)) (l : ℕ) : ℝ :=
  sketchSq G r (l - 1) (i.val / 2 ^ (l - 1)) /
    (sketchSq G r (l - 1) (2 * (i.val / 2 ^ l)) + sketchSq G r (l - 1) (2 * (i.val / 2 ^ l) + 1))

/-- The proposal probability `πᵢ`, p.45: the product of the branching probabilities along the unique
root-to-leaf path to `i` and the final probability `rᵢ²/∑_{s∈S_{κ,j}} r_s²` inside the leaf. -/
noncomputable def proposal (D : ℕ) (G : Fin (skK D) × Fin (2 ^ D) → ℝ) (r : Fin (2 ^ D) → ℝ)
    (i : Fin (2 ^ D)) : ℝ :=
  (∏ l ∈ Finset.Ioc (skKappa D) D, branchProb D G r i l) *
    (r i ^ 2 / energy r (skKappa D) (i.val / 2 ^ skKappa D))

/-- An answer of `Sample`: `Fail`, `⊥`, or a coordinate. -/
inductive Answer (n : ℕ) where
  | fail
  | bot
  | coord (i : Fin n)
  deriving DecidableEq

/-- Algorithm 6, Lines 25–26, as an expectation, for a proposal `i` recorded with probability `p`. -/
noncomputable def acceptExp (Etil : ℝ) (r : Fin n → ℝ) (φ : Answer n → ℝ) (i : Fin n) (p : ℝ) : ℝ :=
  if r i ^ 2 > 2 * Etil * p then φ Answer.fail
  else r i ^ 2 / (2 * Etil * p) * φ (Answer.coord i) +
    (1 - r i ^ 2 / (2 * Etil * p)) * φ Answer.bot

/-- Algorithm 6, Lines 22–26, as an expectation, at the leaf `S_{ℓ,j}` reached with probability `p`. -/
noncomputable def leafExp (Etil : ℝ) (r : Fin n → ℝ) (φ : Answer n → ℝ) (l j : ℕ) (p : ℝ) : ℝ :=
  if energy r l j = 0 then φ Answer.fail
  else ∑ i ∈ node l j, r i ^ 2 / energy r l j *
    acceptExp Etil r φ i (p * (r i ^ 2 / energy r l j))

/-- Algorithm 6, Lines 17–26, as an expectation: `m` further levels below `S_{ℓ,j}`, reached with
probability `p`. -/
noncomputable def walkExp (G : Fin k × Fin n → ℝ) (Etil : ℝ) (r : Fin n → ℝ) (φ : Answer n → ℝ) :
    ℕ → ℕ → ℕ → ℝ → ℝ
  | 0, l, j, p => leafExp Etil r φ l j p
  | m + 1, l, j, p =>
    let a₁ := sketchSq G r (l - 1) (2 * j)
    let a₂ := sketchSq G r (l - 1) (2 * j + 1)
    if a₁ + a₂ = 0 then φ Answer.fail
    else a₁ / (a₁ + a₂) * walkExp G Etil r φ m (l - 1) (2 * j) (p * (a₁ / (a₁ + a₂))) +
      a₂ / (a₁ + a₂) * walkExp G Etil r φ m (l - 1) (2 * j + 1) (p * (a₂ / (a₁ + a₂)))

/-- `Sample(U)`, Algorithm 6, Lines 13–26, as an expectation over its answer, for a fixed `G`. -/
noncomputable def sampleExp (D : ℕ) (G : Fin (skK D) × Fin (2 ^ D) → ℝ) (r : Fin (2 ^ D) → ℝ) (U : ℝ)
    (φ : Answer (2 ^ D) → ℝ) : ℝ :=
  let Etil := estE D G r
  if 2 * Etil > U then φ Answer.fail
  else (1 - 2 * Etil / U) * φ Answer.bot +
    2 * Etil / U * walkExp G Etil r φ (D - skKappa D) D 0 1

/-- The law of the sketch: independent standard Gaussian entries, p.45. -/
noncomputable def sketchLaw (k n : ℕ) : Measure (Fin k × Fin n → ℝ) :=
  Measure.pi fun _ => gaussianReal 0 1

/-- An operation of Lemma A.4: `Update(i, z'ᵢ)` or `Sample(U)`. -/
inductive Op (n : ℕ) where
  | update (i : Fin n) (w : ℝ)
  | sample (U : ℝ)

/-- A transcript: for each operation in order, `none` for an update and `some o` for a query with
answer `o`. -/
abbrev Transcript (n : ℕ) := List (Option (Answer n))

/-- An adaptive adversary, p.32 and p.47: its next operation is a function of the transcript so far
(newest first), or `none` to stop. By its type it sees neither `G` nor any internal draw. -/
abbrev Adversary (n : ℕ) := Transcript n → Option (Op n)

/-- `adv` meets the condition of Lemma A.4 for `m` further operations from the state `z` and the history
`hist`: each query satisfies `U ≥ 4‖r‖₂²`, along every sequence of answers other than `Fail`. -/
noncomputable def ValidAdv (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (adv : Adversary n) :
    ℕ → (Fin n → ℝ) → Transcript n → Prop
  | 0, _, _ => True
  | m + 1, z, hist =>
    match adv hist with
    | none => True
    | some (Op.update i w) => ValidAdv H h adv m (Function.update z i w) (none :: hist)
    | some (Op.sample U) =>
      4 * energyE (residual H h z) ≤ U ∧
        ∀ o, o ≠ Answer.fail → ValidAdv H h adv m z (some o :: hist)

/-- The probability that the data structure with the fixed sketch `G`, against `adv`, for `m` further
operations from the state `z` and the history `hist`, produces the remaining transcript `t`. -/
noncomputable def dsProb (D : ℕ) (G : Fin (skK D) × Fin (2 ^ D) → ℝ)
    (H : Matrix (Fin (2 ^ D)) (Fin (2 ^ D)) ℝ) (h : Fin (2 ^ D) → ℝ) (adv : Adversary (2 ^ D)) :
    ℕ → (Fin (2 ^ D) → ℝ) → Transcript (2 ^ D) → Transcript (2 ^ D) → ℝ
  | 0, _, _, t => if t = [] then 1 else 0
  | m + 1, z, hist, t =>
    match adv hist with
    | none => if t = [] then 1 else 0
    | some (Op.update i w) =>
      match t with
      | none :: t' => dsProb D G H h adv m (Function.update z i w) (none :: hist) t'
      | _ => 0
    | some (Op.sample U) =>
      match t with
      | some o :: t' =>
        sampleExp D G (residual H h z) U (fun o' => if o' = o then 1 else 0) *
          dsProb D G H h adv m z (some o :: hist) t'
      | _ => 0

/-- The answer law of the independent sampler, p.47: coordinate `i` with probability `rᵢ²/U`, `⊥` with
the remaining probability, and never `Fail`. -/
noncomputable def idealAnswer (r : Fin n → ℝ) (U : ℝ) : Answer n → ℝ
  | Answer.fail => 0
  | Answer.bot => 1 - energyE r / U
  | Answer.coord i => r i ^ 2 / U

/-- The probability that the independent sampler, against `adv`, for `m` further operations from the
state `z` and the history `hist`, produces the remaining transcript `t`. -/
noncomputable def idealProb (H : Matrix (Fin n) (Fin n) ℝ) (h : Fin n → ℝ) (adv : Adversary n) :
    ℕ → (Fin n → ℝ) → Transcript n → Transcript n → ℝ
  | 0, _, _, t => if t = [] then 1 else 0
  | m + 1, z, hist, t =>
    match adv hist with
    | none => if t = [] then 1 else 0
    | some (Op.update i w) =>
      match t with
      | none :: t' => idealProb H h adv m (Function.update z i w) (none :: hist) t'
      | _ => 0
    | some (Op.sample U) =>
      match t with
      | some o :: t' =>
        idealAnswer (residual H h z) U o * idealProb H h adv m z (some o :: hist) t'
      | _ => 0

end MatMulTimeLP


