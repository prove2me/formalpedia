-- Prove2me | Definitions.Def_DynOracleConn_Blocks
-- name    : DynOracleConn_Blocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:51:02.44754+00:00
-- url     : https://prove2.me/theorems/d0a3cdac-da37-481a-bce1-f58ed783c62e
-- title:
--   Blocks, red and blue intervals, checkpoints, and the constants of Corollaries 3.3 and 3.6
-- statement:
--   These are the objects of §3.2.1. Let $\ell=\lfloor d/(64B)\rfloor$. The first $64B$ intervals of $\ell$ consecutive slots alternate red and blue, giving $R_1,B_1,\dots,R_{32B},B_{32B}$. A block of $512B$ queries **occupies** a red interval if some queried item has its slot in it, and $\mathcal E$ is the event that at least $16B$ red intervals are occupied.
--
--   On $\mathcal E$, take the first $8B+1$ occupied red intervals, the earliest epoch mapped into each, and their slots $t_1<\dots<t_{8B+1}$. Set $P_k=\{t_k+1,\dots,t_{k+1}\}$ and
--
--   $$Y_k=\bigoplus_{j\in P_k}z_j.$$
--
--   The event **Y-correct** says each $Y_k$ is the xor of the two outputs at the corresponding epochs. For offsets $\Phi=(\phi_1,\dots,\phi_{8B})$, the **checkpoint** $u_k$ is the $\phi_k$-th slot of the blue interval following the red interval of $t_k$, and $H_c$ counts hit checkpoints.
--
--   `Cor33Holds` and `Cor36Holds` are the conclusions of Corollaries 3.3 and 3.6 as propositions in their constants, so later results can be stated "for $c_L$, $c_B$ according to" them. The stream of Corollary 3.6 has $512B\cdot4\lceil c_Bd/B\rceil$ epochs.
--
--   **Formalization Note** Everything is 0-based. Red interval $a$ is $[2a\ell,(2a+1)\ell)$ and blue interval $a$ is $[(2a+1)\ell,(2a+2)\ell)$. Off $\mathcal E$ the $k$-indexed objects take default values, and they are only used with $\mathcal E$ in the statements. Probabilities over uniform $(\pi,z)$, blocks and offsets are written as counts. The paper's "4c_Bd/B blocks" is rounded up to $4\lceil c_Bd/B\rceil$ so that the count is an integer and the $1/3$ Markov step stays exact.
-- source:
--   Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, Connectivity in a New Bounded-Space Dynamic Model, STOC 2027 submission (manuscript sha256 e9b19480…), §3.2.1, pp.21–22; Corollary 3.3, p.23; Corollary 3.6, p.25

import Mathlib
import Definitions.Def_DynOracleConn_PPHP

namespace DynOracleConn

/-!
# Blocks, red and blue intervals, checkpoints (§3.2.1) and the chained constants

Aryanfard, Henzinger, Kuszmaul, Nogler, Vassilevska Williams, *Connectivity in a New Bounded-Space
Dynamic Model*, STOC 2027 submission (manuscript sha256 e9b19480…), §3.2.1, pp.20–22:

"Assume B ≤ d/128 is an integer and let ℓ := ⌊d/(64B)⌋ ≥ d/(128B). Now, partition the input stream
into blocks of 512B epochs each … Partition the slots [d] into intervals of ℓ consecutive slots.
Color the first 64B ≥ d/(2ℓ) intervals alternately red and blue, starting with red, resulting in
intervals R1, B1, R2, B2, . . . , R32B, B32B, each of length ℓ. … We call a red interval Ra occupied if
for some I_k ∈ Iᵗ, π(I_k) ∈ Ra, and empty otherwise. … Let ℰ be the event that at least 16B red
intervals (i.e., at least half of them) are occupied. … On ℰ, take the first 8B + 1 occupied red
intervals, take the earliest epoch whose queried item lies in each of them, and let the slots of
these items be t1 < t2 < . . . < t8B+1. For every k ∈ [8B], let Pk = {tk + 1, . . . , tk+1}. … we can
calculate Yk = ⊕_{j∈Pk} zj … If tk ∈ Rq, let uk be the ϕk-th slot of Bq. Call these points
checkpoints."

**Formalization Note.**
1. Everything is 0-based. Slots are natural numbers `< d`; red interval `a < 32B` is
   `[2aℓ, (2a+1)ℓ)` and blue interval `a` is `[(2a+1)ℓ, (2a+2)ℓ)`; the checkpoint of blue
   interval `a` with offset `φ < ℓ` is `(2a+1)ℓ + φ`. A block is `I : Fin (512B) → Fin d`.
2. `occupiedList` lists the occupied red intervals in increasing order; `q k` is the `k`-th of
   them, `firstEpoch k` the earliest epoch of the block mapped into red interval `q k`, and
   `tslot k` its slot (`t_{k+1}` of the paper). These are meaningful on `EventE`, which guarantees
   `8B + 1` occupied red intervals when `B ≥ 1`; off `EventE` they take default values.
3. A block algorithm's output is a function `Fin (512B) → Bool`; `outAt` reads it at a natural
   index. `YCorrect` is the paper's "Y-correct": for every `k < 8B` the xor of the outputs at the
   epochs `firstEpoch k` and `firstEpoch (k+1)` equals `Y_k`.
4. `Cor33Holds cL η` is the conclusion of Corollary 3.3 for given constants, `Cor36Holds cL η cB`
   that of Corollary 3.6; later results are stated "for c_L, c_B according to Corollary 3.3/3.6"
   by assuming these. `Cor33Holds` has the printed range `10 ≤ B ≤ ηd`; `Cor36Holds` also carries
   the section's standing `B ≤ d/128` (§3.2.1, p.21). Probabilities over uniform `(π, z)`, `I`, `Φ`
   are written as counts:
   `P[E] ≤ p` becomes `#E ≤ p · (number of outcomes)`.
5. Corollary 3.6 uses `4⌈c_B d/B⌉` blocks (the paper writes `4c_B d/B`), so the stream has
   `numEpochs cB d B = 512B · 4⌈c_B d/B⌉` epochs.
-/

/-- `ℓ = ⌊d / (64B)⌋`, the length of the red and blue intervals. -/
def ell (d B : ℕ) : ℕ := d / (64 * B)

/-- Slot `j` lies in red interval `a`, i.e. in `[2aℓ, (2a+1)ℓ)`. -/
def InRed (d B a j : ℕ) : Prop := 2 * a * ell d B ≤ j ∧ j < (2 * a + 1) * ell d B

instance (d B a j : ℕ) : Decidable (InRed d B a j) := by unfold InRed; infer_instance

/-- The `φ`-th slot (0-based) of blue interval `a`: `(2a+1)ℓ + φ`. -/
def checkpointAt (d B a φ : ℕ) : ℕ := (2 * a + 1) * ell d B + φ

/-- Red interval `a` is occupied by the block `I`: some epoch of the block is mapped into it. -/
def Occupied (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) (a : ℕ) : Prop :=
  ∃ m, InRed d B a (π (I m)).val

instance (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) (a : ℕ) :
    Decidable (Occupied d B π I a) := by unfold Occupied; infer_instance

/-- The occupied red intervals among the `32B` red intervals, in increasing order. -/
def occupiedList (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) : List ℕ :=
  (List.range (32 * B)).filter (fun a => decide (Occupied d B π I a))

/-- The event ℰ: at least `16B` red intervals are occupied. -/
def EventE (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) : Prop :=
  16 * B ≤ (occupiedList d B π I).length

/-- The `k`-th occupied red interval (0-based; `0` if there is none). -/
def qInt (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) (k : ℕ) : ℕ :=
  (occupiedList d B π I).getD k 0

/-- The earliest epoch of the block whose queried item lies in red interval `qInt k`
(`512B` if there is none). -/
def firstEpoch (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) (k : ℕ) : ℕ :=
  (List.finRange (512 * B)).findIdx (fun m => decide (InRed d B (qInt d B π I k) (π (I m)).val))

/-- The slot of that epoch's item (the paper's `t_{k+1}`, 0-based `k`). -/
def tslot (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d) (k : ℕ) : ℕ :=
  if h : firstEpoch d B π I k < 512 * B then (π (I ⟨firstEpoch d B π I k, h⟩)).val else 0

/-- `Y_k = ⊕_{j ∈ P_k} z_j` with `P_k = {t_k + 1, …, t_{k+1}}` (0-based `k`). -/
def Yk (d B : ℕ) (X : PPHPInst d) (I : Fin (512 * B) → Fin d) (k : ℕ) : Bool :=
  parity X.2 (Finset.univ.filter (fun j : Fin d =>
    tslot d B X.1 I k < j.val ∧ j.val ≤ tslot d B X.1 I (k + 1)))

/-- The output of a block at epoch index `m` (`false` out of range). -/
def outAt {N : ℕ} (out : Fin N → Bool) (m : ℕ) : Bool :=
  if h : m < N then out ⟨m, h⟩ else false

/-- "Y-correct": for every `k < 8B`, the xor of the outputs at the epochs of `t_k` and `t_{k+1}`
equals `Y_k`. -/
def YCorrect (d B : ℕ) (X : PPHPInst d) (I : Fin (512 * B) → Fin d)
    (out : Fin (512 * B) → Bool) : Prop :=
  ∀ k < 8 * B, xor (outAt out (firstEpoch d B X.1 I k)) (outAt out (firstEpoch d B X.1 I (k + 1)))
    = Yk d B X I k

/-- The checkpoint `u_k`: the `Φ k`-th slot of the blue interval following red interval `qInt k`. -/
def checkpoint (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d)
    (Φ : Fin (8 * B) → Fin (ell d B)) (k : Fin (8 * B)) : ℕ :=
  checkpointAt d B (qInt d B π I k.val) (Φ k).val

/-- `H_c`: the number of checkpoints lying in the set `W` of hit slots. -/
def numHitCheckpoints (d B : ℕ) (π : Equiv.Perm (Fin d)) (I : Fin (512 * B) → Fin d)
    (Φ : Fin (8 * B) → Fin (ell d B)) (W : Finset ℕ) : ℕ :=
  (Finset.univ.filter (fun k => checkpoint d B π I Φ k ∈ W)).card

/-- "correct" for a block: every output equals `y_{I_m}`. -/
def BlockCorrect {d N : ℕ} (X : PPHPInst d) (I : Fin N → Fin d) (out : Fin N → Bool) : Prop :=
  ∀ m, out m = yval X (I m)

/-- The conclusion of Corollary 3.3 for the constants `cL, η`: for `10 ≤ B ≤ ηd`, every algorithm
that receives a `B`-bit advice `M(π, z)` and probes `P_X` has `P_{π,z}[L < c_L d² ∧ high-hit] < 1/16`, where high-hit means `H > Bℓ/32`. -/
def Cor33Holds (cL η : ℝ) : Prop :=
  ∀ d B : ℕ, 10 ≤ B → (B : ℝ) ≤ η * d →
  ∀ (Adv : Type) [Fintype Adv], Fintype.card Adv ≤ 2 ^ B →
  ∀ (R : Type) (M : PPHPInst d → Adv) (alg : Adv → PPHPTree d R),
    (Set.ncard {X : PPHPInst d |
        (((alg (M X)).cost (pOracle X) : ℕ) : ℝ) < cL * (d : ℝ) ^ 2 ∧
        (B : ℝ) * (ell d B : ℝ) / 32 < (numHits (alg (M X)) X : ℝ)} : ℝ)
      < ((d.factorial : ℝ) * 2 ^ d) / 16

/-- The number of epochs of Corollary 3.6's stream: `4⌈c_B d/B⌉` blocks of `512B` epochs. -/
noncomputable def numEpochs (cB : ℝ) (d B : ℕ) : ℕ :=
  512 * B * (4 * ⌈cB * (d : ℝ) / (B : ℝ)⌉₊)

/-- The conclusion of Corollary 3.6 for the constants `cL, η, cB`: for `10 ≤ B ≤ ηd` (and the
standing `B ≤ d/128`), every deterministic stream algorithm with at most `2^B` states satisfies
`P_{π,z,ℐ}[correct_total ∧ L_total ≤ c_B c_L d³/B] ≤ 1/3` on a stream of `numEpochs cB d B`
uniform queries. -/
def Cor36Holds (cL η cB : ℝ) : Prop :=
  ∀ d B : ℕ, 10 ≤ B → 128 * B ≤ d → (B : ℝ) ≤ η * d →
  ∀ (S : Type) [Fintype S], Fintype.card S ≤ 2 ^ B → ∀ A : PPHPAlg d S,
    (Set.ncard {p : PPHPInst d × (Fin (numEpochs cB d B) → Fin d) |
        A.correctTotal p.1 (List.ofFn p.2) ∧
        (A.Ltotal p.1 (List.ofFn p.2) : ℝ) ≤ cB * cL * (d : ℝ) ^ 3 / B} : ℝ)
      ≤ (1 / 3 : ℝ) * ((d.factorial : ℝ) * 2 ^ d * (d : ℝ) ^ numEpochs cB d B)

end DynOracleConn


